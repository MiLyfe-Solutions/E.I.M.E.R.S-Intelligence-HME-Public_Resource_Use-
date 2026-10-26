import V185TrunkScan23Chunk0926

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5487269 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_5487269 : Nat := 118140960795 + 5487269 * 2 ^ 59
def prefixEnd_5487269 : Nat := 4983230072969 + 3 ^ 40 * 5487269 * 2
def baseEnd_5487269 : Nat := 2817606477516196768502015

theorem tailTrace_5487269 : CollatzResearch.WordTrace tailWord_5487269 prefixEnd_5487269 2817606477516196768502015 := by
  unfold tailWord_5487269
  simp only [CollatzResearch.WordTrace]
  refine ⟨200137142357569038779912861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133424761571712692519941907 200137142357569038779912861)
  ·
    refine ⟨75051428384088389542467323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200137142357569038779912861 75051428384088389542467323)
    ·
      refine ⟨112577142576132584313700985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75051428384088389542467323 112577142576132584313700985)
      ·
        refine ⟨84432856932099438235275739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112577142576132584313700985 84432856932099438235275739)
        ·
          refine ⟨126649285398149157352913609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84432856932099438235275739 126649285398149157352913609)
          ·
            refine ⟨94986964048611868014685207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126649285398149157352913609 94986964048611868014685207)
            ·
              refine ⟨142480446072917802022027811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94986964048611868014685207 142480446072917802022027811)
              ·
                refine ⟨213720669109376703033041717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142480446072917802022027811 213720669109376703033041717)
                ·
                  refine ⟨20036312729004065909347661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213720669109376703033041717 20036312729004065909347661)
                  ·
                    refine ⟨7513617273376524716005373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20036312729004065909347661 7513617273376524716005373)
                    ·
                      refine ⟨2817606477516196768502015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513617273376524716005373 2817606477516196768502015)
                      ·
                        rfl

theorem cell23_5487269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_5487269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487269 prefixEnd_5487269 := by exact prefixLift 5487269
  have htrace : WordTrace (prefixWord ++ tailWord_5487269) baseStart_5487269 baseEnd_5487269 := by
    simpa [prefixWord, tailWord_5487269, baseEnd_5487269] using wordTrace_append hprefix tailTrace_5487269
  have hstable : (prefixWord ++ tailWord_5487269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487269).length < 2 ^ (prefixWord ++ tailWord_5487269).sum := by decide
  have hdescent : baseEnd_5487269 < baseStart_5487269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487313 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_5487313 : Nat := 118140960795 + 5487313 * 2 ^ 59
def prefixEnd_5487313 : Nat := 4983230072969 + 3 ^ 40 * 5487313 * 2
def baseEnd_5487313 : Nat := 2817629070664994596351813

theorem tailTrace_5487313 : CollatzResearch.WordTrace tailWord_5487313 prefixEnd_5487313 2817629070664994596351813 := by
  unfold tailWord_5487313
  simp only [CollatzResearch.WordTrace]
  refine ⟨200138747169409634294514593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133425831446273089529676395 200138747169409634294514593)
  ·
    refine ⟨150104060377057225720885945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200138747169409634294514593 150104060377057225720885945)
    ·
      refine ⟨112578045282792919290664459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150104060377057225720885945 112578045282792919290664459)
      ·
        refine ⟨168867067924189378935996689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112578045282792919290664459 168867067924189378935996689)
        ·
          refine ⟨126650300943142034201997517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168867067924189378935996689 126650300943142034201997517)
          ·
            refine ⟨47493862853678262825749069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126650300943142034201997517 47493862853678262825749069)
            ·
              refine ⟨17810198570129348559655901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47493862853678262825749069 17810198570129348559655901)
              ·
                refine ⟨6678824463798505709870963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17810198570129348559655901 6678824463798505709870963)
                ·
                  refine ⟨10018236695697758564806445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6678824463798505709870963 10018236695697758564806445)
                  ·
                    refine ⟨3756838760886659461802417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10018236695697758564806445 3756838760886659461802417)
                    ·
                      refine ⟨2817629070664994596351813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756838760886659461802417 2817629070664994596351813)
                      ·
                        rfl

theorem cell23_5487313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_5487313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487313 prefixEnd_5487313 := by exact prefixLift 5487313
  have htrace : WordTrace (prefixWord ++ tailWord_5487313) baseStart_5487313 baseEnd_5487313 := by
    simpa [prefixWord, tailWord_5487313, baseEnd_5487313] using wordTrace_append hprefix tailTrace_5487313
  have hstable : (prefixWord ++ tailWord_5487313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487313).length < 2 ^ (prefixWord ++ tailWord_5487313).sum := by decide
  have hdescent : baseEnd_5487313 < baseStart_5487313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487319 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 2, 6]
def baseStart_5487319 : Nat := 118140960795 + 5487319 * 2 ^ 59
def prefixEnd_5487319 : Nat := 4983230072969 + 3 ^ 40 * 5487319 * 2
def baseEnd_5487319 : Nat := 939210717182973857625595

theorem tailTrace_5487319 : CollatzResearch.WordTrace tailWord_5487319 prefixEnd_5487319 939210717182973857625595 := by
  unfold tailWord_5487319
  simp only [CollatzResearch.WordTrace]
  refine ⟨200138966007387897319233011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133425977338258598212822007 200138966007387897319233011)
  ·
    refine ⟨300208449011081845978849517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200138966007387897319233011 300208449011081845978849517)
    ·
      refine ⟨112578168379155692242068569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300208449011081845978849517 112578168379155692242068569)
      ·
        refine ⟨84433626284366769181551427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112578168379155692242068569 84433626284366769181551427)
        ·
          refine ⟨126650439426550153772327141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84433626284366769181551427 126650439426550153772327141)
          ·
            refine ⟨23746957392478153832311339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126650439426550153772327141 23746957392478153832311339)
            ·
              refine ⟨35620436088717230748467009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23746957392478153832311339 35620436088717230748467009)
              ·
                refine ⟨26715327066537923061350257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35620436088717230748467009 26715327066537923061350257)
                ·
                  refine ⟨20036495299903442296012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26715327066537923061350257 20036495299903442296012693)
                  ·
                    refine ⟨939210717182973857625595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20036495299903442296012693 939210717182973857625595)
                    ·
                      rfl

theorem cell23_5487319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_5487319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487319 prefixEnd_5487319 := by exact prefixLift 5487319
  have htrace : WordTrace (prefixWord ++ tailWord_5487319) baseStart_5487319 baseEnd_5487319 := by
    simpa [prefixWord, tailWord_5487319, baseEnd_5487319] using wordTrace_append hprefix tailTrace_5487319
  have hstable : (prefixWord ++ tailWord_5487319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487319).length < 2 ^ (prefixWord ++ tailWord_5487319).sum := by decide
  have hdescent : baseEnd_5487319 < baseStart_5487319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487320 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_5487320 : Nat := 118140960795 + 5487320 * 2 ^ 59
def prefixEnd_5487320 : Nat := 4983230072969 + 3 ^ 40 * 5487320 * 2
def baseEnd_5487320 : Nat := 2817632665029576068964281

theorem tailTrace_5487320 : CollatzResearch.WordTrace tailWord_5487320 prefixEnd_5487320 2817632665029576068964281 := by
  unfold tailWord_5487320
  simp only [CollatzResearch.WordTrace]
  refine ⟨100069501240192137245009707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133426001653589516326679609 100069501240192137245009707)
  ·
    refine ⟨150104251860288205867514561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100069501240192137245009707 150104251860288205867514561)
    ·
      refine ⟨112578188895216154400635921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150104251860288205867514561 112578188895216154400635921)
      ·
        refine ⟨84433641671412115800476941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112578188895216154400635921 84433641671412115800476941)
        ·
          refine ⟨31662615626779543425178853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84433641671412115800476941 31662615626779543425178853)
          ·
            refine ⟨5936740430021164392221035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31662615626779543425178853 5936740430021164392221035)
            ·
              refine ⟨8905110645031746588331553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936740430021164392221035 8905110645031746588331553)
              ·
                refine ⟨6678832983773809941248665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8905110645031746588331553 6678832983773809941248665)
                ·
                  refine ⟨5009124737830357455936499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678832983773809941248665 5009124737830357455936499)
                  ·
                    refine ⟨7513687106745536183904749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009124737830357455936499 7513687106745536183904749)
                    ·
                      refine ⟨2817632665029576068964281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513687106745536183904749 2817632665029576068964281)
                      ·
                        rfl

theorem cell23_5487320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_5487320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487320 prefixEnd_5487320 := by exact prefixLift 5487320
  have htrace : WordTrace (prefixWord ++ tailWord_5487320) baseStart_5487320 baseEnd_5487320 := by
    simpa [prefixWord, tailWord_5487320, baseEnd_5487320] using wordTrace_append hprefix tailTrace_5487320
  have hstable : (prefixWord ++ tailWord_5487320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487320).length < 2 ^ (prefixWord ++ tailWord_5487320).sum := by decide
  have hdescent : baseEnd_5487320 < baseStart_5487320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487343 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 1, 4, 2]
def baseStart_5487343 : Nat := 118140960795 + 5487343 * 2 ^ 59
def prefixEnd_5487343 : Nat := 4983230072969 + 3 ^ 40 * 5487343 * 2
def baseEnd_5487343 : Nat := 2817644475084629478976675

theorem tailTrace_5487343 : CollatzResearch.WordTrace tailWord_5487343 prefixEnd_5487343 2817644475084629478976675 := by
  unfold tailWord_5487343
  simp only [CollatzResearch.WordTrace]
  refine ⟨200139841359300949418106683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133426560906200632945404455 200139841359300949418106683)
  ·
    refine ⟨300209762038951424127160025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200139841359300949418106683 300209762038951424127160025)
    ·
      refine ⟨225157321529213568095370019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300209762038951424127160025 225157321529213568095370019)
      ·
        refine ⟨337735982293820352143055029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225157321529213568095370019 337735982293820352143055029)
        ·
          refine ⟨31662748340045658013411409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 337735982293820352143055029 31662748340045658013411409)
          ·
            refine ⟨23747061255034243510058557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31662748340045658013411409 23747061255034243510058557)
            ·
              refine ⟨8905147970637841316271959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23747061255034243510058557 8905147970637841316271959)
              ·
                refine ⟨13357721955956761974407939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8905147970637841316271959 13357721955956761974407939)
                ·
                  refine ⟨20036582933935142961611909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13357721955956761974407939 20036582933935142961611909)
                  ·
                    refine ⟨3756859300112839305302233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20036582933935142961611909 3756859300112839305302233)
                    ·
                      refine ⟨2817644475084629478976675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756859300112839305302233 2817644475084629478976675)
                      ·
                        rfl

theorem cell23_5487343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4, 2].length) (baseStart_5487343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487343 prefixEnd_5487343 := by exact prefixLift 5487343
  have htrace : WordTrace (prefixWord ++ tailWord_5487343) baseStart_5487343 baseEnd_5487343 := by
    simpa [prefixWord, tailWord_5487343, baseEnd_5487343] using wordTrace_append hprefix tailTrace_5487343
  have hstable : (prefixWord ++ tailWord_5487343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487343).length < 2 ^ (prefixWord ++ tailWord_5487343).sum := by decide
  have hdescent : baseEnd_5487343 < baseStart_5487343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487383 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 7]
def baseStart_5487383 : Nat := 118140960795 + 5487383 * 2 ^ 59
def prefixEnd_5487383 : Nat := 4983230072969 + 3 ^ 40 * 5487383 * 2
def baseEnd_5487383 : Nat := 313073890478978813608499

theorem tailTrace_5487383 : CollatzResearch.WordTrace tailWord_5487383 prefixEnd_5487383 313073890478978813608499 := by
  unfold tailWord_5487383
  simp only [CollatzResearch.WordTrace]
  refine ⟨200141300279156036249562803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133427533519437357499708535 200141300279156036249562803)
  ·
    refine ⟨300211950418734054374344205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200141300279156036249562803 300211950418734054374344205)
    ·
      refine ⟨112579481407025270390379077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300211950418734054374344205 112579481407025270390379077)
      ·
        refine ⟨21108652763817238198196077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112579481407025270390379077 21108652763817238198196077)
        ·
          refine ⟨7915744786431464324323529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21108652763817238198196077 7915744786431464324323529)
          ·
            refine ⟨5936808589823598243242647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7915744786431464324323529 5936808589823598243242647)
            ·
              refine ⟨8905212884735397364863971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936808589823598243242647 8905212884735397364863971)
              ·
                refine ⟨13357819327103096047295957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8905212884735397364863971 13357819327103096047295957)
                ·
                  refine ⟨313073890478978813608499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13357819327103096047295957 313073890478978813608499)
                  ·
                    rfl

theorem cell23_5487383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 7].length) (baseStart_5487383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487383 prefixEnd_5487383 := by exact prefixLift 5487383
  have htrace : WordTrace (prefixWord ++ tailWord_5487383) baseStart_5487383 baseEnd_5487383 := by
    simpa [prefixWord, tailWord_5487383, baseEnd_5487383] using wordTrace_append hprefix tailTrace_5487383
  have hstable : (prefixWord ++ tailWord_5487383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487383).length < 2 ^ (prefixWord ++ tailWord_5487383).sum := by decide
  have hdescent : baseEnd_5487383 < baseStart_5487383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487394 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_5487394 : Nat := 118140960795 + 5487394 * 2 ^ 59
def prefixEnd_5487394 : Nat := 4983230072969 + 3 ^ 40 * 5487394 * 2
def baseEnd_5487394 : Nat := 2817670662598008779438941

theorem tailTrace_5487394 : CollatzResearch.WordTrace tailWord_5487394 prefixEnd_5487394 2817670662598008779438941 := by
  unfold tailWord_5487394
  simp only [CollatzResearch.WordTrace]
  refine ⟨50035425370529046282053309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133427800988077456752142157 50035425370529046282053309)
  ·
    refine ⟨18763284513948392355769991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50035425370529046282053309 18763284513948392355769991)
    ·
      refine ⟨28144926770922588533654987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763284513948392355769991 28144926770922588533654987)
      ·
        refine ⟨42217390156383882800482481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28144926770922588533654987 42217390156383882800482481)
        ·
          refine ⟨31663042617287912100361861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42217390156383882800482481 31663042617287912100361861)
          ·
            refine ⟨5936820490741483518817849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31663042617287912100361861 5936820490741483518817849)
            ·
              refine ⟨4452615368056112639113387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936820490741483518817849 4452615368056112639113387)
              ·
                refine ⟨6678923052084168958670081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452615368056112639113387 6678923052084168958670081)
                ·
                  refine ⟨5009192289063126719002561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678923052084168958670081 5009192289063126719002561)
                  ·
                    refine ⟨3756894216797345039251921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5009192289063126719002561 3756894216797345039251921)
                    ·
                      refine ⟨2817670662598008779438941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756894216797345039251921 2817670662598008779438941)
                      ·
                        rfl

theorem cell23_5487394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_5487394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487394 prefixEnd_5487394 := by exact prefixLift 5487394
  have htrace : WordTrace (prefixWord ++ tailWord_5487394) baseStart_5487394 baseEnd_5487394 := by
    simpa [prefixWord, tailWord_5487394, baseEnd_5487394] using wordTrace_append hprefix tailTrace_5487394
  have hstable : (prefixWord ++ tailWord_5487394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487394).length < 2 ^ (prefixWord ++ tailWord_5487394).sum := by decide
  have hdescent : baseEnd_5487394 < baseStart_5487394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487413 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_5487413 : Nat := 118140960795 + 5487413 * 2 ^ 59
def prefixEnd_5487413 : Nat := 4983230072969 + 3 ^ 40 * 5487413 * 2
def baseEnd_5487413 : Nat := 939226806243481401700451

theorem tailTrace_5487413 : CollatzResearch.WordTrace tailWord_5487413 prefixEnd_5487413 939226806243481401700451 := by
  unfold tailWord_5487413
  simp only [CollatzResearch.WordTrace]
  refine ⟨200142394469047351373154893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133428262979364900915436595 200142394469047351373154893)
  ·
    refine ⟨75053397925892756764933085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200142394469047351373154893 75053397925892756764933085)
    ·
      refine ⟨28145024222209783786849907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75053397925892756764933085 28145024222209783786849907)
      ·
        refine ⟨42217536333314675680274861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28145024222209783786849907 42217536333314675680274861)
        ·
          refine ⟨15831576124993003380103073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42217536333314675680274861 15831576124993003380103073)
          ·
            refine ⟨11873682093744752535077305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15831576124993003380103073 11873682093744752535077305)
            ·
              refine ⟨8905261570308564401307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11873682093744752535077305 8905261570308564401307979)
              ·
                refine ⟨13357892355462846601961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8905261570308564401307979 13357892355462846601961969)
                ·
                  refine ⟨10018419266597134951471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13357892355462846601961969 10018419266597134951471477)
                  ·
                    refine ⟨939226806243481401700451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10018419266597134951471477 939226806243481401700451)
                    ·
                      rfl

theorem cell23_5487413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_5487413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487413 prefixEnd_5487413 := by exact prefixLift 5487413
  have htrace : WordTrace (prefixWord ++ tailWord_5487413) baseStart_5487413 baseEnd_5487413 := by
    simpa [prefixWord, tailWord_5487413, baseEnd_5487413] using wordTrace_append hprefix tailTrace_5487413
  have hstable : (prefixWord ++ tailWord_5487413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487413).length < 2 ^ (prefixWord ++ tailWord_5487413).sum := by decide
  have hdescent : baseEnd_5487413 < baseStart_5487413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487456 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 6]
def baseStart_5487456 : Nat := 118140960795 + 5487456 * 2 ^ 59
def prefixEnd_5487456 : Nat := 4983230072969 + 3 ^ 40 * 5487456 * 2
def baseEnd_5487456 : Nat := 313078055377620837429295

theorem tailTrace_5487456 : CollatzResearch.WordTrace tailWord_5487456 prefixEnd_5487456 313078055377620837429295 := by
  unfold tailWord_5487456
  simp only [CollatzResearch.WordTrace]
  refine ⟨100071981403945784858485111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133429308538594379811313481 100071981403945784858485111)
  ·
    refine ⟨150107972105918677287727667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100071981403945784858485111 150107972105918677287727667)
    ·
      refine ⟨225161958158878015931591501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150107972105918677287727667 225161958158878015931591501)
      ·
        refine ⟨84435734309579255974346813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225161958158878015931591501 84435734309579255974346813)
        ·
          refine ⟨31663400366092220990380055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84435734309579255974346813 31663400366092220990380055)
          ·
            refine ⟨47495100549138331485570083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31663400366092220990380055 47495100549138331485570083)
            ·
              refine ⟨71242650823707497228355125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47495100549138331485570083 71242650823707497228355125)
              ·
                refine ⟨6678998514722577865158293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71242650823707497228355125 6678998514722577865158293)
                ·
                  refine ⟨313078055377620837429295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6678998514722577865158293 313078055377620837429295)
                  ·
                    rfl

theorem cell23_5487456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_5487456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487456 prefixEnd_5487456 := by exact prefixLift 5487456
  have htrace : WordTrace (prefixWord ++ tailWord_5487456) baseStart_5487456 baseEnd_5487456 := by
    simpa [prefixWord, tailWord_5487456, baseEnd_5487456] using wordTrace_append hprefix tailTrace_5487456
  have hstable : (prefixWord ++ tailWord_5487456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487456).length < 2 ^ (prefixWord ++ tailWord_5487456).sum := by decide
  have hdescent : baseEnd_5487456 < baseStart_5487456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487470 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_5487470 : Nat := 118140960795 + 5487470 * 2 ^ 59
def prefixEnd_5487470 : Nat := 4983230072969 + 3 ^ 40 * 5487470 * 2
def baseEnd_5487470 : Nat := 2817709687127750482088591

theorem tailTrace_5487470 : CollatzResearch.WordTrace tailWord_5487470 prefixEnd_5487470 2817709687127750482088591 := by
  unfold tailWord_5487470
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018059178730106263497483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133429648953227233405319909 25018059178730106263497483)
  ·
    refine ⟨37527088768095159395246225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25018059178730106263497483 37527088768095159395246225)
    ·
      refine ⟨28145316576071369546434669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37527088768095159395246225 28145316576071369546434669)
      ·
        refine ⟨10554493716026763579913001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28145316576071369546434669 10554493716026763579913001)
        ·
          refine ⟨7915870287020072684934751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10554493716026763579913001 7915870287020072684934751)
          ·
            refine ⟨11873805430530109027402127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7915870287020072684934751 11873805430530109027402127)
            ·
              refine ⟨17810708145795163541103191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11873805430530109027402127 17810708145795163541103191)
              ·
                refine ⟨26716062218692745311654787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17810708145795163541103191 26716062218692745311654787)
                ·
                  refine ⟨40074093328039117967482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26716062218692745311654787 40074093328039117967482181)
                  ·
                    refine ⟨7513892499007334618902909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40074093328039117967482181 7513892499007334618902909)
                    ·
                      refine ⟨2817709687127750482088591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513892499007334618902909 2817709687127750482088591)
                      ·
                        rfl

theorem cell23_5487470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_5487470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487470 prefixEnd_5487470 := by exact prefixLift 5487470
  have htrace : WordTrace (prefixWord ++ tailWord_5487470) baseStart_5487470 baseEnd_5487470 := by
    simpa [prefixWord, tailWord_5487470, baseEnd_5487470] using wordTrace_append hprefix tailTrace_5487470
  have hstable : (prefixWord ++ tailWord_5487470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487470).length < 2 ^ (prefixWord ++ tailWord_5487470).sum := by decide
  have hdescent : baseEnd_5487470 < baseStart_5487470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487477 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5487477 : Nat := 118140960795 + 5487477 * 2 ^ 59
def prefixEnd_5487477 : Nat := 4983230072969 + 3 ^ 40 * 5487477 * 2
def baseEnd_5487477 : Nat := 939237760497443984900353

theorem tailTrace_5487477 : CollatzResearch.WordTrace tailWord_5487477 prefixEnd_5487477 939237760497443984900353 := by
  unfold tailWord_5487477
  simp only [CollatzResearch.WordTrace]
  refine ⟨200144728740815490303484685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133429819160543660202323123 200144728740815490303484685)
  ·
    refine ⟨75054273277805808863806757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200144728740815490303484685 75054273277805808863806757)
    ·
      refine ⟨14072676239588589161963767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75054273277805808863806757 14072676239588589161963767)
      ·
        refine ⟨21109014359382883742945651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072676239588589161963767 21109014359382883742945651)
        ·
          refine ⟨31663521539074325614418477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21109014359382883742945651 31663521539074325614418477)
          ·
            refine ⟨11873820577152872105406929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31663521539074325614418477 11873820577152872105406929)
            ·
              refine ⟨8905365432864654079055197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11873820577152872105406929 8905365432864654079055197)
              ·
                refine ⟨3339512037324245279645699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8905365432864654079055197 3339512037324245279645699)
                ·
                  refine ⟨5009268055986367919468549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339512037324245279645699 5009268055986367919468549)
                  ·
                    refine ⟨939237760497443984900353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009268055986367919468549 939237760497443984900353)
                    ·
                      rfl

theorem cell23_5487477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5487477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487477 prefixEnd_5487477 := by exact prefixLift 5487477
  have htrace : WordTrace (prefixWord ++ tailWord_5487477) baseStart_5487477 baseEnd_5487477 := by
    simpa [prefixWord, tailWord_5487477, baseEnd_5487477] using wordTrace_append hprefix tailTrace_5487477
  have hstable : (prefixWord ++ tailWord_5487477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487477).length < 2 ^ (prefixWord ++ tailWord_5487477).sum := by decide
  have hdescent : baseEnd_5487477 < baseStart_5487477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487523 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 4]
def baseStart_5487523 : Nat := 118140960795 + 5487523 * 2 ^ 59
def prefixEnd_5487523 : Nat := 4983230072969 + 3 ^ 40 * 5487523 * 2
def baseEnd_5487523 : Nat := 2817736901602438774725847

theorem tailTrace_5487523 : CollatzResearch.WordTrace tailWord_5487523 prefixEnd_5487523 2817736901602438774725847 := by
  unfold tailWord_5487523
  simp only [CollatzResearch.WordTrace]
  refine ⟨200146406498648840159659223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133430937665765893439772815 200146406498648840159659223)
  ·
    refine ⟨300219609747973260239488835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200146406498648840159659223 300219609747973260239488835)
    ·
      refine ⟨450329414621959890359233253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300219609747973260239488835 450329414621959890359233253)
      ·
        refine ⟨84436765241617479442356235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 450329414621959890359233253 84436765241617479442356235)
        ·
          refine ⟨126655147862426219163534353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84436765241617479442356235 126655147862426219163534353)
          ·
            refine ⟨94991360896819664372650765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126655147862426219163534353 94991360896819664372650765)
            ·
              refine ⟨35621760336307374139744037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94991360896819664372650765 35621760336307374139744037)
              ·
                refine ⟨6679080063057632651202007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35621760336307374139744037 6679080063057632651202007)
                ·
                  refine ⟨10018620094586448976803011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679080063057632651202007 10018620094586448976803011)
                  ·
                    refine ⟨15027930141879673465204517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10018620094586448976803011 15027930141879673465204517)
                    ·
                      refine ⟨2817736901602438774725847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15027930141879673465204517 2817736901602438774725847)
                      ·
                        rfl

theorem cell23_5487523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_5487523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487523 prefixEnd_5487523 := by exact prefixLift 5487523
  have htrace : WordTrace (prefixWord ++ tailWord_5487523) baseStart_5487523 baseEnd_5487523 := by
    simpa [prefixWord, tailWord_5487523, baseEnd_5487523] using wordTrace_append hprefix tailTrace_5487523
  have hstable : (prefixWord ++ tailWord_5487523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487523).length < 2 ^ (prefixWord ++ tailWord_5487523).sum := by decide
  have hdescent : baseEnd_5487523 < baseStart_5487523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487550 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_5487550 : Nat := 118140960795 + 5487550 * 2 ^ 59
def prefixEnd_5487550 : Nat := 4983230072969 + 3 ^ 40 * 5487550 * 2
def baseEnd_5487550 : Nat := 939250255193370056362741

theorem tailTrace_5487550 : CollatzResearch.WordTrace tailWord_5487550 prefixEnd_5487550 939250255193370056362741 := by
  unfold tailWord_5487550
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018423908693877971361513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133431594179700682513928069 25018423908693877971361513)
  ·
    refine ⟨18763817931520408478521135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25018423908693877971361513 18763817931520408478521135)
    ·
      refine ⟨28145726897280612717781703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763817931520408478521135 28145726897280612717781703)
      ·
        refine ⟨42218590345920919076672555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28145726897280612717781703 42218590345920919076672555)
        ·
          refine ⟨63327885518881378615008833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42218590345920919076672555 63327885518881378615008833)
          ·
            refine ⟨47495914139161033961256625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63327885518881378615008833 47495914139161033961256625)
            ·
              refine ⟨35621935604370775470942469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47495914139161033961256625 35621935604370775470942469)
              ·
                refine ⟨6679112925819520400801713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35621935604370775470942469 6679112925819520400801713)
                ·
                  refine ⟨5009334694364640300601285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679112925819520400801713 5009334694364640300601285)
                  ·
                    refine ⟨939250255193370056362741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009334694364640300601285 939250255193370056362741)
                    ·
                      rfl

theorem cell23_5487550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_5487550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487550 prefixEnd_5487550 := by exact prefixLift 5487550
  have htrace : WordTrace (prefixWord ++ tailWord_5487550) baseStart_5487550 baseEnd_5487550 := by
    simpa [prefixWord, tailWord_5487550, baseEnd_5487550] using wordTrace_append hprefix tailTrace_5487550
  have hstable : (prefixWord ++ tailWord_5487550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487550).length < 2 ^ (prefixWord ++ tailWord_5487550).sum := by decide
  have hdescent : baseEnd_5487550 < baseStart_5487550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487558 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_5487558 : Nat := 118140960795 + 5487558 * 2 ^ 59
def prefixEnd_5487558 : Nat := 4983230072969 + 3 ^ 40 * 5487558 * 2
def baseEnd_5487558 : Nat := 313083874825038459754243

theorem tailTrace_5487558 : CollatzResearch.WordTrace tailWord_5487558 prefixEnd_5487558 313083874825038459754243 := by
  unfold tailWord_5487558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254615095422563785536979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133431788702348027424788885 6254615095422563785536979)
  ·
    refine ⟨9381922643133845678305469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6254615095422563785536979 9381922643133845678305469)
    ·
      refine ⟨3518220991175192129364551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9381922643133845678305469 3518220991175192129364551)
      ·
        refine ⟨5277331486762788194046827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518220991175192129364551 5277331486762788194046827)
        ·
          refine ⟨7915997230144182291070241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277331486762788194046827 7915997230144182291070241)
          ·
            refine ⟨5936997922608136718302681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7915997230144182291070241 5936997922608136718302681)
            ·
              refine ⟨4452748441956102538727011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936997922608136718302681 4452748441956102538727011)
              ·
                refine ⟨6679122662934153808090517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452748441956102538727011 6679122662934153808090517)
                ·
                  refine ⟨313083874825038459754243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6679122662934153808090517 313083874825038459754243)
                  ·
                    rfl

theorem cell23_5487558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_5487558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487558 prefixEnd_5487558 := by exact prefixLift 5487558
  have htrace : WordTrace (prefixWord ++ tailWord_5487558) baseStart_5487558 baseEnd_5487558 := by
    simpa [prefixWord, tailWord_5487558, baseEnd_5487558] using wordTrace_append hprefix tailTrace_5487558
  have hstable : (prefixWord ++ tailWord_5487558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487558).length < 2 ^ (prefixWord ++ tailWord_5487558).sum := by decide
  have hdescent : baseEnd_5487558 < baseStart_5487558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487567 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 2, 4]
def baseStart_5487567 : Nat := 118140960795 + 5487567 * 2 ^ 59
def prefixEnd_5487567 : Nat := 4983230072969 + 3 ^ 40 * 5487567 * 2
def baseEnd_5487567 : Nat := 939253164917078867525215

theorem tailTrace_5487567 : CollatzResearch.WordTrace tailWord_5487567 prefixEnd_5487567 939253164917078867525215 := by
  unfold tailWord_5487567
  simp only [CollatzResearch.WordTrace]
  refine ⟨200148011310489435674260955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133432007540326290449507303 200148011310489435674260955)
  ·
    refine ⟨300222016965734153511391433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200148011310489435674260955 300222016965734153511391433)
    ·
      refine ⟨225166512724300615133543575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300222016965734153511391433 225166512724300615133543575)
      ·
        refine ⟨337749769086450922700315363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225166512724300615133543575 337749769086450922700315363)
        ·
          refine ⟨506624653629676384050473045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337749769086450922700315363 506624653629676384050473045)
          ·
            refine ⟨5937007659722770125591481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 506624653629676384050473045 5937007659722770125591481)
            ·
              refine ⟨4452755744792077594193611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5937007659722770125591481 4452755744792077594193611)
              ·
                refine ⟨6679133617188116391290417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452755744792077594193611 6679133617188116391290417)
                ·
                  refine ⟨5009350212891087293467813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679133617188116391290417 5009350212891087293467813)
                  ·
                    refine ⟨939253164917078867525215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009350212891087293467813 939253164917078867525215)
                    ·
                      rfl

theorem cell23_5487567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_5487567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487567 prefixEnd_5487567 := by exact prefixLift 5487567
  have htrace : WordTrace (prefixWord ++ tailWord_5487567) baseStart_5487567 baseEnd_5487567 := by
    simpa [prefixWord, tailWord_5487567, baseEnd_5487567] using wordTrace_append hprefix tailTrace_5487567
  have hstable : (prefixWord ++ tailWord_5487567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487567).length < 2 ^ (prefixWord ++ tailWord_5487567).sum := by decide
  have hdescent : baseEnd_5487567 < baseStart_5487567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487574 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5487574 : Nat := 118140960795 + 5487574 * 2 ^ 59
def prefixEnd_5487574 : Nat := 4983230072969 + 3 ^ 40 * 5487574 * 2
def baseEnd_5487574 : Nat := 2817763089115818075188113

theorem tailTrace_5487574 : CollatzResearch.WordTrace tailWord_5487574 prefixEnd_5487574 2817763089115818075188113 := by
  unfold tailWord_5487574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509266663841504741860361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133432177747642717246510517 12509266663841504741860361)
  ·
    refine ⟨9381949997881128556395271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12509266663841504741860361 9381949997881128556395271)
    ·
      refine ⟨14072924996821692834592907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9381949997881128556395271 14072924996821692834592907)
      ·
        refine ⟨21109387495232539251889361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072924996821692834592907 21109387495232539251889361)
        ·
          refine ⟨15832040621424404438917021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21109387495232539251889361 15832040621424404438917021)
          ·
            refine ⟨5937015233034151664593883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15832040621424404438917021 5937015233034151664593883)
            ·
              refine ⟨8905522849551227496890825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937015233034151664593883 8905522849551227496890825)
              ·
                refine ⟨6679142137163420622668119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8905522849551227496890825 6679142137163420622668119)
                ·
                  refine ⟨10018713205745130934002179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679142137163420622668119 10018713205745130934002179)
                  ·
                    refine ⟨15028069808617696401003269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10018713205745130934002179 15028069808617696401003269)
                    ·
                      refine ⟨2817763089115818075188113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15028069808617696401003269 2817763089115818075188113)
                      ·
                        rfl

theorem cell23_5487574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5487574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487574 prefixEnd_5487574 := by exact prefixLift 5487574
  have htrace : WordTrace (prefixWord ++ tailWord_5487574) baseStart_5487574 baseEnd_5487574 := by
    simpa [prefixWord, tailWord_5487574, baseEnd_5487574] using wordTrace_append hprefix tailTrace_5487574
  have hstable : (prefixWord ++ tailWord_5487574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487574).length < 2 ^ (prefixWord ++ tailWord_5487574).sum := by decide
  have hdescent : baseEnd_5487574 < baseStart_5487574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487577 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_5487577 : Nat := 118140960795 + 5487577 * 2 ^ 59
def prefixEnd_5487577 : Nat := 4983230072969 + 3 ^ 40 * 5487577 * 2
def baseEnd_5487577 : Nat := 2817764629557781563450599

theorem tailTrace_5487577 : CollatzResearch.WordTrace tailWord_5487577 prefixEnd_5487577 2817764629557781563450599 := by
  unfold tailWord_5487577
  simp only [CollatzResearch.WordTrace]
  refine ⟨200148376040453207382124985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133432250693635471588083323 200148376040453207382124985)
  ·
    refine ⟨150111282030339905536593739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200148376040453207382124985 150111282030339905536593739)
    ·
      refine ⟨225166923045509858304890609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150111282030339905536593739 225166923045509858304890609)
      ·
        refine ⟨168875192284132393728667957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225166923045509858304890609 168875192284132393728667957)
        ·
          refine ⟨15832049276637411912062621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168875192284132393728667957 15832049276637411912062621)
          ·
            refine ⟨5937018478739029467023483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15832049276637411912062621 5937018478739029467023483)
            ·
              refine ⟨8905527718108544200535225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937018478739029467023483 8905527718108544200535225)
              ·
                refine ⟨6679145788581408150401419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8905527718108544200535225 6679145788581408150401419)
                ·
                  refine ⟨10018718682872112225602129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679145788581408150401419 10018718682872112225602129)
                  ·
                    refine ⟨7514039012154084169201597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10018718682872112225602129 7514039012154084169201597)
                    ·
                      refine ⟨2817764629557781563450599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514039012154084169201597 2817764629557781563450599)
                      ·
                        rfl

theorem cell23_5487577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_5487577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487577 prefixEnd_5487577 := by exact prefixLift 5487577
  have htrace : WordTrace (prefixWord ++ tailWord_5487577) baseStart_5487577 baseEnd_5487577 := by
    simpa [prefixWord, tailWord_5487577, baseEnd_5487577] using wordTrace_append hprefix tailTrace_5487577
  have hstable : (prefixWord ++ tailWord_5487577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487577).length < 2 ^ (prefixWord ++ tailWord_5487577).sum := by decide
  have hdescent : baseEnd_5487577 < baseStart_5487577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487623 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 2, 6]
def baseStart_5487623 : Nat := 118140960795 + 5487623 * 2 ^ 59
def prefixEnd_5487623 : Nat := 4983230072969 + 3 ^ 40 * 5487623 * 2
def baseEnd_5487623 : Nat := 939262749889296127825129

theorem tailTrace_5487623 : CollatzResearch.WordTrace tailWord_5487623 prefixEnd_5487623 939262749889296127825129 := by
  unfold tailWord_5487623
  simp only [CollatzResearch.WordTrace]
  refine ⟨200150053798286557238299523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133433369198857704825533015 200150053798286557238299523)
  ·
    refine ⟨300225080697429835857449285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200150053798286557238299523 300225080697429835857449285)
    ·
      refine ⟨56292202630768094223271741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300225080697429835857449285 56292202630768094223271741)
      ·
        refine ⟨21109575986538035333726903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56292202630768094223271741 21109575986538035333726903)
        ·
          refine ⟨31664363979807053000590355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21109575986538035333726903 31664363979807053000590355)
          ·
            refine ⟨47496545969710579500885533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31664363979807053000590355 47496545969710579500885533)
            ·
              refine ⟨17811204738641467312832075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47496545969710579500885533 17811204738641467312832075)
              ·
                refine ⟨26716807107962200969248113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17811204738641467312832075 26716807107962200969248113)
                ·
                  refine ⟨20037605330971650726936085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26716807107962200969248113 20037605330971650726936085)
                  ·
                    refine ⟨939262749889296127825129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20037605330971650726936085 939262749889296127825129)
                    ·
                      rfl

theorem cell23_5487623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_5487623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487623 prefixEnd_5487623 := by exact prefixLift 5487623
  have htrace : WordTrace (prefixWord ++ tailWord_5487623) baseStart_5487623 baseEnd_5487623 := by
    simpa [prefixWord, tailWord_5487623, baseEnd_5487623] using wordTrace_append hprefix tailTrace_5487623
  have hstable : (prefixWord ++ tailWord_5487623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487623).length < 2 ^ (prefixWord ++ tailWord_5487623).sum := by decide
  have hdescent : baseEnd_5487623 < baseStart_5487623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487670 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_5487670 : Nat := 118140960795 + 5487670 * 2 ^ 59
def prefixEnd_5487670 : Nat := 4983230072969 + 3 ^ 40 * 5487670 * 2
def baseEnd_5487670 : Nat := 313090264806516633287519

theorem tailTrace_5487670 : CollatzResearch.WordTrace tailWord_5487670 prefixEnd_5487670 313090264806516633287519 := by
  unfold tailWord_5487670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509485501819767766578779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133434512019410856176840309 12509485501819767766578779)
  ·
    refine ⟨18764228252729651649868169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12509485501819767766578779 18764228252729651649868169)
    ·
      refine ⟨14073171189547238737401127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18764228252729651649868169 14073171189547238737401127)
      ·
        refine ⟨21109756784320858106101691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14073171189547238737401127 21109756784320858106101691)
        ·
          refine ⟨31664635176481287159152537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21109756784320858106101691 31664635176481287159152537)
          ·
            refine ⟨23748476382360965369364403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31664635176481287159152537 23748476382360965369364403)
            ·
              refine ⟨35622714573541448054046605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23748476382360965369364403 35622714573541448054046605)
              ·
                refine ⟨13358517965078043020267477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35622714573541448054046605 13358517965078043020267477)
                ·
                  refine ⟨313090264806516633287519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13358517965078043020267477 313090264806516633287519)
                  ·
                    rfl

theorem cell23_5487670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_5487670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487670 prefixEnd_5487670 := by exact prefixLift 5487670
  have htrace : WordTrace (prefixWord ++ tailWord_5487670) baseStart_5487670 baseEnd_5487670 := by
    simpa [prefixWord, tailWord_5487670, baseEnd_5487670] using wordTrace_append hprefix tailTrace_5487670
  have hstable : (prefixWord ++ tailWord_5487670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487670).length < 2 ^ (prefixWord ++ tailWord_5487670).sum := by decide
  have hdescent : baseEnd_5487670 < baseStart_5487670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487681 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5487681 : Nat := 118140960795 + 5487681 * 2 ^ 59
def prefixEnd_5487681 : Nat := 4983230072969 + 3 ^ 40 * 5487681 * 2
def baseEnd_5487681 : Nat := 2817818031545849156550121

theorem tailTrace_5487681 : CollatzResearch.WordTrace tailWord_5487681 prefixEnd_5487681 2817818031545849156550121 := by
  unfold tailWord_5487681
  simp only [CollatzResearch.WordTrace]
  refine ⟨200152169232076433143910897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133434779488050955429273931 200152169232076433143910897)
  ·
    refine ⟨150114126924057324857933173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200152169232076433143910897 150114126924057324857933173)
    ·
      refine ⟨14073199399130374205431235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150114126924057324857933173 14073199399130374205431235)
      ·
        refine ⟨21109799098695561308146853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14073199399130374205431235 21109799098695561308146853)
        ·
          refine ⟨3958087331005417745277535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21109799098695561308146853 3958087331005417745277535)
          ·
            refine ⟨5937130996508126617916303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958087331005417745277535 5937130996508126617916303)
            ·
              refine ⟨8905696494762189926874455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937130996508126617916303 8905696494762189926874455)
              ·
                refine ⟨13358544742143284890311683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8905696494762189926874455 13358544742143284890311683)
                ·
                  refine ⟨20037817113214927335467525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13358544742143284890311683 20037817113214927335467525)
                  ·
                    refine ⟨3757090708727798875400161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20037817113214927335467525 3757090708727798875400161)
                    ·
                      refine ⟨2817818031545849156550121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757090708727798875400161 2817818031545849156550121)
                      ·
                        rfl

theorem cell23_5487681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5487681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487681 prefixEnd_5487681 := by exact prefixLift 5487681
  have htrace : WordTrace (prefixWord ++ tailWord_5487681) baseStart_5487681 baseEnd_5487681 := by
    simpa [prefixWord, tailWord_5487681, baseEnd_5487681] using wordTrace_append hprefix tailTrace_5487681
  have hstable : (prefixWord ++ tailWord_5487681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487681).length < 2 ^ (prefixWord ++ tailWord_5487681).sum := by decide
  have hdescent : baseEnd_5487681 < baseStart_5487681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487690 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_5487690 : Nat := 118140960795 + 5487690 * 2 ^ 59
def prefixEnd_5487690 : Nat := 4983230072969 + 3 ^ 40 * 5487690 * 2
def baseEnd_5487690 : Nat := 2817822652871739621337579

theorem tailTrace_5487690 : CollatzResearch.WordTrace tailWord_5487690 prefixEnd_5487690 2817822652871739621337579 := by
  unfold tailWord_5487690
  simp only [CollatzResearch.WordTrace]
  refine ⟨50038124372260956920247131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133434998326029218453992349 50038124372260956920247131)
  ·
    refine ⟨75057186558391435380370697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50038124372260956920247131 75057186558391435380370697)
    ·
      refine ⟨56292889918793576535278023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75057186558391435380370697 56292889918793576535278023)
      ·
        refine ⟨84439334878190364802917035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56292889918793576535278023 84439334878190364802917035)
        ·
          refine ⟨126659002317285547204375553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84439334878190364802917035 126659002317285547204375553)
          ·
            refine ⟨94994251737964160403281665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126659002317285547204375553 94994251737964160403281665)
            ·
              refine ⟨71245688803473120302461249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94994251737964160403281665 71245688803473120302461249)
              ·
                refine ⟨53434266602604840226845937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71245688803473120302461249 53434266602604840226845937)
                ·
                  refine ⟨40075699951953630170134453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53434266602604840226845937 40075699951953630170134453)
                  ·
                    refine ⟨3757096870495652828450105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40075699951953630170134453 3757096870495652828450105)
                    ·
                      refine ⟨2817822652871739621337579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757096870495652828450105 2817822652871739621337579)
                      ·
                        rfl

theorem cell23_5487690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_5487690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487690 prefixEnd_5487690 := by exact prefixLift 5487690
  have htrace : WordTrace (prefixWord ++ tailWord_5487690) baseStart_5487690 baseEnd_5487690 := by
    simpa [prefixWord, tailWord_5487690, baseEnd_5487690] using wordTrace_append hprefix tailTrace_5487690
  have hstable : (prefixWord ++ tailWord_5487690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487690).length < 2 ^ (prefixWord ++ tailWord_5487690).sum := by decide
  have hdescent : baseEnd_5487690 < baseStart_5487690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3]
def baseStart_5487723 : Nat := 118140960795 + 5487723 * 2 ^ 59
def prefixEnd_5487723 : Nat := 4983230072969 + 3 ^ 40 * 5487723 * 2
def baseEnd_5487723 : Nat := 2817839597733337992224927

theorem tailTrace_5487723 : CollatzResearch.WordTrace tailWord_5487723 prefixEnd_5487723 2817839597733337992224927 := by
  unfold tailWord_5487723
  simp only [CollatzResearch.WordTrace]
  refine ⟨200153701097924274316939823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133435800731949516211293215 200153701097924274316939823)
  ·
    refine ⟨300230551646886411475409735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200153701097924274316939823 300230551646886411475409735)
    ·
      refine ⟨450345827470329617213114603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300230551646886411475409735 450345827470329617213114603)
      ·
        refine ⟨675518741205494425819671905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450345827470329617213114603 675518741205494425819671905)
        ·
          refine ⟨506639055904120819364753929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675518741205494425819671905 506639055904120819364753929)
          ·
            refine ⟨379979291928090614523565447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506639055904120819364753929 379979291928090614523565447)
            ·
              refine ⟨569968937892135921785348171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379979291928090614523565447 569968937892135921785348171)
              ·
                refine ⟨854953406838203882678022257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569968937892135921785348171 854953406838203882678022257)
                ·
                  refine ⟨641215055128652912008516693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854953406838203882678022257 641215055128652912008516693)
                  ·
                    refine ⟨7514238927288901312599805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 641215055128652912008516693 7514238927288901312599805)
                    ·
                      refine ⟨2817839597733337992224927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514238927288901312599805 2817839597733337992224927)
                      ·
                        rfl

theorem cell23_5487723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3].length) (baseStart_5487723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487723 prefixEnd_5487723 := by exact prefixLift 5487723
  have htrace : WordTrace (prefixWord ++ tailWord_5487723) baseStart_5487723 baseEnd_5487723 := by
    simpa [prefixWord, tailWord_5487723, baseEnd_5487723] using wordTrace_append hprefix tailTrace_5487723
  have hstable : (prefixWord ++ tailWord_5487723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487723).length < 2 ^ (prefixWord ++ tailWord_5487723).sum := by decide
  have hdescent : baseEnd_5487723 < baseStart_5487723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487740 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_5487740 : Nat := 118140960795 + 5487740 * 2 ^ 59
def prefixEnd_5487740 : Nat := 4983230072969 + 3 ^ 40 * 5487740 * 2
def baseEnd_5487740 : Nat := 2817848326904464425712349

theorem tailTrace_5487740 : CollatzResearch.WordTrace tailWord_5487740 prefixEnd_5487740 2817848326904464425712349 := by
  unfold tailWord_5487740
  simp only [CollatzResearch.WordTrace]
  refine ⟨100077160569431343110154337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133436214092575124146872449 100077160569431343110154337)
  ·
    refine ⟨75057870427073507332615753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100077160569431343110154337 75057870427073507332615753)
    ·
      refine ⟨56293402820305130499461815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75057870427073507332615753 56293402820305130499461815)
      ·
        refine ⟨84440104230457695749192723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56293402820305130499461815 84440104230457695749192723)
        ·
          refine ⟨126660156345686543623789085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84440104230457695749192723 126660156345686543623789085)
          ·
            refine ⟨47497558629632453858920907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126660156345686543623789085 47497558629632453858920907)
            ·
              refine ⟨71246337944448680788381361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47497558629632453858920907 71246337944448680788381361)
              ·
                refine ⟨53434753458336510591286021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71246337944448680788381361 53434753458336510591286021)
                ·
                  refine ⟨10019016273438095735866129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53434753458336510591286021 10019016273438095735866129)
                  ·
                    refine ⟨7514262205078571801899597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10019016273438095735866129 7514262205078571801899597)
                    ·
                      refine ⟨2817848326904464425712349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514262205078571801899597 2817848326904464425712349)
                      ·
                        rfl

theorem cell23_5487740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_5487740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487740 prefixEnd_5487740 := by exact prefixLift 5487740
  have htrace : WordTrace (prefixWord ++ tailWord_5487740) baseStart_5487740 baseEnd_5487740 := by
    simpa [prefixWord, tailWord_5487740, baseEnd_5487740] using wordTrace_append hprefix tailTrace_5487740
  have hstable : (prefixWord ++ tailWord_5487740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487740).length < 2 ^ (prefixWord ++ tailWord_5487740).sum := by decide
  have hdescent : baseEnd_5487740 < baseStart_5487740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487774 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5487774 : Nat := 118140960795 + 5487774 * 2 ^ 59
def prefixEnd_5487774 : Nat := 4983230072969 + 3 ^ 40 * 5487774 * 2
def baseEnd_5487774 : Nat := 2817865785246717292687193

theorem tailTrace_5487774 : CollatzResearch.WordTrace tailWord_5487774 prefixEnd_5487774 2817865785246717292687193 := by
  unfold tailWord_5487774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25019445152592438753380797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133437040813826340018030917 25019445152592438753380797)
  ·
    refine ⟨9382291932222164532517799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25019445152592438753380797 9382291932222164532517799)
    ·
      refine ⟨14073437898333246798776699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9382291932222164532517799 14073437898333246798776699)
      ·
        refine ⟨21110156847499870198165049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14073437898333246798776699 21110156847499870198165049)
        ·
          refine ⟨15832617635624902648623787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21110156847499870198165049 15832617635624902648623787)
          ·
            refine ⟨23748926453437353972935681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15832617635624902648623787 23748926453437353972935681)
            ·
              refine ⟨17811694840078015479701761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23748926453437353972935681 17811694840078015479701761)
              ·
                refine ⟨13358771130058511609776321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17811694840078015479701761 13358771130058511609776321)
                ·
                  refine ⟨10019078347543883707332241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13358771130058511609776321 10019078347543883707332241)
                  ·
                    refine ⟨7514308760657912780499181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10019078347543883707332241 7514308760657912780499181)
                    ·
                      refine ⟨2817865785246717292687193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514308760657912780499181 2817865785246717292687193)
                      ·
                        rfl

theorem cell23_5487774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5487774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487774 prefixEnd_5487774 := by exact prefixLift 5487774
  have htrace : WordTrace (prefixWord ++ tailWord_5487774) baseStart_5487774 baseEnd_5487774 := by
    simpa [prefixWord, tailWord_5487774, baseEnd_5487774] using wordTrace_append hprefix tailTrace_5487774
  have hstable : (prefixWord ++ tailWord_5487774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487774).length < 2 ^ (prefixWord ++ tailWord_5487774).sum := by decide
  have hdescent : baseEnd_5487774 < baseStart_5487774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487781 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_5487781 : Nat := 118140960795 + 5487781 * 2 ^ 59
def prefixEnd_5487781 : Nat := 4983230072969 + 3 ^ 40 * 5487781 * 2
def baseEnd_5487781 : Nat := 939289793203766255099887

theorem tailTrace_5487781 : CollatzResearch.WordTrace tailWord_5487781 prefixEnd_5487781 939289793203766255099887 := by
  unfold tailWord_5487781
  simp only [CollatzResearch.WordTrace]
  refine ⟨200155816531714150222551197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133437211021142766815034131 200155816531714150222551197)
  ·
    refine ⟨75058431199392806333456699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200155816531714150222551197 75058431199392806333456699)
    ·
      refine ⟨112587646799089209500185049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75058431199392806333456699 112587646799089209500185049)
      ·
        refine ⟨84440735099316907125138787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112587646799089209500185049 84440735099316907125138787)
        ·
          refine ⟨126661102648975360687708181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84440735099316907125138787 126661102648975360687708181)
          ·
            refine ⟨5937239186670720032236321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126661102648975360687708181 5937239186670720032236321)
            ·
              refine ⟨4452929390003040024177241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5937239186670720032236321 4452929390003040024177241)
              ·
                refine ⟨3339697042502280018132931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4452929390003040024177241 3339697042502280018132931)
                ·
                  refine ⟨5009545563753420027199397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339697042502280018132931 5009545563753420027199397)
                  ·
                    refine ⟨939289793203766255099887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009545563753420027199397 939289793203766255099887)
                    ·
                      rfl

theorem cell23_5487781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_5487781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487781 prefixEnd_5487781 := by exact prefixLift 5487781
  have htrace : WordTrace (prefixWord ++ tailWord_5487781) baseStart_5487781 baseEnd_5487781 := by
    simpa [prefixWord, tailWord_5487781, baseEnd_5487781] using wordTrace_append hprefix tailTrace_5487781
  have hstable : (prefixWord ++ tailWord_5487781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487781).length < 2 ^ (prefixWord ++ tailWord_5487781).sum := by decide
  have hdescent : baseEnd_5487781 < baseStart_5487781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487804 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_5487804 : Nat := 118140960795 + 5487804 * 2 ^ 59
def prefixEnd_5487804 : Nat := 4983230072969 + 3 ^ 40 * 5487804 * 2
def baseEnd_5487804 : Nat := 2817881189666352175312055

theorem tailTrace_5487804 : CollatzResearch.WordTrace tailWord_5487804 prefixEnd_5487804 2817881189666352175312055 := by
  unfold tailWord_5487804
  simp only [CollatzResearch.WordTrace]
  refine ⟨100078327705315412575319233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133437770273753883433758977 100078327705315412575319233)
  ·
    refine ⟨75058745778986559431489425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100078327705315412575319233 75058745778986559431489425)
    ·
      refine ⟨56294059334239919573617069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75058745778986559431489425 56294059334239919573617069)
      ·
        refine ⟨21110272250339969840106401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56294059334239919573617069 21110272250339969840106401)
        ·
          refine ⟨15832704187754977380079801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21110272250339969840106401 15832704187754977380079801)
          ·
            refine ⟨11874528140816233035059851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15832704187754977380079801 11874528140816233035059851)
            ·
              refine ⟨17811792211224349552589777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11874528140816233035059851 17811792211224349552589777)
              ·
                refine ⟨13358844158418262164442333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17811792211224349552589777 13358844158418262164442333)
                ·
                  refine ⟨5009566559406848311665875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13358844158418262164442333 5009566559406848311665875)
                  ·
                    refine ⟨7514349839110272467498813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009566559406848311665875 7514349839110272467498813)
                    ·
                      refine ⟨2817881189666352175312055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514349839110272467498813 2817881189666352175312055)
                      ·
                        rfl

theorem cell23_5487804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_5487804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487804 prefixEnd_5487804 := by exact prefixLift 5487804
  have htrace : WordTrace (prefixWord ++ tailWord_5487804) baseStart_5487804 baseEnd_5487804 := by
    simpa [prefixWord, tailWord_5487804, baseEnd_5487804] using wordTrace_append hprefix tailTrace_5487804
  have hstable : (prefixWord ++ tailWord_5487804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487804).length < 2 ^ (prefixWord ++ tailWord_5487804).sum := by decide
  have hdescent : baseEnd_5487804 < baseStart_5487804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487844 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_5487844 : Nat := 118140960795 + 5487844 * 2 ^ 59
def prefixEnd_5487844 : Nat := 4983230072969 + 3 ^ 40 * 5487844 * 2
def baseEnd_5487844 : Nat := 2817901728892532018811871

theorem tailTrace_5487844 : CollatzResearch.WordTrace tailWord_5487844 prefixEnd_5487844 2817901728892532018811871 := by
  unfold tailWord_5487844
  simp only [CollatzResearch.WordTrace]
  refine ⟨100079057165242955991047293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133438742886990607988063057 100079057165242955991047293)
  ·
    refine ⟨37529646436966108496642735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100079057165242955991047293 37529646436966108496642735)
    ·
      refine ⟨56294469655449162744964103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37529646436966108496642735 56294469655449162744964103)
      ·
        refine ⟨84441704483173744117446155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56294469655449162744964103 84441704483173744117446155)
        ·
          refine ⟨126662556724760616176169233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84441704483173744117446155 126662556724760616176169233)
          ·
            refine ⟨94996917543570462132126925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126662556724760616176169233 94996917543570462132126925)
            ·
              refine ⟨35623844078838923299547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94996917543570462132126925 35623844078838923299547597)
              ·
                refine ⟨13358941529564596237330349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35623844078838923299547597 13358941529564596237330349)
                ·
                  refine ⟨5009603073586723588998881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13358941529564596237330349 5009603073586723588998881)
                  ·
                    refine ⟨3757202305190042691749161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5009603073586723588998881 3757202305190042691749161)
                    ·
                      refine ⟨2817901728892532018811871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757202305190042691749161 2817901728892532018811871)
                      ·
                        rfl

theorem cell23_5487844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_5487844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487844 prefixEnd_5487844 := by exact prefixLift 5487844
  have htrace : WordTrace (prefixWord ++ tailWord_5487844) baseStart_5487844 baseEnd_5487844 := by
    simpa [prefixWord, tailWord_5487844, baseEnd_5487844] using wordTrace_append hprefix tailTrace_5487844
  have hstable : (prefixWord ++ tailWord_5487844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487844).length < 2 ^ (prefixWord ++ tailWord_5487844).sum := by decide
  have hdescent : baseEnd_5487844 < baseStart_5487844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487877 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_5487877 : Nat := 118140960795 + 5487877 * 2 ^ 59
def prefixEnd_5487877 : Nat := 4983230072969 + 3 ^ 40 * 5487877 * 2
def baseEnd_5487877 : Nat := 2817918673754130389699219

theorem tailTrace_5487877 : CollatzResearch.WordTrace tailWord_5487877 prefixEnd_5487877 2817918673754130389699219 := by
  unfold tailWord_5487877
  simp only [CollatzResearch.WordTrace]
  refine ⟨200159317939366358618045885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133439545292910905745363923 200159317939366358618045885)
  ·
    refine ⟨75059744227262384481767207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200159317939366358618045885 75059744227262384481767207)
    ·
      refine ⟨112589616340893576722650811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75059744227262384481767207 112589616340893576722650811)
      ·
        refine ⟨168884424511340365083976217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112589616340893576722650811 168884424511340365083976217)
        ·
          refine ⟨126663318383505273812982163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168884424511340365083976217 126663318383505273812982163)
          ·
            refine ⟨189994977575257910719473245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126663318383505273812982163 189994977575257910719473245)
            ·
              refine ⟨71248116590721716519802467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189994977575257910719473245 71248116590721716519802467)
              ·
                refine ⟨106872174886082574779703701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71248116590721716519802467 106872174886082574779703701)
                ·
                  refine ⟨5009633197785120692798611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106872174886082574779703701 5009633197785120692798611)
                  ·
                    refine ⟨7514449796677681039197917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009633197785120692798611 7514449796677681039197917)
                    ·
                      refine ⟨2817918673754130389699219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514449796677681039197917 2817918673754130389699219)
                      ·
                        rfl

theorem cell23_5487877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_5487877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487877 prefixEnd_5487877 := by exact prefixLift 5487877
  have htrace : WordTrace (prefixWord ++ tailWord_5487877) baseStart_5487877 baseEnd_5487877 := by
    simpa [prefixWord, tailWord_5487877, baseEnd_5487877] using wordTrace_append hprefix tailTrace_5487877
  have hstable : (prefixWord ++ tailWord_5487877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487877).length < 2 ^ (prefixWord ++ tailWord_5487877).sum := by decide
  have hdescent : baseEnd_5487877 < baseStart_5487877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487887 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 7, 3, 2]
def baseStart_5487887 : Nat := 118140960795 + 5487887 * 2 ^ 59
def prefixEnd_5487887 : Nat := 4983230072969 + 3 ^ 40 * 5487887 * 2
def baseEnd_5487887 : Nat := 2817923808560675350574173

theorem tailTrace_5487887 : CollatzResearch.WordTrace tailWord_5487887 prefixEnd_5487887 2817923808560675350574173 := by
  unfold tailWord_5487887
  simp only [CollatzResearch.WordTrace]
  refine ⟨200159682669330130325909915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133439788446220086883939943 200159682669330130325909915)
  ·
    refine ⟨300239524003995195488864873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200159682669330130325909915 300239524003995195488864873)
    ·
      refine ⟨225179643002996396616648655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300239524003995195488864873 225179643002996396616648655)
      ·
        refine ⟨337769464504494594924972983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225179643002996396616648655 337769464504494594924972983)
        ·
          refine ⟨506654196756741892387459475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337769464504494594924972983 506654196756741892387459475)
          ·
            refine ⟨759981295135112838581189213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506654196756741892387459475 759981295135112838581189213)
            ·
              refine ⟨284992985675667314467945955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759981295135112838581189213 284992985675667314467945955)
              ·
                refine ⟨427489478513500971701918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284992985675667314467945955 427489478513500971701918933)
                ·
                  refine ⟨10019284652660179024263725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 427489478513500971701918933 10019284652660179024263725)
                  ·
                    refine ⟨3757231744747567134098897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10019284652660179024263725 3757231744747567134098897)
                    ·
                      refine ⟨2817923808560675350574173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757231744747567134098897 2817923808560675350574173)
                      ·
                        rfl

theorem cell23_5487887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 3, 2].length) (baseStart_5487887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487887 prefixEnd_5487887 := by exact prefixLift 5487887
  have htrace : WordTrace (prefixWord ++ tailWord_5487887) baseStart_5487887 baseEnd_5487887 := by
    simpa [prefixWord, tailWord_5487887, baseEnd_5487887] using wordTrace_append hprefix tailTrace_5487887
  have hstable : (prefixWord ++ tailWord_5487887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487887).length < 2 ^ (prefixWord ++ tailWord_5487887).sum := by decide
  have hdescent : baseEnd_5487887 < baseStart_5487887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487920 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_5487920 : Nat := 118140960795 + 5487920 * 2 ^ 59
def prefixEnd_5487920 : Nat := 4983230072969 + 3 ^ 40 * 5487920 * 2
def baseEnd_5487920 : Nat := 2817940753422273721461521

theorem tailTrace_5487920 : CollatzResearch.WordTrace tailWord_5487920 prefixEnd_5487920 2817940753422273721461521 := by
  unfold tailWord_5487920
  simp only [CollatzResearch.WordTrace]
  refine ⟨100080443139105288480930607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133440590852140384641240809 100080443139105288480930607)
  ·
    refine ⟨150120664708657932721395911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100080443139105288480930607 150120664708657932721395911)
    ·
      refine ⟨225180997062986899082093867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150120664708657932721395911 225180997062986899082093867)
      ·
        refine ⟨337771495594480348623140801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225180997062986899082093867 337771495594480348623140801)
        ·
          refine ⟨253328621695860261467355601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337771495594480348623140801 253328621695860261467355601)
          ·
            refine ⟨189996466271895196100516701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253328621695860261467355601 189996466271895196100516701)
            ·
              refine ⟨71248674851960698537693763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189996466271895196100516701 71248674851960698537693763)
              ·
                refine ⟨106873012277941047806540645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71248674851960698537693763 106873012277941047806540645)
                ·
                  refine ⟨20038689802113946463726371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106873012277941047806540645 20038689802113946463726371)
                  ·
                    refine ⟨30058034703170919695589557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20038689802113946463726371 30058034703170919695589557)
                    ·
                      refine ⟨2817940753422273721461521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30058034703170919695589557 2817940753422273721461521)
                      ·
                        rfl

theorem cell23_5487920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_5487920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487920 prefixEnd_5487920 := by exact prefixLift 5487920
  have htrace : WordTrace (prefixWord ++ tailWord_5487920) baseStart_5487920 baseEnd_5487920 := by
    simpa [prefixWord, tailWord_5487920, baseEnd_5487920] using wordTrace_append hprefix tailTrace_5487920
  have hstable : (prefixWord ++ tailWord_5487920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487920).length < 2 ^ (prefixWord ++ tailWord_5487920).sum := by decide
  have hdescent : baseEnd_5487920 < baseStart_5487920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487921 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_5487921 : Nat := 118140960795 + 5487921 * 2 ^ 59
def prefixEnd_5487921 : Nat := 4983230072969 + 3 ^ 40 * 5487921 * 2
def baseEnd_5487921 : Nat := 2817941266902928217549017

theorem tailTrace_5487921 : CollatzResearch.WordTrace tailWord_5487921 prefixEnd_5487921 2817941266902928217549017 := by
  unfold tailWord_5487921
  simp only [CollatzResearch.WordTrace]
  refine ⟨200160922751206954132647617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133440615167471302755098411 200160922751206954132647617)
  ·
    refine ⟨150120692063405215599485713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200160922751206954132647617 150120692063405215599485713)
    ·
      refine ⟨112590519047553911699614285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150120692063405215599485713 112590519047553911699614285)
      ·
        refine ⟨42221444642832716887355357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112590519047553911699614285 42221444642832716887355357)
        ·
          refine ⟨15833041741062268832758259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42221444642832716887355357 15833041741062268832758259)
          ·
            refine ⟨23749562611593403249137389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15833041741062268832758259 23749562611593403249137389)
            ·
              refine ⟨8906085979347526218426521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23749562611593403249137389 8906085979347526218426521)
              ·
                refine ⟨6679564484510644663819891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8906085979347526218426521 6679564484510644663819891)
                ·
                  refine ⟨10019346726765966995729837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679564484510644663819891 10019346726765966995729837)
                  ·
                    refine ⟨3757255022537237623398689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10019346726765966995729837 3757255022537237623398689)
                    ·
                      refine ⟨2817941266902928217549017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757255022537237623398689 2817941266902928217549017)
                      ·
                        rfl

theorem cell23_5487921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_5487921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487921 prefixEnd_5487921 := by exact prefixLift 5487921
  have htrace : WordTrace (prefixWord ++ tailWord_5487921) baseStart_5487921 baseEnd_5487921 := by
    simpa [prefixWord, tailWord_5487921, baseEnd_5487921] using wordTrace_append hprefix tailTrace_5487921
  have hstable : (prefixWord ++ tailWord_5487921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487921).length < 2 ^ (prefixWord ++ tailWord_5487921).sum := by decide
  have hdescent : baseEnd_5487921 < baseStart_5487921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488000 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_5488000 : Nat := 118140960795 + 5488000 * 2 ^ 59
def prefixEnd_5488000 : Nat := 4983230072969 + 3 ^ 40 * 5488000 * 2
def baseEnd_5488000 : Nat := 939327277291544469487051

theorem tailTrace_5488000 : CollatzResearch.WordTrace tailWord_5488000 prefixEnd_5488000 939327277291544469487051 := by
  unfold tailWord_5488000
  simp only [CollatzResearch.WordTrace]
  refine ⟨100081902058960375312386727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133442536078613833749848969 100081902058960375312386727)
  ·
    refine ⟨150122853088440562968580091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100081902058960375312386727 150122853088440562968580091)
    ·
      refine ⟨225184279632660844452870137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150122853088440562968580091 225184279632660844452870137)
      ·
        refine ⟨168888209724495633339652603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225184279632660844452870137 168888209724495633339652603)
        ·
          refine ⟨253332314586743450009478905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168888209724495633339652603 253332314586743450009478905)
          ·
            refine ⟨189999235940057587507109179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253332314586743450009478905 189999235940057587507109179)
            ·
              refine ⟨284998853910086381260663769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189999235940057587507109179 284998853910086381260663769)
              ·
                refine ⟨213749140432564785945497827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284998853910086381260663769 213749140432564785945497827)
                ·
                  refine ⟨320623710648847178918246741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213749140432564785945497827 320623710648847178918246741)
                  ·
                    refine ⟨939327277291544469487051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 320623710648847178918246741 939327277291544469487051)
                    ·
                      rfl

theorem cell23_5488000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_5488000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488000 prefixEnd_5488000 := by exact prefixLift 5488000
  have htrace : WordTrace (prefixWord ++ tailWord_5488000) baseStart_5488000 baseEnd_5488000 := by
    simpa [prefixWord, tailWord_5488000, baseEnd_5488000] using wordTrace_append hprefix tailTrace_5488000
  have hstable : (prefixWord ++ tailWord_5488000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488000).length < 2 ^ (prefixWord ++ tailWord_5488000).sum := by decide
  have hdescent : baseEnd_5488000 < baseStart_5488000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488002 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5488002 : Nat := 118140960795 + 5488002 * 2 ^ 59
def prefixEnd_5488002 : Nat := 4983230072969 + 3 ^ 40 * 5488002 * 2
def baseEnd_5488002 : Nat := 2817982858835942400636145

theorem tailTrace_5488002 : CollatzResearch.WordTrace tailWord_5488002 prefixEnd_5488002 2817982858835942400636145 := by
  unfold tailWord_5488002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50040969265978376241586565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133442584709275669977564173 50040969265978376241586565)
  ·
    refine ⟨9382681737370945545297481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50040969265978376241586565 9382681737370945545297481)
    ·
      refine ⟨7037011303028209158973111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9382681737370945545297481 7037011303028209158973111)
      ·
        refine ⟨10555516954542313738459667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037011303028209158973111 10555516954542313738459667)
        ·
          refine ⟨15833275431813470607689501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10555516954542313738459667 15833275431813470607689501)
          ·
            refine ⟨5937478286930051477883563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15833275431813470607689501 5937478286930051477883563)
            ·
              refine ⟨8906217430395077216825345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937478286930051477883563 8906217430395077216825345)
              ·
                refine ⟨6679663072796307912619009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8906217430395077216825345 6679663072796307912619009)
                ·
                  refine ⟨5009747304597230934464257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679663072796307912619009 5009747304597230934464257)
                  ·
                    refine ⟨3757310478447923200848193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5009747304597230934464257 3757310478447923200848193)
                    ·
                      refine ⟨2817982858835942400636145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757310478447923200848193 2817982858835942400636145)
                      ·
                        rfl

theorem cell23_5488002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5488002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488002 prefixEnd_5488002 := by exact prefixLift 5488002
  have htrace : WordTrace (prefixWord ++ tailWord_5488002) baseStart_5488002 baseEnd_5488002 := by
    simpa [prefixWord, tailWord_5488002, baseEnd_5488002] using wordTrace_append hprefix tailTrace_5488002
  have hstable : (prefixWord ++ tailWord_5488002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488002).length < 2 ^ (prefixWord ++ tailWord_5488002).sum := by decide
  have hdescent : baseEnd_5488002 < baseStart_5488002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488017 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_5488017 : Nat := 118140960795 + 5488017 * 2 ^ 59
def prefixEnd_5488017 : Nat := 4983230072969 + 3 ^ 40 * 5488017 * 2
def baseEnd_5488017 : Nat := 939330187015253280649525

theorem tailTrace_5488017 : CollatzResearch.WordTrace tailWord_5488017 prefixEnd_5488017 939330187015253280649525 := by
  unfold tailWord_5488017
  simp only [CollatzResearch.WordTrace]
  refine ⟨200164424158859162528142305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133442949439239441685428203 200164424158859162528142305)
  ·
    refine ⟨150123318119144371896106729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200164424158859162528142305 150123318119144371896106729)
    ·
      refine ⟨112592488589358278922080047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150123318119144371896106729 112592488589358278922080047)
      ·
        refine ⟨168888732884037418383120071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112592488589358278922080047 168888732884037418383120071)
        ·
          refine ⟨253333099326056127574680107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168888732884037418383120071 253333099326056127574680107)
          ·
            refine ⟨379999648989084191362020161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253333099326056127574680107 379999648989084191362020161)
            ·
              refine ⟨284999736741813143521515121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379999648989084191362020161 284999736741813143521515121)
              ·
                refine ⟨213749802556359857641136341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284999736741813143521515121 213749802556359857641136341)
                ·
                  refine ⟨5009760997414684163464133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213749802556359857641136341 5009760997414684163464133)
                  ·
                    refine ⟨939330187015253280649525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009760997414684163464133 939330187015253280649525)
                    ·
                      rfl

theorem cell23_5488017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_5488017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488017 prefixEnd_5488017 := by exact prefixLift 5488017
  have htrace : WordTrace (prefixWord ++ tailWord_5488017) baseStart_5488017 baseEnd_5488017 := by
    simpa [prefixWord, tailWord_5488017, baseEnd_5488017] using wordTrace_append hprefix tailTrace_5488017
  have hstable : (prefixWord ++ tailWord_5488017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488017).length < 2 ^ (prefixWord ++ tailWord_5488017).sum := by decide
  have hdescent : baseEnd_5488017 < baseStart_5488017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488068 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_5488068 : Nat := 118140960795 + 5488068 * 2 ^ 59
def prefixEnd_5488068 : Nat := 4983230072969 + 3 ^ 40 * 5488068 * 2
def baseEnd_5488068 : Nat := 939338916186379714136947

theorem tailTrace_5488068 : CollatzResearch.WordTrace tailWord_5488068 prefixEnd_5488068 939338916186379714136947 := by
  unfold tailWord_5488068
  simp only [CollatzResearch.WordTrace]
  refine ⟨100083142140837199119124429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133444189521116265492165905 100083142140837199119124429)
  ·
    refine ⟨37531178302813949669671661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100083142140837199119124429 37531178302813949669671661)
    ·
      refine ⟨14074191863555231126126873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37531178302813949669671661 14074191863555231126126873)
      ·
        refine ⟨10555643897666423344595155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14074191863555231126126873 10555643897666423344595155)
        ·
          refine ⟨15833465846499635016892733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10555643897666423344595155 15833465846499635016892733)
          ·
            refine ⟨5937549692437363131334775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15833465846499635016892733 5937549692437363131334775)
            ·
              refine ⟨8906324538656044697002163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937549692437363131334775 8906324538656044697002163)
              ·
                refine ⟨13359486807984067045503245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8906324538656044697002163 13359486807984067045503245)
                ·
                  refine ⟨5009807552994025142063717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13359486807984067045503245 5009807552994025142063717)
                  ·
                    refine ⟨939338916186379714136947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009807552994025142063717 939338916186379714136947)
                    ·
                      rfl

theorem cell23_5488068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_5488068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488068 prefixEnd_5488068 := by exact prefixLift 5488068
  have htrace : WordTrace (prefixWord ++ tailWord_5488068) baseStart_5488068 baseEnd_5488068 := by
    simpa [prefixWord, tailWord_5488068, baseEnd_5488068] using wordTrace_append hprefix tailTrace_5488068
  have hstable : (prefixWord ++ tailWord_5488068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488068).length < 2 ^ (prefixWord ++ tailWord_5488068).sum := by decide
  have hdescent : baseEnd_5488068 < baseStart_5488068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488118 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5488118 : Nat := 118140960795 + 5488118 * 2 ^ 59
def prefixEnd_5488118 : Nat := 4983230072969 + 3 ^ 40 * 5488118 * 2
def baseEnd_5488118 : Nat := 2818042422591863946785611

theorem tailTrace_5488118 : CollatzResearch.WordTrace tailWord_5488118 prefixEnd_5488118 2818042422591863946785611 := by
  unfold tailWord_5488118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12510506745718328548598063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133445405287662171185046005 12510506745718328548598063)
  ·
    refine ⟨18765760118577492822897095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12510506745718328548598063 18765760118577492822897095)
    ·
      refine ⟨28148640177866239234345643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18765760118577492822897095 28148640177866239234345643)
      ·
        refine ⟨42222960266799358851518465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28148640177866239234345643 42222960266799358851518465)
        ·
          refine ⟨31667220200099519138638849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42222960266799358851518465 31667220200099519138638849)
          ·
            refine ⟨23750415150074639353979137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31667220200099519138638849 23750415150074639353979137)
            ·
              refine ⟨17812811362555979515484353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23750415150074639353979137 17812811362555979515484353)
              ·
                refine ⟨13359608521916984636613265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17812811362555979515484353 13359608521916984636613265)
                ·
                  refine ⟨10019706391437738477459949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13359608521916984636613265 10019706391437738477459949)
                  ·
                    refine ⟨3757389896789151929047481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10019706391437738477459949 3757389896789151929047481)
                    ·
                      refine ⟨2818042422591863946785611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757389896789151929047481 2818042422591863946785611)
                      ·
                        rfl

theorem cell23_5488118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5488118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488118 prefixEnd_5488118 := by exact prefixLift 5488118
  have htrace : WordTrace (prefixWord ++ tailWord_5488118) baseStart_5488118 baseEnd_5488118 := by
    simpa [prefixWord, tailWord_5488118, baseEnd_5488118] using wordTrace_append hprefix tailTrace_5488118
  have hstable : (prefixWord ++ tailWord_5488118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488118).length < 2 ^ (prefixWord ++ tailWord_5488118).sum := by decide
  have hdescent : baseEnd_5488118 < baseStart_5488118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488124 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_5488124 : Nat := 118140960795 + 5488124 * 2 ^ 59
def prefixEnd_5488124 : Nat := 4983230072969 + 3 ^ 40 * 5488124 * 2
def baseEnd_5488124 : Nat := 939348501158596974436861

theorem tailTrace_5488124 : CollatzResearch.WordTrace tailWord_5488124 prefixEnd_5488124 939348501158596974436861 := by
  unfold tailWord_5488124
  simp only [CollatzResearch.WordTrace]
  refine ⟨100084163384735759901143713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133445551179647679868191617 100084163384735759901143713)
  ·
    refine ⟨75063122538551819925857785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100084163384735759901143713 75063122538551819925857785)
    ·
      refine ⟨56297341903913864944393339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75063122538551819925857785 56297341903913864944393339)
      ·
        refine ⟨84446012855870797416590009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56297341903913864944393339 84446012855870797416590009)
        ·
          refine ⟨63334509641903098062442507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84446012855870797416590009 63334509641903098062442507)
          ·
            refine ⟨95001764462854647093663761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63334509641903098062442507 95001764462854647093663761)
            ·
              refine ⟨71251323347140985320247821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95001764462854647093663761 71251323347140985320247821)
              ·
                refine ⟨26719246255177869495092933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71251323347140985320247821 26719246255177869495092933)
                ·
                  refine ⟨5009858672845850530329925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26719246255177869495092933 5009858672845850530329925)
                  ·
                    refine ⟨939348501158596974436861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009858672845850530329925 939348501158596974436861)
                    ·
                      rfl

theorem cell23_5488124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_5488124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488124 prefixEnd_5488124 := by exact prefixLift 5488124
  have htrace : WordTrace (prefixWord ++ tailWord_5488124) baseStart_5488124 baseEnd_5488124 := by
    simpa [prefixWord, tailWord_5488124, baseEnd_5488124] using wordTrace_append hprefix tailTrace_5488124
  have hstable : (prefixWord ++ tailWord_5488124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488124).length < 2 ^ (prefixWord ++ tailWord_5488124).sum := by decide
  have hdescent : baseEnd_5488124 < baseStart_5488124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488125 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_5488125 : Nat := 118140960795 + 5488125 * 2 ^ 59
def prefixEnd_5488125 : Nat := 4983230072969 + 3 ^ 40 * 5488125 * 2
def baseEnd_5488125 : Nat := 2818046016956445419398079

theorem tailTrace_5488125 : CollatzResearch.WordTrace tailWord_5488125 prefixEnd_5488125 2818046016956445419398079 := by
  unfold tailWord_5488125
  simp only [CollatzResearch.WordTrace]
  refine ⟨200168363242467896973073829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133445575494978597982049219 200168363242467896973073829)
  ·
    refine ⟨37531568107962730682451343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200168363242467896973073829 37531568107962730682451343)
    ·
      refine ⟨56297352161944096023677015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37531568107962730682451343 56297352161944096023677015)
      ·
        refine ⟨84446028242916144035515523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56297352161944096023677015 84446028242916144035515523)
        ·
          refine ⟨126669042364374216053273285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84446028242916144035515523 126669042364374216053273285)
          ·
            refine ⟨23750445443320165509988741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126669042364374216053273285 23750445443320165509988741)
            ·
              refine ⟨4453208520622531033122889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23750445443320165509988741 4453208520622531033122889)
              ·
                refine ⟨3339906390466898274842167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453208520622531033122889 3339906390466898274842167)
                ·
                  refine ⟨5009859585700347412263251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339906390466898274842167 5009859585700347412263251)
                  ·
                    refine ⟨7514789378550521118394877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009859585700347412263251 7514789378550521118394877)
                    ·
                      refine ⟨2818046016956445419398079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514789378550521118394877 2818046016956445419398079)
                      ·
                        rfl

theorem cell23_5488125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_5488125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488125 prefixEnd_5488125 := by exact prefixLift 5488125
  have htrace : WordTrace (prefixWord ++ tailWord_5488125) baseStart_5488125 baseEnd_5488125 := by
    simpa [prefixWord, tailWord_5488125, baseEnd_5488125] using wordTrace_append hprefix tailTrace_5488125
  have hstable : (prefixWord ++ tailWord_5488125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488125).length < 2 ^ (prefixWord ++ tailWord_5488125).sum := by decide
  have hdescent : baseEnd_5488125 < baseStart_5488125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488127 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_5488127 : Nat := 118140960795 + 5488127 * 2 ^ 59
def prefixEnd_5488127 : Nat := 4983230072969 + 3 ^ 40 * 5488127 * 2
def baseEnd_5488127 : Nat := 2818047043917754411573069

theorem tailTrace_5488127 : CollatzResearch.WordTrace tailWord_5488127 prefixEnd_5488127 2818047043917754411573069 := by
  unfold tailWord_5488127
  simp only [CollatzResearch.WordTrace]
  refine ⟨200168436188460651314646635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133445624125640434209764423 200168436188460651314646635)
  ·
    refine ⟨300252654282690976971969953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200168436188460651314646635 300252654282690976971969953)
    ·
      refine ⟨225189490712018232728977465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300252654282690976971969953 225189490712018232728977465)
      ·
        refine ⟨168892118034013674546733099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225189490712018232728977465 168892118034013674546733099)
        ·
          refine ⟨253338177051020511820099649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168892118034013674546733099 253338177051020511820099649)
          ·
            refine ⟨190003632788265383865074737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253338177051020511820099649 190003632788265383865074737)
            ·
              refine ⟨142502724591199037898806053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190003632788265383865074737 142502724591199037898806053)
              ·
                refine ⟨26719260860849819606026135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142502724591199037898806053 26719260860849819606026135)
                ·
                  refine ⟨40078891291274729409039203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26719260860849819606026135 40078891291274729409039203)
                  ·
                    refine ⟨60118336936912094113558805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40078891291274729409039203 60118336936912094113558805)
                    ·
                      refine ⟨2818047043917754411573069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60118336936912094113558805 2818047043917754411573069)
                      ·
                        rfl

theorem cell23_5488127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_5488127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488127 prefixEnd_5488127 := by exact prefixLift 5488127
  have htrace : WordTrace (prefixWord ++ tailWord_5488127) baseStart_5488127 baseEnd_5488127 := by
    simpa [prefixWord, tailWord_5488127, baseEnd_5488127] using wordTrace_append hprefix tailTrace_5488127
  have hstable : (prefixWord ++ tailWord_5488127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488127).length < 2 ^ (prefixWord ++ tailWord_5488127).sum := by decide
  have hdescent : baseEnd_5488127 < baseStart_5488127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488182 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5488182 : Nat := 118140960795 + 5488182 * 2 ^ 59
def prefixEnd_5488182 : Nat := 4983230072969 + 3 ^ 40 * 5488182 * 2
def baseEnd_5488182 : Nat := 2818075285353751696385317

theorem tailTrace_5488182 : CollatzResearch.WordTrace tailWord_5488182 prefixEnd_5488182 2818075285353751696385317 := by
  unfold tailWord_5488182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12510652637703837231743675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133446961468840930471932533 12510652637703837231743675)
  ·
    refine ⟨18765978956555755847615513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12510652637703837231743675 18765978956555755847615513)
    ·
      refine ⟨14074484217416816885711635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18765978956555755847615513 14074484217416816885711635)
      ·
        refine ⟨21111726326125225328567453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14074484217416816885711635 21111726326125225328567453)
        ·
          refine ⟨7916897372296959498212795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21111726326125225328567453 7916897372296959498212795)
          ·
            refine ⟨11875346058445439247319193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916897372296959498212795 11875346058445439247319193)
            ·
              refine ⟨8906509543834079435489395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11875346058445439247319193 8906509543834079435489395)
              ·
                refine ⟨13359764315751119153234093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8906509543834079435489395 13359764315751119153234093)
                ·
                  refine ⟨5009911618406669682462785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13359764315751119153234093 5009911618406669682462785)
                  ·
                    refine ⟨3757433713805002261847089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5009911618406669682462785 3757433713805002261847089)
                    ·
                      refine ⟨2818075285353751696385317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757433713805002261847089 2818075285353751696385317)
                      ·
                        rfl

theorem cell23_5488182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5488182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488182 prefixEnd_5488182 := by exact prefixLift 5488182
  have htrace : WordTrace (prefixWord ++ tailWord_5488182) baseStart_5488182 baseEnd_5488182 := by
    simpa [prefixWord, tailWord_5488182, baseEnd_5488182] using wordTrace_append hprefix tailTrace_5488182
  have hstable : (prefixWord ++ tailWord_5488182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488182).length < 2 ^ (prefixWord ++ tailWord_5488182).sum := by decide
  have hdescent : baseEnd_5488182 < baseStart_5488182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488205 : List Nat := [1, 6, 1, 1, 4, 1, 2, 7]
def baseStart_5488205 : Nat := 118140960795 + 5488205 * 2 ^ 59
def prefixEnd_5488205 : Nat := 4983230072969 + 3 ^ 40 * 5488205 * 2
def baseEnd_5488205 : Nat := 104373596126252040977693

theorem tailTrace_5488205 : CollatzResearch.WordTrace tailWord_5488205 prefixEnd_5488205 104373596126252040977693 := by
  unfold tailWord_5488205
  simp only [CollatzResearch.WordTrace]
  refine ⟨200171281082178070635986069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133447520721452047090657379 200171281082178070635986069)
  ·
    refine ⟨9383028800727097061061847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200171281082178070635986069 9383028800727097061061847)
    ·
      refine ⟨14074543201090645591592771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9383028800727097061061847 14074543201090645591592771)
      ·
        refine ⟨21111814801635968387389157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14074543201090645591592771 21111814801635968387389157)
        ·
          refine ⟨3958465275306744072635467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21111814801635968387389157 3958465275306744072635467)
          ·
            refine ⟨5937697912960116108953201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958465275306744072635467 5937697912960116108953201)
            ·
              refine ⟨4453273434720087081714901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5937697912960116108953201 4453273434720087081714901)
              ·
                refine ⟨104373596126252040977693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4453273434720087081714901 104373596126252040977693)
                ·
                  rfl

theorem cell23_5488205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 7].length) (baseStart_5488205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488205 prefixEnd_5488205 := by exact prefixLift 5488205
  have htrace : WordTrace (prefixWord ++ tailWord_5488205) baseStart_5488205 baseEnd_5488205 := by
    simpa [prefixWord, tailWord_5488205, baseEnd_5488205] using wordTrace_append hprefix tailTrace_5488205
  have hstable : (prefixWord ++ tailWord_5488205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488205).length < 2 ^ (prefixWord ++ tailWord_5488205).sum := by decide
  have hdescent : baseEnd_5488205 < baseStart_5488205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488208 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2]
def baseStart_5488208 : Nat := 118140960795 + 5488208 * 2 ^ 59
def prefixEnd_5488208 : Nat := 4983230072969 + 3 ^ 40 * 5488208 * 2
def baseEnd_5488208 : Nat := 2818088635850768594660197

theorem tailTrace_5488208 : CollatzResearch.WordTrace tailWord_5488208 prefixEnd_5488208 2818088635850768594660197 := by
  unfold tailWord_5488208
  simp only [CollatzResearch.WordTrace]
  refine ⟨100085695250583601074172639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133447593667444801432230185 100085695250583601074172639)
  ·
    refine ⟨150128542875875401611258959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100085695250583601074172639 150128542875875401611258959)
    ·
      refine ⟨225192814313813102416888439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150128542875875401611258959 225192814313813102416888439)
      ·
        refine ⟨337789221470719653625332659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225192814313813102416888439 337789221470719653625332659)
        ·
          refine ⟨506683832206079480437998989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337789221470719653625332659 506683832206079480437998989)
          ·
            refine ⟨190006437077279805164249621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506683832206079480437998989 190006437077279805164249621)
            ·
              refine ⟨8906551737997490867074201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 190006437077279805164249621 8906551737997490867074201)
              ·
                refine ⟨6679913803498118150305651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8906551737997490867074201 6679913803498118150305651)
                ·
                  refine ⟨10019870705247177225458477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679913803498118150305651 10019870705247177225458477)
                  ·
                    refine ⟨3757451514467691459546929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10019870705247177225458477 3757451514467691459546929)
                    ·
                      refine ⟨2818088635850768594660197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757451514467691459546929 2818088635850768594660197)
                      ·
                        rfl

theorem cell23_5488208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2].length) (baseStart_5488208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488208 prefixEnd_5488208 := by exact prefixLift 5488208
  have htrace : WordTrace (prefixWord ++ tailWord_5488208) baseStart_5488208 baseEnd_5488208 := by
    simpa [prefixWord, tailWord_5488208, baseEnd_5488208] using wordTrace_append hprefix tailTrace_5488208
  have hstable : (prefixWord ++ tailWord_5488208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488208).length < 2 ^ (prefixWord ++ tailWord_5488208).sum := by decide
  have hdescent : baseEnd_5488208 < baseStart_5488208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488224 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_5488224 : Nat := 118140960795 + 5488224 * 2 ^ 59
def prefixEnd_5488224 : Nat := 4983230072969 + 3 ^ 40 * 5488224 * 2
def baseEnd_5488224 : Nat := 2818096851541240532060123

theorem tailTrace_5488224 : CollatzResearch.WordTrace tailWord_5488224 prefixEnd_5488224 2818096851541240532060123 := by
  unfold tailWord_5488224
  simp only [CollatzResearch.WordTrace]
  refine ⟨100085987034554618440463863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133447982712739491253951817 100085987034554618440463863)
  ·
    refine ⟨150128980551831927660695795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100085987034554618440463863 150128980551831927660695795)
    ·
      refine ⟨225193470827747891491043693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150128980551831927660695795 225193470827747891491043693)
      ·
        refine ⟨84447551560405459309141385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225193470827747891491043693 84447551560405459309141385)
        ·
          refine ⟨63335663670304094481856039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84447551560405459309141385 63335663670304094481856039)
          ·
            refine ⟨95003495505456141722784059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63335663670304094481856039 95003495505456141722784059)
            ·
              refine ⟨142505243258184212584176089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95003495505456141722784059 142505243258184212584176089)
              ·
                refine ⟨106878932443638159438132067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142505243258184212584176089 106878932443638159438132067)
                ·
                  refine ⟨160318398665457239157198101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106878932443638159438132067 160318398665457239157198101)
                  ·
                    refine ⟨7514924937443308085493661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160318398665457239157198101 7514924937443308085493661)
                    ·
                      refine ⟨2818096851541240532060123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7514924937443308085493661 2818096851541240532060123)
                      ·
                        rfl

theorem cell23_5488224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_5488224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488224 prefixEnd_5488224 := by exact prefixLift 5488224
  have htrace : WordTrace (prefixWord ++ tailWord_5488224) baseStart_5488224 baseEnd_5488224 := by
    simpa [prefixWord, tailWord_5488224, baseEnd_5488224] using wordTrace_append hprefix tailTrace_5488224
  have hstable : (prefixWord ++ tailWord_5488224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488224).length < 2 ^ (prefixWord ++ tailWord_5488224).sum := by decide
  have hdescent : baseEnd_5488224 < baseStart_5488224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488301 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5488301 : Nat := 118140960795 + 5488301 * 2 ^ 59
def prefixEnd_5488301 : Nat := 4983230072969 + 3 ^ 40 * 5488301 * 2
def baseEnd_5488301 : Nat := 2818136389551636730797269

theorem tailTrace_5488301 : CollatzResearch.WordTrace tailWord_5488301 prefixEnd_5488301 2818136389551636730797269 := by
  unfold tailWord_5488301
  simp only [CollatzResearch.WordTrace]
  refine ⟨200174782489830279031480757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133449854993220186020987171 200174782489830279031480757)
  ·
    refine ⟨18766385858421588659201321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200174782489830279031480757 18766385858421588659201321)
    ·
      refine ⟨14074789393816191494400991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18766385858421588659201321 14074789393816191494400991)
      ·
        refine ⟨21112184090724287241601487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14074789393816191494400991 21112184090724287241601487)
        ·
          refine ⟨31668276136086430862402231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21112184090724287241601487 31668276136086430862402231)
          ·
            refine ⟨47502414204129646293603347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31668276136086430862402231 47502414204129646293603347)
            ·
              refine ⟨71253621306194469440405021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47502414204129646293603347 71253621306194469440405021)
              ·
                refine ⟨26720107989822926040151883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71253621306194469440405021 26720107989822926040151883)
                ·
                  refine ⟨40080161984734389060227825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26720107989822926040151883 40080161984734389060227825)
                  ·
                    refine ⟨30060121488550791795170869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40080161984734389060227825 30060121488550791795170869)
                    ·
                      refine ⟨2818136389551636730797269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30060121488550791795170869 2818136389551636730797269)
                      ·
                        rfl

theorem cell23_5488301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5488301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488301 prefixEnd_5488301 := by exact prefixLift 5488301
  have htrace : WordTrace (prefixWord ++ tailWord_5488301) baseStart_5488301 baseEnd_5488301 := by
    simpa [prefixWord, tailWord_5488301, baseEnd_5488301] using wordTrace_append hprefix tailTrace_5488301
  have hstable : (prefixWord ++ tailWord_5488301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488301).length < 2 ^ (prefixWord ++ tailWord_5488301).sum := by decide
  have hdescent : baseEnd_5488301 < baseStart_5488301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488355 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 3, 4]
def baseStart_5488355 : Nat := 118140960795 + 5488355 * 2 ^ 59
def prefixEnd_5488355 : Nat := 4983230072969 + 3 ^ 40 * 5488355 * 2
def baseEnd_5488355 : Nat := 939388039168993173174007

theorem tailTrace_5488355 : CollatzResearch.WordTrace tailWord_5488355 prefixEnd_5488355 939388039168993173174007 := by
  unfold tailWord_5488355
  simp only [CollatzResearch.WordTrace]
  refine ⟨200176752031634646253946519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133451168021089764169297679 200176752031634646253946519)
  ·
    refine ⟨300265128047451969380919779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200176752031634646253946519 300265128047451969380919779)
    ·
      refine ⟨450397692071177954071379669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300265128047451969380919779 450397692071177954071379669)
      ·
        refine ⟨10556195907918233298547961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 450397692071177954071379669 10556195907918233298547961)
        ·
          refine ⟨7917146930938674973910971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10556195907918233298547961 7917146930938674973910971)
          ·
            refine ⟨11875720396408012460866457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917146930938674973910971 11875720396408012460866457)
            ·
              refine ⟨8906790297306009345649843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11875720396408012460866457 8906790297306009345649843)
              ·
                refine ⟨13360185445959014018474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8906790297306009345649843 13360185445959014018474765)
                ·
                  refine ⟨5010069542234630256928037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13360185445959014018474765 5010069542234630256928037)
                  ·
                    refine ⟨939388039168993173174007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010069542234630256928037 939388039168993173174007)
                    ·
                      rfl

theorem cell23_5488355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 4].length) (baseStart_5488355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488355 prefixEnd_5488355 := by exact prefixLift 5488355
  have htrace : WordTrace (prefixWord ++ tailWord_5488355) baseStart_5488355 baseEnd_5488355 := by
    simpa [prefixWord, tailWord_5488355, baseEnd_5488355] using wordTrace_append hprefix tailTrace_5488355
  have hstable : (prefixWord ++ tailWord_5488355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488355).length < 2 ^ (prefixWord ++ tailWord_5488355).sum := by decide
  have hdescent : baseEnd_5488355 < baseStart_5488355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488372 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5488372 : Nat := 118140960795 + 5488372 * 2 ^ 59
def prefixEnd_5488372 : Nat := 4983230072969 + 3 ^ 40 * 5488372 * 2
def baseEnd_5488372 : Nat := 939390948892701984336481

theorem tailTrace_5488372 : CollatzResearch.WordTrace tailWord_5488372 prefixEnd_5488372 939390948892701984336481 := by
  unfold tailWord_5488372
  simp only [CollatzResearch.WordTrace]
  refine ⟨100088686036286529078657685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133451581381715372104876913 100088686036286529078657685)
  ·
    refine ⟨4691657157950931050562079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100088686036286529078657685 4691657157950931050562079)
    ·
      refine ⟨7037485736926396575843119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4691657157950931050562079 7037485736926396575843119)
      ·
        refine ⟨10556228605389594863764679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037485736926396575843119 10556228605389594863764679)
        ·
          refine ⟨15834342908084392295647019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10556228605389594863764679 15834342908084392295647019)
          ·
            refine ⟨23751514362126588443470529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15834342908084392295647019 23751514362126588443470529)
            ·
              refine ⟨17813635771594941332602897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23751514362126588443470529 17813635771594941332602897)
              ·
                refine ⟨13360226828696205999452173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17813635771594941332602897 13360226828696205999452173)
                ·
                  refine ⟨5010085060761077249794565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13360226828696205999452173 5010085060761077249794565)
                  ·
                    refine ⟨939390948892701984336481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010085060761077249794565 939390948892701984336481)
                    ·
                      rfl

theorem cell23_5488372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5488372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488372 prefixEnd_5488372 := by exact prefixLift 5488372
  have htrace : WordTrace (prefixWord ++ tailWord_5488372) baseStart_5488372 baseEnd_5488372 := by
    simpa [prefixWord, tailWord_5488372, baseEnd_5488372] using wordTrace_append hprefix tailTrace_5488372
  have hstable : (prefixWord ++ tailWord_5488372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488372).length < 2 ^ (prefixWord ++ tailWord_5488372).sum := by decide
  have hdescent : baseEnd_5488372 < baseStart_5488372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488398 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_5488398 : Nat := 118140960795 + 5488398 * 2 ^ 59
def prefixEnd_5488398 : Nat := 4983230072969 + 3 ^ 40 * 5488398 * 2
def baseEnd_5488398 : Nat := 939395399058374283761441

theorem tailTrace_5488398 : CollatzResearch.WordTrace tailWord_5488398 prefixEnd_5488398 939395399058374283761441 := by
  unfold tailWord_5488398
  simp only [CollatzResearch.WordTrace]
  refine ⟨25022290046309858074720231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133452213580319243065174565 25022290046309858074720231)
  ·
    refine ⟨37533435069464787112080347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25022290046309858074720231 37533435069464787112080347)
    ·
      refine ⟨56300152604197180668120521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37533435069464787112080347 56300152604197180668120521)
      ·
        refine ⟨42225114453147885501090391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56300152604197180668120521 42225114453147885501090391)
        ·
          refine ⟨63337671679721828251635587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42225114453147885501090391 63337671679721828251635587)
          ·
            refine ⟨95006507519582742377453381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63337671679721828251635587 95006507519582742377453381)
            ·
              refine ⟨17813720159921764195772509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95006507519582742377453381 17813720159921764195772509)
              ·
                refine ⟨6680145059970661573414691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17813720159921764195772509 6680145059970661573414691)
                ·
                  refine ⟨10020217589955992360122037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680145059970661573414691 10020217589955992360122037)
                  ·
                    refine ⟨939395399058374283761441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10020217589955992360122037 939395399058374283761441)
                    ·
                      rfl

theorem cell23_5488398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_5488398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488398 prefixEnd_5488398 := by exact prefixLift 5488398
  have htrace : WordTrace (prefixWord ++ tailWord_5488398) baseStart_5488398 baseEnd_5488398 := by
    simpa [prefixWord, tailWord_5488398, baseEnd_5488398] using wordTrace_append hprefix tailTrace_5488398
  have hstable : (prefixWord ++ tailWord_5488398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488398).length < 2 ^ (prefixWord ++ tailWord_5488398).sum := by decide
  have hdescent : baseEnd_5488398 < baseStart_5488398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488401 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_5488401 : Nat := 118140960795 + 5488401 * 2 ^ 59
def prefixEnd_5488401 : Nat := 4983230072969 + 3 ^ 40 * 5488401 * 2
def baseEnd_5488401 : Nat := 2818187737617086339546809

theorem tailTrace_5488401 : CollatzResearch.WordTrace tailWord_5488401 prefixEnd_5488401 2818187737617086339546809 := by
  unfold tailWord_5488401
  simp only [CollatzResearch.WordTrace]
  refine ⟨200178429789467996110121057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133452286526311997406747371 200178429789467996110121057)
  ·
    refine ⟨150133822342100997082590793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200178429789467996110121057 150133822342100997082590793)
    ·
      refine ⟨112600366756575747811943095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150133822342100997082590793 112600366756575747811943095)
      ·
        refine ⟨168900550134863621717914643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112600366756575747811943095 168900550134863621717914643)
        ·
          refine ⟨253350825202295432576871965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168900550134863621717914643 253350825202295432576871965)
          ·
            refine ⟨95006559450860787216326987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253350825202295432576871965 95006559450860787216326987)
            ·
              refine ⟨142509839176291180824490481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95006559450860787216326987 142509839176291180824490481)
              ·
                refine ⟨106882379382218385618367861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142509839176291180824490481 106882379382218385618367861)
                ·
                  refine ⟨10020223067082973651721987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106882379382218385618367861 10020223067082973651721987)
                  ·
                    refine ⟨15030334600624460477582981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10020223067082973651721987 15030334600624460477582981)
                    ·
                      refine ⟨2818187737617086339546809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15030334600624460477582981 2818187737617086339546809)
                      ·
                        rfl

theorem cell23_5488401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_5488401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488401 prefixEnd_5488401 := by exact prefixLift 5488401
  have htrace : WordTrace (prefixWord ++ tailWord_5488401) baseStart_5488401 baseEnd_5488401 := by
    simpa [prefixWord, tailWord_5488401, baseEnd_5488401] using wordTrace_append hprefix tailTrace_5488401
  have hstable : (prefixWord ++ tailWord_5488401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488401).length < 2 ^ (prefixWord ++ tailWord_5488401).sum := by decide
  have hdescent : baseEnd_5488401 < baseStart_5488401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488405 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_5488405 : Nat := 118140960795 + 5488405 * 2 ^ 59
def prefixEnd_5488405 : Nat := 4983230072969 + 3 ^ 40 * 5488405 * 2
def baseEnd_5488405 : Nat := 2818189791539704323896791

theorem tailTrace_5488405 : CollatzResearch.WordTrace tailWord_5488405 prefixEnd_5488405 2818189791539704323896791 := by
  unfold tailWord_5488405
  simp only [CollatzResearch.WordTrace]
  refine ⟨200178575681453504793266669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133452383787635669862177779 200178575681453504793266669)
  ·
    refine ⟨75066965880545064297475001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200178575681453504793266669 75066965880545064297475001)
    ·
      refine ⟨56300224410408798223106251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75066965880545064297475001 56300224410408798223106251)
      ·
        refine ⟨84450336615613197334659377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56300224410408798223106251 84450336615613197334659377)
        ·
          refine ⟨63337752461709898000994533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84450336615613197334659377 63337752461709898000994533)
          ·
            refine ⟨11875828586570605875186475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63337752461709898000994533 11875828586570605875186475)
            ·
              refine ⟨17813742879855908812779713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11875828586570605875186475 17813742879855908812779713)
              ·
                refine ⟨13360307159891931609584785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17813742879855908812779713 13360307159891931609584785)
                ·
                  refine ⟨10020230369918948707188589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13360307159891931609584785 10020230369918948707188589)
                  ·
                    refine ⟨3757586388719605765195721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10020230369918948707188589 3757586388719605765195721)
                    ·
                      refine ⟨2818189791539704323896791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757586388719605765195721 2818189791539704323896791)
                      ·
                        rfl

theorem cell23_5488405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_5488405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488405 prefixEnd_5488405 := by exact prefixLift 5488405
  have htrace : WordTrace (prefixWord ++ tailWord_5488405) baseStart_5488405 baseEnd_5488405 := by
    simpa [prefixWord, tailWord_5488405, baseEnd_5488405] using wordTrace_append hprefix tailTrace_5488405
  have hstable : (prefixWord ++ tailWord_5488405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488405).length < 2 ^ (prefixWord ++ tailWord_5488405).sum := by decide
  have hdescent : baseEnd_5488405 < baseStart_5488405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488418 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_5488418 : Nat := 118140960795 + 5488418 * 2 ^ 59
def prefixEnd_5488418 : Nat := 4983230072969 + 3 ^ 40 * 5488418 * 2
def baseEnd_5488418 : Nat := 2818196466788212773034231

theorem tailTrace_5488418 : CollatzResearch.WordTrace tailWord_5488418 prefixEnd_5488418 2818196466788212773034231 := by
  unfold tailWord_5488418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50044762457601602003372477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133452699886937605342326605 50044762457601602003372477)
  ·
    refine ⟨18766785921600600751264679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50044762457601602003372477 18766785921600600751264679)
    ·
      refine ⟨28150178882400901126897019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18766785921600600751264679 28150178882400901126897019)
      ·
        refine ⟨42225268323601351690345529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28150178882400901126897019 42225268323601351690345529)
        ·
          refine ⟨31668951242701013767759147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42225268323601351690345529 31668951242701013767759147)
          ·
            refine ⟨47503426864051520651638721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31668951242701013767759147 47503426864051520651638721)
            ·
              refine ⟨35627570148038640488729041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47503426864051520651638721 35627570148038640488729041)
              ·
                refine ⟨26720677611028980366546781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35627570148038640488729041 26720677611028980366546781)
                ·
                  refine ⟨10020254104135867637455043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26720677611028980366546781 10020254104135867637455043)
                  ·
                    refine ⟨15030381156203801456182565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10020254104135867637455043 15030381156203801456182565)
                    ·
                      refine ⟨2818196466788212773034231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15030381156203801456182565 2818196466788212773034231)
                      ·
                        rfl

theorem cell23_5488418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_5488418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488418 prefixEnd_5488418 := by exact prefixLift 5488418
  have htrace : WordTrace (prefixWord ++ tailWord_5488418) baseStart_5488418 baseEnd_5488418 := by
    simpa [prefixWord, tailWord_5488418, baseEnd_5488418] using wordTrace_append hprefix tailTrace_5488418
  have hstable : (prefixWord ++ tailWord_5488418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488418).length < 2 ^ (prefixWord ++ tailWord_5488418).sum := by decide
  have hdescent : baseEnd_5488418 < baseStart_5488418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488469 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_5488469 : Nat := 118140960795 + 5488469 * 2 ^ 59
def prefixEnd_5488469 : Nat := 4983230072969 + 3 ^ 40 * 5488469 * 2
def baseEnd_5488469 : Nat := 2818222654301592073496497

theorem tailTrace_5488469 : CollatzResearch.WordTrace tailWord_5488469 prefixEnd_5488469 2818222654301592073496497 := by
  unfold tailWord_5488469
  simp only [CollatzResearch.WordTrace]
  refine ⟨200180909953221643723596461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133453939968814429149064307 200180909953221643723596461)
  ·
    refine ⟨75067841232458116396348673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200180909953221643723596461 75067841232458116396348673)
    ·
      refine ⟨56300880924343587297261505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75067841232458116396348673 56300880924343587297261505)
      ·
        refine ⟨42225660693257690472946129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56300880924343587297261505 42225660693257690472946129)
        ·
          refine ⟨31669245519943267854709597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42225660693257690472946129 31669245519943267854709597)
          ·
            refine ⟨11875967069978725445516099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31669245519943267854709597 11875967069978725445516099)
            ·
              refine ⟨17813950604968088168274149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11875967069978725445516099 17813950604968088168274149)
              ·
                refine ⟨3340115738431516531551403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17813950604968088168274149 3340115738431516531551403)
                ·
                  refine ⟨5010173607647274797327105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340115738431516531551403 5010173607647274797327105)
                  ·
                    refine ⟨3757630205735456097995329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010173607647274797327105 3757630205735456097995329)
                    ·
                      refine ⟨2818222654301592073496497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757630205735456097995329 2818222654301592073496497)
                      ·
                        rfl

theorem cell23_5488469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_5488469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488469 prefixEnd_5488469 := by exact prefixLift 5488469
  have htrace : WordTrace (prefixWord ++ tailWord_5488469) baseStart_5488469 baseEnd_5488469 := by
    simpa [prefixWord, tailWord_5488469, baseEnd_5488469] using wordTrace_append hprefix tailTrace_5488469
  have hstable : (prefixWord ++ tailWord_5488469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488469).length < 2 ^ (prefixWord ++ tailWord_5488469).sum := by decide
  have hdescent : baseEnd_5488469 < baseStart_5488469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488491 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_5488491 : Nat := 118140960795 + 5488491 * 2 ^ 59
def prefixEnd_5488491 : Nat := 4983230072969 + 3 ^ 40 * 5488491 * 2
def baseEnd_5488491 : Nat := 2818233950875990987421395

theorem tailTrace_5488491 : CollatzResearch.WordTrace tailWord_5488491 prefixEnd_5488491 2818233950875990987421395 := by
  unfold tailWord_5488491
  simp only [CollatzResearch.WordTrace]
  refine ⟨200181712359141941480897327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133454474906094627653931551 200181712359141941480897327)
  ·
    refine ⟨300272568538712912221345991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200181712359141941480897327 300272568538712912221345991)
    ·
      refine ⟨450408852808069368332018987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300272568538712912221345991 450408852808069368332018987)
      ·
        refine ⟨675613279212104052498028481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450408852808069368332018987 675613279212104052498028481)
        ·
          refine ⟨506709959409078039373521361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675613279212104052498028481 506709959409078039373521361)
          ·
            refine ⟨380032469556808529530141021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506709959409078039373521361 380032469556808529530141021)
            ·
              refine ⟨142512176083803198573802883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380032469556808529530141021 142512176083803198573802883)
              ·
                refine ⟨213768264125704797860704325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142512176083803198573802883 213768264125704797860704325)
                ·
                  refine ⟨40081549523569649598882061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213768264125704797860704325 40081549523569649598882061)
                  ·
                    refine ⟨15030581071338618599580773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40081549523569649598882061 15030581071338618599580773)
                    ·
                      refine ⟨2818233950875990987421395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15030581071338618599580773 2818233950875990987421395)
                      ·
                        rfl

theorem cell23_5488491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_5488491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488491 prefixEnd_5488491 := by exact prefixLift 5488491
  have htrace : WordTrace (prefixWord ++ tailWord_5488491) baseStart_5488491 baseEnd_5488491 := by
    simpa [prefixWord, tailWord_5488491, baseEnd_5488491] using wordTrace_append hprefix tailTrace_5488491
  have hstable : (prefixWord ++ tailWord_5488491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488491).length < 2 ^ (prefixWord ++ tailWord_5488491).sum := by decide
  have hdescent : baseEnd_5488491 < baseStart_5488491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488511 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_5488511 : Nat := 118140960795 + 5488511 * 2 ^ 59
def prefixEnd_5488511 : Nat := 4983230072969 + 3 ^ 40 * 5488511 * 2
def baseEnd_5488511 : Nat := 2818244220489080909171303

theorem tailTrace_5488511 : CollatzResearch.WordTrace tailWord_5488511 prefixEnd_5488511 2818244220489080909171303 := by
  unfold tailWord_5488511
  simp only [CollatzResearch.WordTrace]
  refine ⟨200182441819069484896625387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133454961212712989931083591 200182441819069484896625387)
  ·
    refine ⟨300273662728604227344938081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200182441819069484896625387 300273662728604227344938081)
    ·
      refine ⟨225205247046453170508703561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300273662728604227344938081 225205247046453170508703561)
      ·
        refine ⟨168903935284839877881527671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225205247046453170508703561 168903935284839877881527671)
        ·
          refine ⟨253355902927259816822291507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168903935284839877881527671 253355902927259816822291507)
          ·
            refine ⟨380033854390889725233437261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253355902927259816822291507 380033854390889725233437261)
            ·
              refine ⟨142512695396583646962538973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380033854390889725233437261 142512695396583646962538973)
              ·
                refine ⟨53442260773718867610952115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142512695396583646962538973 53442260773718867610952115)
                ·
                  refine ⟨80163391160578301416428173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53442260773718867610952115 80163391160578301416428173)
                  ·
                    refine ⟨30061271685216863031160565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80163391160578301416428173 30061271685216863031160565)
                    ·
                      refine ⟨2818244220489080909171303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30061271685216863031160565 2818244220489080909171303)
                      ·
                        rfl

theorem cell23_5488511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_5488511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488511 prefixEnd_5488511 := by exact prefixLift 5488511
  have htrace : WordTrace (prefixWord ++ tailWord_5488511) baseStart_5488511 baseEnd_5488511 := by
    simpa [prefixWord, tailWord_5488511, baseEnd_5488511] using wordTrace_append hprefix tailTrace_5488511
  have hstable : (prefixWord ++ tailWord_5488511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488511).length < 2 ^ (prefixWord ++ tailWord_5488511).sum := by decide
  have hdescent : baseEnd_5488511 < baseStart_5488511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488519 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_5488519 : Nat := 118140960795 + 5488519 * 2 ^ 59
def prefixEnd_5488519 : Nat := 4983230072969 + 3 ^ 40 * 5488519 * 2
def baseEnd_5488519 : Nat := 2818248328334316877871267

theorem tailTrace_5488519 : CollatzResearch.WordTrace tailWord_5488519 prefixEnd_5488519 2818248328334316877871267 := by
  unfold tailWord_5488519
  simp only [CollatzResearch.WordTrace]
  refine ⟨200182733603040502262916611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133455155735360334841944407 200182733603040502262916611)
  ·
    refine ⟨300274100404560753394374917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200182733603040502262916611 300274100404560753394374917)
    ·
      refine ⟨56301393825855141261445297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300274100404560753394374917 56301393825855141261445297)
      ·
        refine ⟨42226045369391355946083973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56301393825855141261445297 42226045369391355946083973)
        ·
          refine ⟨7917383506760879239890745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42226045369391355946083973 7917383506760879239890745)
          ·
            refine ⟨5938037630070659429918059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917383506760879239890745 5938037630070659429918059)
            ·
              refine ⟨8907056445105989144877089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938037630070659429918059 8907056445105989144877089)
              ·
                refine ⟨6680292333829491858657817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8907056445105989144877089 6680292333829491858657817)
                ·
                  refine ⟨5010219250372118893993363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6680292333829491858657817 5010219250372118893993363)
                  ·
                    refine ⟨7515328875558178340990045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010219250372118893993363 7515328875558178340990045)
                    ·
                      refine ⟨2818248328334316877871267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515328875558178340990045 2818248328334316877871267)
                      ·
                        rfl

theorem cell23_5488519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_5488519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488519 prefixEnd_5488519 := by exact prefixLift 5488519
  have htrace : WordTrace (prefixWord ++ tailWord_5488519) baseStart_5488519 baseEnd_5488519 := by
    simpa [prefixWord, tailWord_5488519, baseEnd_5488519] using wordTrace_append hprefix tailTrace_5488519
  have hstable : (prefixWord ++ tailWord_5488519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488519).length < 2 ^ (prefixWord ++ tailWord_5488519).sum := by decide
  have hdescent : baseEnd_5488519 < baseStart_5488519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488536 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5488536 : Nat := 118140960795 + 5488536 * 2 ^ 59
def prefixEnd_5488536 : Nat := 4983230072969 + 3 ^ 40 * 5488536 * 2
def baseEnd_5488536 : Nat := 2818257057505443311358689

theorem tailTrace_5488536 : CollatzResearch.WordTrace tailWord_5488536 prefixEnd_5488536 2818257057505443311358689 := by
  unfold tailWord_5488536
  simp only [CollatzResearch.WordTrace]
  refine ⟨100091676821989457083142731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133455569095985942777523641 100091676821989457083142731)
  ·
    refine ⟨150137515232984185624714097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100091676821989457083142731 150137515232984185624714097)
    ·
      refine ⟨112603136424738139218535573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150137515232984185624714097 112603136424738139218535573)
      ·
        refine ⟨5278272019909600275868855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112603136424738139218535573 5278272019909600275868855)
        ·
          refine ⟨7917408029864400413803283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278272019909600275868855 7917408029864400413803283)
          ·
            refine ⟨11876112044796600620704925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917408029864400413803283 11876112044796600620704925)
            ·
              refine ⟨4453542016798725232764347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876112044796600620704925 4453542016798725232764347)
              ·
                refine ⟨6680313025198087849146521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453542016798725232764347 6680313025198087849146521)
                ·
                  refine ⟨5010234768898565886859891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6680313025198087849146521 5010234768898565886859891)
                  ·
                    refine ⟨7515352153347848830289837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010234768898565886859891 7515352153347848830289837)
                    ·
                      refine ⟨2818257057505443311358689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515352153347848830289837 2818257057505443311358689)
                      ·
                        rfl

theorem cell23_5488536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5488536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488536 prefixEnd_5488536 := by exact prefixLift 5488536
  have htrace : WordTrace (prefixWord ++ tailWord_5488536) baseStart_5488536 baseEnd_5488536 := by
    simpa [prefixWord, tailWord_5488536, baseEnd_5488536] using wordTrace_append hprefix tailTrace_5488536
  have hstable : (prefixWord ++ tailWord_5488536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488536).length < 2 ^ (prefixWord ++ tailWord_5488536).sum := by decide
  have hdescent : baseEnd_5488536 < baseStart_5488536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488548 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 7]
def baseStart_5488548 : Nat := 118140960795 + 5488548 * 2 ^ 59
def prefixEnd_5488548 : Nat := 4983230072969 + 3 ^ 40 * 5488548 * 2
def baseEnd_5488548 : Nat := 313140357697033029378737

theorem tailTrace_5488548 : CollatzResearch.WordTrace tailWord_5488548 prefixEnd_5488548 313140357697033029378737 := by
  unfold tailWord_5488548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100091895659967720107861149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133455860879956960143814865 100091895659967720107861149)
  ·
    refine ⟨37534460872487895040447931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100091895659967720107861149 37534460872487895040447931)
    ·
      refine ⟨56301691308731842560671897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37534460872487895040447931 56301691308731842560671897)
      ·
        refine ⟨42226268481548881920503923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56301691308731842560671897 42226268481548881920503923)
        ·
          refine ⟨63339402722323322880755885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42226268481548881920503923 63339402722323322880755885)
          ·
            refine ⟨23752276020871246080283457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63339402722323322880755885 23752276020871246080283457)
            ·
              refine ⟨17814207015653434560212593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23752276020871246080283457 17814207015653434560212593)
              ·
                refine ⟨13360655261740075920159445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17814207015653434560212593 13360655261740075920159445)
                ·
                  refine ⟨313140357697033029378737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13360655261740075920159445 313140357697033029378737)
                  ·
                    rfl

theorem cell23_5488548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_5488548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488548 prefixEnd_5488548 := by exact prefixLift 5488548
  have htrace : WordTrace (prefixWord ++ tailWord_5488548) baseStart_5488548 baseEnd_5488548 := by
    simpa [prefixWord, tailWord_5488548, baseEnd_5488548] using wordTrace_append hprefix tailTrace_5488548
  have hstable : (prefixWord ++ tailWord_5488548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488548).length < 2 ^ (prefixWord ++ tailWord_5488548).sum := by decide
  have hdescent : baseEnd_5488548 < baseStart_5488548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488588 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5488588 : Nat := 118140960795 + 5488588 * 2 ^ 59
def prefixEnd_5488588 : Nat := 4983230072969 + 3 ^ 40 * 5488588 * 2
def baseEnd_5488588 : Nat := 2818283758499477107908449

theorem tailTrace_5488588 : CollatzResearch.WordTrace tailWord_5488588 prefixEnd_5488588 2818283758499477107908449 := by
  unfold tailWord_5488588
  simp only [CollatzResearch.WordTrace]
  refine ⟨100092625119895263523589209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133456833493193684698118945 100092625119895263523589209)
  ·
    refine ⟨75069468839921447642691907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100092625119895263523589209 75069468839921447642691907)
    ·
      refine ⟨112604203259882171464037861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75069468839921447642691907 112604203259882171464037861)
      ·
        refine ⟨21113288111227907149507099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112604203259882171464037861 21113288111227907149507099)
        ·
          refine ⟨31669932166841860724260649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21113288111227907149507099 31669932166841860724260649)
          ·
            refine ⟨23752449125131395543195487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31669932166841860724260649 23752449125131395543195487)
            ·
              refine ⟨35628673687697093314793231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23752449125131395543195487 35628673687697093314793231)
              ·
                refine ⟨53443010531545639972189847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35628673687697093314793231 53443010531545639972189847)
                ·
                  refine ⟨80164515797318459958284771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53443010531545639972189847 80164515797318459958284771)
                  ·
                    refine ⟨120246773695977689937427157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80164515797318459958284771 120246773695977689937427157)
                    ·
                      refine ⟨2818283758499477107908449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120246773695977689937427157 2818283758499477107908449)
                      ·
                        rfl

theorem cell23_5488588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5488588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488588 prefixEnd_5488588 := by exact prefixLift 5488588
  have htrace : WordTrace (prefixWord ++ tailWord_5488588) baseStart_5488588 baseEnd_5488588 := by
    simpa [prefixWord, tailWord_5488588, baseEnd_5488588] using wordTrace_append hprefix tailTrace_5488588
  have hstable : (prefixWord ++ tailWord_5488588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488588).length < 2 ^ (prefixWord ++ tailWord_5488588).sum := by decide
  have hdescent : baseEnd_5488588 < baseStart_5488588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488635 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3]
def baseStart_5488635 : Nat := 118140960795 + 5488635 * 2 ^ 59
def prefixEnd_5488635 : Nat := 4983230072969 + 3 ^ 40 * 5488635 * 2
def baseEnd_5488635 : Nat := 2818307892090238424020733

theorem tailTrace_5488635 : CollatzResearch.WordTrace tailWord_5488635 prefixEnd_5488635 2818307892090238424020733 := by
  unfold tailWord_5488635
  simp only [CollatzResearch.WordTrace]
  refine ⟨200186964470620254074139359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133457976313746836049426239 200186964470620254074139359)
  ·
    refine ⟨300280446705930381111209039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200186964470620254074139359 300280446705930381111209039)
    ·
      refine ⟨450420670058895571666813559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300280446705930381111209039 450420670058895571666813559)
      ·
        refine ⟨675631005088343357500220339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450420670058895571666813559 675631005088343357500220339)
        ·
          refine ⟨1013446507632515036250330509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675631005088343357500220339 1013446507632515036250330509)
          ·
            refine ⟨380042440362193138593873941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1013446507632515036250330509 380042440362193138593873941)
            ·
              refine ⟨17814489391977803371587841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380042440362193138593873941 17814489391977803371587841)
              ·
                refine ⟨13360867043983352528690881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17814489391977803371587841 13360867043983352528690881)
                ·
                  refine ⟨10020650282987514396518161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13360867043983352528690881 10020650282987514396518161)
                  ·
                    refine ⟨7515487712240635797388621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10020650282987514396518161 7515487712240635797388621)
                    ·
                      refine ⟨2818307892090238424020733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515487712240635797388621 2818307892090238424020733)
                      ·
                        rfl

theorem cell23_5488635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3].length) (baseStart_5488635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488635 prefixEnd_5488635 := by exact prefixLift 5488635
  have htrace : WordTrace (prefixWord ++ tailWord_5488635) baseStart_5488635 baseEnd_5488635 := by
    simpa [prefixWord, tailWord_5488635, baseEnd_5488635] using wordTrace_append hprefix tailTrace_5488635
  have hstable : (prefixWord ++ tailWord_5488635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488635).length < 2 ^ (prefixWord ++ tailWord_5488635).sum := by decide
  have hdescent : baseEnd_5488635 < baseStart_5488635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488669 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_5488669 : Nat := 118140960795 + 5488669 * 2 ^ 59
def prefixEnd_5488669 : Nat := 4983230072969 + 3 ^ 40 * 5488669 * 2
def baseEnd_5488669 : Nat := 2818325350432491290995577

theorem tailTrace_5488669 : CollatzResearch.WordTrace tailWord_5488669 prefixEnd_5488669 2818325350432491290995577 := by
  unfold tailWord_5488669
  simp only [CollatzResearch.WordTrace]
  refine ⟨200188204552497077880877061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133458803034998051920584707 200188204552497077880877061)
  ·
    refine ⟨37535288353593202102664449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200188204552497077880877061 37535288353593202102664449)
    ·
      refine ⟨28151466265194901576998337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37535288353593202102664449 28151466265194901576998337)
      ·
        refine ⟨21113599698896176182748753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28151466265194901576998337 21113599698896176182748753)
        ·
          refine ⟨15835199774172132137061565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21113599698896176182748753 15835199774172132137061565)
          ·
            refine ⟨5938199915314549551398087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15835199774172132137061565 5938199915314549551398087)
            ·
              refine ⟨8907299872971824327097131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938199915314549551398087 8907299872971824327097131)
              ·
                refine ⟨13360949809457736490645697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907299872971824327097131 13360949809457736490645697)
                ·
                  refine ⟨10020712357093302367984273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13360949809457736490645697 10020712357093302367984273)
                  ·
                    refine ⟨7515534267819976775988205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10020712357093302367984273 7515534267819976775988205)
                    ·
                      refine ⟨2818325350432491290995577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515534267819976775988205 2818325350432491290995577)
                      ·
                        rfl

theorem cell23_5488669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_5488669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488669 prefixEnd_5488669 := by exact prefixLift 5488669
  have htrace : WordTrace (prefixWord ++ tailWord_5488669) baseStart_5488669 baseEnd_5488669 := by
    simpa [prefixWord, tailWord_5488669, baseEnd_5488669] using wordTrace_append hprefix tailTrace_5488669
  have hstable : (prefixWord ++ tailWord_5488669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488669).length < 2 ^ (prefixWord ++ tailWord_5488669).sum := by decide
  have hdescent : baseEnd_5488669 < baseStart_5488669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488676 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_5488676 : Nat := 118140960795 + 5488676 * 2 ^ 59
def prefixEnd_5488676 : Nat := 4983230072969 + 3 ^ 40 * 5488676 * 2
def baseEnd_5488676 : Nat := 939442981599024254536015

theorem tailTrace_5488676 : CollatzResearch.WordTrace tailWord_5488676 prefixEnd_5488676 939442981599024254536015 := by
  unfold tailWord_5488676
  simp only [CollatzResearch.WordTrace]
  refine ⟨100094229931735859038190941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133458973242314478717587921 100094229931735859038190941)
  ·
    refine ⟨37535336224400947139321603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100094229931735859038190941 37535336224400947139321603)
    ·
      refine ⟨56303004336601420708982405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37535336224400947139321603 56303004336601420708982405)
      ·
        refine ⟨10556813313112766382934201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56303004336601420708982405 10556813313112766382934201)
        ·
          refine ⟨7917609984834574787200651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10556813313112766382934201 7917609984834574787200651)
          ·
            refine ⟨11876414977251862180800977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7917609984834574787200651 11876414977251862180800977)
            ·
              refine ⟨8907311232938896635600733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11876414977251862180800977 8907311232938896635600733)
              ·
                refine ⟨3340241712352086238350275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8907311232938896635600733 3340241712352086238350275)
                ·
                  refine ⟨5010362568528129357525413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340241712352086238350275 5010362568528129357525413)
                  ·
                    refine ⟨939442981599024254536015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010362568528129357525413 939442981599024254536015)
                    ·
                      rfl

theorem cell23_5488676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_5488676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488676 prefixEnd_5488676 := by exact prefixLift 5488676
  have htrace : WordTrace (prefixWord ++ tailWord_5488676) baseStart_5488676 baseEnd_5488676 := by
    simpa [prefixWord, tailWord_5488676, baseEnd_5488676] using wordTrace_append hprefix tailTrace_5488676
  have hstable : (prefixWord ++ tailWord_5488676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488676).length < 2 ^ (prefixWord ++ tailWord_5488676).sum := by decide
  have hdescent : baseEnd_5488676 < baseStart_5488676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488726 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5488726 : Nat := 118140960795 + 5488726 * 2 ^ 59
def prefixEnd_5488726 : Nat := 4983230072969 + 3 ^ 40 * 5488726 * 2
def baseEnd_5488726 : Nat := 2818354618829797567982815

theorem tailTrace_5488726 : CollatzResearch.WordTrace tailWord_5488726 prefixEnd_5488726 2818354618829797567982815 := by
  unfold tailWord_5488726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511892719580661038481377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133460189008860384410468021 12511892719580661038481377)
  ·
    refine ⟨9383919539685495778861033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12511892719580661038481377 9383919539685495778861033)
    ·
      refine ⟨7037939654764121834145775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9383919539685495778861033 7037939654764121834145775)
      ·
        refine ⟨10556909482146182751218663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037939654764121834145775 10556909482146182751218663)
        ·
          refine ⟨15835364223219274126827995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10556909482146182751218663 15835364223219274126827995)
          ·
            refine ⟨23753046334828911190241993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835364223219274126827995 23753046334828911190241993)
            ·
              refine ⟨17814784751121683392681495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23753046334828911190241993 17814784751121683392681495)
              ·
                refine ⟨26722177126682525089022243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17814784751121683392681495 26722177126682525089022243)
                ·
                  refine ⟨40083265690023787633533365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26722177126682525089022243 40083265690023787633533365)
                  ·
                    refine ⟨3757806158439730090643753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40083265690023787633533365 3757806158439730090643753)
                    ·
                      refine ⟨2818354618829797567982815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757806158439730090643753 2818354618829797567982815)
                      ·
                        rfl

theorem cell23_5488726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5488726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488726 prefixEnd_5488726 := by exact prefixLift 5488726
  have htrace : WordTrace (prefixWord ++ tailWord_5488726) baseStart_5488726 baseEnd_5488726 := by
    simpa [prefixWord, tailWord_5488726, baseEnd_5488726] using wordTrace_append hprefix tailTrace_5488726
  have hstable : (prefixWord ++ tailWord_5488726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488726).length < 2 ^ (prefixWord ++ tailWord_5488726).sum := by decide
  have hdescent : baseEnd_5488726 < baseStart_5488726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488732 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_5488732 : Nat := 118140960795 + 5488732 * 2 ^ 59
def prefixEnd_5488732 : Nat := 4983230072969 + 3 ^ 40 * 5488732 * 2
def baseEnd_5488732 : Nat := 939452566571241514835929

theorem tailTrace_5488732 : CollatzResearch.WordTrace tailWord_5488732 prefixEnd_5488732 939452566571241514835929 := by
  unfold tailWord_5488732
  simp only [CollatzResearch.WordTrace]
  refine ⟨100095251175634419820210225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133460334900845893093613633 100095251175634419820210225)
  ·
    refine ⟨75071438381725814865157669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100095251175634419820210225 75071438381725814865157669)
    ·
      refine ⟨14075894696573590287217063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75071438381725814865157669 14075894696573590287217063)
      ·
        refine ⟨21113842044860385430825595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14075894696573590287217063 21113842044860385430825595)
        ·
          refine ⟨31670763067290578146238393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21113842044860385430825595 31670763067290578146238393)
          ·
            refine ⟨23753072300467933609678795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31670763067290578146238393 23753072300467933609678795)
            ·
              refine ⟨35629608450701900414518193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23753072300467933609678795 35629608450701900414518193)
              ·
                refine ⟨26722206338026425310888645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35629608450701900414518193 26722206338026425310888645)
                ·
                  refine ⟨5010413688379954745791621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26722206338026425310888645 5010413688379954745791621)
                  ·
                    refine ⟨939452566571241514835929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010413688379954745791621 939452566571241514835929)
                    ·
                      rfl

theorem cell23_5488732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_5488732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488732 prefixEnd_5488732 := by exact prefixLift 5488732
  have htrace : WordTrace (prefixWord ++ tailWord_5488732) baseStart_5488732 baseEnd_5488732 := by
    simpa [prefixWord, tailWord_5488732, baseEnd_5488732] using wordTrace_append hprefix tailTrace_5488732
  have hstable : (prefixWord ++ tailWord_5488732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488732).length < 2 ^ (prefixWord ++ tailWord_5488732).sum := by decide
  have hdescent : baseEnd_5488732 < baseStart_5488732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488733 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5488733 : Nat := 118140960795 + 5488733 * 2 ^ 59
def prefixEnd_5488733 : Nat := 4983230072969 + 3 ^ 40 * 5488733 * 2
def baseEnd_5488733 : Nat := 2818358213194379040595283

theorem tailTrace_5488733 : CollatzResearch.WordTrace tailWord_5488733 prefixEnd_5488733 2818358213194379040595283 := by
  unfold tailWord_5488733
  simp only [CollatzResearch.WordTrace]
  refine ⟨200190538824265216811206853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133460359216176811207471235 200190538824265216811206853)
  ·
    refine ⟨37535726029549728152101285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200190538824265216811206853 37535726029549728152101285)
    ·
      refine ⟨7037948630540574028518991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37535726029549728152101285 7037948630540574028518991)
      ·
        refine ⟨10556922945810861042778487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7037948630540574028518991 10556922945810861042778487)
        ·
          refine ⟨15835384418716291564167731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10556922945810861042778487 15835384418716291564167731)
          ·
            refine ⟨23753076628074437346251597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835384418716291564167731 23753076628074437346251597)
            ·
              refine ⟨8907403735527914004844349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23753076628074437346251597 8907403735527914004844349)
              ·
                refine ⟨3340276400822967751816631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8907403735527914004844349 3340276400822967751816631)
                ·
                  refine ⟨5010414601234451627724947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340276400822967751816631 5010414601234451627724947)
                  ·
                    refine ⟨7515621901851677441587421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010414601234451627724947 7515621901851677441587421)
                    ·
                      refine ⟨2818358213194379040595283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515621901851677441587421 2818358213194379040595283)
                      ·
                        rfl

theorem cell23_5488733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5488733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488733 prefixEnd_5488733 := by exact prefixLift 5488733
  have htrace : WordTrace (prefixWord ++ tailWord_5488733) baseStart_5488733 baseEnd_5488733 := by
    simpa [prefixWord, tailWord_5488733, baseEnd_5488733] using wordTrace_append hprefix tailTrace_5488733
  have hstable : (prefixWord ++ tailWord_5488733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488733).length < 2 ^ (prefixWord ++ tailWord_5488733).sum := by decide
  have hdescent : baseEnd_5488733 < baseStart_5488733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488772 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_5488772 : Nat := 118140960795 + 5488772 * 2 ^ 59
def prefixEnd_5488772 : Nat := 4983230072969 + 3 ^ 40 * 5488772 * 2
def baseEnd_5488772 : Nat := 2818378238939904388007603

theorem tailTrace_5488772 : CollatzResearch.WordTrace tailWord_5488772 prefixEnd_5488772 2818378238939904388007603 := by
  unfold tailWord_5488772
  simp only [CollatzResearch.WordTrace]
  refine ⟨100095980635561963235938285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133461307514082617647917713 100095980635561963235938285)
  ·
    refine ⟨37535992738335736213476857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100095980635561963235938285 37535992738335736213476857)
    ·
      refine ⟨28151994553751802160107643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37535992738335736213476857 28151994553751802160107643)
      ·
        refine ⟨42227991830627703240161465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28151994553751802160107643 42227991830627703240161465)
        ·
          refine ⟨31670993872970777430121099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42227991830627703240161465 31670993872970777430121099)
          ·
            refine ⟨47506490809456166145181649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31670993872970777430121099 47506490809456166145181649)
            ·
              refine ⟨35629868107092124608886237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47506490809456166145181649 35629868107092124608886237)
              ·
                refine ⟨13361200540159546728332339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35629868107092124608886237 13361200540159546728332339)
                ·
                  refine ⟨20041800810239320092498509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13361200540159546728332339 20041800810239320092498509)
                  ·
                    refine ⟨7515675303839745034686941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20041800810239320092498509 7515675303839745034686941)
                    ·
                      refine ⟨2818378238939904388007603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515675303839745034686941 2818378238939904388007603)
                      ·
                        rfl

theorem cell23_5488772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_5488772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488772 prefixEnd_5488772 := by exact prefixLift 5488772
  have htrace : WordTrace (prefixWord ++ tailWord_5488772) baseStart_5488772 baseEnd_5488772 := by
    simpa [prefixWord, tailWord_5488772, baseEnd_5488772] using wordTrace_append hprefix tailTrace_5488772
  have hstable : (prefixWord ++ tailWord_5488772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488772).length < 2 ^ (prefixWord ++ tailWord_5488772).sum := by decide
  have hdescent : baseEnd_5488772 < baseStart_5488772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488776 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5488776 : Nat := 118140960795 + 5488776 * 2 ^ 59
def prefixEnd_5488776 : Nat := 4983230072969 + 3 ^ 40 * 5488776 * 2
def baseEnd_5488776 : Nat := 2818380292862522372357585

theorem tailTrace_5488776 : CollatzResearch.WordTrace tailWord_5488776 prefixEnd_5488776 2818380292862522372357585 := by
  unfold tailWord_5488776
  simp only [CollatzResearch.WordTrace]
  refine ⟨100096053581554717577511091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133461404775406290103348121 100096053581554717577511091)
  ·
    refine ⟨150144080372332076366266637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100096053581554717577511091 150144080372332076366266637)
    ·
      refine ⟨56304030139624528637349989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150144080372332076366266637 56304030139624528637349989)
      ·
        refine ⟨10557005651179599119503123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56304030139624528637349989 10557005651179599119503123)
        ·
          refine ⟨15835508476769398679254685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557005651179599119503123 15835508476769398679254685)
          ·
            refine ⟨5938315678788524504720507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15835508476769398679254685 5938315678788524504720507)
            ·
              refine ⟨8907473518182786757080761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938315678788524504720507 8907473518182786757080761)
              ·
                refine ⟨6680605138637090067810571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8907473518182786757080761 6680605138637090067810571)
                ·
                  refine ⟨10020907707955635101715857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680605138637090067810571 10020907707955635101715857)
                  ·
                    refine ⟨7515680780966726326286893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10020907707955635101715857 7515680780966726326286893)
                    ·
                      refine ⟨2818380292862522372357585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515680780966726326286893 2818380292862522372357585)
                      ·
                        rfl

theorem cell23_5488776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5488776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488776 prefixEnd_5488776 := by exact prefixLift 5488776
  have htrace : WordTrace (prefixWord ++ tailWord_5488776) baseStart_5488776 baseEnd_5488776 := by
    simpa [prefixWord, tailWord_5488776, baseEnd_5488776] using wordTrace_append hprefix tailTrace_5488776
  have hstable : (prefixWord ++ tailWord_5488776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488776).length < 2 ^ (prefixWord ++ tailWord_5488776).sum := by decide
  have hdescent : baseEnd_5488776 < baseStart_5488776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488805 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_5488805 : Nat := 118140960795 + 5488805 * 2 ^ 59
def prefixEnd_5488805 : Nat := 4983230072969 + 3 ^ 40 * 5488805 * 2
def baseEnd_5488805 : Nat := 939465061267167586298317

theorem tailTrace_5488805 : CollatzResearch.WordTrace tailWord_5488805 prefixEnd_5488805 939465061267167586298317 := by
  unfold tailWord_5488805
  simp only [CollatzResearch.WordTrace]
  refine ⟨200193164880004373107827869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133462109920002915405218579 200193164880004373107827869)
  ·
    refine ⟨75072436830001639915435451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200193164880004373107827869 75072436830001639915435451)
    ·
      refine ⟨112608655245002459873153177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75072436830001639915435451 112608655245002459873153177)
      ·
        refine ⟨84456491433751844904864883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112608655245002459873153177 84456491433751844904864883)
        ·
          refine ⟨126684737150627767357297325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84456491433751844904864883 126684737150627767357297325)
          ·
            refine ⟨47506776431485412758986497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126684737150627767357297325 47506776431485412758986497)
            ·
              refine ⟨35630082323614059569239873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47506776431485412758986497 35630082323614059569239873)
              ·
                refine ⟨26722561742710544676929905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35630082323614059569239873 26722561742710544676929905)
                ·
                  refine ⟨20041921307032908507697429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26722561742710544676929905 20041921307032908507697429)
                  ·
                    refine ⟨939465061267167586298317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20041921307032908507697429 939465061267167586298317)
                    ·
                      rfl

theorem cell23_5488805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_5488805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488805 prefixEnd_5488805 := by exact prefixLift 5488805
  have htrace : WordTrace (prefixWord ++ tailWord_5488805) baseStart_5488805 baseEnd_5488805 := by
    simpa [prefixWord, tailWord_5488805, baseEnd_5488805] using wordTrace_append hprefix tailTrace_5488805
  have hstable : (prefixWord ++ tailWord_5488805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488805).length < 2 ^ (prefixWord ++ tailWord_5488805).sum := by decide
  have hdescent : baseEnd_5488805 < baseStart_5488805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488807 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5488807 : Nat := 118140960795 + 5488807 * 2 ^ 59
def prefixEnd_5488807 : Nat := 4983230072969 + 3 ^ 40 * 5488807 * 2
def baseEnd_5488807 : Nat := 2818396210762811751069943

theorem tailTrace_5488807 : CollatzResearch.WordTrace tailWord_5488807 prefixEnd_5488807 2818396210762811751069943 := by
  unfold tailWord_5488807
  simp only [CollatzResearch.WordTrace]
  refine ⟨200193237825997127449400675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133462158550664751632933783 200193237825997127449400675)
  ·
    refine ⟨300289856738995691174101013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200193237825997127449400675 300289856738995691174101013)
    ·
      refine ⟨14076087034640423023785985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300289856738995691174101013 14076087034640423023785985)
      ·
        refine ⟨10557065275980317267839489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14076087034640423023785985 10557065275980317267839489)
        ·
          refine ⟨7917798956985237950879617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10557065275980317267839489 7917798956985237950879617)
          ·
            refine ⟨5938349217738928463159713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917798956985237950879617 5938349217738928463159713)
            ·
              refine ⟨4453761913304196347369785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938349217738928463159713 4453761913304196347369785)
              ·
                refine ⟨3340321434978147260527339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453761913304196347369785 3340321434978147260527339)
                ·
                  refine ⟨5010482152467220890791009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340321434978147260527339 5010482152467220890791009)
                  ·
                    refine ⟨3757861614350415668093257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010482152467220890791009 3757861614350415668093257)
                    ·
                      refine ⟨2818396210762811751069943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757861614350415668093257 2818396210762811751069943)
                      ·
                        rfl

theorem cell23_5488807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5488807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488807 prefixEnd_5488807 := by exact prefixLift 5488807
  have htrace : WordTrace (prefixWord ++ tailWord_5488807) baseStart_5488807 baseEnd_5488807 := by
    simpa [prefixWord, tailWord_5488807, baseEnd_5488807] using wordTrace_append hprefix tailTrace_5488807
  have hstable : (prefixWord ++ tailWord_5488807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488807).length < 2 ^ (prefixWord ++ tailWord_5488807).sum := by decide
  have hdescent : baseEnd_5488807 < baseStart_5488807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488829 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_5488829 : Nat := 118140960795 + 5488829 * 2 ^ 59
def prefixEnd_5488829 : Nat := 4983230072969 + 3 ^ 40 * 5488829 * 2
def baseEnd_5488829 : Nat := 2818407507337210664994841

theorem tailTrace_5488829 : CollatzResearch.WordTrace tailWord_5488829 prefixEnd_5488829 2818407507337210664994841 := by
  unfold tailWord_5488829
  simp only [CollatzResearch.WordTrace]
  refine ⟨200194040231917425206701541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133462693487944950137801027 200194040231917425206701541)
  ·
    refine ⟨37536382543484517226256539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200194040231917425206701541 37536382543484517226256539)
    ·
      refine ⟨56304573815226775839384809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37536382543484517226256539 56304573815226775839384809)
      ·
        refine ⟨42228430361420081879538607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56304573815226775839384809 42228430361420081879538607)
        ·
          refine ⟨63342645542130122819307911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42228430361420081879538607 63342645542130122819307911)
          ·
            refine ⟨95013968313195184228961867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63342645542130122819307911 95013968313195184228961867)
            ·
              refine ⟨142520952469792776343442801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95013968313195184228961867 142520952469792776343442801)
              ·
                refine ⟨106890714352344582257582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142520952469792776343442801 106890714352344582257582101)
                ·
                  refine ⟨5010502235266152293324161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106890714352344582257582101 5010502235266152293324161)
                  ·
                    refine ⟨3757876676449614219993121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010502235266152293324161 3757876676449614219993121)
                    ·
                      refine ⟨2818407507337210664994841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757876676449614219993121 2818407507337210664994841)
                      ·
                        rfl

theorem cell23_5488829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_5488829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488829 prefixEnd_5488829 := by exact prefixLift 5488829
  have htrace : WordTrace (prefixWord ++ tailWord_5488829) baseStart_5488829 baseEnd_5488829 := by
    simpa [prefixWord, tailWord_5488829, baseEnd_5488829] using wordTrace_append hprefix tailTrace_5488829
  have hstable : (prefixWord ++ tailWord_5488829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488829).length < 2 ^ (prefixWord ++ tailWord_5488829).sum := by decide
  have hdescent : baseEnd_5488829 < baseStart_5488829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488869 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 5]
def baseStart_5488869 : Nat := 118140960795 + 5488869 * 2 ^ 59
def prefixEnd_5488869 : Nat := 4983230072969 + 3 ^ 40 * 5488869 * 2
def baseEnd_5488869 : Nat := 313158671840376723166073

theorem tailTrace_5488869 : CollatzResearch.WordTrace tailWord_5488869 prefixEnd_5488869 313158671840376723166073 := by
  unfold tailWord_5488869
  simp only [CollatzResearch.WordTrace]
  refine ⟨200195499151772512038157661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133463666101181674692105107 200195499151772512038157661)
  ·
    refine ⟨75073312181914692014309123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200195499151772512038157661 75073312181914692014309123)
    ·
      refine ⟨112609968272872038021463685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75073312181914692014309123 112609968272872038021463685)
      ·
        refine ⟨21114369051163507129024441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112609968272872038021463685 21114369051163507129024441)
        ·
          refine ⟨15835776788372630346768331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21114369051163507129024441 15835776788372630346768331)
          ·
            refine ⟨23753665182558945520152497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835776788372630346768331 23753665182558945520152497)
            ·
              refine ⟨17815248886919209140114373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23753665182558945520152497 17815248886919209140114373)
              ·
                refine ⟨3340359166297351713771445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17815248886919209140114373 3340359166297351713771445)
                ·
                  refine ⟨313158671840376723166073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340359166297351713771445 313158671840376723166073)
                  ·
                    rfl

theorem cell23_5488869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_5488869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488869 prefixEnd_5488869 := by exact prefixLift 5488869
  have htrace : WordTrace (prefixWord ++ tailWord_5488869) baseStart_5488869 baseEnd_5488869 := by
    simpa [prefixWord, tailWord_5488869, baseEnd_5488869] using wordTrace_append hprefix tailTrace_5488869
  have hstable : (prefixWord ++ tailWord_5488869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488869).length < 2 ^ (prefixWord ++ tailWord_5488869).sum := by decide
  have hdescent : baseEnd_5488869 < baseStart_5488869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488875 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_5488875 : Nat := 118140960795 + 5488875 * 2 ^ 59
def prefixEnd_5488875 : Nat := 4983230072969 + 3 ^ 40 * 5488875 * 2
def baseEnd_5488875 : Nat := 2818431127447317485019629

theorem tailTrace_5488875 : CollatzResearch.WordTrace tailWord_5488875 prefixEnd_5488875 2818431127447317485019629 := by
  unfold tailWord_5488875
  simp only [CollatzResearch.WordTrace]
  refine ⟨200195717989750775062876079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133463811993167183375250719 200195717989750775062876079)
  ·
    refine ⟨300293576984626162594314119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200195717989750775062876079 300293576984626162594314119)
    ·
      refine ⟨450440365476939243891471179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300293576984626162594314119 450440365476939243891471179)
      ·
        refine ⟨675660548215408865837206769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450440365476939243891471179 675660548215408865837206769)
        ·
          refine ⟨506745411161556649377905077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675660548215408865837206769 506745411161556649377905077)
          ·
            refine ⟨47507382296395935879178601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 506745411161556649377905077 47507382296395935879178601)
            ·
              refine ⟨35630536722296951909383951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47507382296395935879178601 35630536722296951909383951)
              ·
                refine ⟨53445805083445427864075927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35630536722296951909383951 53445805083445427864075927)
                ·
                  refine ⟨80168707625168141796113891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53445805083445427864075927 80168707625168141796113891)
                  ·
                    refine ⟨120253061437752212694170837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80168707625168141796113891 120253061437752212694170837)
                    ·
                      refine ⟨2818431127447317485019629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120253061437752212694170837 2818431127447317485019629)
                      ·
                        rfl

theorem cell23_5488875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_5488875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488875 prefixEnd_5488875 := by exact prefixLift 5488875
  have htrace : WordTrace (prefixWord ++ tailWord_5488875) baseStart_5488875 baseEnd_5488875 := by
    simpa [prefixWord, tailWord_5488875, baseEnd_5488875] using wordTrace_append hprefix tailTrace_5488875
  have hstable : (prefixWord ++ tailWord_5488875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488875).length < 2 ^ (prefixWord ++ tailWord_5488875).sum := by decide
  have hdescent : baseEnd_5488875 < baseStart_5488875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488882 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_5488882 : Nat := 118140960795 + 5488882 * 2 ^ 59
def prefixEnd_5488882 : Nat := 4983230072969 + 3 ^ 40 * 5488882 * 2
def baseEnd_5488882 : Nat := 939478240603966319210699

theorem tailTrace_5488882 : CollatzResearch.WordTrace tailWord_5488882 prefixEnd_5488882 939478240603966319210699 := by
  unfold tailWord_5488882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50048993325181353814595225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133463982200483610172253933 50048993325181353814595225)
  ·
    refine ⟨37536744993886015360946419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50048993325181353814595225 37536744993886015360946419)
    ·
      refine ⟨56305117490829023041419629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37536744993886015360946419 56305117490829023041419629)
      ·
        refine ⟨21114419059060883640532361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56305117490829023041419629 21114419059060883640532361)
        ·
          refine ⟨15835814294295662730399271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21114419059060883640532361 15835814294295662730399271)
          ·
            refine ⟨23753721441443494095598907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15835814294295662730399271 23753721441443494095598907)
            ·
              refine ⟨35630582162165241143398361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23753721441443494095598907 35630582162165241143398361)
              ·
                refine ⟨26722936621623930857548771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35630582162165241143398361 26722936621623930857548771)
                ·
                  refine ⟨40084404932435896286323157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26722936621623930857548771 40084404932435896286323157)
                  ·
                    refine ⟨939478240603966319210699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40084404932435896286323157 939478240603966319210699)
                    ·
                      rfl

theorem cell23_5488882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_5488882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488882 prefixEnd_5488882 := by exact prefixLift 5488882
  have htrace : WordTrace (prefixWord ++ tailWord_5488882) baseStart_5488882 baseEnd_5488882 := by
    simpa [prefixWord, tailWord_5488882, baseEnd_5488882] using wordTrace_append hprefix tailTrace_5488882
  have hstable : (prefixWord ++ tailWord_5488882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488882).length < 2 ^ (prefixWord ++ tailWord_5488882).sum := by decide
  have hdescent : baseEnd_5488882 < baseStart_5488882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488895 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 8]
def baseStart_5488895 : Nat := 118140960795 + 5488895 * 2 ^ 59
def prefixEnd_5488895 : Nat := 4983230072969 + 3 ^ 40 * 5488895 * 2
def baseEnd_5488895 : Nat := 939480465686802468923179

theorem tailTrace_5488895 : CollatzResearch.WordTrace tailWord_5488895 prefixEnd_5488895 939480465686802468923179 := by
  unfold tailWord_5488895
  simp only [CollatzResearch.WordTrace]
  refine ⟨200196447449678318478604139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133464298299785545652402759 200196447449678318478604139)
  ·
    refine ⟨300294671174517477717906209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200196447449678318478604139 300294671174517477717906209)
    ·
      refine ⟨225221003380888108288429657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300294671174517477717906209 225221003380888108288429657)
      ·
        refine ⟨168915752535666081216322243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225221003380888108288429657 168915752535666081216322243)
        ·
          refine ⟨253373628803499121824483365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168915752535666081216322243 253373628803499121824483365)
          ·
            refine ⟨47507555400656085342090631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253373628803499121824483365 47507555400656085342090631)
            ·
              refine ⟨71261333100984128013135947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47507555400656085342090631 71261333100984128013135947)
              ·
                refine ⟨106891999651476192019703921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71261333100984128013135947 106891999651476192019703921)
                ·
                  refine ⟨80168999738607144014777941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106891999651476192019703921 80168999738607144014777941)
                  ·
                    refine ⟨939480465686802468923179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80168999738607144014777941 939480465686802468923179)
                    ·
                      rfl

theorem cell23_5488895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_5488895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488895 prefixEnd_5488895 := by exact prefixLift 5488895
  have htrace : WordTrace (prefixWord ++ tailWord_5488895) baseStart_5488895 baseEnd_5488895 := by
    simpa [prefixWord, tailWord_5488895, baseEnd_5488895] using wordTrace_append hprefix tailTrace_5488895
  have hstable : (prefixWord ++ tailWord_5488895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488895).length < 2 ^ (prefixWord ++ tailWord_5488895).sum := by decide
  have hdescent : baseEnd_5488895 < baseStart_5488895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488903 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 5]
def baseStart_5488903 : Nat := 118140960795 + 5488903 * 2 ^ 59
def prefixEnd_5488903 : Nat := 4983230072969 + 3 ^ 40 * 5488903 * 2
def baseEnd_5488903 : Nat := 313160611656182597274389

theorem tailTrace_5488903 : CollatzResearch.WordTrace tailWord_5488903 prefixEnd_5488903 313160611656182597274389 := by
  unfold tailWord_5488903
  simp only [CollatzResearch.WordTrace]
  refine ⟨200196739233649335844895363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133464492822432890563263575 200196739233649335844895363)
  ·
    refine ⟨300295108850474003767343045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200196739233649335844895363 300295108850474003767343045)
    ·
      refine ⟨56305332909463875706376821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300295108850474003767343045 56305332909463875706376821)
      ·
        refine ⟨5278624960262238347472827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56305332909463875706376821 5278624960262238347472827)
        ·
          refine ⟨7917937440393357521209241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278624960262238347472827 7917937440393357521209241)
          ·
            refine ⟨5938453080295018140906931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917937440393357521209241 5938453080295018140906931)
            ·
              refine ⟨8907679620442527211360397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938453080295018140906931 8907679620442527211360397)
              ·
                refine ⟨3340379857665947704260149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8907679620442527211360397 3340379857665947704260149)
                ·
                  refine ⟨313160611656182597274389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340379857665947704260149 313160611656182597274389)
                  ·
                    rfl

theorem cell23_5488903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 5].length) (baseStart_5488903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488903 prefixEnd_5488903 := by exact prefixLift 5488903
  have htrace : WordTrace (prefixWord ++ tailWord_5488903) baseStart_5488903 baseEnd_5488903 := by
    simpa [prefixWord, tailWord_5488903, baseEnd_5488903] using wordTrace_append hprefix tailTrace_5488903
  have hstable : (prefixWord ++ tailWord_5488903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488903).length < 2 ^ (prefixWord ++ tailWord_5488903).sum := by decide
  have hdescent : baseEnd_5488903 < baseStart_5488903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488915 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_5488915 : Nat := 118140960795 + 5488915 * 2 ^ 59
def prefixEnd_5488915 : Nat := 4983230072969 + 3 ^ 40 * 5488915 * 2
def baseEnd_5488915 : Nat := 2818451666673497328519445

theorem tailTrace_5488915 : CollatzResearch.WordTrace tailWord_5488915 prefixEnd_5488915 2818451666673497328519445 := by
  unfold tailWord_5488915
  simp only [CollatzResearch.WordTrace]
  refine ⟨200197176909605861894332199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133464784606403907929554799 200197176909605861894332199)
  ·
    refine ⟨300295765364408792841498299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200197176909605861894332199 300295765364408792841498299)
    ·
      refine ⟨450443648046613189262247449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300295765364408792841498299 450443648046613189262247449)
      ·
        refine ⟨337832736034959891946685587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450443648046613189262247449 337832736034959891946685587)
        ·
          refine ⟨506749104052439837920028381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337832736034959891946685587 506749104052439837920028381)
          ·
            refine ⟨190030914019664939220010643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506749104052439837920028381 190030914019664939220010643)
            ·
              refine ⟨285046371029497408830015965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190030914019664939220010643 285046371029497408830015965)
              ·
                refine ⟨106892389136061528311255987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285046371029497408830015965 106892389136061528311255987)
                ·
                  refine ⟨160338583704092292466883981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106892389136061528311255987 160338583704092292466883981)
                  ·
                    refine ⟨60126968889034609675081493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160338583704092292466883981 60126968889034609675081493)
                    ·
                      refine ⟨2818451666673497328519445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60126968889034609675081493 2818451666673497328519445)
                      ·
                        rfl

theorem cell23_5488915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_5488915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488915 prefixEnd_5488915 := by exact prefixLift 5488915
  have htrace : WordTrace (prefixWord ++ tailWord_5488915) baseStart_5488915 baseEnd_5488915 := by
    simpa [prefixWord, tailWord_5488915, baseEnd_5488915] using wordTrace_append hprefix tailTrace_5488915
  have hstable : (prefixWord ++ tailWord_5488915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488915).length < 2 ^ (prefixWord ++ tailWord_5488915).sum := by decide
  have hdescent : baseEnd_5488915 < baseStart_5488915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488919 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5488919 : Nat := 118140960795 + 5488919 * 2 ^ 59
def prefixEnd_5488919 : Nat := 4983230072969 + 3 ^ 40 * 5488919 * 2
def baseEnd_5488919 : Nat := 2818453720596115312869427

theorem tailTrace_5488919 : CollatzResearch.WordTrace tailWord_5488919 prefixEnd_5488919 2818453720596115312869427 := by
  unfold tailWord_5488919
  simp only [CollatzResearch.WordTrace]
  refine ⟨200197322801591370577477811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133464881867727580384985207 200197322801591370577477811)
  ·
    refine ⟨300295984202387055866216717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200197322801591370577477811 300295984202387055866216717)
    ·
      refine ⟨112610994075895145949831269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300295984202387055866216717 112610994075895145949831269)
      ·
        refine ⟨21114561389230339865593363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112610994075895145949831269 21114561389230339865593363)
        ·
          refine ⟨31671842083845509798390045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21114561389230339865593363 31671842083845509798390045)
          ·
            refine ⟨11876940781442066174396267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31671842083845509798390045 11876940781442066174396267)
            ·
              refine ⟨17815411172163099261594401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11876940781442066174396267 17815411172163099261594401)
              ·
                refine ⟨13361558379122324446195801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17815411172163099261594401 13361558379122324446195801)
                ·
                  refine ⟨10021168784341743334646851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13361558379122324446195801 10021168784341743334646851)
                  ·
                    refine ⟨15031753176512615001970277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10021168784341743334646851 15031753176512615001970277)
                    ·
                      refine ⟨2818453720596115312869427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15031753176512615001970277 2818453720596115312869427)
                      ·
                        rfl

theorem cell23_5488919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5488919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488919 prefixEnd_5488919 := by exact prefixLift 5488919
  have htrace : WordTrace (prefixWord ++ tailWord_5488919) baseStart_5488919 baseEnd_5488919 := by
    simpa [prefixWord, tailWord_5488919, baseEnd_5488919] using wordTrace_append hprefix tailTrace_5488919
  have hstable : (prefixWord ++ tailWord_5488919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488919).length < 2 ^ (prefixWord ++ tailWord_5488919).sum := by decide
  have hdescent : baseEnd_5488919 < baseStart_5488919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488926 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5488926 : Nat := 118140960795 + 5488926 * 2 ^ 59
def prefixEnd_5488926 : Nat := 4983230072969 + 3 ^ 40 * 5488926 * 2
def baseEnd_5488926 : Nat := 2818457314960696785481895

theorem tailTrace_5488926 : CollatzResearch.WordTrace tailWord_5488926 prefixEnd_5488926 2818457314960696785481895 := by
  unfold tailWord_5488926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25024697264070751346622829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133465052075044007181988421 25024697264070751346622829)
  ·
    refine ⟨9384261474026531754983561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25024697264070751346622829 9384261474026531754983561)
    ·
      refine ⟨7038196105519898816237671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9384261474026531754983561 7038196105519898816237671)
      ·
        refine ⟨10557294158279848224356507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038196105519898816237671 10557294158279848224356507)
        ·
          refine ⟨15835941237419772336534761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557294158279848224356507 15835941237419772336534761)
          ·
            refine ⟨11876955928064829252401071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15835941237419772336534761 11876955928064829252401071)
            ·
              refine ⟨17815433892097243878601607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11876955928064829252401071 17815433892097243878601607)
              ·
                refine ⟨26723150838145865817902411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17815433892097243878601607 26723150838145865817902411)
                ·
                  refine ⟨40084726257218798726853617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26723150838145865817902411 40084726257218798726853617)
                  ·
                    refine ⟨30063544692914099045140213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40084726257218798726853617 30063544692914099045140213)
                    ·
                      refine ⟨2818457314960696785481895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30063544692914099045140213 2818457314960696785481895)
                      ·
                        rfl

theorem cell23_5488926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5488926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488926 prefixEnd_5488926 := by exact prefixLift 5488926
  have htrace : WordTrace (prefixWord ++ tailWord_5488926) baseStart_5488926 baseEnd_5488926 := by
    simpa [prefixWord, tailWord_5488926, baseEnd_5488926] using wordTrace_append hprefix tailTrace_5488926
  have hstable : (prefixWord ++ tailWord_5488926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488926).length < 2 ^ (prefixWord ++ tailWord_5488926).sum := by decide
  have hdescent : baseEnd_5488926 < baseStart_5488926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488929 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_5488929 : Nat := 118140960795 + 5488929 * 2 ^ 59
def prefixEnd_5488929 : Nat := 4983230072969 + 3 ^ 40 * 5488929 * 2
def baseEnd_5488929 : Nat := 939486285134220091248127

theorem tailTrace_5488929 : CollatzResearch.WordTrace tailWord_5488929 prefixEnd_5488929 939486285134220091248127 := by
  unfold tailWord_5488929
  simp only [CollatzResearch.WordTrace]
  refine ⟨200197687531555142285341841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133465125021036761523561227 200197687531555142285341841)
  ·
    refine ⟨150148265648666356714006381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200197687531555142285341841 150148265648666356714006381)
    ·
      refine ⟨56305599618249883767752393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150148265648666356714006381 56305599618249883767752393)
      ·
        refine ⟨42229199713687412825814295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56305599618249883767752393 42229199713687412825814295)
        ·
          refine ⟨63343799570531119238721443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42229199713687412825814295 63343799570531119238721443)
          ·
            refine ⟨95015699355796678858082165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63343799570531119238721443 95015699355796678858082165)
            ·
              refine ⟨8907721814605938642945203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95015699355796678858082165 8907721814605938642945203)
              ·
                refine ⟨13361582721908907964417805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907721814605938642945203 13361582721908907964417805)
                ·
                  refine ⟨5010593520715840486656677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13361582721908907964417805 5010593520715840486656677)
                  ·
                    refine ⟨939486285134220091248127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010593520715840486656677 939486285134220091248127)
                    ·
                      rfl

theorem cell23_5488929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_5488929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488929 prefixEnd_5488929 := by exact prefixLift 5488929
  have htrace : WordTrace (prefixWord ++ tailWord_5488929) baseStart_5488929 baseEnd_5488929 := by
    simpa [prefixWord, tailWord_5488929, baseEnd_5488929] using wordTrace_append hprefix tailTrace_5488929
  have hstable : (prefixWord ++ tailWord_5488929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488929).length < 2 ^ (prefixWord ++ tailWord_5488929).sum := by decide
  have hdescent : baseEnd_5488929 < baseStart_5488929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488952 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_5488952 : Nat := 118140960795 + 5488952 * 2 ^ 59
def prefixEnd_5488952 : Nat := 4983230072969 + 3 ^ 40 * 5488952 * 2
def baseEnd_5488952 : Nat := 2818470665457713683756775

theorem tailTrace_5488952 : CollatzResearch.WordTrace tailWord_5488952 prefixEnd_5488952 2818470665457713683756775 := by
  unfold tailWord_5488952
  simp only [CollatzResearch.WordTrace]
  refine ⟨100099263205235908606714555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133465684273647878142286073 100099263205235908606714555)
  ·
    refine ⟨150148894807853862910071833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100099263205235908606714555 150148894807853862910071833)
    ·
      refine ⟨112611671105890397182553875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150148894807853862910071833 112611671105890397182553875)
      ·
        refine ⟨168917506658835595773830813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112611671105890397182553875 168917506658835595773830813)
        ·
          refine ⟨63344064997063348415186555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168917506658835595773830813 63344064997063348415186555)
          ·
            refine ⟨95016097495595022622779833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63344064997063348415186555 95016097495595022622779833)
            ·
              refine ⟨71262073121696266967084875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95016097495595022622779833 71262073121696266967084875)
              ·
                refine ⟨106893109682544400450627313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71262073121696266967084875 106893109682544400450627313)
                ·
                  refine ⟨80169832261908300337970485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106893109682544400450627313 80169832261908300337970485)
                  ·
                    refine ⟨7515921774553903156684733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80169832261908300337970485 7515921774553903156684733)
                    ·
                      refine ⟨2818470665457713683756775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7515921774553903156684733 2818470665457713683756775)
                      ·
                        rfl

theorem cell23_5488952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_5488952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488952 prefixEnd_5488952 := by exact prefixLift 5488952
  have htrace : WordTrace (prefixWord ++ tailWord_5488952) baseStart_5488952 baseEnd_5488952 := by
    simpa [prefixWord, tailWord_5488952, baseEnd_5488952] using wordTrace_append hprefix tailTrace_5488952
  have hstable : (prefixWord ++ tailWord_5488952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488952).length < 2 ^ (prefixWord ++ tailWord_5488952).sum := by decide
  have hdescent : baseEnd_5488952 < baseStart_5488952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488979 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 4, 3, 2]
def baseStart_5488979 : Nat := 118140960795 + 5488979 * 2 ^ 59
def prefixEnd_5488979 : Nat := 4983230072969 + 3 ^ 40 * 5488979 * 2
def baseEnd_5488979 : Nat := 2818484529435385078119151

theorem tailTrace_5488979 : CollatzResearch.WordTrace tailWord_5488979 prefixEnd_5488979 2818484529435385078119151 := by
  unfold tailWord_5488979
  simp only [CollatzResearch.WordTrace]
  refine ⟨200199511181374000824661991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133466340787582667216441327 200199511181374000824661991)
  ·
    refine ⟨300299266772061001236992987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200199511181374000824661991 300299266772061001236992987)
    ·
      refine ⟨450448900158091501855489481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300299266772061001236992987 450448900158091501855489481)
      ·
        refine ⟨337836675118568626391617111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450448900158091501855489481 337836675118568626391617111)
        ·
          refine ⟨506755012677852939587425667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337836675118568626391617111 506755012677852939587425667)
          ·
            refine ⟨760132519016779409381138501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506755012677852939587425667 760132519016779409381138501)
            ·
              refine ⟨142524847315646139258963469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 760132519016779409381138501 142524847315646139258963469)
              ·
                refine ⟨53446817743367302222111301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142524847315646139258963469 53446817743367302222111301)
                ·
                  refine ⟨10021278326881369166645869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53446817743367302222111301 10021278326881369166645869)
                  ·
                    refine ⟨3757979372580513437492201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10021278326881369166645869 3757979372580513437492201)
                    ·
                      refine ⟨2818484529435385078119151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3757979372580513437492201 2818484529435385078119151)
                      ·
                        rfl

theorem cell23_5488979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 3, 2].length) (baseStart_5488979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488979 prefixEnd_5488979 := by exact prefixLift 5488979
  have htrace : WordTrace (prefixWord ++ tailWord_5488979) baseStart_5488979 baseEnd_5488979 := by
    simpa [prefixWord, tailWord_5488979, baseEnd_5488979] using wordTrace_append hprefix tailTrace_5488979
  have hstable : (prefixWord ++ tailWord_5488979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488979).length < 2 ^ (prefixWord ++ tailWord_5488979).sum := by decide
  have hdescent : baseEnd_5488979 < baseStart_5488979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5488980 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5488980 : Nat := 118140960795 + 5488980 * 2 ^ 59
def prefixEnd_5488980 : Nat := 4983230072969 + 3 ^ 40 * 5488980 * 2
def baseEnd_5488980 : Nat := 939495014305346524735549

theorem tailTrace_5488980 : CollatzResearch.WordTrace tailWord_5488980 prefixEnd_5488980 939495014305346524735549 := by
  unfold tailWord_5488980
  simp only [CollatzResearch.WordTrace]
  refine ⟨100099773827185188997724197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133466365102913585330298929 100099773827185188997724197)
  ·
    refine ⟨18768707592597222937073287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100099773827185188997724197 18768707592597222937073287)
    ·
      refine ⟨28153061388895834405609931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18768707592597222937073287 28153061388895834405609931)
      ·
        refine ⟨42229592083343751608414897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28153061388895834405609931 42229592083343751608414897)
        ·
          refine ⟨31672194062507813706311173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42229592083343751608414897 31672194062507813706311173)
          ·
            refine ⟨5938536386720215069933345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31672194062507813706311173 5938536386720215069933345)
            ·
              refine ⟨4453902290040161302450009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938536386720215069933345 4453902290040161302450009)
              ·
                refine ⟨3340426717530120976837507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4453902290040161302450009 3340426717530120976837507)
                ·
                  refine ⟨5010640076295181465256261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340426717530120976837507 5010640076295181465256261)
                  ·
                    refine ⟨939495014305346524735549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010640076295181465256261 939495014305346524735549)
                    ·
                      rfl

theorem cell23_5488980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5488980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5488980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5488980 prefixEnd_5488980 := by exact prefixLift 5488980
  have htrace : WordTrace (prefixWord ++ tailWord_5488980) baseStart_5488980 baseEnd_5488980 := by
    simpa [prefixWord, tailWord_5488980, baseEnd_5488980] using wordTrace_append hprefix tailTrace_5488980
  have hstable : (prefixWord ++ tailWord_5488980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5488980).length < 2 ^ (prefixWord ++ tailWord_5488980).sum := by decide
  have hdescent : baseEnd_5488980 < baseStart_5488980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5488980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489009 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_5489009 : Nat := 118140960795 + 5489009 * 2 ^ 59
def prefixEnd_5489009 : Nat := 4983230072969 + 3 ^ 40 * 5489009 * 2
def baseEnd_5489009 : Nat := 2818499933855019960744013

theorem tailTrace_5489009 : CollatzResearch.WordTrace tailWord_5489009 prefixEnd_5489009 2818499933855019960744013 := by
  unfold tailWord_5489009
  simp only [CollatzResearch.WordTrace]
  refine ⟨200200605371265315948254081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133467070247510210632169387 200200605371265315948254081)
  ·
    refine ⟨150150454028448986961190561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200200605371265315948254081 150150454028448986961190561)
    ·
      refine ⟨112612840521336740220892921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150150454028448986961190561 112612840521336740220892921)
      ·
        refine ⟨84459630391002555165669691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112612840521336740220892921 84459630391002555165669691)
        ·
          refine ⟨126689445586503832748504537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84459630391002555165669691 126689445586503832748504537)
          ·
            refine ⟨95017084189877874561378403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126689445586503832748504537 95017084189877874561378403)
            ·
              refine ⟨142525626284816811842067605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95017084189877874561378403 142525626284816811842067605)
              ·
                refine ⟨6680888732100788055096919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142525626284816811842067605 6680888732100788055096919)
                ·
                  refine ⟨10021333098151182082645379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680888732100788055096919 10021333098151182082645379)
                  ·
                    refine ⟨15031999647226773123968069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10021333098151182082645379 15031999647226773123968069)
                    ·
                      refine ⟨2818499933855019960744013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15031999647226773123968069 2818499933855019960744013)
                      ·
                        rfl

theorem cell23_5489009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_5489009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489009 prefixEnd_5489009 := by exact prefixLift 5489009
  have htrace : WordTrace (prefixWord ++ tailWord_5489009) baseStart_5489009 baseEnd_5489009 := by
    simpa [prefixWord, tailWord_5489009, baseEnd_5489009] using wordTrace_append hprefix tailTrace_5489009
  have hstable : (prefixWord ++ tailWord_5489009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489009).length < 2 ^ (prefixWord ++ tailWord_5489009).sum := by decide
  have hdescent : baseEnd_5489009 < baseStart_5489009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489013 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5489013 : Nat := 118140960795 + 5489013 * 2 ^ 59
def prefixEnd_5489013 : Nat := 4983230072969 + 3 ^ 40 * 5489013 * 2
def baseEnd_5489013 : Nat := 2818501987777637945093995

theorem tailTrace_5489013 : CollatzResearch.WordTrace tailWord_5489013 prefixEnd_5489013 2818501987777637945093995 := by
  unfold tailWord_5489013
  simp only [CollatzResearch.WordTrace]
  refine ⟨200200751263250824631399693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133467167508833883087599795 200200751263250824631399693)
  ·
    refine ⟨75075281723719059236774885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200200751263250824631399693 75075281723719059236774885)
    ·
      refine ⟨14076615323197323606895291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75075281723719059236774885 14076615323197323606895291)
      ·
        refine ⟨21114922984795985410342937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076615323197323606895291 21114922984795985410342937)
        ·
          refine ⟨15836192238596989057757203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21114922984795985410342937 15836192238596989057757203)
          ·
            refine ⟨23754288357895483586635805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15836192238596989057757203 23754288357895483586635805)
            ·
              refine ⟨8907858134210806344988427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23754288357895483586635805 8907858134210806344988427)
              ·
                refine ⟨13361787201316209517482641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907858134210806344988427 13361787201316209517482641)
                ·
                  refine ⟨10021340400987157138111981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13361787201316209517482641 10021340400987157138111981)
                  ·
                    refine ⟨3758002650370183926791993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10021340400987157138111981 3758002650370183926791993)
                    ·
                      refine ⟨2818501987777637945093995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758002650370183926791993 2818501987777637945093995)
                      ·
                        rfl

theorem cell23_5489013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5489013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489013 prefixEnd_5489013 := by exact prefixLift 5489013
  have htrace : WordTrace (prefixWord ++ tailWord_5489013) baseStart_5489013 baseEnd_5489013 := by
    simpa [prefixWord, tailWord_5489013, baseEnd_5489013] using wordTrace_append hprefix tailTrace_5489013
  have hstable : (prefixWord ++ tailWord_5489013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489013).length < 2 ^ (prefixWord ++ tailWord_5489013).sum := by decide
  have hdescent : baseEnd_5489013 < baseStart_5489013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489032 : List Nat := [2, 1, 3, 3, 1, 1, 12]
def baseStart_5489032 : Nat := 118140960795 + 5489032 * 2 ^ 59
def prefixEnd_5489032 : Nat := 4983230072969 + 3 ^ 40 * 5489032 * 2
def baseEnd_5489032 : Nat := 34796441282840411984647

theorem tailTrace_5489032 : CollatzResearch.WordTrace tailWord_5489032 prefixEnd_5489032 34796441282840411984647 := by
  unfold tailWord_5489032
  simp only [CollatzResearch.WordTrace]
  refine ⟨100100722125090995438170675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133467629500121327250894233 100100722125090995438170675)
  ·
    refine ⟨150151083187636493157256013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100100722125090995438170675 150151083187636493157256013)
    ·
      refine ⟨56306656195363684933971005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150151083187636493157256013 56306656195363684933971005)
      ·
        refine ⟨21114996073261381850239127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56306656195363684933971005 21114996073261381850239127)
        ·
          refine ⟨31672494109892072775358691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21114996073261381850239127 31672494109892072775358691)
          ·
            refine ⟨47508741164838109163038037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31672494109892072775358691 47508741164838109163038037)
            ·
              refine ⟨34796441282840411984647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47508741164838109163038037 34796441282840411984647)
              ·
                rfl

theorem cell23_5489032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 12].length) (baseStart_5489032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489032 prefixEnd_5489032 := by exact prefixLift 5489032
  have htrace : WordTrace (prefixWord ++ tailWord_5489032) baseStart_5489032 baseEnd_5489032 := by
    simpa [prefixWord, tailWord_5489032, baseEnd_5489032] using wordTrace_append hprefix tailTrace_5489032
  have hstable : (prefixWord ++ tailWord_5489032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489032).length < 2 ^ (prefixWord ++ tailWord_5489032).sum := by decide
  have hdescent : baseEnd_5489032 < baseStart_5489032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489036 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_5489036 : Nat := 118140960795 + 5489036 * 2 ^ 59
def prefixEnd_5489036 : Nat := 4983230072969 + 3 ^ 40 * 5489036 * 2
def baseEnd_5489036 : Nat := 939504599277563785035463

theorem tailTrace_5489036 : CollatzResearch.WordTrace tailWord_5489036 prefixEnd_5489036 939504599277563785035463 := by
  unfold tailWord_5489036
  simp only [CollatzResearch.WordTrace]
  refine ⟨100100795071083749779743481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133467726761444999706324641 100100795071083749779743481)
  ·
    refine ⟨75075596303312812334807611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100100795071083749779743481 75075596303312812334807611)
    ·
      refine ⟨112613394454969218502211417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75075596303312812334807611 112613394454969218502211417)
      ·
        refine ⟨84460045841226913876658563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112613394454969218502211417 84460045841226913876658563)
        ·
          refine ⟨126690068761840370814987845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84460045841226913876658563 126690068761840370814987845)
          ·
            refine ⟨23754387892845069527810221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126690068761840370814987845 23754387892845069527810221)
            ·
              refine ⟨8907895459816901072928833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23754387892845069527810221 8907895459816901072928833)
              ·
                refine ⟨6680921594862675804696625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8907895459816901072928833 6680921594862675804696625)
                ·
                  refine ⟨5010691196147006853522469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6680921594862675804696625 5010691196147006853522469)
                  ·
                    refine ⟨939504599277563785035463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010691196147006853522469 939504599277563785035463)
                    ·
                      rfl

theorem cell23_5489036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_5489036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489036 prefixEnd_5489036 := by exact prefixLift 5489036
  have htrace : WordTrace (prefixWord ++ tailWord_5489036) baseStart_5489036 baseEnd_5489036 := by
    simpa [prefixWord, tailWord_5489036, baseEnd_5489036] using wordTrace_append hprefix tailTrace_5489036
  have hstable : (prefixWord ++ tailWord_5489036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489036).length < 2 ^ (prefixWord ++ tailWord_5489036).sum := by decide
  have hdescent : baseEnd_5489036 < baseStart_5489036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489053 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_5489053 : Nat := 118140960795 + 5489053 * 2 ^ 59
def prefixEnd_5489053 : Nat := 4983230072969 + 3 ^ 40 * 5489053 * 2
def baseEnd_5489053 : Nat := 939507509001272596197937

theorem tailTrace_5489053 : CollatzResearch.WordTrace tailWord_5489053 prefixEnd_5489053 939507509001272596197937 := by
  unfold tailWord_5489053
  simp only [CollatzResearch.WordTrace]
  refine ⟨200202210183105911462855813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133468140122070607641903875 200202210183105911462855813)
  ·
    refine ⟨37537914409332358399285465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200202210183105911462855813 37537914409332358399285465)
    ·
      refine ⟨28153435806999268799464099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37537914409332358399285465 28153435806999268799464099)
      ·
        refine ⟨42230153710498903199196149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28153435806999268799464099 42230153710498903199196149)
        ·
          refine ⟨3959076910359272174924639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42230153710498903199196149 3959076910359272174924639)
          ·
            refine ⟨5938615365538908262386959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959076910359272174924639 5938615365538908262386959)
            ·
              refine ⟨8907923048308362393580439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938615365538908262386959 8907923048308362393580439)
              ·
                refine ⟨13361884572462543590370659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907923048308362393580439 13361884572462543590370659)
                ·
                  refine ⟨20042826858693815385555989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13361884572462543590370659 20042826858693815385555989)
                  ·
                    refine ⟨939507509001272596197937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20042826858693815385555989 939507509001272596197937)
                    ·
                      rfl

theorem cell23_5489053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_5489053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489053 prefixEnd_5489053 := by exact prefixLift 5489053
  have htrace : WordTrace (prefixWord ++ tailWord_5489053) baseStart_5489053 baseEnd_5489053 := by
    simpa [prefixWord, tailWord_5489053, baseEnd_5489053] using wordTrace_append hprefix tailTrace_5489053
  have hstable : (prefixWord ++ tailWord_5489053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489053).length < 2 ^ (prefixWord ++ tailWord_5489053).sum := by decide
  have hdescent : baseEnd_5489053 < baseStart_5489053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489056 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_5489056 : Nat := 118140960795 + 5489056 * 2 ^ 59
def prefixEnd_5489056 : Nat := 4983230072969 + 3 ^ 40 * 5489056 * 2
def baseEnd_5489056 : Nat := 2818524067445781276856297

theorem tailTrace_5489056 : CollatzResearch.WordTrace tailWord_5489056 prefixEnd_5489056 2818524067445781276856297 := by
  unfold tailWord_5489056
  simp only [CollatzResearch.WordTrace]
  refine ⟨100101159801047521487607511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133468213068063361983476681 100101159801047521487607511)
  ·
    refine ⟨150151739701571282231411267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100101159801047521487607511 150151739701571282231411267)
    ·
      refine ⟨225227609552356923347116901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150151739701571282231411267 225227609552356923347116901)
      ·
        refine ⟨42230176791066923127584419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225227609552356923347116901 42230176791066923127584419)
        ·
          refine ⟨63345265186600384691376629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42230176791066923127584419 63345265186600384691376629)
          ·
            refine ⟨5938618611243786064816559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63345265186600384691376629 5938618611243786064816559)
            ·
              refine ⟨8907927916865679097224839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938618611243786064816559 8907927916865679097224839)
              ·
                refine ⟨13361891875298518645837259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8907927916865679097224839 13361891875298518645837259)
                ·
                  refine ⟨20042837812947777968755889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13361891875298518645837259 20042837812947777968755889)
                  ·
                    refine ⟨15032128359710833476566917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20042837812947777968755889 15032128359710833476566917)
                    ·
                      refine ⟨2818524067445781276856297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15032128359710833476566917 2818524067445781276856297)
                      ·
                        rfl

theorem cell23_5489056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_5489056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489056 prefixEnd_5489056 := by exact prefixLift 5489056
  have htrace : WordTrace (prefixWord ++ tailWord_5489056) baseStart_5489056 baseEnd_5489056 := by
    simpa [prefixWord, tailWord_5489056, baseEnd_5489056] using wordTrace_append hprefix tailTrace_5489056
  have hstable : (prefixWord ++ tailWord_5489056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489056).length < 2 ^ (prefixWord ++ tailWord_5489056).sum := by decide
  have hdescent : baseEnd_5489056 < baseStart_5489056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489063 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5489063 : Nat := 118140960795 + 5489063 * 2 ^ 59
def prefixEnd_5489063 : Nat := 4983230072969 + 3 ^ 40 * 5489063 * 2
def baseEnd_5489063 : Nat := 2818527661810362749468765

theorem tailTrace_5489063 : CollatzResearch.WordTrace tailWord_5489063 prefixEnd_5489063 2818527661810362749468765 := by
  unfold tailWord_5489063
  simp only [CollatzResearch.WordTrace]
  refine ⟨200202574913069683170719843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133468383275379788780479895 200202574913069683170719843)
  ·
    refine ⟨300303862369604524756079765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200202574913069683170719843 300303862369604524756079765)
    ·
      refine ⟨14076743548575212097941239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 300303862369604524756079765 14076743548575212097941239)
      ·
        refine ⟨21115115322862818146911859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076743548575212097941239 21115115322862818146911859)
        ·
          refine ⟨31672672984294227220367789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21115115322862818146911859 31672672984294227220367789)
          ·
            refine ⟨11877252369110335207637921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31672672984294227220367789 11877252369110335207637921)
            ·
              refine ⟨8907939276832751405728441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11877252369110335207637921 8907939276832751405728441)
              ·
                refine ⟨6680954457624563554296331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8907939276832751405728441 6680954457624563554296331)
                ·
                  refine ⟨10021431686436845331444497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680954457624563554296331 10021431686436845331444497)
                  ·
                    refine ⟨7516073764827633998583373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10021431686436845331444497 7516073764827633998583373)
                    ·
                      refine ⟨2818527661810362749468765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516073764827633998583373 2818527661810362749468765)
                      ·
                        rfl

theorem cell23_5489063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5489063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489063 prefixEnd_5489063 := by exact prefixLift 5489063
  have htrace : WordTrace (prefixWord ++ tailWord_5489063) baseStart_5489063 baseEnd_5489063 := by
    simpa [prefixWord, tailWord_5489063, baseEnd_5489063] using wordTrace_append hprefix tailTrace_5489063
  have hstable : (prefixWord ++ tailWord_5489063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489063).length < 2 ^ (prefixWord ++ tailWord_5489063).sum := by decide
  have hdescent : baseEnd_5489063 < baseStart_5489063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489082 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_5489082 : Nat := 118140960795 + 5489082 * 2 ^ 59
def prefixEnd_5489082 : Nat := 4983230072969 + 3 ^ 40 * 5489082 * 2
def baseEnd_5489082 : Nat := 2818537417942798175131177

theorem tailTrace_5489082 : CollatzResearch.WordTrace tailWord_5489082 prefixEnd_5489082 2818537417942798175131177 := by
  unfold tailWord_5489082
  simp only [CollatzResearch.WordTrace]
  refine ⟨50050816975000212353915375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133468845266667232943774333 50050816975000212353915375)
  ·
    refine ⟨75076225462500318530873063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50050816975000212353915375 75076225462500318530873063)
    ·
      refine ⟨112614338193750477796309595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75076225462500318530873063 112614338193750477796309595)
      ·
        refine ⟨168921507290625716694464393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112614338193750477796309595 168921507290625716694464393)
        ·
          refine ⟨126691130467969287520848295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168921507290625716694464393 126691130467969287520848295)
          ·
            refine ⟨190036695701953931281272443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126691130467969287520848295 190036695701953931281272443)
            ·
              refine ⟨285055043552930896921908665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190036695701953931281272443 285055043552930896921908665)
              ·
                refine ⟨213791282664698172691431499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285055043552930896921908665 213791282664698172691431499)
                ·
                  refine ⟨320686923997047259037147249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213791282664698172691431499 320686923997047259037147249)
                  ·
                    refine ⟨240515192997785444277860437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320686923997047259037147249 240515192997785444277860437)
                    ·
                      refine ⟨2818537417942798175131177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 240515192997785444277860437 2818537417942798175131177)
                      ·
                        rfl

theorem cell23_5489082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_5489082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489082 prefixEnd_5489082 := by exact prefixLift 5489082
  have htrace : WordTrace (prefixWord ++ tailWord_5489082) baseStart_5489082 baseEnd_5489082 := by
    simpa [prefixWord, tailWord_5489082, baseEnd_5489082] using wordTrace_append hprefix tailTrace_5489082
  have hstable : (prefixWord ++ tailWord_5489082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489082).length < 2 ^ (prefixWord ++ tailWord_5489082).sum := by decide
  have hdescent : baseEnd_5489082 < baseStart_5489082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489110 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5489110 : Nat := 118140960795 + 5489110 * 2 ^ 59
def prefixEnd_5489110 : Nat := 4983230072969 + 3 ^ 40 * 5489110 * 2
def baseEnd_5489110 : Nat := 2818551795401124065581049

theorem tailTrace_5489110 : CollatzResearch.WordTrace tailWord_5489110 prefixEnd_5489110 2818551795401124065581049 := by
  unfold tailWord_5489110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512768071493713137355049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133469526095932940131787189 12512768071493713137355049)
  ·
    refine ⟨9384576053620284853016287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12512768071493713137355049 9384576053620284853016287)
    ·
      refine ⟨14076864080430427279524431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384576053620284853016287 14076864080430427279524431)
      ·
        refine ⟨21115296120645640919286647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076864080430427279524431 21115296120645640919286647)
        ·
          refine ⟨31672944180968461378929971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21115296120645640919286647 31672944180968461378929971)
          ·
            refine ⟨47509416271452692068394957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31672944180968461378929971 47509416271452692068394957)
            ·
              refine ⟨17816031101794759525648109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47509416271452692068394957 17816031101794759525648109)
              ·
                refine ⟨6681011663173034822118041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17816031101794759525648109 6681011663173034822118041)
                ·
                  refine ⟨5010758747379776116588531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6681011663173034822118041 5010758747379776116588531)
                  ·
                    refine ⟨7516138121069664174882797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010758747379776116588531 7516138121069664174882797)
                    ·
                      refine ⟨2818551795401124065581049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516138121069664174882797 2818551795401124065581049)
                      ·
                        rfl

theorem cell23_5489110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5489110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489110 prefixEnd_5489110 := by exact prefixLift 5489110
  have htrace : WordTrace (prefixWord ++ tailWord_5489110) baseStart_5489110 baseEnd_5489110 := by
    simpa [prefixWord, tailWord_5489110, baseEnd_5489110] using wordTrace_append hprefix tailTrace_5489110
  have hstable : (prefixWord ++ tailWord_5489110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489110).length < 2 ^ (prefixWord ++ tailWord_5489110).sum := by decide
  have hdescent : baseEnd_5489110 < baseStart_5489110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489119 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_5489119 : Nat := 118140960795 + 5489119 * 2 ^ 59
def prefixEnd_5489119 : Nat := 4983230072969 + 3 ^ 40 * 5489119 * 2
def baseEnd_5489119 : Nat := 2818556416727014530368507

theorem tailTrace_5489119 : CollatzResearch.WordTrace tailWord_5489119 prefixEnd_5489119 2818556416727014530368507 := by
  unfold tailWord_5489119
  simp only [CollatzResearch.WordTrace]
  refine ⟨200204617400866804734758411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133469744933911203156505607 200204617400866804734758411)
  ·
    refine ⟨300306926101300207102137617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200204617400866804734758411 300306926101300207102137617)
    ·
      refine ⟨225230194575975155326603213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300306926101300207102137617 225230194575975155326603213)
      ·
        refine ⟨84461322965990683247476205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225230194575975155326603213 84461322965990683247476205)
        ·
          refine ⟨31672996112246506217803577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84461322965990683247476205 31672996112246506217803577)
          ·
            refine ⟨23754747084184879663352683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31672996112246506217803577 23754747084184879663352683)
            ·
              refine ⟨35632120626277319495029025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23754747084184879663352683 35632120626277319495029025)
              ·
                refine ⟨26724090469707989621271769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35632120626277319495029025 26724090469707989621271769)
                ·
                  refine ⟨20043067852280992215953827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26724090469707989621271769 20043067852280992215953827)
                  ·
                    refine ⟨30064601778421488323930741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20043067852280992215953827 30064601778421488323930741)
                    ·
                      refine ⟨2818556416727014530368507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30064601778421488323930741 2818556416727014530368507)
                      ·
                        rfl

theorem cell23_5489119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_5489119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489119 prefixEnd_5489119 := by exact prefixLift 5489119
  have htrace : WordTrace (prefixWord ++ tailWord_5489119) baseStart_5489119 baseEnd_5489119 := by
    simpa [prefixWord, tailWord_5489119, baseEnd_5489119] using wordTrace_append hprefix tailTrace_5489119
  have hstable : (prefixWord ++ tailWord_5489119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489119).length < 2 ^ (prefixWord ++ tailWord_5489119).sum := by decide
  have hdescent : baseEnd_5489119 < baseStart_5489119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489133 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5489133 : Nat := 118140960795 + 5489133 * 2 ^ 59
def prefixEnd_5489133 : Nat := 4983230072969 + 3 ^ 40 * 5489133 * 2
def baseEnd_5489133 : Nat := 2818563605456177475593443

theorem tailTrace_5489133 : CollatzResearch.WordTrace tailWord_5489133 prefixEnd_5489133 2818563605456177475593443 := by
  unfold tailWord_5489133
  simp only [CollatzResearch.WordTrace]
  refine ⟨200205128022816085125768053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133470085348544056750512035 200205128022816085125768053)
  ·
    refine ⟨18769230752139007980540755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200205128022816085125768053 18769230752139007980540755)
    ·
      refine ⟨28153846128208511970811133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18769230752139007980540755 28153846128208511970811133)
      ·
        refine ⟨10557692298078191989054175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28153846128208511970811133 10557692298078191989054175)
        ·
          refine ⟨15836538447117287983581263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557692298078191989054175 15836538447117287983581263)
          ·
            refine ⟨23754807670675931975371895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15836538447117287983581263 23754807670675931975371895)
            ·
              refine ⟨35632211506013897963057843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23754807670675931975371895 35632211506013897963057843)
              ·
                refine ⟨53448317259020846944586765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35632211506013897963057843 53448317259020846944586765)
                ·
                  refine ⟨20043118972132817604220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53448317259020846944586765 20043118972132817604220037)
                  ·
                    refine ⟨3758084807274903300791257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20043118972132817604220037 3758084807274903300791257)
                    ·
                      refine ⟨2818563605456177475593443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758084807274903300791257 2818563605456177475593443)
                      ·
                        rfl

theorem cell23_5489133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5489133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489133 prefixEnd_5489133 := by exact prefixLift 5489133
  have htrace : WordTrace (prefixWord ++ tailWord_5489133) baseStart_5489133 baseEnd_5489133 := by
    simpa [prefixWord, tailWord_5489133, baseEnd_5489133] using wordTrace_append hprefix tailTrace_5489133
  have hstable : (prefixWord ++ tailWord_5489133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489133).length < 2 ^ (prefixWord ++ tailWord_5489133).sum := by decide
  have hdescent : baseEnd_5489133 < baseStart_5489133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489166 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5489166 : Nat := 118140960795 + 5489166 * 2 ^ 59
def prefixEnd_5489166 : Nat := 4983230072969 + 3 ^ 40 * 5489166 * 2
def baseEnd_5489166 : Nat := 2818580550317775846480791

theorem tailTrace_5489166 : CollatzResearch.WordTrace tailWord_5489166 prefixEnd_5489166 2818580550317775846480791 := by
  unfold tailWord_5489166
  simp only [CollatzResearch.WordTrace]
  refine ⟨25025791453962066470214919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133470887754464354507812901 25025791453962066470214919)
  ·
    refine ⟨37538687180943099705322379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25025791453962066470214919 37538687180943099705322379)
    ·
      refine ⟨56308030771414649557983569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37538687180943099705322379 56308030771414649557983569)
      ·
        refine ⟨42231023078560987168487677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56308030771414649557983569 42231023078560987168487677)
        ·
          refine ⟨15836633654460370188182879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42231023078560987168487677 15836633654460370188182879)
          ·
            refine ⟨23754950481690555282274319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15836633654460370188182879 23754950481690555282274319)
            ·
              refine ⟨35632425722535832923411479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23754950481690555282274319 35632425722535832923411479)
              ·
                refine ⟨53448638583803749385117219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35632425722535832923411479 53448638583803749385117219)
                ·
                  refine ⟨80172957875705624077675829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53448638583803749385117219 80172957875705624077675829)
                  ·
                    refine ⟨7516214800847402257282109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80172957875705624077675829 7516214800847402257282109)
                    ·
                      refine ⟨2818580550317775846480791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516214800847402257282109 2818580550317775846480791)
                      ·
                        rfl

theorem cell23_5489166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5489166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489166 prefixEnd_5489166 := by exact prefixLift 5489166
  have htrace : WordTrace (prefixWord ++ tailWord_5489166) baseStart_5489166 baseEnd_5489166 := by
    simpa [prefixWord, tailWord_5489166, baseEnd_5489166] using wordTrace_append hprefix tailTrace_5489166
  have hstable : (prefixWord ++ tailWord_5489166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489166).length < 2 ^ (prefixWord ++ tailWord_5489166).sum := by decide
  have hdescent : baseEnd_5489166 < baseStart_5489166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489216 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_5489216 : Nat := 118140960795 + 5489216 * 2 ^ 59
def prefixEnd_5489216 : Nat := 4983230072969 + 3 ^ 40 * 5489216 * 2
def baseEnd_5489216 : Nat := 939535408116833550285187

theorem tailTrace_5489216 : CollatzResearch.WordTrace tailWord_5489216 prefixEnd_5489216 939535408116833550285187 := by
  unfold tailWord_5489216
  simp only [CollatzResearch.WordTrace]
  refine ⟨100104077640757695150519751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133472103521010260200693001 100104077640757695150519751)
  ·
    refine ⟨150156116461136542725779627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100104077640757695150519751 150156116461136542725779627)
    ·
      refine ⟨225234174691704814088669441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150156116461136542725779627 225234174691704814088669441)
      ·
        refine ⟨168925631018778610566502081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225234174691704814088669441 168925631018778610566502081)
        ·
          refine ⟨126694223264083957924876561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168925631018778610566502081 126694223264083957924876561)
          ·
            refine ⟨95020667448062968443657421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126694223264083957924876561 95020667448062968443657421)
            ·
              refine ⟨35632750293023613166371533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95020667448062968443657421 35632750293023613166371533)
              ·
                refine ⟨13362281359883854937389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35632750293023613166371533 13362281359883854937389325)
                ·
                  refine ⟨5010855509956445601520997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13362281359883854937389325 5010855509956445601520997)
                  ·
                    refine ⟨939535408116833550285187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010855509956445601520997 939535408116833550285187)
                    ·
                      rfl

theorem cell23_5489216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_5489216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489216 prefixEnd_5489216 := by exact prefixLift 5489216
  have htrace : WordTrace (prefixWord ++ tailWord_5489216) baseStart_5489216 baseEnd_5489216 := by
    simpa [prefixWord, tailWord_5489216, baseEnd_5489216] using wordTrace_append hprefix tailTrace_5489216
  have hstable : (prefixWord ++ tailWord_5489216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489216).length < 2 ^ (prefixWord ++ tailWord_5489216).sum := by decide
  have hdescent : baseEnd_5489216 < baseStart_5489216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489223 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_5489223 : Nat := 118140960795 + 5489223 * 2 ^ 59
def prefixEnd_5489223 : Nat := 4983230072969 + 3 ^ 40 * 5489223 * 2
def baseEnd_5489223 : Nat := 2818609818715082123468029

theorem tailTrace_5489223 : CollatzResearch.WordTrace tailWord_5489223 prefixEnd_5489223 2818609818715082123468029 := by
  unfold tailWord_5489223
  simp only [CollatzResearch.WordTrace]
  refine ⟨200208410592490030496544323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133472273728326686997696215 200208410592490030496544323)
  ·
    refine ⟨300312615888735045744816485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200208410592490030496544323 300312615888735045744816485)
    ·
      refine ⟨56308615479137821077153091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300312615888735045744816485 56308615479137821077153091)
      ·
        refine ⟨84462923218706731615729637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56308615479137821077153091 84462923218706731615729637)
        ·
          refine ⟨15836798103507512177949307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84462923218706731615729637 15836798103507512177949307)
          ·
            refine ⟨23755197155261268266923961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15836798103507512177949307 23755197155261268266923961)
            ·
              refine ⟨17816397866445951200192971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23755197155261268266923961 17816397866445951200192971)
              ·
                refine ⟨26724596799668926800289457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17816397866445951200192971 26724596799668926800289457)
                ·
                  refine ⟨20043447599751695100217093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26724596799668926800289457 20043447599751695100217093)
                  ·
                    refine ⟨3758146424953442831290705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20043447599751695100217093 3758146424953442831290705)
                    ·
                      refine ⟨2818609818715082123468029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758146424953442831290705 2818609818715082123468029)
                      ·
                        rfl

theorem cell23_5489223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_5489223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489223 prefixEnd_5489223 := by exact prefixLift 5489223
  have htrace : WordTrace (prefixWord ++ tailWord_5489223) baseStart_5489223 baseEnd_5489223 := by
    simpa [prefixWord, tailWord_5489223, baseEnd_5489223] using wordTrace_append hprefix tailTrace_5489223
  have hstable : (prefixWord ++ tailWord_5489223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489223).length < 2 ^ (prefixWord ++ tailWord_5489223).sum := by decide
  have hdescent : baseEnd_5489223 < baseStart_5489223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489226 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_5489226 : Nat := 118140960795 + 5489226 * 2 ^ 59
def prefixEnd_5489226 : Nat := 4983230072969 + 3 ^ 40 * 5489226 * 2
def baseEnd_5489226 : Nat := 2818611359157045611730515

theorem tailTrace_5489226 : CollatzResearch.WordTrace tailWord_5489226 prefixEnd_5489226 2818611359157045611730515 := by
  unfold tailWord_5489226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052130002869790502225883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133472346674319441339269021 50052130002869790502225883)
  ·
    refine ⟨75078195004304685753338825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50052130002869790502225883 75078195004304685753338825)
    ·
      refine ⟨56308646253228514315004119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75078195004304685753338825 56308646253228514315004119)
      ·
        refine ⟨84462969379842771472506179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56308646253228514315004119 84462969379842771472506179)
        ·
          refine ⟨126694454069764157208759269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84462969379842771472506179 126694454069764157208759269)
          ·
            refine ⟨23755210138080779476642363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126694454069764157208759269 23755210138080779476642363)
            ·
              refine ⟨35632815207121169214963545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23755210138080779476642363 35632815207121169214963545)
              ·
                refine ⟨26724611405340876911222659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35632815207121169214963545 26724611405340876911222659)
                ·
                  refine ⟨40086917108011315366833989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26724611405340876911222659 40086917108011315366833989)
                  ·
                    refine ⟨7516296957752121631281373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40086917108011315366833989 7516296957752121631281373)
                    ·
                      refine ⟨2818611359157045611730515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516296957752121631281373 2818611359157045611730515)
                      ·
                        rfl

theorem cell23_5489226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_5489226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489226 prefixEnd_5489226 := by exact prefixLift 5489226
  have htrace : WordTrace (prefixWord ++ tailWord_5489226) baseStart_5489226 baseEnd_5489226 := by
    simpa [prefixWord, tailWord_5489226, baseEnd_5489226] using wordTrace_append hprefix tailTrace_5489226
  have hstable : (prefixWord ++ tailWord_5489226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489226).length < 2 ^ (prefixWord ++ tailWord_5489226).sum := by decide
  have hdescent : baseEnd_5489226 < baseStart_5489226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489330 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_5489330 : Nat := 118140960795 + 5489330 * 2 ^ 59
def prefixEnd_5489330 : Nat := 4983230072969 + 3 ^ 40 * 5489330 * 2
def baseEnd_5489330 : Nat := 2818664761145113204830037

theorem tailTrace_5489330 : CollatzResearch.WordTrace tailWord_5489330 prefixEnd_5489330 2818664761145113204830037 := by
  unfold tailWord_5489330
  simp only [CollatzResearch.WordTrace]
  refine ⟨50053078300775596942672361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133474875468734925180459629 50053078300775596942672361)
  ·
    refine ⟨37539808725581697707004271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50053078300775596942672361 37539808725581697707004271)
    ·
      refine ⟨56309713088372546560506407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37539808725581697707004271 56309713088372546560506407)
      ·
        refine ⟨84464569632558819840759611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56309713088372546560506407 84464569632558819840759611)
        ·
          refine ⟨126696854448838229761139417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84464569632558819840759611 126696854448838229761139417)
          ·
            refine ⟨95022640836628672320854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126696854448838229761139417 95022640836628672320854563)
            ·
              refine ⟨142533961254943008481281845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95022640836628672320854563 142533961254943008481281845)
              ·
                refine ⟨13362558867650907045120173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142533961254943008481281845 13362558867650907045120173)
                ·
                  refine ⟨5010959575369090141920065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13362558867650907045120173 5010959575369090141920065)
                  ·
                    refine ⟨3758219681526817606440049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5010959575369090141920065 3758219681526817606440049)
                    ·
                      refine ⟨2818664761145113204830037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758219681526817606440049 2818664761145113204830037)
                      ·
                        rfl

theorem cell23_5489330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_5489330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489330 prefixEnd_5489330 := by exact prefixLift 5489330
  have htrace : WordTrace (prefixWord ++ tailWord_5489330) baseStart_5489330 baseEnd_5489330 := by
    simpa [prefixWord, tailWord_5489330, baseEnd_5489330] using wordTrace_append hprefix tailTrace_5489330
  have hstable : (prefixWord ++ tailWord_5489330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489330).length < 2 ^ (prefixWord ++ tailWord_5489330).sum := by decide
  have hdescent : baseEnd_5489330 < baseStart_5489330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489343 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_5489343 : Nat := 118140960795 + 5489343 * 2 ^ 59
def prefixEnd_5489343 : Nat := 4983230072969 + 3 ^ 40 * 5489343 * 2
def baseEnd_5489343 : Nat := 2818671436393621653967477

theorem tailTrace_5489343 : CollatzResearch.WordTrace tailWord_5489343 prefixEnd_5489343 2818671436393621653967477 := by
  unfold tailWord_5489343
  simp only [CollatzResearch.WordTrace]
  refine ⟨200212787352055290990912683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133475191568036860660608455 200212787352055290990912683)
  ·
    refine ⟨300319181028082936486369025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200212787352055290990912683 300319181028082936486369025)
    ·
      refine ⟨225239385771062202364776769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300319181028082936486369025 225239385771062202364776769)
      ·
        refine ⟨168929539328296651773582577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225239385771062202364776769 168929539328296651773582577)
        ·
          refine ⟨126697154496222488830186933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168929539328296651773582577 126697154496222488830186933)
          ·
            refine ⟨11877858234020858327830025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126697154496222488830186933 11877858234020858327830025)
            ·
              refine ⟨8908393675515643745872519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11877858234020858327830025 8908393675515643745872519)
              ·
                refine ⟨13362590513273465618808779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8908393675515643745872519 13362590513273465618808779)
                ·
                  refine ⟨20043885769910198428213169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13362590513273465618808779 20043885769910198428213169)
                  ·
                    refine ⟨15032914327432648821159877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20043885769910198428213169 15032914327432648821159877)
                    ·
                      refine ⟨2818671436393621653967477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15032914327432648821159877 2818671436393621653967477)
                      ·
                        rfl

theorem cell23_5489343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_5489343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489343 prefixEnd_5489343 := by exact prefixLift 5489343
  have htrace : WordTrace (prefixWord ++ tailWord_5489343) baseStart_5489343 baseEnd_5489343 := by
    simpa [prefixWord, tailWord_5489343, baseEnd_5489343] using wordTrace_append hprefix tailTrace_5489343
  have hstable : (prefixWord ++ tailWord_5489343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489343).length < 2 ^ (prefixWord ++ tailWord_5489343).sum := by decide
  have hdescent : baseEnd_5489343 < baseStart_5489343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489364 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5489364 : Nat := 118140960795 + 5489364 * 2 ^ 59
def prefixEnd_5489364 : Nat := 4983230072969 + 3 ^ 40 * 5489364 * 2
def baseEnd_5489364 : Nat := 2818682219487366071804881

theorem tailTrace_5489364 : CollatzResearch.WordTrace tailWord_5489364 prefixEnd_5489364 2818682219487366071804881 := by
  unfold tailWord_5489364
  simp only [CollatzResearch.WordTrace]
  refine ⟨100106776642489605788713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133475702189986141051618097 100106776642489605788713573)
  ·
    refine ⟨18770020620466801085383795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100106776642489605788713573 18770020620466801085383795)
    ·
      refine ⟨28155030930700201628075693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18770020620466801085383795 28155030930700201628075693)
      ·
        refine ⟨10558136599012575610528385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28155030930700201628075693 10558136599012575610528385)
        ·
          refine ⟨7918602449259431707896289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10558136599012575610528385 7918602449259431707896289)
          ·
            refine ⟨5938951836944573780922217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7918602449259431707896289 5938951836944573780922217)
            ·
              refine ⟨4454213877708430335691663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938951836944573780922217 4454213877708430335691663)
              ·
                refine ⟨6681320816562645503537495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454213877708430335691663 6681320816562645503537495)
                ·
                  refine ⟨10021981224843968255306243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681320816562645503537495 10021981224843968255306243)
                  ·
                    refine ⟨15032971837265952382959365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10021981224843968255306243 15032971837265952382959365)
                    ·
                      refine ⟨2818682219487366071804881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15032971837265952382959365 2818682219487366071804881)
                      ·
                        rfl

theorem cell23_5489364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5489364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489364 prefixEnd_5489364 := by exact prefixLift 5489364
  have htrace : WordTrace (prefixWord ++ tailWord_5489364) baseStart_5489364 baseEnd_5489364 := by
    simpa [prefixWord, tailWord_5489364, baseEnd_5489364] using wordTrace_append hprefix tailTrace_5489364
  have hstable : (prefixWord ++ tailWord_5489364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489364).length < 2 ^ (prefixWord ++ tailWord_5489364).sum := by decide
  have hdescent : baseEnd_5489364 < baseStart_5489364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489367 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_5489367 : Nat := 118140960795 + 5489367 * 2 ^ 59
def prefixEnd_5489367 : Nat := 4983230072969 + 3 ^ 40 * 5489367 * 2
def baseEnd_5489367 : Nat := 2818683759929329560067367

theorem tailTrace_5489367 : CollatzResearch.WordTrace tailWord_5489367 prefixEnd_5489367 2818683759929329560067367 := by
  unfold tailWord_5489367
  simp only [CollatzResearch.WordTrace]
  refine ⟨200213662703968343089786355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133475775135978895393190903 200213662703968343089786355)
  ·
    refine ⟨300320494055952514634679533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200213662703968343089786355 300320494055952514634679533)
    ·
      refine ⟨112620185270982192988004825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300320494055952514634679533 112620185270982192988004825)
      ·
        refine ⟨84465138953236644741003619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112620185270982192988004825 84465138953236644741003619)
        ·
          refine ⟨126697708429854967111505429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84465138953236644741003619 126697708429854967111505429)
          ·
            refine ⟨5938955082649451583351817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126697708429854967111505429 5938955082649451583351817)
            ·
              refine ⟨4454216311987088687513863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938955082649451583351817 4454216311987088687513863)
              ·
                refine ⟨6681324467980633031270795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454216311987088687513863 6681324467980633031270795)
                ·
                  refine ⟨10021986701970949546906193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681324467980633031270795 10021986701970949546906193)
                  ·
                    refine ⟨7516490026478212160179645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10021986701970949546906193 7516490026478212160179645)
                    ·
                      refine ⟨2818683759929329560067367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516490026478212160179645 2818683759929329560067367)
                      ·
                        rfl

theorem cell23_5489367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_5489367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489367 prefixEnd_5489367 := by exact prefixLift 5489367
  have htrace : WordTrace (prefixWord ++ tailWord_5489367) baseStart_5489367 baseEnd_5489367 := by
    simpa [prefixWord, tailWord_5489367, baseEnd_5489367] using wordTrace_append hprefix tailTrace_5489367
  have hstable : (prefixWord ++ tailWord_5489367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489367).length < 2 ^ (prefixWord ++ tailWord_5489367).sum := by decide
  have hdescent : baseEnd_5489367 < baseStart_5489367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489380 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_5489380 : Nat := 118140960795 + 5489380 * 2 ^ 59
def prefixEnd_5489380 : Nat := 4983230072969 + 3 ^ 40 * 5489380 * 2
def baseEnd_5489380 : Nat := 2818690435177838009204807

theorem tailTrace_5489380 : CollatzResearch.WordTrace tailWord_5489380 prefixEnd_5489380 2818690435177838009204807 := by
  unfold tailWord_5489380
  simp only [CollatzResearch.WordTrace]
  refine ⟨100107068426460623155004797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133476091235280830873339729 100107068426460623155004797)
  ·
    refine ⟨37540150659922733683126799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100107068426460623155004797 37540150659922733683126799)
    ·
      refine ⟨56310225989884100524690199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37540150659922733683126799 56310225989884100524690199)
      ·
        refine ⟨84465338984826150787035299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56310225989884100524690199 84465338984826150787035299)
        ·
          refine ⟨126698008477239226180552949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84465338984826150787035299 126698008477239226180552949)
          ·
            refine ⟨11877938294741177454426839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126698008477239226180552949 11877938294741177454426839)
            ·
              refine ⟨17816907442111766181640259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11877938294741177454426839 17816907442111766181640259)
              ·
                refine ⟨26725361163167649272460389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17816907442111766181640259 26725361163167649272460389)
                ·
                  refine ⟨5011005218093934238586323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26725361163167649272460389 5011005218093934238586323)
                  ·
                    refine ⟨7516507827140901357879485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011005218093934238586323 7516507827140901357879485)
                    ·
                      refine ⟨2818690435177838009204807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516507827140901357879485 2818690435177838009204807)
                      ·
                        rfl

theorem cell23_5489380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_5489380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489380 prefixEnd_5489380 := by exact prefixLift 5489380
  have htrace : WordTrace (prefixWord ++ tailWord_5489380) baseStart_5489380 baseEnd_5489380 := by
    simpa [prefixWord, tailWord_5489380, baseEnd_5489380] using wordTrace_append hprefix tailTrace_5489380
  have hstable : (prefixWord ++ tailWord_5489380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489380).length < 2 ^ (prefixWord ++ tailWord_5489380).sum := by decide
  have hdescent : baseEnd_5489380 < baseStart_5489380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489456 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_5489456 : Nat := 118140960795 + 5489456 * 2 ^ 59
def prefixEnd_5489456 : Nat := 4983230072969 + 3 ^ 40 * 5489456 * 2
def baseEnd_5489456 : Nat := 939576486569193237284819

theorem tailTrace_5489456 : CollatzResearch.WordTrace tailWord_5489456 prefixEnd_5489456 939576486569193237284819 := by
  unfold tailWord_5489456
  simp only [CollatzResearch.WordTrace]
  refine ⟨100108454400322955644888111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133477939200430607526517481 100108454400322955644888111)
  ·
    refine ⟨150162681600484433467332167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100108454400322955644888111 150162681600484433467332167)
    ·
      refine ⟨225244022400726650200998251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150162681600484433467332167 225244022400726650200998251)
      ·
        refine ⟨337866033601089975301497377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225244022400726650200998251 337866033601089975301497377)
        ·
          refine ⟨253399525200817481476123033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337866033601089975301497377 253399525200817481476123033)
          ·
            refine ⟨190049643900613111107092275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253399525200817481476123033 190049643900613111107092275)
            ·
              refine ⟨285074465850919666660638413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190049643900613111107092275 285074465850919666660638413)
              ·
                refine ⟨106902924694094874997739405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285074465850919666660638413 106902924694094874997739405)
                ·
                  refine ⟨40088596760285578124152277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106902924694094874997739405 40088596760285578124152277)
                  ·
                    refine ⟨939576486569193237284819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40088596760285578124152277 939576486569193237284819)
                    ·
                      rfl

theorem cell23_5489456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_5489456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489456 prefixEnd_5489456 := by exact prefixLift 5489456
  have htrace : WordTrace (prefixWord ++ tailWord_5489456) baseStart_5489456 baseEnd_5489456 := by
    simpa [prefixWord, tailWord_5489456, baseEnd_5489456] using wordTrace_append hprefix tailTrace_5489456
  have hstable : (prefixWord ++ tailWord_5489456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489456).length < 2 ^ (prefixWord ++ tailWord_5489456).sum := by decide
  have hdescent : baseEnd_5489456 < baseStart_5489456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489500 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5489500 : Nat := 118140960795 + 5489500 * 2 ^ 59
def prefixEnd_5489500 : Nat := 4983230072969 + 3 ^ 40 * 5489500 * 2
def baseEnd_5489500 : Nat := 2818752052856377539704255

theorem tailTrace_5489500 : CollatzResearch.WordTrace tailWord_5489500 prefixEnd_5489500 2818752052856377539704255 := by
  unfold tailWord_5489500
  simp only [CollatzResearch.WordTrace]
  refine ⟨100109256806243253402188977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133479009074991004536251969 100109256806243253402188977)
  ·
    refine ⟨75081942604682440051641733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100109256806243253402188977 75081942604682440051641733)
    ·
      refine ⟨14077864238377957509682825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75081942604682440051641733 14077864238377957509682825)
      ·
        refine ⟨10558398178783468132262119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14077864238377957509682825 10558398178783468132262119)
        ·
          refine ⟨15837597268175202198393179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558398178783468132262119 15837597268175202198393179)
          ·
            refine ⟨23756395902262803297589769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15837597268175202198393179 23756395902262803297589769)
            ·
              refine ⟨17817296926697102473192327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23756395902262803297589769 17817296926697102473192327)
              ·
                refine ⟨26725945390045653709788491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17817296926697102473192327 26725945390045653709788491)
                ·
                  refine ⟨40088918085068480564682737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26725945390045653709788491 40088918085068480564682737)
                  ·
                    refine ⟨30066688563801360423512053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40088918085068480564682737 30066688563801360423512053)
                    ·
                      refine ⟨2818752052856377539704255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30066688563801360423512053 2818752052856377539704255)
                      ·
                        rfl

theorem cell23_5489500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5489500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489500 prefixEnd_5489500 := by exact prefixLift 5489500
  have htrace : WordTrace (prefixWord ++ tailWord_5489500) baseStart_5489500 baseEnd_5489500 := by
    simpa [prefixWord, tailWord_5489500, baseEnd_5489500] using wordTrace_append hprefix tailTrace_5489500
  have hstable : (prefixWord ++ tailWord_5489500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489500).length < 2 ^ (prefixWord ++ tailWord_5489500).sum := by decide
  have hdescent : baseEnd_5489500 < baseStart_5489500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489554 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5489554 : Nat := 118140960795 + 5489554 * 2 ^ 59
def prefixEnd_5489554 : Nat := 4983230072969 + 3 ^ 40 * 5489554 * 2
def baseEnd_5489554 : Nat := 939593260270573442809669

theorem tailTrace_5489554 : CollatzResearch.WordTrace tailWord_5489554 prefixEnd_5489554 939593260270573442809669 := by
  unfold tailWord_5489554
  simp only [CollatzResearch.WordTrace]
  refine ⟨50055120788572718506710929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133480322102860582684562477 50055120788572718506710929)
  ·
    refine ⟨37541340591429538880033197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50055120788572718506710929 37541340591429538880033197)
    ·
      refine ⟨14078002721786077080012449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37541340591429538880033197 14078002721786077080012449)
      ·
        refine ⟨10558502041339557810009337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14078002721786077080012449 10558502041339557810009337)
        ·
          refine ⟨7918876531004668357507003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10558502041339557810009337 7918876531004668357507003)
          ·
            refine ⟨11878314796507002536260505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918876531004668357507003 11878314796507002536260505)
            ·
              refine ⟨8908736097380251902195379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11878314796507002536260505 8908736097380251902195379)
              ·
                refine ⟨13363104146070377853293069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8908736097380251902195379 13363104146070377853293069)
                ·
                  refine ⟨5011164054776391694984901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13363104146070377853293069 5011164054776391694984901)
                  ·
                    refine ⟨939593260270573442809669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011164054776391694984901 939593260270573442809669)
                    ·
                      rfl

theorem cell23_5489554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5489554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489554 prefixEnd_5489554 := by exact prefixLift 5489554
  have htrace : WordTrace (prefixWord ++ tailWord_5489554) baseStart_5489554 baseEnd_5489554 := by
    simpa [prefixWord, tailWord_5489554, baseEnd_5489554] using wordTrace_append hprefix tailTrace_5489554
  have hstable : (prefixWord ++ tailWord_5489554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489554).length < 2 ^ (prefixWord ++ tailWord_5489554).sum := by decide
  have hdescent : baseEnd_5489554 < baseStart_5489554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489567 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 6]
def baseStart_5489567 : Nat := 118140960795 + 5489567 * 2 ^ 59
def prefixEnd_5489567 : Nat := 4983230072969 + 3 ^ 40 * 5489567 * 2
def baseEnd_5489567 : Nat := 313198495117803197507383

theorem tailTrace_5489567 : CollatzResearch.WordTrace tailWord_5489567 prefixEnd_5489567 313198495117803197507383 := by
  unfold tailWord_5489567
  simp only [CollatzResearch.WordTrace]
  refine ⟨200220957303243777247066955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133480638202162518164711303 200220957303243777247066955)
  ·
    refine ⟨300331435954865665870600433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200220957303243777247066955 300331435954865665870600433)
    ·
      refine ⟨225248576966149249402950325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300331435954865665870600433 225248576966149249402950325)
      ·
        refine ⟨21117054090576492131526593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225248576966149249402950325 21117054090576492131526593)
        ·
          refine ⟨15837790567932369098644945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21117054090576492131526593 15837790567932369098644945)
          ·
            refine ⟨11878342925949276823983709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15837790567932369098644945 11878342925949276823983709)
            ·
              refine ⟨4454378597230978808993891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11878342925949276823983709 4454378597230978808993891)
              ·
                refine ⟨6681567895846468213490837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454378597230978808993891 6681567895846468213490837)
                ·
                  refine ⟨313198495117803197507383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6681567895846468213490837 313198495117803197507383)
                  ·
                    rfl

theorem cell23_5489567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 6].length) (baseStart_5489567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489567 prefixEnd_5489567 := by exact prefixLift 5489567
  have htrace : WordTrace (prefixWord ++ tailWord_5489567) baseStart_5489567 baseEnd_5489567 := by
    simpa [prefixWord, tailWord_5489567, baseEnd_5489567] using wordTrace_append hprefix tailTrace_5489567
  have hstable : (prefixWord ++ tailWord_5489567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489567).length < 2 ^ (prefixWord ++ tailWord_5489567).sum := by decide
  have hdescent : baseEnd_5489567 < baseStart_5489567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489588 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5489588 : Nat := 118140960795 + 5489588 * 2 ^ 59
def prefixEnd_5489588 : Nat := 4983230072969 + 3 ^ 40 * 5489588 * 2
def baseEnd_5489588 : Nat := 939599079717991065134617

theorem tailTrace_5489588 : CollatzResearch.WordTrace tailWord_5489588 prefixEnd_5489588 939599079717991065134617 := by
  unfold tailWord_5489588
  simp only [CollatzResearch.WordTrace]
  refine ⟨100110861618083848916790709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133481148824111798555720945 100110861618083848916790709)
  ·
    refine ⟨9385393276695360835949129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100110861618083848916790709 9385393276695360835949129)
    ·
      refine ⟨7039044957521520626961847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9385393276695360835949129 7039044957521520626961847)
      ·
        refine ⟨10558567436282280940442771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039044957521520626961847 10558567436282280940442771)
        ·
          refine ⟨15837851154423421410664157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558567436282280940442771 15837851154423421410664157)
          ·
            refine ⟨5939194182908783028999059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15837851154423421410664157 5939194182908783028999059)
            ·
              refine ⟨8908791274363174543498589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939194182908783028999059 8908791274363174543498589)
              ·
                refine ⟨3340796727886190453811971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8908791274363174543498589 3340796727886190453811971)
                ·
                  refine ⟨5011195091829285680717957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340796727886190453811971 5011195091829285680717957)
                  ·
                    refine ⟨939599079717991065134617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011195091829285680717957 939599079717991065134617)
                    ·
                      rfl

theorem cell23_5489588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5489588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489588 prefixEnd_5489588 := by exact prefixLift 5489588
  have htrace : WordTrace (prefixWord ++ tailWord_5489588) baseStart_5489588 baseEnd_5489588 := by
    simpa [prefixWord, tailWord_5489588, baseEnd_5489588] using wordTrace_append hprefix tailTrace_5489588
  have hstable : (prefixWord ++ tailWord_5489588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489588).length < 2 ^ (prefixWord ++ tailWord_5489588).sum := by decide
  have hdescent : baseEnd_5489588 < baseStart_5489588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_5489603 : Nat := 118140960795 + 5489603 * 2 ^ 59
def prefixEnd_5489603 : Nat := 4983230072969 + 3 ^ 40 * 5489603 * 2
def baseEnd_5489603 : Nat := 2818804941363790636716281

theorem tailTrace_5489603 : CollatzResearch.WordTrace tailWord_5489603 prefixEnd_5489603 2818804941363790636716281 := by
  unfold tailWord_5489603
  simp only [CollatzResearch.WordTrace]
  refine ⟨200222270331113355395377463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133481513554075570263584975 200222270331113355395377463)
  ·
    refine ⟨300333405496670033093066195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200222270331113355395377463 300333405496670033093066195)
    ·
      refine ⟨450500108245005049639599293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300333405496670033093066195 450500108245005049639599293)
      ·
        refine ⟨168937540591876893614849735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450500108245005049639599293 168937540591876893614849735)
        ·
          refine ⟨253406310887815340422274603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168937540591876893614849735 253406310887815340422274603)
          ·
            refine ⟨380109466331723010633411905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253406310887815340422274603 380109466331723010633411905)
            ·
              refine ⟨285082099748792257975058929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380109466331723010633411905 285082099748792257975058929)
              ·
                refine ⟨213811574811594193481294197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285082099748792257975058929 213811574811594193481294197)
                ·
                  refine ⟨20044835138586955638871331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213811574811594193481294197 20044835138586955638871331)
                  ·
                    refine ⟨30067252707880433458306997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20044835138586955638871331 30067252707880433458306997)
                    ·
                      refine ⟨2818804941363790636716281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30067252707880433458306997 2818804941363790636716281)
                      ·
                        rfl

theorem cell23_5489603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_5489603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489603 prefixEnd_5489603 := by exact prefixLift 5489603
  have htrace : WordTrace (prefixWord ++ tailWord_5489603) baseStart_5489603 baseEnd_5489603 := by
    simpa [prefixWord, tailWord_5489603, baseEnd_5489603] using wordTrace_append hprefix tailTrace_5489603
  have hstable : (prefixWord ++ tailWord_5489603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489603).length < 2 ^ (prefixWord ++ tailWord_5489603).sum := by decide
  have hdescent : baseEnd_5489603 < baseStart_5489603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489611 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 1, 1, 3]
def baseStart_5489611 : Nat := 118140960795 + 5489611 * 2 ^ 59
def prefixEnd_5489611 : Nat := 4983230072969 + 3 ^ 40 * 5489611 * 2
def baseEnd_5489611 : Nat := 2818809049209026605416245

theorem tailTrace_5489611 : CollatzResearch.WordTrace tailWord_5489611 prefixEnd_5489611 2818809049209026605416245 := by
  unfold tailWord_5489611
  simp only [CollatzResearch.WordTrace]
  refine ⟨200222562115084372761668687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133481708076722915174445791 200222562115084372761668687)
  ·
    refine ⟨300333843172626559142503031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200222562115084372761668687 300333843172626559142503031)
    ·
      refine ⟨450500764758939838713754547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300333843172626559142503031 450500764758939838713754547)
      ·
        refine ⟨675751147138409758070631821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450500764758939838713754547 675751147138409758070631821)
        ·
          refine ⟨253406680176903659276486933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 675751147138409758070631821 253406680176903659276486933)
          ·
            refine ⟨11878438133292359028585325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253406680176903659276486933 11878438133292359028585325)
            ·
              refine ⟨4454414299984634635719497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11878438133292359028585325 4454414299984634635719497)
              ·
                refine ⟨3340810724988475976789623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454414299984634635719497 3340810724988475976789623)
                ·
                  refine ⟨5011216087482713965184435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340810724988475976789623 5011216087482713965184435)
                  ·
                    refine ⟨7516824131224070947776653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011216087482713965184435 7516824131224070947776653)
                    ·
                      refine ⟨2818809049209026605416245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516824131224070947776653 2818809049209026605416245)
                      ·
                        rfl

theorem cell23_5489611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 1, 1, 3].length) (baseStart_5489611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489611 prefixEnd_5489611 := by exact prefixLift 5489611
  have htrace : WordTrace (prefixWord ++ tailWord_5489611) baseStart_5489611 baseEnd_5489611 := by
    simpa [prefixWord, tailWord_5489611, baseEnd_5489611] using wordTrace_append hprefix tailTrace_5489611
  have hstable : (prefixWord ++ tailWord_5489611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489611).length < 2 ^ (prefixWord ++ tailWord_5489611).sum := by decide
  have hdescent : baseEnd_5489611 < baseStart_5489611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489634 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5489634 : Nat := 118140960795 + 5489634 * 2 ^ 59
def prefixEnd_5489634 : Nat := 4983230072969 + 3 ^ 40 * 5489634 * 2
def baseEnd_5489634 : Nat := 2818820859264080015428639

theorem tailTrace_5489634 : CollatzResearch.WordTrace tailWord_5489634 prefixEnd_5489634 2818820859264080015428639 := by
  unfold tailWord_5489634
  simp only [CollatzResearch.WordTrace]
  refine ⟨50055850248500261922438989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133482267329334031793170637 50055850248500261922438989)
  ·
    refine ⟨18770943843187598220914621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50055850248500261922438989 18770943843187598220914621)
    ·
      refine ⟨7039103941195349332842983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18770943843187598220914621 7039103941195349332842983)
      ·
        refine ⟨10558655911793023999264475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039103941195349332842983 10558655911793023999264475)
        ·
          refine ⟨15837983867689535998896713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558655911793023999264475 15837983867689535998896713)
          ·
            refine ⟨11878487900767151999172535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15837983867689535998896713 11878487900767151999172535)
            ·
              refine ⟨17817731851150727998758803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11878487900767151999172535 17817731851150727998758803)
              ·
                refine ⟨26726597776726091998138205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17817731851150727998758803 26726597776726091998138205)
                ·
                  refine ⟨10022474166272284499301827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26726597776726091998138205 10022474166272284499301827)
                  ·
                    refine ⟨15033711249408426748952741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10022474166272284499301827 15033711249408426748952741)
                    ·
                      refine ⟨2818820859264080015428639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15033711249408426748952741 2818820859264080015428639)
                      ·
                        rfl

theorem cell23_5489634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5489634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489634 prefixEnd_5489634 := by exact prefixLift 5489634
  have htrace : WordTrace (prefixWord ++ tailWord_5489634) baseStart_5489634 baseEnd_5489634 := by
    simpa [prefixWord, tailWord_5489634, baseEnd_5489634] using wordTrace_append hprefix tailTrace_5489634
  have hstable : (prefixWord ++ tailWord_5489634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489634).length < 2 ^ (prefixWord ++ tailWord_5489634).sum := by decide
  have hdescent : baseEnd_5489634 < baseStart_5489634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489654 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5489654 : Nat := 118140960795 + 5489654 * 2 ^ 59
def prefixEnd_5489654 : Nat := 4983230072969 + 3 ^ 40 * 5489654 * 2
def baseEnd_5489654 : Nat := 2818831128877169937178547

theorem tailTrace_5489654 : CollatzResearch.WordTrace tailWord_5489654 prefixEnd_5489654 2818831128877169937178547 := by
  unfold tailWord_5489654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514008153370536944092751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133482753635952394070322677 12514008153370536944092751)
  ·
    refine ⟨18771012230055805416139127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12514008153370536944092751 18771012230055805416139127)
    ·
      refine ⟨28156518345083708124208691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18771012230055805416139127 28156518345083708124208691)
      ·
        refine ⟨42234777517625562186313037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28156518345083708124208691 42234777517625562186313037)
        ·
          refine ⟨15838041569109585819867389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42234777517625562186313037 15838041569109585819867389)
          ·
            refine ⟨5939265588416094682450271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15838041569109585819867389 5939265588416094682450271)
            ·
              refine ⟨8908898382624142023675407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939265588416094682450271 8908898382624142023675407)
              ·
                refine ⟨13363347573936213035513111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8908898382624142023675407 13363347573936213035513111)
                ·
                  refine ⟨20045021360904319553269667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13363347573936213035513111 20045021360904319553269667)
                  ·
                    refine ⟨30067532041356479329904501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20045021360904319553269667 30067532041356479329904501)
                    ·
                      refine ⟨2818831128877169937178547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30067532041356479329904501 2818831128877169937178547)
                      ·
                        rfl

theorem cell23_5489654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5489654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489654 prefixEnd_5489654 := by exact prefixLift 5489654
  have htrace : WordTrace (prefixWord ++ tailWord_5489654) baseStart_5489654 baseEnd_5489654 := by
    simpa [prefixWord, tailWord_5489654, baseEnd_5489654] using wordTrace_append hprefix tailTrace_5489654
  have hstable : (prefixWord ++ tailWord_5489654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489654).length < 2 ^ (prefixWord ++ tailWord_5489654).sum := by decide
  have hdescent : baseEnd_5489654 < baseStart_5489654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489662 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5489662 : Nat := 118140960795 + 5489662 * 2 ^ 59
def prefixEnd_5489662 : Nat := 4983230072969 + 3 ^ 40 * 5489662 * 2
def baseEnd_5489662 : Nat := 2818835236722405905878511

theorem tailTrace_5489662 : CollatzResearch.WordTrace tailWord_5489662 prefixEnd_5489662 2818835236722405905878511 := by
  unfold tailWord_5489662
  simp only [CollatzResearch.WordTrace]
  refine ⟨25028052779737451058971905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133482948158599738981183493 25028052779737451058971905)
  ·
    refine ⟨18771039584803088294228929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25028052779737451058971905 18771039584803088294228929)
    ·
      refine ⟨14078279688602316220671697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18771039584803088294228929 14078279688602316220671697)
      ·
        refine ⟨10558709766451737165503773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14078279688602316220671697 10558709766451737165503773)
        ·
          refine ⟨3959516162419401437063915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10558709766451737165503773 3959516162419401437063915)
          ·
            refine ⟨5939274243629102155595873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959516162419401437063915 5939274243629102155595873)
            ·
              refine ⟨4454455682721826616696905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939274243629102155595873 4454455682721826616696905)
              ·
                refine ⟨3340841762041369962522679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454455682721826616696905 3340841762041369962522679)
                ·
                  refine ⟨5011262643062054943784019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340841762041369962522679 5011262643062054943784019)
                  ·
                    refine ⟨7516893964593082415676029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011262643062054943784019 7516893964593082415676029)
                    ·
                      refine ⟨2818835236722405905878511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516893964593082415676029 2818835236722405905878511)
                      ·
                        rfl

theorem cell23_5489662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5489662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489662 prefixEnd_5489662 := by exact prefixLift 5489662
  have htrace : WordTrace (prefixWord ++ tailWord_5489662) baseStart_5489662 baseEnd_5489662 := by
    simpa [prefixWord, tailWord_5489662, baseEnd_5489662] using wordTrace_append hprefix tailTrace_5489662
  have hstable : (prefixWord ++ tailWord_5489662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489662).length < 2 ^ (prefixWord ++ tailWord_5489662).sum := by decide
  have hdescent : baseEnd_5489662 < baseStart_5489662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489663 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_5489663 : Nat := 118140960795 + 5489663 * 2 ^ 59
def prefixEnd_5489663 : Nat := 4983230072969 + 3 ^ 40 * 5489663 * 2
def baseEnd_5489663 : Nat := 2818835750203060401966005

theorem tailTrace_5489663 : CollatzResearch.WordTrace tailWord_5489663 prefixEnd_5489663 2818835750203060401966005 := by
  unfold tailWord_5489663
  simp only [CollatzResearch.WordTrace]
  refine ⟨200224458710895985642561643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133482972473930657095041095 200224458710895985642561643)
  ·
    refine ⟨300336688066343978463842465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200224458710895985642561643 300336688066343978463842465)
    ·
      refine ⟨225252516049757983847881849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300336688066343978463842465 225252516049757983847881849)
      ·
        refine ⟨168939387037318487885911387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225252516049757983847881849 168939387037318487885911387)
        ·
          refine ⟨253409080555977731828867081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168939387037318487885911387 253409080555977731828867081)
          ·
            refine ⟨190056810416983298871650311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253409080555977731828867081 190056810416983298871650311)
            ·
              refine ⟨285085215625474948307475467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190056810416983298871650311 285085215625474948307475467)
              ·
                refine ⟨427627823438212422461213201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285085215625474948307475467 427627823438212422461213201)
                ·
                  refine ⟨320720867578659316845909901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427627823438212422461213201 320720867578659316845909901)
                  ·
                    refine ⟨120270325341997243817216213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320720867578659316845909901 120270325341997243817216213)
                    ·
                      refine ⟨2818835750203060401966005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120270325341997243817216213 2818835750203060401966005)
                      ·
                        rfl

theorem cell23_5489663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_5489663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489663 prefixEnd_5489663 := by exact prefixLift 5489663
  have htrace : WordTrace (prefixWord ++ tailWord_5489663) baseStart_5489663 baseEnd_5489663 := by
    simpa [prefixWord, tailWord_5489663, baseEnd_5489663] using wordTrace_append hprefix tailTrace_5489663
  have hstable : (prefixWord ++ tailWord_5489663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489663).length < 2 ^ (prefixWord ++ tailWord_5489663).sum := by decide
  have hdescent : baseEnd_5489663 < baseStart_5489663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489690 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5489690 : Nat := 118140960795 + 5489690 * 2 ^ 59
def prefixEnd_5489690 : Nat := 4983230072969 + 3 ^ 40 * 5489690 * 2
def baseEnd_5489690 : Nat := 2818849614180731796328381

theorem tailTrace_5489690 : CollatzResearch.WordTrace tailWord_5489690 prefixEnd_5489690 2818849614180731796328381 := by
  unfold tailWord_5489690
  simp only [CollatzResearch.WordTrace]
  refine ⟨50056360870449542313448631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133483628987865446169196349 50056360870449542313448631)
  ·
    refine ⟨75084541305674313470172947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50056360870449542313448631 75084541305674313470172947)
    ·
      refine ⟨112626811958511470205259421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75084541305674313470172947 112626811958511470205259421)
      ·
        refine ⟨42235054484441801326972283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112626811958511470205259421 42235054484441801326972283)
        ·
          refine ⟨63352581726662701990458425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42235054484441801326972283 63352581726662701990458425)
          ·
            refine ⟨47514436294997026492843819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63352581726662701990458425 47514436294997026492843819)
            ·
              refine ⟨71271654442495539739265729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47514436294997026492843819 71271654442495539739265729)
              ·
                refine ⟨53453740831871654804449297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71271654442495539739265729 53453740831871654804449297)
                ·
                  refine ⟨40090305623903741103336973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53453740831871654804449297 40090305623903741103336973)
                  ·
                    refine ⟨15033864608963902913751365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40090305623903741103336973 15033864608963902913751365)
                    ·
                      refine ⟨2818849614180731796328381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15033864608963902913751365 2818849614180731796328381)
                      ·
                        rfl

theorem cell23_5489690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5489690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489690 prefixEnd_5489690 := by exact prefixLift 5489690
  have htrace : WordTrace (prefixWord ++ tailWord_5489690) baseStart_5489690 baseEnd_5489690 := by
    simpa [prefixWord, tailWord_5489690, baseEnd_5489690] using wordTrace_append hprefix tailTrace_5489690
  have hstable : (prefixWord ++ tailWord_5489690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489690).length < 2 ^ (prefixWord ++ tailWord_5489690).sum := by decide
  have hdescent : baseEnd_5489690 < baseStart_5489690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489707 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 1, 4, 2]
def baseStart_5489707 : Nat := 118140960795 + 5489707 * 2 ^ 59
def prefixEnd_5489707 : Nat := 4983230072969 + 3 ^ 40 * 5489707 * 2
def baseEnd_5489707 : Nat := 2818858343351858229815803

theorem tailTrace_5489707 : CollatzResearch.WordTrace tailWord_5489707 prefixEnd_5489707 2818858343351858229815803 := by
  unfold tailWord_5489707
  simp only [CollatzResearch.WordTrace]
  refine ⟨200226063522736581157163375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133484042348491054104775583 200226063522736581157163375)
  ·
    refine ⟨300339095284104871735745063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200226063522736581157163375 300339095284104871735745063)
    ·
      refine ⟨450508642926157307603617595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300339095284104871735745063 450508642926157307603617595)
      ·
        refine ⟨675762964389235961405426393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450508642926157307603617595 675762964389235961405426393)
        ·
          refine ⟨506822223291926971054069795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675762964389235961405426393 506822223291926971054069795)
          ·
            refine ⟨760233334937890456581104693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506822223291926971054069795 760233334937890456581104693)
            ·
              refine ⟨71271875150427230304478565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 760233334937890456581104693 71271875150427230304478565)
              ·
                refine ⟨13363476590705105682089731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71271875150427230304478565 13363476590705105682089731)
                ·
                  refine ⟨20045214886057658523134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13363476590705105682089731 20045214886057658523134597)
                  ·
                    refine ⟨3758477791135810973087737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20045214886057658523134597 3758477791135810973087737)
                    ·
                      refine ⟨2818858343351858229815803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758477791135810973087737 2818858343351858229815803)
                      ·
                        rfl

theorem cell23_5489707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4, 2].length) (baseStart_5489707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489707 prefixEnd_5489707 := by exact prefixLift 5489707
  have htrace : WordTrace (prefixWord ++ tailWord_5489707) baseStart_5489707 baseEnd_5489707 := by
    simpa [prefixWord, tailWord_5489707, baseEnd_5489707] using wordTrace_append hprefix tailTrace_5489707
  have hstable : (prefixWord ++ tailWord_5489707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489707).length < 2 ^ (prefixWord ++ tailWord_5489707).sum := by decide
  have hdescent : baseEnd_5489707 < baseStart_5489707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489718 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5489718 : Nat := 118140960795 + 5489718 * 2 ^ 59
def prefixEnd_5489718 : Nat := 4983230072969 + 3 ^ 40 * 5489718 * 2
def baseEnd_5489718 : Nat := 2818863991639057686778253

theorem tailTrace_5489718 : CollatzResearch.WordTrace tailWord_5489718 prefixEnd_5489718 2818863991639057686778253 := by
  unfold tailWord_5489718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514154045356045627238363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133484309817131153357209205 12514154045356045627238363)
  ·
    refine ⟨18771231068034068440857545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12514154045356045627238363 18771231068034068440857545)
    ·
      refine ⟨14078423301025551330643159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18771231068034068440857545 14078423301025551330643159)
      ·
        refine ⟨21117634951538326995964739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14078423301025551330643159 21117634951538326995964739)
        ·
          refine ⟨31676452427307490493947109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21117634951538326995964739 31676452427307490493947109)
          ·
            refine ⟨5939334830120154467615083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31676452427307490493947109 5939334830120154467615083)
            ·
              refine ⟨8909002245180231701422625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939334830120154467615083 8909002245180231701422625)
              ·
                refine ⟨6681751683885173776066969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909002245180231701422625 6681751683885173776066969)
                ·
                  refine ⟨5011313762913880332050227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6681751683885173776066969 5011313762913880332050227)
                  ·
                    refine ⟨7516970644370820498075341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011313762913880332050227 7516970644370820498075341)
                    ·
                      refine ⟨2818863991639057686778253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7516970644370820498075341 2818863991639057686778253)
                      ·
                        rfl

theorem cell23_5489718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5489718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489718 prefixEnd_5489718 := by exact prefixLift 5489718
  have htrace : WordTrace (prefixWord ++ tailWord_5489718) baseStart_5489718 baseEnd_5489718 := by
    simpa [prefixWord, tailWord_5489718, baseEnd_5489718] using wordTrace_append hprefix tailTrace_5489718
  have hstable : (prefixWord ++ tailWord_5489718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489718).length < 2 ^ (prefixWord ++ tailWord_5489718).sum := by decide
  have hdescent : baseEnd_5489718 < baseStart_5489718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489734 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5489734 : Nat := 118140960795 + 5489734 * 2 ^ 59
def prefixEnd_5489734 : Nat := 4983230072969 + 3 ^ 40 * 5489734 * 2
def baseEnd_5489734 : Nat := 939624069109843208059393

theorem tailTrace_5489734 : CollatzResearch.WordTrace tailWord_5489734 prefixEnd_5489734 939624069109843208059393 := by
  unfold tailWord_5489734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6257095259176211399012383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133484698862425843178930837 6257095259176211399012383)
  ·
    refine ⟨9385642888764317098518575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6257095259176211399012383 9385642888764317098518575)
    ·
      refine ⟨14078464333146475647777863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9385642888764317098518575 14078464333146475647777863)
      ·
        refine ⟨21117696499719713471666795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14078464333146475647777863 21117696499719713471666795)
        ·
          refine ⟨31676544749579570207500193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21117696499719713471666795 31676544749579570207500193)
          ·
            refine ⟨23757408562184677655625145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31676544749579570207500193 23757408562184677655625145)
            ·
              refine ⟨17818056421638508241718859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23757408562184677655625145 17818056421638508241718859)
              ·
                refine ⟨26727084632457762362578289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17818056421638508241718859 26727084632457762362578289)
                ·
                  refine ⟨20045313474343321771933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26727084632457762362578289 20045313474343321771933717)
                  ·
                    refine ⟨939624069109843208059393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20045313474343321771933717 939624069109843208059393)
                    ·
                      rfl

theorem cell23_5489734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5489734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489734 prefixEnd_5489734 := by exact prefixLift 5489734
  have htrace : WordTrace (prefixWord ++ tailWord_5489734) baseStart_5489734 baseEnd_5489734 := by
    simpa [prefixWord, tailWord_5489734, baseEnd_5489734] using wordTrace_append hprefix tailTrace_5489734
  have hstable : (prefixWord ++ tailWord_5489734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489734).length < 2 ^ (prefixWord ++ tailWord_5489734).sum := by decide
  have hdescent : baseEnd_5489734 < baseStart_5489734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489741 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_5489741 : Nat := 118140960795 + 5489741 * 2 ^ 59
def prefixEnd_5489741 : Nat := 4983230072969 + 3 ^ 40 * 5489741 * 2
def baseEnd_5489741 : Nat := 2818875801694111096790647

theorem tailTrace_5489741 : CollatzResearch.WordTrace tailWord_5489741 prefixEnd_5489741 2818875801694111096790647 := by
  unfold tailWord_5489741
  simp only [CollatzResearch.WordTrace]
  refine ⟨200227303604613404963901077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133484869069742269975934051 200227303604613404963901077)
  ·
    refine ⟨9385654856466253357682863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200227303604613404963901077 9385654856466253357682863)
    ·
      refine ⟨14078482284699380036524295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9385654856466253357682863 14078482284699380036524295)
      ·
        refine ⟨21117723427049070054786443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14078482284699380036524295 21117723427049070054786443)
        ·
          refine ⟨31676585140573605082179665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21117723427049070054786443 31676585140573605082179665)
          ·
            refine ⟨23757438855430203811634749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31676585140573605082179665 23757438855430203811634749)
            ·
              refine ⟨8909039570786326429363031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23757438855430203811634749 8909039570786326429363031)
              ·
                refine ⟨13363559356179489644044547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909039570786326429363031 13363559356179489644044547)
                ·
                  refine ⟨20045339034269234466066821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13363559356179489644044547 20045339034269234466066821)
                  ·
                    refine ⟨3758501068925481462387529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20045339034269234466066821 3758501068925481462387529)
                    ·
                      refine ⟨2818875801694111096790647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758501068925481462387529 2818875801694111096790647)
                      ·
                        rfl

theorem cell23_5489741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_5489741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489741 prefixEnd_5489741 := by exact prefixLift 5489741
  have htrace : WordTrace (prefixWord ++ tailWord_5489741) baseStart_5489741 baseEnd_5489741 := by
    simpa [prefixWord, tailWord_5489741, baseEnd_5489741] using wordTrace_append hprefix tailTrace_5489741
  have hstable : (prefixWord ++ tailWord_5489741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489741).length < 2 ^ (prefixWord ++ tailWord_5489741).sum := by decide
  have hdescent : baseEnd_5489741 < baseStart_5489741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489760 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_5489760 : Nat := 118140960795 + 5489760 * 2 ^ 59
def prefixEnd_5489760 : Nat := 4983230072969 + 3 ^ 40 * 5489760 * 2
def baseEnd_5489760 : Nat := 939628519275515507484353

theorem tailTrace_5489760 : CollatzResearch.WordTrace tailWord_5489760 prefixEnd_5489760 939628519275515507484353 := by
  unfold tailWord_5489760
  simp only [CollatzResearch.WordTrace]
  refine ⟨100113998295772285604421367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133485331061029714139228489 100113998295772285604421367)
  ·
    refine ⟨150170997443658428406632051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100113998295772285604421367 150170997443658428406632051)
    ·
      refine ⟨225256496165487642609948077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150170997443658428406632051 225256496165487642609948077)
      ·
        refine ⟨84471186062057865978730529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225256496165487642609948077 84471186062057865978730529)
        ·
          refine ⟨63353389546543399484047897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84471186062057865978730529 63353389546543399484047897)
          ·
            refine ⟨47515042159907549613035923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63353389546543399484047897 47515042159907549613035923)
            ·
              refine ⟨71272563239861324419553885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47515042159907549613035923 71272563239861324419553885)
              ·
                refine ⟨26727211214947996657332707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71272563239861324419553885 26727211214947996657332707)
                ·
                  refine ⟨40090816822421994985999061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26727211214947996657332707 40090816822421994985999061)
                  ·
                    refine ⟨939628519275515507484353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40090816822421994985999061 939628519275515507484353)
                    ·
                      rfl

theorem cell23_5489760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_5489760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489760 prefixEnd_5489760 := by exact prefixLift 5489760
  have htrace : WordTrace (prefixWord ++ tailWord_5489760) baseStart_5489760 baseEnd_5489760 := by
    simpa [prefixWord, tailWord_5489760, baseEnd_5489760] using wordTrace_append hprefix tailTrace_5489760
  have hstable : (prefixWord ++ tailWord_5489760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489760).length < 2 ^ (prefixWord ++ tailWord_5489760).sum := by decide
  have hdescent : baseEnd_5489760 < baseStart_5489760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489781 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 7]
def baseStart_5489781 : Nat := 118140960795 + 5489781 * 2 ^ 59
def prefixEnd_5489781 : Nat := 4983230072969 + 3 ^ 40 * 5489781 * 2
def baseEnd_5489781 : Nat := 313210704546698993365607

theorem tailTrace_5489781 : CollatzResearch.WordTrace tailWord_5489781 prefixEnd_5489781 313210704546698993365607 := by
  unfold tailWord_5489781
  simp only [CollatzResearch.WordTrace]
  refine ⟨200228762524468491795357197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133485841682978994530238131 200228762524468491795357197)
  ·
    refine ⟨75085785946675684423258949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200228762524468491795357197 75085785946675684423258949)
    ·
      refine ⟨14078584865001690829361053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75085785946675684423258949 14078584865001690829361053)
      ·
        refine ⟨5279469324375634061010395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14078584865001690829361053 5279469324375634061010395)
        ·
          refine ⟨7919203986563451091515593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279469324375634061010395 7919203986563451091515593)
          ·
            refine ⟨5939402989922588318636695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919203986563451091515593 5939402989922588318636695)
            ·
              refine ⟨8909104484883882477955043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939402989922588318636695 8909104484883882477955043)
              ·
                refine ⟨13363656727325823716932565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909104484883882477955043 13363656727325823716932565)
                ·
                  refine ⟨313210704546698993365607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13363656727325823716932565 313210704546698993365607)
                  ·
                    rfl

theorem cell23_5489781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_5489781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489781 prefixEnd_5489781 := by exact prefixLift 5489781
  have htrace : WordTrace (prefixWord ++ tailWord_5489781) baseStart_5489781 baseEnd_5489781 := by
    simpa [prefixWord, tailWord_5489781, baseEnd_5489781] using wordTrace_append hprefix tailTrace_5489781
  have hstable : (prefixWord ++ tailWord_5489781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489781).length < 2 ^ (prefixWord ++ tailWord_5489781).sum := by decide
  have hdescent : baseEnd_5489781 < baseStart_5489781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_5489840 : Nat := 118140960795 + 5489840 * 2 ^ 59
def prefixEnd_5489840 : Nat := 4983230072969 + 3 ^ 40 * 5489840 * 2
def baseEnd_5489840 : Nat := 2818926636278906209452691

theorem tailTrace_5489840 : CollatzResearch.WordTrace tailWord_5489840 prefixEnd_5489840 2818926636278906209452691 := by
  unfold tailWord_5489840
  simp only [CollatzResearch.WordTrace]
  refine ⟨100115457215627372435877487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133487276287503163247836649 100115457215627372435877487)
  ·
    refine ⟨150173185823441058653816231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100115457215627372435877487 150173185823441058653816231)
    ·
      refine ⟨225259778735161587980724347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150173185823441058653816231 225259778735161587980724347)
      ·
        refine ⟨337889668102742381971086521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225259778735161587980724347 337889668102742381971086521)
        ·
          refine ⟨253417251077056786478314891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337889668102742381971086521 253417251077056786478314891)
          ·
            refine ⟨380125876615585179717472337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253417251077056786478314891 380125876615585179717472337)
            ·
              refine ⟨285094407461688884788104253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380125876615585179717472337 285094407461688884788104253)
              ·
                refine ⟨106910402798133331795539095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285094407461688884788104253 106910402798133331795539095)
                ·
                  refine ⟨160365604197199997693308643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106910402798133331795539095 160365604197199997693308643)
                  ·
                    refine ⟨240548406295799996539962965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160365604197199997693308643 240548406295799996539962965)
                    ·
                      refine ⟨2818926636278906209452691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 240548406295799996539962965 2818926636278906209452691)
                      ·
                        rfl

theorem cell23_5489840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_5489840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489840 prefixEnd_5489840 := by exact prefixLift 5489840
  have htrace : WordTrace (prefixWord ++ tailWord_5489840) baseStart_5489840 baseEnd_5489840 := by
    simpa [prefixWord, tailWord_5489840, baseEnd_5489840] using wordTrace_append hprefix tailTrace_5489840
  have hstable : (prefixWord ++ tailWord_5489840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489840).length < 2 ^ (prefixWord ++ tailWord_5489840).sum := by decide
  have hdescent : baseEnd_5489840 < baseStart_5489840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489854 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_5489854 : Nat := 118140960795 + 5489854 * 2 ^ 59
def prefixEnd_5489854 : Nat := 4983230072969 + 3 ^ 40 * 5489854 * 2
def baseEnd_5489854 : Nat := 313214869445341017186403

theorem tailTrace_5489854 : CollatzResearch.WordTrace tailWord_5489854 prefixEnd_5489854 313214869445341017186403 := by
  unfold tailWord_5489854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25028928131650503157845577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133487616702136016841843077 25028928131650503157845577)
  ·
    refine ⟨18771696098737877368384183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25028928131650503157845577 18771696098737877368384183)
    ·
      refine ⟨28157544148106816052576275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18771696098737877368384183 28157544148106816052576275)
      ·
        refine ⟨42236316222160224078864413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28157544148106816052576275 42236316222160224078864413)
        ·
          refine ⟨15838618583310084029574155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42236316222160224078864413 15838618583310084029574155)
          ·
            refine ⟨23757927874965126044361233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15838618583310084029574155 23757927874965126044361233)
            ·
              refine ⟨17818445906223844533270925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23757927874965126044361233 17818445906223844533270925)
              ·
                refine ⟨6681917214833941699976597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17818445906223844533270925 6681917214833941699976597)
                ·
                  refine ⟨313214869445341017186403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6681917214833941699976597 313214869445341017186403)
                  ·
                    rfl

theorem cell23_5489854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_5489854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489854 prefixEnd_5489854 := by exact prefixLift 5489854
  have htrace : WordTrace (prefixWord ++ tailWord_5489854) baseStart_5489854 baseEnd_5489854 := by
    simpa [prefixWord, tailWord_5489854, baseEnd_5489854] using wordTrace_append hprefix tailTrace_5489854
  have hstable : (prefixWord ++ tailWord_5489854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489854).length < 2 ^ (prefixWord ++ tailWord_5489854).sum := by decide
  have hdescent : baseEnd_5489854 < baseStart_5489854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489862 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5489862 : Nat := 118140960795 + 5489862 * 2 ^ 59
def prefixEnd_5489862 : Nat := 4983230072969 + 3 ^ 40 * 5489862 * 2
def baseEnd_5489862 : Nat := 939645977617768374459197

theorem tailTrace_5489862 : CollatzResearch.WordTrace tailWord_5489862 prefixEnd_5489862 939645977617768374459197 := by
  unfold tailWord_5489862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6257241151161720082157995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133487811224783361752703893 6257241151161720082157995)
  ·
    refine ⟨9385861726742580123236993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6257241151161720082157995 9385861726742580123236993)
    ·
      refine ⟨7039396295056935092427745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9385861726742580123236993 7039396295056935092427745)
      ·
        refine ⟨5279547221292701319320809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7039396295056935092427745 5279547221292701319320809)
        ·
          refine ⟨3959660415969525989490607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5279547221292701319320809 3959660415969525989490607)
          ·
            refine ⟨5939490623954288984235911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959660415969525989490607 5939490623954288984235911)
            ·
              refine ⟨8909235935931433476353867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939490623954288984235911 8909235935931433476353867)
              ·
                refine ⟨13363853903897150214530801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909235935931433476353867 13363853903897150214530801)
                ·
                  refine ⟨10022890427922862660898101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13363853903897150214530801 10022890427922862660898101)
                  ·
                    refine ⟨939645977617768374459197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10022890427922862660898101 939645977617768374459197)
                    ·
                      rfl

theorem cell23_5489862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5489862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489862 prefixEnd_5489862 := by exact prefixLift 5489862
  have htrace : WordTrace (prefixWord ++ tailWord_5489862) baseStart_5489862 baseEnd_5489862 := by
    simpa [prefixWord, tailWord_5489862, baseEnd_5489862] using wordTrace_append hprefix tailTrace_5489862
  have hstable : (prefixWord ++ tailWord_5489862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489862).length < 2 ^ (prefixWord ++ tailWord_5489862).sum := by decide
  have hdescent : baseEnd_5489862 < baseStart_5489862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489864 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_5489864 : Nat := 118140960795 + 5489864 * 2 ^ 59
def prefixEnd_5489864 : Nat := 4983230072969 + 3 ^ 40 * 5489864 * 2
def baseEnd_5489864 : Nat := 2818938959814614115552581

theorem tailTrace_5489864 : CollatzResearch.WordTrace tailWord_5489864 prefixEnd_5489864 2818938959814614115552581 := by
  unfold tailWord_5489864
  simp only [CollatzResearch.WordTrace]
  refine ⟨100115894891583898485314323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133487859855445197980419097 100115894891583898485314323)
  ·
    refine ⟨150173842337375847727971485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100115894891583898485314323 150173842337375847727971485)
    ·
      refine ⟨56315190876515942897989307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150173842337375847727971485 56315190876515942897989307)
      ·
        refine ⟨84472786314773914346983961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56315190876515942897989307 84472786314773914346983961)
        ·
          refine ⟨63354589736080435760237971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84472786314773914346983961 63354589736080435760237971)
          ·
            refine ⟨95031884604120653640356957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63354589736080435760237971 95031884604120653640356957)
            ·
              refine ⟨35636956726545245115133859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95031884604120653640356957 35636956726545245115133859)
              ·
                refine ⟨53455435089817867672700789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35636956726545245115133859 53455435089817867672700789)
                ·
                  refine ⟨5011447039670425094315699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53455435089817867672700789 5011447039670425094315699)
                  ·
                    refine ⟨7517170559505637641473549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011447039670425094315699 7517170559505637641473549)
                    ·
                      refine ⟨2818938959814614115552581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7517170559505637641473549 2818938959814614115552581)
                      ·
                        rfl

theorem cell23_5489864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_5489864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489864 prefixEnd_5489864 := by exact prefixLift 5489864
  have htrace : WordTrace (prefixWord ++ tailWord_5489864) baseStart_5489864 baseEnd_5489864 := by
    simpa [prefixWord, tailWord_5489864, baseEnd_5489864] using wordTrace_append hprefix tailTrace_5489864
  have hstable : (prefixWord ++ tailWord_5489864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489864).length < 2 ^ (prefixWord ++ tailWord_5489864).sum := by decide
  have hdescent : baseEnd_5489864 < baseStart_5489864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489898 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_5489898 : Nat := 118140960795 + 5489898 * 2 ^ 59
def prefixEnd_5489898 : Nat := 4983230072969 + 3 ^ 40 * 5489898 * 2
def baseEnd_5489898 : Nat := 2818956418156866982527425

theorem tailTrace_5489898 : CollatzResearch.WordTrace tailWord_5489898 prefixEnd_5489898 2818956418156866982527425 := by
  unfold tailWord_5489898
  simp only [CollatzResearch.WordTrace]
  refine ⟨50058257466261155194341587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133488686576696413851577565 50058257466261155194341587)
  ·
    refine ⟨75087386199391732791512381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50058257466261155194341587 75087386199391732791512381)
    ·
      refine ⟨28157769824771899796817143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75087386199391732791512381 28157769824771899796817143)
      ·
        refine ⟨42236654737157849695225715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28157769824771899796817143 42236654737157849695225715)
        ·
          refine ⟨63354982105736774542838573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42236654737157849695225715 63354982105736774542838573)
          ·
            refine ⟨23758118289651290453564465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63354982105736774542838573 23758118289651290453564465)
            ·
              refine ⟨17818588717238467840173349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23758118289651290453564465 17818588717238467840173349)
              ·
                refine ⟨3340985384482212720032503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17818588717238467840173349 3340985384482212720032503)
                ·
                  refine ⟨5011478076723319080048755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340985384482212720032503 5011478076723319080048755)
                  ·
                    refine ⟨7517217115084978620073133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011478076723319080048755 7517217115084978620073133)
                    ·
                      refine ⟨2818956418156866982527425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7517217115084978620073133 2818956418156866982527425)
                      ·
                        rfl

theorem cell23_5489898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_5489898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489898 prefixEnd_5489898 := by exact prefixLift 5489898
  have htrace : WordTrace (prefixWord ++ tailWord_5489898) baseStart_5489898 baseEnd_5489898 := by
    simpa [prefixWord, tailWord_5489898, baseEnd_5489898] using wordTrace_append hprefix tailTrace_5489898
  have hstable : (prefixWord ++ tailWord_5489898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489898).length < 2 ^ (prefixWord ++ tailWord_5489898).sum := by decide
  have hdescent : baseEnd_5489898 < baseStart_5489898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489907 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_5489907 : Nat := 118140960795 + 5489907 * 2 ^ 59
def prefixEnd_5489907 : Nat := 4983230072969 + 3 ^ 40 * 5489907 * 2
def baseEnd_5489907 : Nat := 2818961039482757447314883

theorem tailTrace_5489907 : CollatzResearch.WordTrace tailWord_5489907 prefixEnd_5489907 2818961039482757447314883 := by
  unfold tailWord_5489907
  simp only [CollatzResearch.WordTrace]
  refine ⟨200233358122012015314443975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133488905414674676876295983 200233358122012015314443975)
  ·
    refine ⟨300350037183018022971665963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200233358122012015314443975 300350037183018022971665963)
    ·
      refine ⟨450525055774527034457498945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300350037183018022971665963 450525055774527034457498945)
      ·
        refine ⟨337893791830895275843124209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450525055774527034457498945 337893791830895275843124209)
        ·
          refine ⟨253420343873171456882343157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337893791830895275843124209 253420343873171456882343157)
          ·
            refine ⟨23758157238109824082719671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 253420343873171456882343157 23758157238109824082719671)
            ·
              refine ⟨35637235857164736124079507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23758157238109824082719671 35637235857164736124079507)
              ·
                refine ⟨53455853785747104186119261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35637235857164736124079507 53455853785747104186119261)
                ·
                  refine ⟨20045945169655164069794723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53455853785747104186119261 20045945169655164069794723)
                  ·
                    refine ⟨30068917754482746104692085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20045945169655164069794723 30068917754482746104692085)
                    ·
                      refine ⟨2818961039482757447314883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30068917754482746104692085 2818961039482757447314883)
                      ·
                        rfl

theorem cell23_5489907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_5489907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489907 prefixEnd_5489907 := by exact prefixLift 5489907
  have htrace : WordTrace (prefixWord ++ tailWord_5489907) baseStart_5489907 baseEnd_5489907 := by
    simpa [prefixWord, tailWord_5489907, baseEnd_5489907] using wordTrace_append hprefix tailTrace_5489907
  have hstable : (prefixWord ++ tailWord_5489907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489907).length < 2 ^ (prefixWord ++ tailWord_5489907).sum := by decide
  have hdescent : baseEnd_5489907 < baseStart_5489907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489921 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_5489921 : Nat := 118140960795 + 5489921 * 2 ^ 59
def prefixEnd_5489921 : Nat := 4983230072969 + 3 ^ 40 * 5489921 * 2
def baseEnd_5489921 : Nat := 2818968228211920392539819

theorem tailTrace_5489921 : CollatzResearch.WordTrace tailWord_5489921 prefixEnd_5489921 2818968228211920392539819 := by
  unfold tailWord_5489921
  simp only [CollatzResearch.WordTrace]
  refine ⟨200233868743961295705453617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133489245829307530470302411 200233868743961295705453617)
  ·
    refine ⟨150175401557970971779090213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200233868743961295705453617 150175401557970971779090213)
    ·
      refine ⟨28157887792119557208579415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150175401557970971779090213 28157887792119557208579415)
      ·
        refine ⟨42236831688179335812869123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28157887792119557208579415 42236831688179335812869123)
        ·
          refine ⟨63355247532269003719303685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42236831688179335812869123 63355247532269003719303685)
          ·
            refine ⟨11879108912300438197369441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63355247532269003719303685 11879108912300438197369441)
            ·
              refine ⟨8909331684225328648027081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11879108912300438197369441 8909331684225328648027081)
              ·
                refine ⟨6681998763168996486020311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909331684225328648027081 6681998763168996486020311)
                ·
                  refine ⟨10022998144753494729030467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6681998763168996486020311 10022998144753494729030467)
                  ·
                    refine ⟨15034497217130242093545701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10022998144753494729030467 15034497217130242093545701)
                    ·
                      refine ⟨2818968228211920392539819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15034497217130242093545701 2818968228211920392539819)
                      ·
                        rfl

theorem cell23_5489921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_5489921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489921 prefixEnd_5489921 := by exact prefixLift 5489921
  have htrace : WordTrace (prefixWord ++ tailWord_5489921) baseStart_5489921 baseEnd_5489921 := by
    simpa [prefixWord, tailWord_5489921, baseEnd_5489921] using wordTrace_append hprefix tailTrace_5489921
  have hstable : (prefixWord ++ tailWord_5489921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489921).length < 2 ^ (prefixWord ++ tailWord_5489921).sum := by decide
  have hdescent : baseEnd_5489921 < baseStart_5489921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489964 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_5489964 : Nat := 118140960795 + 5489964 * 2 ^ 59
def prefixEnd_5489964 : Nat := 4983230072969 + 3 ^ 40 * 5489964 * 2
def baseEnd_5489964 : Nat := 2818990307880063724302121

theorem tailTrace_5489964 : CollatzResearch.WordTrace tailWord_5489964 prefixEnd_5489964 2818990307880063724302121 := by
  unfold tailWord_5489964
  simp only [CollatzResearch.WordTrace]
  refine ⟨100117718541402757024634473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133490291388537009366179297 100117718541402757024634473)
  ·
    refine ⟨75088288906052067768475855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100117718541402757024634473 75088288906052067768475855)
    ·
      refine ⟨112632433359078101652713783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75088288906052067768475855 112632433359078101652713783)
      ·
        refine ⟨168948650038617152479070675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112632433359078101652713783 168948650038617152479070675)
        ·
          refine ⟨253422975057925728718606013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168948650038617152479070675 253422975057925728718606013)
          ·
            refine ⟨95033615646722148269477255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253422975057925728718606013 95033615646722148269477255)
            ·
              refine ⟨142550423470083222404215883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95033615646722148269477255 142550423470083222404215883)
              ·
                refine ⟨213825635205124833606323825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142550423470083222404215883 213825635205124833606323825)
                ·
                  refine ⟨160369226403843625204742869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213825635205124833606323825 160369226403843625204742869)
                  ·
                    refine ⟨3758653743840084965736161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 160369226403843625204742869 3758653743840084965736161)
                    ·
                      refine ⟨2818990307880063724302121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758653743840084965736161 2818990307880063724302121)
                      ·
                        rfl

theorem cell23_5489964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_5489964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489964 prefixEnd_5489964 := by exact prefixLift 5489964
  have htrace : WordTrace (prefixWord ++ tailWord_5489964) baseStart_5489964 baseEnd_5489964 := by
    simpa [prefixWord, tailWord_5489964, baseEnd_5489964] using wordTrace_append hprefix tailTrace_5489964
  have hstable : (prefixWord ++ tailWord_5489964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489964).length < 2 ^ (prefixWord ++ tailWord_5489964).sum := by decide
  have hdescent : baseEnd_5489964 < baseStart_5489964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489965 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5489965 : Nat := 118140960795 + 5489965 * 2 ^ 59
def prefixEnd_5489965 : Nat := 4983230072969 + 3 ^ 40 * 5489965 * 2
def baseEnd_5489965 : Nat := 939663607120239406796539

theorem tailTrace_5489965 : CollatzResearch.WordTrace tailWord_5489965 prefixEnd_5489965 939663607120239406796539 := by
  unfold tailWord_5489965
  simp only [CollatzResearch.WordTrace]
  refine ⟨200235473555801891220055349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133490315703867927480036899 200235473555801891220055349)
  ·
    refine ⟨18772075645856427301880189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200235473555801891220055349 18772075645856427301880189)
    ·
      refine ⟨7039528367196160238205071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18772075645856427301880189 7039528367196160238205071)
      ·
        refine ⟨10559292550794240357307607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039528367196160238205071 10559292550794240357307607)
        ·
          refine ⟨15838938826191360535961411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10559292550794240357307607 15838938826191360535961411)
          ·
            refine ⟨23758408239287040803942117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15838938826191360535961411 23758408239287040803942117)
            ·
              refine ⟨4454701544866320150739147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23758408239287040803942117 4454701544866320150739147)
              ·
                refine ⟨6682052317299480226108721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454701544866320150739147 6682052317299480226108721)
                ·
                  refine ⟨5011539237974610169581541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682052317299480226108721 5011539237974610169581541)
                  ·
                    refine ⟨939663607120239406796539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011539237974610169581541 939663607120239406796539)
                    ·
                      rfl

theorem cell23_5489965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5489965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489965 prefixEnd_5489965 := by exact prefixLift 5489965
  have htrace : WordTrace (prefixWord ++ tailWord_5489965) baseStart_5489965 baseEnd_5489965 := by
    simpa [prefixWord, tailWord_5489965, baseEnd_5489965] using wordTrace_append hprefix tailTrace_5489965
  have hstable : (prefixWord ++ tailWord_5489965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489965).length < 2 ^ (prefixWord ++ tailWord_5489965).sum := by decide
  have hdescent : baseEnd_5489965 < baseStart_5489965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489987 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 4, 6]
def baseStart_5489987 : Nat := 118140960795 + 5489987 * 2 ^ 59
def prefixEnd_5489987 : Nat := 4983230072969 + 3 ^ 40 * 5489987 * 2
def baseEnd_5489987 : Nat := 939667372645039044771505

theorem tailTrace_5489987 : CollatzResearch.WordTrace tailWord_5489987 prefixEnd_5489987 939667372645039044771505 := by
  unfold tailWord_5489987
  simp only [CollatzResearch.WordTrace]
  refine ⟨200236275961722188977356215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133490850641148125984904143 200236275961722188977356215)
  ·
    refine ⟨300354413942583283466034323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200236275961722188977356215 300354413942583283466034323)
    ·
      refine ⟨450531620913874925199051485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300354413942583283466034323 450531620913874925199051485)
      ·
        refine ⟨168949357842703096949644307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450531620913874925199051485 168949357842703096949644307)
        ·
          refine ⟨253424036764054645424466461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168949357842703096949644307 253424036764054645424466461)
          ·
            refine ⟨95034013786520492034174923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253424036764054645424466461 95034013786520492034174923)
            ·
              refine ⟨142551020679780738051262385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95034013786520492034174923 142551020679780738051262385)
              ·
                refine ⟨106913265509835553538446789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142551020679780738051262385 106913265509835553538446789)
                ·
                  refine ⟨20046237283094166288458773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106913265509835553538446789 20046237283094166288458773)
                  ·
                    refine ⟨939667372645039044771505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20046237283094166288458773 939667372645039044771505)
                    ·
                      rfl

theorem cell23_5489987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_5489987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489987 prefixEnd_5489987 := by exact prefixLift 5489987
  have htrace : WordTrace (prefixWord ++ tailWord_5489987) baseStart_5489987 baseEnd_5489987 := by
    simpa [prefixWord, tailWord_5489987, baseEnd_5489987] using wordTrace_append hprefix tailTrace_5489987
  have hstable : (prefixWord ++ tailWord_5489987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489987).length < 2 ^ (prefixWord ++ tailWord_5489987).sum := by decide
  have hdescent : baseEnd_5489987 < baseStart_5489987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5489988 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5489988 : Nat := 118140960795 + 5489988 * 2 ^ 59
def prefixEnd_5489988 : Nat := 4983230072969 + 3 ^ 40 * 5489988 * 2
def baseEnd_5489988 : Nat := 2819002631415771630402011

theorem tailTrace_5489988 : CollatzResearch.WordTrace tailWord_5489988 prefixEnd_5489988 2819002631415771630402011 := by
  unfold tailWord_5489988
  simp only [CollatzResearch.WordTrace]
  refine ⟨100118156217359283074071309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133490874956479044098761745 100118156217359283074071309)
  ·
    refine ⟨37544308581509731152776741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100118156217359283074071309 37544308581509731152776741)
    ·
      refine ⟨7039557859033074591145639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37544308581509731152776741 7039557859033074591145639)
      ·
        refine ⟨10559336788549611886718459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039557859033074591145639 10559336788549611886718459)
        ·
          refine ⟨15839005182824417830077689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10559336788549611886718459 15839005182824417830077689)
          ·
            refine ⟨11879253887118313372558267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15839005182824417830077689 11879253887118313372558267)
            ·
              refine ⟨17818880830677470058837401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11879253887118313372558267 17818880830677470058837401)
              ·
                refine ⟨13364160623008102544128051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17818880830677470058837401 13364160623008102544128051)
                ·
                  refine ⟨20046240934512153816192077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13364160623008102544128051 20046240934512153816192077)
                  ·
                    refine ⟨7517340350442057681072029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20046240934512153816192077 7517340350442057681072029)
                    ·
                      refine ⟨2819002631415771630402011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7517340350442057681072029 2819002631415771630402011)
                      ·
                        rfl

theorem cell23_5489988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5489988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5489988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5489988 prefixEnd_5489988 := by exact prefixLift 5489988
  have htrace : WordTrace (prefixWord ++ tailWord_5489988) baseStart_5489988 baseEnd_5489988 := by
    simpa [prefixWord, tailWord_5489988, baseEnd_5489988] using wordTrace_append hprefix tailTrace_5489988
  have hstable : (prefixWord ++ tailWord_5489988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5489988).length < 2 ^ (prefixWord ++ tailWord_5489988).sum := by decide
  have hdescent : baseEnd_5489988 < baseStart_5489988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5489988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490004 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_5490004 : Nat := 118140960795 + 5490004 * 2 ^ 59
def prefixEnd_5490004 : Nat := 4983230072969 + 3 ^ 40 * 5490004 * 2
def baseEnd_5490004 : Nat := 939670282368747855933979

theorem tailTrace_5490004 : CollatzResearch.WordTrace tailWord_5490004 prefixEnd_5490004 939670282368747855933979 := by
  unfold tailWord_5490004
  simp only [CollatzResearch.WordTrace]
  refine ⟨100118448001330300440362533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133491264001773733920483377 100118448001330300440362533)
  ·
    refine ⟨18772209000249431332567975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100118448001330300440362533 18772209000249431332567975)
    ·
      refine ⟨28158313500374146998851963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18772209000249431332567975 28158313500374146998851963)
      ·
        refine ⟨42237470250561220498277945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28158313500374146998851963 42237470250561220498277945)
        ·
          refine ⟨31678102687920915373708459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42237470250561220498277945 31678102687920915373708459)
          ·
            refine ⟨47517154031881373060562689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31678102687920915373708459 47517154031881373060562689)
            ·
              refine ⟨35637865523911029795422017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47517154031881373060562689 35637865523911029795422017)
              ·
                refine ⟨26728399142933272346566513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35637865523911029795422017 26728399142933272346566513)
                ·
                  refine ⟨20046299357199954259924885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26728399142933272346566513 20046299357199954259924885)
                  ·
                    refine ⟨939670282368747855933979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20046299357199954259924885 939670282368747855933979)
                    ·
                      rfl

theorem cell23_5490004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_5490004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490004 prefixEnd_5490004 := by exact prefixLift 5490004
  have htrace : WordTrace (prefixWord ++ tailWord_5490004) baseStart_5490004 baseEnd_5490004 := by
    simpa [prefixWord, tailWord_5490004, baseEnd_5490004] using wordTrace_append hprefix tailTrace_5490004
  have hstable : (prefixWord ++ tailWord_5490004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490004).length < 2 ^ (prefixWord ++ tailWord_5490004).sum := by decide
  have hdescent : baseEnd_5490004 < baseStart_5490004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490017 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 11]
def baseStart_5490017 : Nat := 118140960795 + 5490017 * 2 ^ 59
def prefixEnd_5490017 : Nat := 4983230072969 + 3 ^ 40 * 5490017 * 2
def baseEnd_5490017 : Nat := 313224169150528001882153

theorem tailTrace_5490017 : CollatzResearch.WordTrace tailWord_5490017 prefixEnd_5490017 313224169150528001882153 := by
  unfold tailWord_5490017
  simp only [CollatzResearch.WordTrace]
  refine ⟨200237370151613504100948305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133491580101075669400632203 200237370151613504100948305)
  ·
    refine ⟨150178027613710128075711229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200237370151613504100948305 150178027613710128075711229)
    ·
      refine ⟨56316760355141298028391711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150178027613710128075711229 56316760355141298028391711)
      ·
        refine ⟨84475140532711947042587567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56316760355141298028391711 84475140532711947042587567)
        ·
          refine ⟨126712710799067920563881351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84475140532711947042587567 126712710799067920563881351)
          ·
            refine ⟨190069066198601880845822027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126712710799067920563881351 190069066198601880845822027)
            ·
              refine ⟨285103599297902821268733041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190069066198601880845822027 285103599297902821268733041)
              ·
                refine ⟨213827699473427115951549781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285103599297902821268733041 213827699473427115951549781)
                ·
                  refine ⟨313224169150528001882153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 213827699473427115951549781 313224169150528001882153)
                  ·
                    rfl

theorem cell23_5490017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_5490017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490017 prefixEnd_5490017 := by exact prefixLift 5490017
  have htrace : WordTrace (prefixWord ++ tailWord_5490017) baseStart_5490017 baseEnd_5490017 := by
    simpa [prefixWord, tailWord_5490017, baseEnd_5490017] using wordTrace_append hprefix tailTrace_5490017
  have hstable : (prefixWord ++ tailWord_5490017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490017).length < 2 ^ (prefixWord ++ tailWord_5490017).sum := by decide
  have hdescent : baseEnd_5490017 < baseStart_5490017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490028 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_5490028 : Nat := 118140960795 + 5490028 * 2 ^ 59
def prefixEnd_5490028 : Nat := 4983230072969 + 3 ^ 40 * 5490028 * 2
def baseEnd_5490028 : Nat := 2819023170641951473901827

theorem tailTrace_5490028 : CollatzResearch.WordTrace tailWord_5490028 prefixEnd_5490028 2819023170641951473901827 := by
  unfold tailWord_5490028
  simp only [CollatzResearch.WordTrace]
  refine ⟨100118885677286826489799369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133491847569715768653065825 100118885677286826489799369)
  ·
    refine ⟨75089164257965119867349527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100118885677286826489799369 75089164257965119867349527)
    ·
      refine ⟨112633746386947679801024291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75089164257965119867349527 112633746386947679801024291)
      ·
        refine ⟨168950619580421519701536437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112633746386947679801024291 168950619580421519701536437)
        ·
          refine ⟨15839120585664517472019041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168950619580421519701536437 15839120585664517472019041)
          ·
            refine ⟨11879340439248388104014281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15839120585664517472019041 11879340439248388104014281)
            ·
              refine ⟨8909505329436291078010711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11879340439248388104014281 8909505329436291078010711)
              ·
                refine ⟨13364257994154436617016067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909505329436291078010711 13364257994154436617016067)
                ·
                  refine ⟨20046386991231654925524101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13364257994154436617016067 20046386991231654925524101)
                  ·
                    refine ⟨3758697560855935298535769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20046386991231654925524101 3758697560855935298535769)
                    ·
                      refine ⟨2819023170641951473901827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758697560855935298535769 2819023170641951473901827)
                      ·
                        rfl

theorem cell23_5490028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_5490028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490028 prefixEnd_5490028 := by exact prefixLift 5490028
  have htrace : WordTrace (prefixWord ++ tailWord_5490028) baseStart_5490028 baseEnd_5490028 := by
    simpa [prefixWord, tailWord_5490028, baseEnd_5490028] using wordTrace_append hprefix tailTrace_5490028
  have hstable : (prefixWord ++ tailWord_5490028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490028).length < 2 ^ (prefixWord ++ tailWord_5490028).sum := by decide
  have hdescent : baseEnd_5490028 < baseStart_5490028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490034 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_5490034 : Nat := 118140960795 + 5490034 * 2 ^ 59
def prefixEnd_5490034 : Nat := 4983230072969 + 3 ^ 40 * 5490034 * 2
def baseEnd_5490034 : Nat := 313225139058430938936311

theorem tailTrace_5490034 : CollatzResearch.WordTrace tailWord_5490034 prefixEnd_5490034 313225139058430938936311 := by
  unfold tailWord_5490034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50059497548137979001079289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133491993461701277336211437 50059497548137979001079289)
  ·
    refine ⟨37544623161103484250809467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50059497548137979001079289 37544623161103484250809467)
    ·
      refine ⟨56316934741655226376214201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37544623161103484250809467 56316934741655226376214201)
      ·
        refine ⟨42237701056241419782160651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56316934741655226376214201 42237701056241419782160651)
        ·
          refine ⟨63356551584362129673240977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42237701056241419782160651 63356551584362129673240977)
          ·
            refine ⟨47517413688271597254930733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63356551584362129673240977 47517413688271597254930733)
            ·
              refine ⟨17819030133101848970599025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47517413688271597254930733 17819030133101848970599025)
              ·
                refine ⟨13364272599826386727949269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17819030133101848970599025 13364272599826386727949269)
                ·
                  refine ⟨313225139058430938936311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13364272599826386727949269 313225139058430938936311)
                  ·
                    rfl

theorem cell23_5490034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_5490034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490034 prefixEnd_5490034 := by exact prefixLift 5490034
  have htrace : WordTrace (prefixWord ++ tailWord_5490034) baseStart_5490034 baseEnd_5490034 := by
    simpa [prefixWord, tailWord_5490034, baseEnd_5490034] using wordTrace_append hprefix tailTrace_5490034
  have hstable : (prefixWord ++ tailWord_5490034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490034).length < 2 ^ (prefixWord ++ tailWord_5490034).sum := by decide
  have hdescent : baseEnd_5490034 < baseStart_5490034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490044 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_5490044 : Nat := 118140960795 + 5490044 * 2 ^ 59
def prefixEnd_5490044 : Nat := 4983230072969 + 3 ^ 40 * 5490044 * 2
def baseEnd_5490044 : Nat := 2819031386332423411301753

theorem tailTrace_5490044 : CollatzResearch.WordTrace tailWord_5490044 prefixEnd_5490044 2819031386332423411301753 := by
  unfold tailWord_5490044
  simp only [CollatzResearch.WordTrace]
  refine ⟨100119177461257843856090593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133492236615010458474787457 100119177461257843856090593)
  ·
    refine ⟨75089383095943382892067945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100119177461257843856090593 75089383095943382892067945)
    ·
      refine ⟨56317037321957537169050959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75089383095943382892067945 56317037321957537169050959)
      ·
        refine ⟨84475555982936305753576439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56317037321957537169050959 84475555982936305753576439)
        ·
          refine ⟨126713333974404458630364659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84475555982936305753576439 126713333974404458630364659)
          ·
            refine ⟨190070000961606687945546989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126713333974404458630364659 190070000961606687945546989)
            ·
              refine ⟨71276250360602507979580121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190070000961606687945546989 71276250360602507979580121)
              ·
                refine ⟨53457187770451880984685091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71276250360602507979580121 53457187770451880984685091)
                ·
                  refine ⟨80185781655677821477027637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53457187770451880984685091 80185781655677821477027637)
                  ·
                    refine ⟨7517417030219795763471341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80185781655677821477027637 7517417030219795763471341)
                    ·
                      refine ⟨2819031386332423411301753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7517417030219795763471341 2819031386332423411301753)
                      ·
                        rfl

theorem cell23_5490044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_5490044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490044 prefixEnd_5490044 := by exact prefixLift 5490044
  have htrace : WordTrace (prefixWord ++ tailWord_5490044) baseStart_5490044 baseEnd_5490044 := by
    simpa [prefixWord, tailWord_5490044, baseEnd_5490044] using wordTrace_append hprefix tailTrace_5490044
  have hstable : (prefixWord ++ tailWord_5490044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490044).length < 2 ^ (prefixWord ++ tailWord_5490044).sum := by decide
  have hdescent : baseEnd_5490044 < baseStart_5490044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490049 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_5490049 : Nat := 118140960795 + 5490049 * 2 ^ 59
def prefixEnd_5490049 : Nat := 4983230072969 + 3 ^ 40 * 5490049 * 2
def baseEnd_5490049 : Nat := 2819033953735695891739231

theorem tailTrace_5490049 : CollatzResearch.WordTrace tailWord_5490049 prefixEnd_5490049 2819033953735695891739231 := by
  unfold tailWord_5490049
  simp only [CollatzResearch.WordTrace]
  refine ⟨200238537287497573566113201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133492358191665049044075467 200238537287497573566113201)
  ·
    refine ⟨150178902965623180174584901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200238537287497573566113201 150178902965623180174584901)
    ·
      refine ⟨28158544306054346282734669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150178902965623180174584901 28158544306054346282734669)
      ·
        refine ⟨10559454114770379856025501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28158544306054346282734669 10559454114770379856025501)
        ·
          refine ⟨3959795293038892446009563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10559454114770379856025501 3959795293038892446009563)
          ·
            refine ⟨5939692939558338669014345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959795293038892446009563 5939692939558338669014345)
            ·
              refine ⟨4454769704668754001760759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939692939558338669014345 4454769704668754001760759)
              ·
                refine ⟨6682154557003131002641139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454769704668754001760759 6682154557003131002641139)
                ·
                  refine ⟨10023231835504696503961709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6682154557003131002641139 10023231835504696503961709)
                  ·
                    refine ⟨3758711938314261188985641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10023231835504696503961709 3758711938314261188985641)
                    ·
                      refine ⟨2819033953735695891739231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758711938314261188985641 2819033953735695891739231)
                      ·
                        rfl

theorem cell23_5490049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_5490049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490049 prefixEnd_5490049 := by exact prefixLift 5490049
  have htrace : WordTrace (prefixWord ++ tailWord_5490049) baseStart_5490049 baseEnd_5490049 := by
    simpa [prefixWord, tailWord_5490049, baseEnd_5490049] using wordTrace_append hprefix tailTrace_5490049
  have hstable : (prefixWord ++ tailWord_5490049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490049).length < 2 ^ (prefixWord ++ tailWord_5490049).sum := by decide
  have hdescent : baseEnd_5490049 < baseStart_5490049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490051 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 5]
def baseStart_5490051 : Nat := 118140960795 + 5490051 * 2 ^ 59
def prefixEnd_5490051 : Nat := 4983230072969 + 3 ^ 40 * 5490051 * 2
def baseEnd_5490051 : Nat := 313226108966333875990469

theorem tailTrace_5490051 : CollatzResearch.WordTrace tailWord_5490051 prefixEnd_5490051 313226108966333875990469 := by
  unfold tailWord_5490051
  simp only [CollatzResearch.WordTrace]
  refine ⟨200238610233490327907686007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133492406822326885271790671 200238610233490327907686007)
  ·
    refine ⟨300357915350235491861529011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200238610233490327907686007 300357915350235491861529011)
    ·
      refine ⟨450536873025353237792293517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300357915350235491861529011 450536873025353237792293517)
      ·
        refine ⟨168951327384507464172110069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450536873025353237792293517 168951327384507464172110069)
        ·
          refine ⟨15839186942297574766135319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168951327384507464172110069 15839186942297574766135319)
          ·
            refine ⟨23758780413446362149202979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15839186942297574766135319 23758780413446362149202979)
            ·
              refine ⟨35638170620169543223804469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23758780413446362149202979 35638170620169543223804469)
              ·
                refine ⟨3341078495640894677231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35638170620169543223804469 3341078495640894677231669)
                ·
                  refine ⟨313226108966333875990469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341078495640894677231669 313226108966333875990469)
                  ·
                    rfl

theorem cell23_5490051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 5].length) (baseStart_5490051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490051 prefixEnd_5490051 := by exact prefixLift 5490051
  have htrace : WordTrace (prefixWord ++ tailWord_5490051) baseStart_5490051 baseEnd_5490051 := by
    simpa [prefixWord, tailWord_5490051, baseEnd_5490051] using wordTrace_append hprefix tailTrace_5490051
  have hstable : (prefixWord ++ tailWord_5490051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490051).length < 2 ^ (prefixWord ++ tailWord_5490051).sum := by decide
  have hdescent : baseEnd_5490051 < baseStart_5490051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490068 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 5]
def baseStart_5490068 : Nat := 118140960795 + 5490068 * 2 ^ 59
def prefixEnd_5490068 : Nat := 4983230072969 + 3 ^ 40 * 5490068 * 2
def baseEnd_5490068 : Nat := 313227078874236813044627

theorem tailTrace_5490068 : CollatzResearch.WordTrace tailWord_5490068 prefixEnd_5490068 313227078874236813044627 := by
  unfold tailWord_5490068
  simp only [CollatzResearch.WordTrace]
  refine ⟨100119615137214369905527429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133492820182952493207369905 100119615137214369905527429)
  ·
    refine ⟨18772427838227694357286393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100119615137214369905527429 18772427838227694357286393)
    ·
      refine ⟨14079320878670770767964795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18772427838227694357286393 14079320878670770767964795)
      ·
        refine ⟨21118981318006156151947193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14079320878670770767964795 21118981318006156151947193)
        ·
          refine ⟨15839235988504617113960395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21118981318006156151947193 15839235988504617113960395)
          ·
            refine ⟨23758853982756925670940593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15839235988504617113960395 23758853982756925670940593)
            ·
              refine ⟨17819140487067694253205445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23758853982756925670940593 17819140487067694253205445)
              ·
                refine ⟨3341088841325192672476021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17819140487067694253205445 3341088841325192672476021)
                ·
                  refine ⟨313227078874236813044627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341088841325192672476021 313227078874236813044627)
                  ·
                    rfl

theorem cell23_5490068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_5490068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490068 prefixEnd_5490068 := by exact prefixLift 5490068
  have htrace : WordTrace (prefixWord ++ tailWord_5490068) baseStart_5490068 baseEnd_5490068 := by
    simpa [prefixWord, tailWord_5490068, baseEnd_5490068] using wordTrace_append hprefix tailTrace_5490068
  have hstable : (prefixWord ++ tailWord_5490068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490068).length < 2 ^ (prefixWord ++ tailWord_5490068).sum := by decide
  have hdescent : baseEnd_5490068 < baseStart_5490068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490074 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5490074 : Nat := 118140960795 + 5490074 * 2 ^ 59
def prefixEnd_5490074 : Nat := 4983230072969 + 3 ^ 40 * 5490074 * 2
def baseEnd_5490074 : Nat := 2819046790752058293926615

theorem tailTrace_5490074 : CollatzResearch.WordTrace tailWord_5490074 prefixEnd_5490074 2819046790752058293926615 := by
  unfold tailWord_5490074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50059862278101750708943319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133492966074938001890515517 50059862278101750708943319)
  ·
    refine ⟨75089793417152626063414979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50059862278101750708943319 75089793417152626063414979)
    ·
      refine ⟨112634690125728939095122469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75089793417152626063414979 112634690125728939095122469)
      ·
        refine ⟨21119004398574176080335463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112634690125728939095122469 21119004398574176080335463)
        ·
          refine ⟨31678506597861264120503195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21119004398574176080335463 31678506597861264120503195)
          ·
            refine ⟨47517759896791896180754793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31678506597861264120503195 47517759896791896180754793)
            ·
              refine ⟨35638319922593922135566095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47517759896791896180754793 35638319922593922135566095)
              ·
                refine ⟨53457479883890883203349143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35638319922593922135566095 53457479883890883203349143)
                ·
                  refine ⟨80186219825836324805023715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53457479883890883203349143 80186219825836324805023715)
                  ·
                    refine ⟨120279329738754487207535573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80186219825836324805023715 120279329738754487207535573)
                    ·
                      refine ⟨2819046790752058293926615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120279329738754487207535573 2819046790752058293926615)
                      ·
                        rfl

theorem cell23_5490074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5490074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490074 prefixEnd_5490074 := by exact prefixLift 5490074
  have htrace : WordTrace (prefixWord ++ tailWord_5490074) baseStart_5490074 baseEnd_5490074 := by
    simpa [prefixWord, tailWord_5490074, baseEnd_5490074] using wordTrace_append hprefix tailTrace_5490074
  have hstable : (prefixWord ++ tailWord_5490074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490074).length < 2 ^ (prefixWord ++ tailWord_5490074).sum := by decide
  have hdescent : baseEnd_5490074 < baseStart_5490074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490101 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5490101 : Nat := 118140960795 + 5490101 * 2 ^ 59
def prefixEnd_5490101 : Nat := 4983230072969 + 3 ^ 40 * 5490101 * 2
def baseEnd_5490101 : Nat := 2819060654729729688288991

theorem tailTrace_5490101 : CollatzResearch.WordTrace tailWord_5490101 prefixEnd_5490101 2819060654729729688288991 := by
  unfold tailWord_5490101
  simp only [CollatzResearch.WordTrace]
  refine ⟨200240433883309186447006157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133493622588872790964670771 200240433883309186447006157)
  ·
    refine ⟨75090162706240944917627309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200240433883309186447006157 75090162706240944917627309)
    ·
      refine ⟨28158811014840354344110241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75090162706240944917627309 28158811014840354344110241)
      ·
        refine ⟨21119108261130265758082681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28158811014840354344110241 21119108261130265758082681)
        ·
          refine ⟨15839331195847699318562011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21119108261130265758082681 15839331195847699318562011)
          ·
            refine ⟨23758996793771548977843017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15839331195847699318562011 23758996793771548977843017)
            ·
              refine ⟨17819247595328661733382263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23758996793771548977843017 17819247595328661733382263)
              ·
                refine ⟨26728871392992992600073395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17819247595328661733382263 26728871392992992600073395)
                ·
                  refine ⟨40093307089489488900110093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26728871392992992600073395 40093307089489488900110093)
                  ·
                    refine ⟨15034990158558558337541285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40093307089489488900110093 15034990158558558337541285)
                    ·
                      refine ⟨2819060654729729688288991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15034990158558558337541285 2819060654729729688288991)
                      ·
                        rfl

theorem cell23_5490101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5490101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490101 prefixEnd_5490101 := by exact prefixLift 5490101
  have htrace : WordTrace (prefixWord ++ tailWord_5490101) baseStart_5490101 baseEnd_5490101 := by
    simpa [prefixWord, tailWord_5490101, baseEnd_5490101] using wordTrace_append hprefix tailTrace_5490101
  have hstable : (prefixWord ++ tailWord_5490101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490101).length < 2 ^ (prefixWord ++ tailWord_5490101).sum := by decide
  have hdescent : baseEnd_5490101 < baseStart_5490101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490185 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 1, 1, 3]
def baseStart_5490185 : Nat := 118140960795 + 5490185 * 2 ^ 59
def prefixEnd_5490185 : Nat := 4983230072969 + 3 ^ 40 * 5490185 * 2
def baseEnd_5490185 : Nat := 2819103787104707359638605

theorem tailTrace_5490185 : CollatzResearch.WordTrace tailWord_5490185 prefixEnd_5490185 2819103787104707359638605 := by
  unfold tailWord_5490185
  simp only [CollatzResearch.WordTrace]
  refine ⟨200243497615004868793064009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133495665076669912528709339 200243497615004868793064009)
  ·
    refine ⟨150182623211253651594798007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200243497615004868793064009 150182623211253651594798007)
    ·
      refine ⟨225273934816880477392197011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150182623211253651594798007 225273934816880477392197011)
      ·
        refine ⟨337910902225320716088295517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225273934816880477392197011 337910902225320716088295517)
        ·
          refine ⟨126716588334495268533110819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337910902225320716088295517 126716588334495268533110819)
          ·
            refine ⟨190074882501742902799666229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126716588334495268533110819 190074882501742902799666229)
            ·
              refine ⟨17819520234538397137468709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190074882501742902799666229 17819520234538397137468709)
              ·
                refine ⟨3341160043975949463275383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17819520234538397137468709 3341160043975949463275383)
                ·
                  refine ⟨5011740065963924194913075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341160043975949463275383 5011740065963924194913075)
                  ·
                    refine ⟨7517610098945886292369613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5011740065963924194913075 7517610098945886292369613)
                    ·
                      refine ⟨2819103787104707359638605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7517610098945886292369613 2819103787104707359638605)
                      ·
                        rfl

theorem cell23_5490185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 1, 3].length) (baseStart_5490185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490185 prefixEnd_5490185 := by exact prefixLift 5490185
  have htrace : WordTrace (prefixWord ++ tailWord_5490185) baseStart_5490185 baseEnd_5490185 := by
    simpa [prefixWord, tailWord_5490185, baseEnd_5490185] using wordTrace_append hprefix tailTrace_5490185
  have hstable : (prefixWord ++ tailWord_5490185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490185).length < 2 ^ (prefixWord ++ tailWord_5490185).sum := by decide
  have hdescent : baseEnd_5490185 < baseStart_5490185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490206 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5490206 : Nat := 118140960795 + 5490206 * 2 ^ 59
def prefixEnd_5490206 : Nat := 4983230072969 + 3 ^ 40 * 5490206 * 2
def baseEnd_5490206 : Nat := 2819114570198451777476009

theorem tailTrace_5490206 : CollatzResearch.WordTrace tailWord_5490206 prefixEnd_5490206 2819114570198451777476009 := by
  unfold tailWord_5490206
  simp only [CollatzResearch.WordTrace]
  refine ⟨25030532943491098672447309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133496175698619192919718981 25030532943491098672447309)
  ·
    refine ⟨9386449853809162002167741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25030532943491098672447309 9386449853809162002167741)
    ·
      refine ⟨3519918695178435750812903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9386449853809162002167741 3519918695178435750812903)
      ·
        refine ⟨5279878042767653626219355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519918695178435750812903 5279878042767653626219355)
        ·
          refine ⟨7919817064151480439329033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279878042767653626219355 7919817064151480439329033)
          ·
            refine ⟨5939862798113610329496775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919817064151480439329033 5939862798113610329496775)
            ·
              refine ⟨8909794197170415494245163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939862798113610329496775 8909794197170415494245163)
              ·
                refine ⟨13364691295755623241367745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909794197170415494245163 13364691295755623241367745)
                ·
                  refine ⟨10023518471816717431025809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13364691295755623241367745 10023518471816717431025809)
                  ·
                    refine ⟨7517638853862538073269357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10023518471816717431025809 7517638853862538073269357)
                    ·
                      refine ⟨2819114570198451777476009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7517638853862538073269357 2819114570198451777476009)
                      ·
                        rfl

theorem cell23_5490206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5490206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490206 prefixEnd_5490206 := by exact prefixLift 5490206
  have htrace : WordTrace (prefixWord ++ tailWord_5490206) baseStart_5490206 baseEnd_5490206 := by
    simpa [prefixWord, tailWord_5490206, baseEnd_5490206] using wordTrace_append hprefix tailTrace_5490206
  have hstable : (prefixWord ++ tailWord_5490206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490206).length < 2 ^ (prefixWord ++ tailWord_5490206).sum := by decide
  have hdescent : baseEnd_5490206 < baseStart_5490206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490208 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5490208 : Nat := 118140960795 + 5490208 * 2 ^ 59
def prefixEnd_5490208 : Nat := 4983230072969 + 3 ^ 40 * 5490208 * 2
def baseEnd_5490208 : Nat := 2819115597159760769650999

theorem tailTrace_5490208 : CollatzResearch.WordTrace tailWord_5490208 prefixEnd_5490208 2819115597159760769650999 := by
  unfold tailWord_5490208
  simp only [CollatzResearch.WordTrace]
  refine ⟨100122168246960771860575639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133496224329281029147434185 100122168246960771860575639)
  ·
    refine ⟨150183252370441157790863459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100122168246960771860575639 150183252370441157790863459)
    ·
      refine ⟨225274878555661736686295189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150183252370441157790863459 225274878555661736686295189)
      ·
        refine ⟨10559759932296643907170087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 225274878555661736686295189 10559759932296643907170087)
        ·
          refine ⟨15839639898444965860755131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10559759932296643907170087 15839639898444965860755131)
          ·
            refine ⟨23759459847667448791132697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15839639898444965860755131 23759459847667448791132697)
            ·
              refine ⟨17819594885750586593349523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23759459847667448791132697 17819594885750586593349523)
              ·
                refine ⟨26729392328625879890024285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17819594885750586593349523 26729392328625879890024285)
                ·
                  refine ⟨10023522123234704958759107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26729392328625879890024285 10023522123234704958759107)
                  ·
                    refine ⟨15035283184852057438138661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10023522123234704958759107 15035283184852057438138661)
                    ·
                      refine ⟨2819115597159760769650999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15035283184852057438138661 2819115597159760769650999)
                      ·
                        rfl

theorem cell23_5490208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5490208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490208 prefixEnd_5490208 := by exact prefixLift 5490208
  have htrace : WordTrace (prefixWord ++ tailWord_5490208) baseStart_5490208 baseEnd_5490208 := by
    simpa [prefixWord, tailWord_5490208, baseEnd_5490208] using wordTrace_append hprefix tailTrace_5490208
  have hstable : (prefixWord ++ tailWord_5490208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490208).length < 2 ^ (prefixWord ++ tailWord_5490208).sum := by decide
  have hdescent : baseEnd_5490208 < baseStart_5490208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490218 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5490218 : Nat := 118140960795 + 5490218 * 2 ^ 59
def prefixEnd_5490218 : Nat := 4983230072969 + 3 ^ 40 * 5490218 * 2
def baseEnd_5490218 : Nat := 939706910655435243508651

theorem tailTrace_5490218 : CollatzResearch.WordTrace tailWord_5490218 prefixEnd_5490218 939706910655435243508651 := by
  unfold tailWord_5490218
  simp only [CollatzResearch.WordTrace]
  refine ⟨50061175305971328857253827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133496467482590210286010205 50061175305971328857253827)
  ·
    refine ⟨75091762958956993285880741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50061175305971328857253827 75091762958956993285880741)
    ·
      refine ⟨14079705554804436241102639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75091762958956993285880741 14079705554804436241102639)
      ·
        refine ⟨21119558332206654361653959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14079705554804436241102639 21119558332206654361653959)
        ·
          refine ⟨31679337498309981542480939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21119558332206654361653959 31679337498309981542480939)
          ·
            refine ⟨47519006247464972313721409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31679337498309981542480939 47519006247464972313721409)
            ·
              refine ⟨35639254685598729235291057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47519006247464972313721409 35639254685598729235291057)
              ·
                refine ⟨26729441014199046926468293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35639254685598729235291057 26729441014199046926468293)
                ·
                  refine ⟨5011770190162321298712805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26729441014199046926468293 5011770190162321298712805)
                  ·
                    refine ⟨939706910655435243508651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011770190162321298712805 939706910655435243508651)
                    ·
                      rfl

theorem cell23_5490218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5490218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490218 prefixEnd_5490218 := by exact prefixLift 5490218
  have htrace : WordTrace (prefixWord ++ tailWord_5490218) baseStart_5490218 baseEnd_5490218 := by
    simpa [prefixWord, tailWord_5490218, baseEnd_5490218] using wordTrace_append hprefix tailTrace_5490218
  have hstable : (prefixWord ++ tailWord_5490218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490218).length < 2 ^ (prefixWord ++ tailWord_5490218).sum := by decide
  have hdescent : baseEnd_5490218 < baseStart_5490218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490222 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5490222 : Nat := 118140960795 + 5490222 * 2 ^ 59
def prefixEnd_5490222 : Nat := 4983230072969 + 3 ^ 40 * 5490222 * 2
def baseEnd_5490222 : Nat := 939707595296307904958645

theorem tailTrace_5490222 : CollatzResearch.WordTrace tailWord_5490222 prefixEnd_5490222 939707595296307904958645 := by
  unfold tailWord_5490222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25030605889483853014020115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133496564743913882741440613 25030605889483853014020115)
  ·
    refine ⟨37545908834225779521030173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25030605889483853014020115 37545908834225779521030173)
    ·
      refine ⟨14079715812834667320386315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37545908834225779521030173 14079715812834667320386315)
      ·
        refine ⟨21119573719252000980579473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14079715812834667320386315 21119573719252000980579473)
        ·
          refine ⟨15839680289439000735434605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21119573719252000980579473 15839680289439000735434605)
          ·
            refine ⟨5939880108539625275787977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15839680289439000735434605 5939880108539625275787977)
            ·
              refine ⟨4454910081404718956840983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939880108539625275787977 4454910081404718956840983)
              ·
                refine ⟨6682365122107078435261475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454910081404718956840983 6682365122107078435261475)
                ·
                  refine ⟨10023547683160617652892213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6682365122107078435261475 10023547683160617652892213)
                  ·
                    refine ⟨939707595296307904958645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10023547683160617652892213 939707595296307904958645)
                    ·
                      rfl

theorem cell23_5490222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5490222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490222 prefixEnd_5490222 := by exact prefixLift 5490222
  have htrace : WordTrace (prefixWord ++ tailWord_5490222) baseStart_5490222 baseEnd_5490222 := by
    simpa [prefixWord, tailWord_5490222, baseEnd_5490222] using wordTrace_append hprefix tailTrace_5490222
  have hstable : (prefixWord ++ tailWord_5490222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490222).length < 2 ^ (prefixWord ++ tailWord_5490222).sum := by decide
  have hdescent : baseEnd_5490222 < baseStart_5490222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_5490298 : Nat := 118140960795 + 5490298 * 2 ^ 59
def prefixEnd_5490298 : Nat := 4983230072969 + 3 ^ 40 * 5490298 * 2
def baseEnd_5490298 : Nat := 2819161810418665417525585

theorem tailTrace_5490298 : CollatzResearch.WordTrace tailWord_5490298 prefixEnd_5490298 2819161810418665417525585 := by
  unfold tailWord_5490298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50061904765898872272981887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133498412709063659394618365 50061904765898872272981887)
  ·
    refine ⟨75092857148848308409472831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50061904765898872272981887 75092857148848308409472831)
    ·
      refine ⟨112639285723272462614209247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75092857148848308409472831 112639285723272462614209247)
      ·
        refine ⟨168958928584908693921313871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112639285723272462614209247 168958928584908693921313871)
        ·
          refine ⟨253438392877363040881970807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168958928584908693921313871 253438392877363040881970807)
          ·
            refine ⟨380157589316044561322956211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253438392877363040881970807 380157589316044561322956211)
            ·
              refine ⟨570236383974066841984434317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380157589316044561322956211 570236383974066841984434317)
              ·
                refine ⟨213838643990275065744162869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570236383974066841984434317 213838643990275065744162869)
                ·
                  refine ⟨20047372874088287413515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213838643990275065744162869 20047372874088287413515269)
                  ·
                    refine ⟨3758882413891553890034113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20047372874088287413515269 3758882413891553890034113)
                    ·
                      refine ⟨2819161810418665417525585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758882413891553890034113 2819161810418665417525585)
                      ·
                        rfl

theorem cell23_5490298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_5490298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490298 prefixEnd_5490298 := by exact prefixLift 5490298
  have htrace : WordTrace (prefixWord ++ tailWord_5490298) baseStart_5490298 baseEnd_5490298 := by
    simpa [prefixWord, tailWord_5490298, baseEnd_5490298] using wordTrace_append hprefix tailTrace_5490298
  have hstable : (prefixWord ++ tailWord_5490298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490298).length < 2 ^ (prefixWord ++ tailWord_5490298).sum := by decide
  have hdescent : baseEnd_5490298 < baseStart_5490298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490318 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5490318 : Nat := 118140960795 + 5490318 * 2 ^ 59
def prefixEnd_5490318 : Nat := 4983230072969 + 3 ^ 40 * 5490318 * 2
def baseEnd_5490318 : Nat := 2819172080031755339275493

theorem tailTrace_5490318 : CollatzResearch.WordTrace tailWord_5490318 prefixEnd_5490318 2819172080031755339275493 := by
  unfold tailWord_5490318
  simp only [CollatzResearch.WordTrace]
  refine ⟨25031043565440379063456951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133498899015682021671770405 25031043565440379063456951)
  ·
    refine ⟨37546565348160568595185427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25031043565440379063456951 37546565348160568595185427)
    ·
      refine ⟨56319848022240852892778141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37546565348160568595185427 56319848022240852892778141)
      ·
        refine ⟨21119943008340319834791803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56319848022240852892778141 21119943008340319834791803)
        ·
          refine ⟨31679914512510479752187705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21119943008340319834791803 31679914512510479752187705)
          ·
            refine ⟨23759935884382859814140779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31679914512510479752187705 23759935884382859814140779)
            ·
              refine ⟨35639903826574289721211169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23759935884382859814140779 35639903826574289721211169)
              ·
                refine ⟨26729927869930717290908377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35639903826574289721211169 26729927869930717290908377)
                ·
                  refine ⟨20047445902448037968181283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26729927869930717290908377 20047445902448037968181283)
                  ·
                    refine ⟨30071168853672056952271925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20047445902448037968181283 30071168853672056952271925)
                    ·
                      refine ⟨2819172080031755339275493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30071168853672056952271925 2819172080031755339275493)
                      ·
                        rfl

theorem cell23_5490318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5490318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490318 prefixEnd_5490318 := by exact prefixLift 5490318
  have htrace : WordTrace (prefixWord ++ tailWord_5490318) baseStart_5490318 baseEnd_5490318 := by
    simpa [prefixWord, tailWord_5490318, baseEnd_5490318] using wordTrace_append hprefix tailTrace_5490318
  have hstable : (prefixWord ++ tailWord_5490318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490318).length < 2 ^ (prefixWord ++ tailWord_5490318).sum := by decide
  have hdescent : baseEnd_5490318 < baseStart_5490318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490332 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5490332 : Nat := 118140960795 + 5490332 * 2 ^ 59
def prefixEnd_5490332 : Nat := 4983230072969 + 3 ^ 40 * 5490332 * 2
def baseEnd_5490332 : Nat := 2819179268760918284500429

theorem tailTrace_5490332 : CollatzResearch.WordTrace tailWord_5490332 prefixEnd_5490332 2819179268760918284500429 := by
  unfold tailWord_5490332
  simp only [CollatzResearch.WordTrace]
  refine ⟨100124429572736156449332625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133499239430314875265776833 100124429572736156449332625)
  ·
    refine ⟨75093322179552117336999469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100124429572736156449332625 75093322179552117336999469)
    ·
      refine ⟨28159995817332044001374801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75093322179552117336999469 28159995817332044001374801)
      ·
        refine ⟨21119996862999033001031101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28159995817332044001374801 21119996862999033001031101)
        ·
          refine ⟨7919998823624637375386663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21119996862999033001031101 7919998823624637375386663)
          ·
            refine ⟨11879998235436956063079995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7919998823624637375386663 11879998235436956063079995)
            ·
              refine ⟨17819997353155434094619993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11879998235436956063079995 17819997353155434094619993)
              ·
                refine ⟨13364998014866575570964995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17819997353155434094619993 13364998014866575570964995)
                ·
                  refine ⟨20047497022299863356447493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13364998014866575570964995 20047497022299863356447493)
                  ·
                    refine ⟨3758905691681224379333905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20047497022299863356447493 3758905691681224379333905)
                    ·
                      refine ⟨2819179268760918284500429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758905691681224379333905 2819179268760918284500429)
                      ·
                        rfl

theorem cell23_5490332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5490332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490332 prefixEnd_5490332 := by exact prefixLift 5490332
  have htrace : WordTrace (prefixWord ++ tailWord_5490332) baseStart_5490332 baseEnd_5490332 := by
    simpa [prefixWord, tailWord_5490332, baseEnd_5490332] using wordTrace_append hprefix tailTrace_5490332
  have hstable : (prefixWord ++ tailWord_5490332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490332).length < 2 ^ (prefixWord ++ tailWord_5490332).sum := by decide
  have hdescent : baseEnd_5490332 < baseStart_5490332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490349 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_5490349 : Nat := 118140960795 + 5490349 * 2 ^ 59
def prefixEnd_5490349 : Nat := 4983230072969 + 3 ^ 40 * 5490349 * 2
def baseEnd_5490349 : Nat := 2819187997932044717987851

theorem tailTrace_5490349 : CollatzResearch.WordTrace tailWord_5490349 prefixEnd_5490349 2819187997932044717987851 := by
  unfold tailWord_5490349
  simp only [CollatzResearch.WordTrace]
  refine ⟨200249479186410724802034101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133499652790940483201356067 200249479186410724802034101)
  ·
    refine ⟨18773388673726005450190697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200249479186410724802034101 18773388673726005450190697)
    ·
      refine ⟨14080041505294504087643023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18773388673726005450190697 14080041505294504087643023)
      ·
        refine ⟨21120062257941756131464535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14080041505294504087643023 21120062257941756131464535)
        ·
          refine ⟨31680093386912634197196803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21120062257941756131464535 31680093386912634197196803)
          ·
            refine ⟨47520140080368951295795205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31680093386912634197196803 47520140080368951295795205)
            ·
              refine ⟨8910026265069178367961601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47520140080368951295795205 8910026265069178367961601)
              ·
                refine ⟨6682519698801883775971201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8910026265069178367961601 6682519698801883775971201)
                ·
                  refine ⟨5011889774101412831978401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682519698801883775971201 5011889774101412831978401)
                  ·
                    refine ⟨3758917330576059623983801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5011889774101412831978401 3758917330576059623983801)
                    ·
                      refine ⟨2819187997932044717987851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758917330576059623983801 2819187997932044717987851)
                      ·
                        rfl

theorem cell23_5490349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_5490349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490349 prefixEnd_5490349 := by exact prefixLift 5490349
  have htrace : WordTrace (prefixWord ++ tailWord_5490349) baseStart_5490349 baseEnd_5490349 := by
    simpa [prefixWord, tailWord_5490349, baseEnd_5490349] using wordTrace_append hprefix tailTrace_5490349
  have hstable : (prefixWord ++ tailWord_5490349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490349).length < 2 ^ (prefixWord ++ tailWord_5490349).sum := by decide
  have hdescent : baseEnd_5490349 < baseStart_5490349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490385 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_5490385 : Nat := 118140960795 + 5490385 * 2 ^ 59
def prefixEnd_5490385 : Nat := 4983230072969 + 3 ^ 40 * 5490385 * 2
def baseEnd_5490385 : Nat := 939735494411868859045895

theorem tailTrace_5490385 : CollatzResearch.WordTrace tailWord_5490385 prefixEnd_5490385 939735494411868859045895 := by
  unfold tailWord_5490385
  simp only [CollatzResearch.WordTrace]
  refine ⟨200250792214280302950344609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133500528142853535300229739 200250792214280302950344609)
  ·
    refine ⟨150188094160710227212758457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200250792214280302950344609 150188094160710227212758457)
    ·
      refine ⟨112641070620532670409568843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150188094160710227212758457 112641070620532670409568843)
      ·
        refine ⟨168961605930799005614353265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112641070620532670409568843 168961605930799005614353265)
        ·
          refine ⟨126721204448099254210764949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168961605930799005614353265 126721204448099254210764949)
          ·
            refine ⟨5940056458504652541129607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126721204448099254210764949 5940056458504652541129607)
            ·
              refine ⟨8910084687756978811694411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940056458504652541129607 8910084687756978811694411)
              ·
                refine ⟨13365127031635468217541617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910084687756978811694411 13365127031635468217541617)
                ·
                  refine ⟨10023845273726601163156213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13365127031635468217541617 10023845273726601163156213)
                  ·
                    refine ⟨939735494411868859045895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10023845273726601163156213 939735494411868859045895)
                    ·
                      rfl

theorem cell23_5490385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_5490385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490385 prefixEnd_5490385 := by exact prefixLift 5490385
  have htrace : WordTrace (prefixWord ++ tailWord_5490385) baseStart_5490385 baseEnd_5490385 := by
    simpa [prefixWord, tailWord_5490385, baseEnd_5490385] using wordTrace_append hprefix tailTrace_5490385
  have hstable : (prefixWord ++ tailWord_5490385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490385).length < 2 ^ (prefixWord ++ tailWord_5490385).sum := by decide
  have hdescent : baseEnd_5490385 < baseStart_5490385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490405 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5490405 : Nat := 118140960795 + 5490405 * 2 ^ 59
def prefixEnd_5490405 : Nat := 4983230072969 + 3 ^ 40 * 5490405 * 2
def baseEnd_5490405 : Nat := 2819216752848696498887593

theorem tailTrace_5490405 : CollatzResearch.WordTrace tailWord_5490405 prefixEnd_5490405 2819216752848696498887593 := by
  unfold tailWord_5490405
  simp only [CollatzResearch.WordTrace]
  refine ⟨200251521674207846366072669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133501014449471897577381779 200251521674207846366072669)
  ·
    refine ⟨75094320627827942387277251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200251521674207846366072669 75094320627827942387277251)
    ·
      refine ⟨112641480941741913580915877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75094320627827942387277251 112641480941741913580915877)
      ·
        refine ⟨21120277676576608796421727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112641480941741913580915877 21120277676576608796421727)
        ·
          refine ⟨31680416514864913194632591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21120277676576608796421727 31680416514864913194632591)
          ·
            refine ⟨47520624772297369791948887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31680416514864913194632591 47520624772297369791948887)
            ·
              refine ⟨71280937158446054687923331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47520624772297369791948887 71280937158446054687923331)
              ·
                refine ⟨106921405737669082031884997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71280937158446054687923331 106921405737669082031884997)
                ·
                  refine ⟨20047763575812952880978437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106921405737669082031884997 20047763575812952880978437)
                  ·
                    refine ⟨3758955670464928665183457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20047763575812952880978437 3758955670464928665183457)
                    ·
                      refine ⟨2819216752848696498887593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758955670464928665183457 2819216752848696498887593)
                      ·
                        rfl

theorem cell23_5490405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5490405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490405 prefixEnd_5490405 := by exact prefixLift 5490405
  have htrace : WordTrace (prefixWord ++ tailWord_5490405) baseStart_5490405 baseEnd_5490405 := by
    simpa [prefixWord, tailWord_5490405, baseEnd_5490405] using wordTrace_append hprefix tailTrace_5490405
  have hstable : (prefixWord ++ tailWord_5490405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490405).length < 2 ^ (prefixWord ++ tailWord_5490405).sum := by decide
  have hdescent : baseEnd_5490405 < baseStart_5490405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490415 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 3, 4]
def baseStart_5490415 : Nat := 118140960795 + 5490415 * 2 ^ 59
def prefixEnd_5490415 : Nat := 4983230072969 + 3 ^ 40 * 5490415 * 2
def baseEnd_5490415 : Nat := 939740629218413819920849

theorem tailTrace_5490415 : CollatzResearch.WordTrace tailWord_5490415 prefixEnd_5490415 939740629218413819920849 := by
  unfold tailWord_5490415
  simp only [CollatzResearch.WordTrace]
  refine ⟨200251886404171618073936699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133501257602781078715957799 200251886404171618073936699)
  ·
    refine ⟨300377829606257427110905049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200251886404171618073936699 300377829606257427110905049)
    ·
      refine ⟨225283372204693070333178787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300377829606257427110905049 225283372204693070333178787)
      ·
        refine ⟨337925058307039605499768181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225283372204693070333178787 337925058307039605499768181)
        ·
          refine ⟨31680474216284963015603267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 337925058307039605499768181 31680474216284963015603267)
          ·
            refine ⟨47520711324427444523404901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31680474216284963015603267 47520711324427444523404901)
            ·
              refine ⟨8910133373330145848138419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47520711324427444523404901 8910133373330145848138419)
              ·
                refine ⟨13365200059995218772207629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910133373330145848138419 13365200059995218772207629)
                ·
                  refine ⟨5011950022498207039577861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13365200059995218772207629 5011950022498207039577861)
                  ·
                    refine ⟨939740629218413819920849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011950022498207039577861 939740629218413819920849)
                    ·
                      rfl

theorem cell23_5490415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_5490415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490415 prefixEnd_5490415 := by exact prefixLift 5490415
  have htrace : WordTrace (prefixWord ++ tailWord_5490415) baseStart_5490415 baseEnd_5490415 := by
    simpa [prefixWord, tailWord_5490415, baseEnd_5490415] using wordTrace_append hprefix tailTrace_5490415
  have hstable : (prefixWord ++ tailWord_5490415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490415).length < 2 ^ (prefixWord ++ tailWord_5490415).sum := by decide
  have hdescent : baseEnd_5490415 < baseStart_5490415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490418 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5490418 : Nat := 118140960795 + 5490418 * 2 ^ 59
def prefixEnd_5490418 : Nat := 4983230072969 + 3 ^ 40 * 5490418 * 2
def baseEnd_5490418 : Nat := 2819223428097204948025033

theorem tailTrace_5490418 : CollatzResearch.WordTrace tailWord_5490418 prefixEnd_5490418 2819223428097204948025033 := by
  unfold tailWord_5490418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50062998955790187396573977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133501330548773833057530605 50062998955790187396573977)
  ·
    refine ⟨37547249216842640547430483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50062998955790187396573977 37547249216842640547430483)
    ·
      refine ⟨56320873825263960821145725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37547249216842640547430483 56320873825263960821145725)
      ·
        refine ⟨21120327684473985307929647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56320873825263960821145725 21120327684473985307929647)
        ·
          refine ⟨31680491526710977961894471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21120327684473985307929647 31680491526710977961894471)
          ·
            refine ⟨47520737290066466942841707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31680491526710977961894471 47520737290066466942841707)
            ·
              refine ⟨71281105935099700414262561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47520737290066466942841707 71281105935099700414262561)
              ·
                refine ⟨53460829451324775310696921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71281105935099700414262561 53460829451324775310696921)
                ·
                  refine ⟨40095622088493581483022691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53460829451324775310696921 40095622088493581483022691)
                  ·
                    refine ⟨60143433132740372224534037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40095622088493581483022691 60143433132740372224534037)
                    ·
                      refine ⟨2819223428097204948025033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60143433132740372224534037 2819223428097204948025033)
                      ·
                        rfl

theorem cell23_5490418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5490418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490418 prefixEnd_5490418 := by exact prefixLift 5490418
  have htrace : WordTrace (prefixWord ++ tailWord_5490418) baseStart_5490418 baseEnd_5490418 := by
    simpa [prefixWord, tailWord_5490418, baseEnd_5490418] using wordTrace_append hprefix tailTrace_5490418
  have hstable : (prefixWord ++ tailWord_5490418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490418).length < 2 ^ (prefixWord ++ tailWord_5490418).sum := by decide
  have hdescent : baseEnd_5490418 < baseStart_5490418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490422 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5490422 : Nat := 118140960795 + 5490422 * 2 ^ 59
def prefixEnd_5490422 : Nat := 4983230072969 + 3 ^ 40 * 5490422 * 2
def baseEnd_5490422 : Nat := 2819225482019822932375015

theorem tailTrace_5490422 : CollatzResearch.WordTrace tailWord_5490422 prefixEnd_5490422 2819225482019822932375015 := by
  unfold tailWord_5490422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515758857196641141840095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133501427810097505512961013 12515758857196641141840095)
  ·
    refine ⟨18773638285794961712760143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12515758857196641141840095 18773638285794961712760143)
    ·
      refine ⟨28160457428692442569140215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18773638285794961712760143 28160457428692442569140215)
      ·
        refine ⟨42240686143038663853710323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28160457428692442569140215 42240686143038663853710323)
        ·
          refine ⟨63361029214557995780565485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42240686143038663853710323 63361029214557995780565485)
          ·
            refine ⟨23760385955459248417712057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63361029214557995780565485 23760385955459248417712057)
            ·
              refine ⟨17820289466594436313284043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23760385955459248417712057 17820289466594436313284043)
              ·
                refine ⟨26730434199891654469926065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17820289466594436313284043 26730434199891654469926065)
                ·
                  refine ⟨20047825649918740852444549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26730434199891654469926065 20047825649918740852444549)
                  ·
                    refine ⟨3758967309359763909833353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20047825649918740852444549 3758967309359763909833353)
                    ·
                      refine ⟨2819225482019822932375015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3758967309359763909833353 2819225482019822932375015)
                      ·
                        rfl

theorem cell23_5490422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5490422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490422 prefixEnd_5490422 := by exact prefixLift 5490422
  have htrace : WordTrace (prefixWord ++ tailWord_5490422) baseStart_5490422 baseEnd_5490422 := by
    simpa [prefixWord, tailWord_5490422, baseEnd_5490422] using wordTrace_append hprefix tailTrace_5490422
  have hstable : (prefixWord ++ tailWord_5490422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490422).length < 2 ^ (prefixWord ++ tailWord_5490422).sum := by decide
  have hdescent : baseEnd_5490422 < baseStart_5490422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490522 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_5490522 : Nat := 118140960795 + 5490522 * 2 ^ 59
def prefixEnd_5490522 : Nat := 4983230072969 + 3 ^ 40 * 5490522 * 2
def baseEnd_5490522 : Nat := 939758943361757513708185

theorem tailTrace_5490522 : CollatzResearch.WordTrace tailWord_5490522 prefixEnd_5490522 939758943361757513708185 := by
  unfold tailWord_5490522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50063947253695993837020455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133503859343189316898721213 50063947253695993837020455)
  ·
    refine ⟨75095920880543990755530683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50063947253695993837020455 75095920880543990755530683)
    ·
      refine ⟨112643881320815986133296025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75095920880543990755530683 112643881320815986133296025)
      ·
        refine ⟨84482910990611989599972019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112643881320815986133296025 84482910990611989599972019)
        ·
          refine ⟨126724366485917984399958029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84482910990611989599972019 126724366485917984399958029)
          ·
            refine ⟨47521637432219244149984261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126724366485917984399958029 47521637432219244149984261)
            ·
              refine ⟨8910307018541108278122049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47521637432219244149984261 8910307018541108278122049)
              ·
                refine ⟨6682730263905831208591537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8910307018541108278122049 6682730263905831208591537)
                ·
                  refine ⟨5012047697929373406443653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682730263905831208591537 5012047697929373406443653)
                  ·
                    refine ⟨939758943361757513708185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012047697929373406443653 939758943361757513708185)
                    ·
                      rfl

theorem cell23_5490522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_5490522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490522 prefixEnd_5490522 := by exact prefixLift 5490522
  have htrace : WordTrace (prefixWord ++ tailWord_5490522) baseStart_5490522 baseEnd_5490522 := by
    simpa [prefixWord, tailWord_5490522, baseEnd_5490522] using wordTrace_append hprefix tailTrace_5490522
  have hstable : (prefixWord ++ tailWord_5490522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490522).length < 2 ^ (prefixWord ++ tailWord_5490522).sum := by decide
  have hdescent : baseEnd_5490522 < baseStart_5490522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490542 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5490542 : Nat := 118140960795 + 5490542 * 2 ^ 59
def prefixEnd_5490542 : Nat := 4983230072969 + 3 ^ 40 * 5490542 * 2
def baseEnd_5490542 : Nat := 2819287099698362462874463

theorem tailTrace_5490542 : CollatzResearch.WordTrace tailWord_5490542 prefixEnd_5490542 2819287099698362462874463 := by
  unfold tailWord_5490542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032064809338939845476235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133504345649807679175873253 25032064809338939845476235)
  ·
    refine ⟨37548097214008409768214353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25032064809338939845476235 37548097214008409768214353)
    ·
      refine ⟨28161072910506307326160765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37548097214008409768214353 28161072910506307326160765)
      ·
        refine ⟨10560402341439865247310287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28161072910506307326160765 10560402341439865247310287)
        ·
          refine ⟨15840603512159797870965431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10560402341439865247310287 15840603512159797870965431)
          ·
            refine ⟨23760905268239696806448147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15840603512159797870965431 23760905268239696806448147)
            ·
              refine ⟨35641357902359545209672221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23760905268239696806448147 35641357902359545209672221)
              ·
                refine ⟨13365509213384829453627083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35641357902359545209672221 13365509213384829453627083)
                ·
                  refine ⟨20048263820077244180440625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13365509213384829453627083 20048263820077244180440625)
                  ·
                    refine ⟨15036197865057933135330469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20048263820077244180440625 15036197865057933135330469)
                    ·
                      refine ⟨2819287099698362462874463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15036197865057933135330469 2819287099698362462874463)
                      ·
                        rfl

theorem cell23_5490542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5490542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490542 prefixEnd_5490542 := by exact prefixLift 5490542
  have htrace : WordTrace (prefixWord ++ tailWord_5490542) baseStart_5490542 baseEnd_5490542 := by
    simpa [prefixWord, tailWord_5490542, baseEnd_5490542] using wordTrace_append hprefix tailTrace_5490542
  have hstable : (prefixWord ++ tailWord_5490542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490542).length < 2 ^ (prefixWord ++ tailWord_5490542).sum := by decide
  have hdescent : baseEnd_5490542 < baseStart_5490542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490596 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_5490596 : Nat := 118140960795 + 5490596 * 2 ^ 59
def prefixEnd_5490596 : Nat := 4983230072969 + 3 ^ 40 * 5490596 * 2
def baseEnd_5490596 : Nat := 2819314827653705251599215

theorem tailTrace_5490596 : CollatzResearch.WordTrace tailWord_5490596 prefixEnd_5490596 2819314827653705251599215 := by
  unfold tailWord_5490596
  simp only [CollatzResearch.WordTrace]
  refine ⟨100129244008257942993137821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133505658677677257324183761 100129244008257942993137821)
  ·
    refine ⟨37548466503096728622426683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100129244008257942993137821 37548466503096728622426683)
    ·
      refine ⟨56322699754645092933640025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37548466503096728622426683 56322699754645092933640025)
      ·
        refine ⟨42242024815983819700230019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56322699754645092933640025 42242024815983819700230019)
        ·
          refine ⟨63363037223975729550345029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42242024815983819700230019 63363037223975729550345029)
          ·
            refine ⟨11880569479495449290689693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63363037223975729550345029 11880569479495449290689693)
            ·
              refine ⟨4455213554810793484008635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11880569479495449290689693 4455213554810793484008635)
              ·
                refine ⟨6682820332216190226012953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455213554810793484008635 6682820332216190226012953)
                ·
                  refine ⟨5012115249162142669509715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682820332216190226012953 5012115249162142669509715)
                  ·
                    refine ⟨7518172873743214004264573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5012115249162142669509715 7518172873743214004264573)
                    ·
                      refine ⟨2819314827653705251599215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7518172873743214004264573 2819314827653705251599215)
                      ·
                        rfl

theorem cell23_5490596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_5490596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490596 prefixEnd_5490596 := by exact prefixLift 5490596
  have htrace : WordTrace (prefixWord ++ tailWord_5490596) baseStart_5490596 baseEnd_5490596 := by
    simpa [prefixWord, tailWord_5490596, baseEnd_5490596] using wordTrace_append hprefix tailTrace_5490596
  have hstable : (prefixWord ++ tailWord_5490596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490596).length < 2 ^ (prefixWord ++ tailWord_5490596).sum := by decide
  have hdescent : baseEnd_5490596 < baseStart_5490596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490622 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5490622 : Nat := 118140960795 + 5490622 * 2 ^ 59
def prefixEnd_5490622 : Nat := 4983230072969 + 3 ^ 40 * 5490622 * 2
def baseEnd_5490622 : Nat := 2819328178150722149874095

theorem tailTrace_5490622 : CollatzResearch.WordTrace tailWord_5490622 prefixEnd_5490622 2819328178150722149874095 := by
  unfold tailWord_5490622
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032429539302711553340265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133506290876281128284481413 25032429539302711553340265)
  ·
    refine ⟨18774322154477033665005199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25032429539302711553340265 18774322154477033665005199)
    ·
      refine ⟨28161483231715550497507799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18774322154477033665005199 28161483231715550497507799)
      ·
        refine ⟨42242224847573325746261699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28161483231715550497507799 42242224847573325746261699)
        ·
          refine ⟨63363337271359988619392549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42242224847573325746261699 63363337271359988619392549)
          ·
            refine ⟨11880625738379997866136103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63363337271359988619392549 11880625738379997866136103)
            ·
              refine ⟨17820938607569996799204155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11880625738379997866136103 17820938607569996799204155)
              ·
                refine ⟨26731407911354995198806233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17820938607569996799204155 26731407911354995198806233)
                ·
                  refine ⟨20048555933516246399104675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26731407911354995198806233 20048555933516246399104675)
                  ·
                    refine ⟨30072833900274369598657013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20048555933516246399104675 30072833900274369598657013)
                    ·
                      refine ⟨2819328178150722149874095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30072833900274369598657013 2819328178150722149874095)
                      ·
                        rfl

theorem cell23_5490622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5490622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490622 prefixEnd_5490622 := by exact prefixLift 5490622
  have htrace : WordTrace (prefixWord ++ tailWord_5490622) baseStart_5490622 baseEnd_5490622 := by
    simpa [prefixWord, tailWord_5490622, baseEnd_5490622] using wordTrace_append hprefix tailTrace_5490622
  have hstable : (prefixWord ++ tailWord_5490622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490622).length < 2 ^ (prefixWord ++ tailWord_5490622).sum := by decide
  have hdescent : baseEnd_5490622 < baseStart_5490622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490653 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_5490653 : Nat := 118140960795 + 5490653 * 2 ^ 59
def prefixEnd_5490653 : Nat := 4983230072969 + 3 ^ 40 * 5490653 * 2
def baseEnd_5490653 : Nat := 2819344096051011528586453

theorem tailTrace_5490653 : CollatzResearch.WordTrace tailWord_5490653 prefixEnd_5490653 2819344096051011528586453 := by
  unfold tailWord_5490653
  simp only [CollatzResearch.WordTrace]
  refine ⟨200260566977309384721100613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133507044651539589814067075 200260566977309384721100613)
  ·
    refine ⟨37548856308245509635206365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200260566977309384721100613 37548856308245509635206365)
    ·
      refine ⟨14080821115592066113202387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37548856308245509635206365 14080821115592066113202387)
      ·
        refine ⟨21121231673388099169803581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14080821115592066113202387 21121231673388099169803581)
        ·
          refine ⟨7920461877520537188676343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21121231673388099169803581 7920461877520537188676343)
          ·
            refine ⟨11880692816280805783014515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920461877520537188676343 11880692816280805783014515)
            ·
              refine ⟨17821039224421208674521773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11880692816280805783014515 17821039224421208674521773)
              ·
                refine ⟨6682889709157953252945665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17821039224421208674521773 6682889709157953252945665)
                ·
                  refine ⟨5012167281868464939709249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682889709157953252945665 5012167281868464939709249)
                  ·
                    refine ⟨3759125461401348704781937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5012167281868464939709249 3759125461401348704781937)
                    ·
                      refine ⟨2819344096051011528586453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759125461401348704781937 2819344096051011528586453)
                      ·
                        rfl

theorem cell23_5490653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_5490653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490653 prefixEnd_5490653 := by exact prefixLift 5490653
  have htrace : WordTrace (prefixWord ++ tailWord_5490653) baseStart_5490653 baseEnd_5490653 := by
    simpa [prefixWord, tailWord_5490653, baseEnd_5490653] using wordTrace_append hprefix tailTrace_5490653
  have hstable : (prefixWord ++ tailWord_5490653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490653).length < 2 ^ (prefixWord ++ tailWord_5490653).sum := by decide
  have hdescent : baseEnd_5490653 < baseStart_5490653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490675 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_5490675 : Nat := 118140960795 + 5490675 * 2 ^ 59
def prefixEnd_5490675 : Nat := 4983230072969 + 3 ^ 40 * 5490675 * 2
def baseEnd_5490675 : Nat := 2819355392625410442511351

theorem tailTrace_5490675 : CollatzResearch.WordTrace tailWord_5490675 prefixEnd_5490675 2819355392625410442511351 := by
  unfold tailWord_5490675
  simp only [CollatzResearch.WordTrace]
  refine ⟨200261369383229682478401479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133507579588819788318934319 200261369383229682478401479)
  ·
    refine ⟨300392054074844523717602219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200261369383229682478401479 300392054074844523717602219)
    ·
      refine ⟨450588081112266785576403329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300392054074844523717602219 450588081112266785576403329)
      ·
        refine ⟨337941060834200089182302497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450588081112266785576403329 337941060834200089182302497)
        ·
          refine ⟨253455795625650066886726873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337941060834200089182302497 253455795625650066886726873)
          ·
            refine ⟨190091846719237550165045155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253455795625650066886726873 190091846719237550165045155)
            ·
              refine ⟨285137770078856325247567733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190091846719237550165045155 285137770078856325247567733)
              ·
                refine ⟨26731665944892780491959475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285137770078856325247567733 26731665944892780491959475)
                ·
                  refine ⟨40097498917339170737939213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26731665944892780491959475 40097498917339170737939213)
                  ·
                    refine ⟨15036562094002189026727205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40097498917339170737939213 15036562094002189026727205)
                    ·
                      refine ⟨2819355392625410442511351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15036562094002189026727205 2819355392625410442511351)
                      ·
                        rfl

theorem cell23_5490675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_5490675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490675 prefixEnd_5490675 := by exact prefixLift 5490675
  have htrace : WordTrace (prefixWord ++ tailWord_5490675) baseStart_5490675 baseEnd_5490675 := by
    simpa [prefixWord, tailWord_5490675, baseEnd_5490675] using wordTrace_append hprefix tailTrace_5490675
  have hstable : (prefixWord ++ tailWord_5490675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490675).length < 2 ^ (prefixWord ++ tailWord_5490675).sum := by decide
  have hdescent : baseEnd_5490675 < baseStart_5490675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490705 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_5490705 : Nat := 118140960795 + 5490705 * 2 ^ 59
def prefixEnd_5490705 : Nat := 4983230072969 + 3 ^ 40 * 5490705 * 2
def baseEnd_5490705 : Nat := 2819370797045045325136213

theorem tailTrace_5490705 : CollatzResearch.WordTrace tailWord_5490705 prefixEnd_5490705 2819370797045045325136213 := by
  unfold tailWord_5490705
  simp only [CollatzResearch.WordTrace]
  refine ⟨200262463573120997601993569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133508309048747331734662379 200262463573120997601993569)
  ·
    refine ⟨150196847679840748201495177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200262463573120997601993569 150196847679840748201495177)
    ·
      refine ⟨112647635759880561151121383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150196847679840748201495177 112647635759880561151121383)
      ·
        refine ⟨168971453639820841726682075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112647635759880561151121383 168971453639820841726682075)
        ·
          refine ⟨253457180459731262590023113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168971453639820841726682075 253457180459731262590023113)
          ·
            refine ⟨190092885344798446942517335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253457180459731262590023113 190092885344798446942517335)
            ·
              refine ⟨285139328017197670413776003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190092885344798446942517335 285139328017197670413776003)
              ·
                refine ⟨427708992025796505620664005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285139328017197670413776003 427708992025796505620664005)
                ·
                  refine ⟨80195436004836844803874501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 427708992025796505620664005 80195436004836844803874501)
                  ·
                    refine ⟨15036644250906908400726469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80195436004836844803874501 15036644250906908400726469)
                    ·
                      refine ⟨2819370797045045325136213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15036644250906908400726469 2819370797045045325136213)
                      ·
                        rfl

theorem cell23_5490705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_5490705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490705 prefixEnd_5490705 := by exact prefixLift 5490705
  have htrace : WordTrace (prefixWord ++ tailWord_5490705) baseStart_5490705 baseEnd_5490705 := by
    simpa [prefixWord, tailWord_5490705, baseEnd_5490705] using wordTrace_append hprefix tailTrace_5490705
  have hstable : (prefixWord ++ tailWord_5490705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490705).length < 2 ^ (prefixWord ++ tailWord_5490705).sum := by decide
  have hdescent : baseEnd_5490705 < baseStart_5490705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490712 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_5490712 : Nat := 118140960795 + 5490712 * 2 ^ 59
def prefixEnd_5490712 : Nat := 4983230072969 + 3 ^ 40 * 5490712 * 2
def baseEnd_5490712 : Nat := 2819374391409626797748681

theorem tailTrace_5490712 : CollatzResearch.WordTrace tailWord_5490712 prefixEnd_5490712 2819374391409626797748681 := by
  unfold tailWord_5490712
  simp only [CollatzResearch.WordTrace]
  refine ⟨100131359442047818898749195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133508479256063758531665593 100131359442047818898749195)
  ·
    refine ⟨150197039163071728348123793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100131359442047818898749195 150197039163071728348123793)
    ·
      refine ⟨112647779372303796261092845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150197039163071728348123793 112647779372303796261092845)
      ·
        refine ⟨42242917264613923597909817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112647779372303796261092845 42242917264613923597909817)
        ·
          refine ⟨31682187948460442698432363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42242917264613923597909817 31682187948460442698432363)
          ·
            refine ⟨47523281922690664047648545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31682187948460442698432363 47523281922690664047648545)
            ·
              refine ⟨35642461442017998035736409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47523281922690664047648545 35642461442017998035736409)
              ·
                refine ⟨26731846081513498526802307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35642461442017998035736409 26731846081513498526802307)
                ·
                  refine ⟨40097769122270247790203461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26731846081513498526802307 40097769122270247790203461)
                  ·
                    refine ⟨7518331710425671460663149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40097769122270247790203461 7518331710425671460663149)
                    ·
                      refine ⟨2819374391409626797748681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7518331710425671460663149 2819374391409626797748681)
                      ·
                        rfl

theorem cell23_5490712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_5490712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490712 prefixEnd_5490712 := by exact prefixLift 5490712
  have htrace : WordTrace (prefixWord ++ tailWord_5490712) baseStart_5490712 baseEnd_5490712 := by
    simpa [prefixWord, tailWord_5490712, baseEnd_5490712] using wordTrace_append hprefix tailTrace_5490712
  have hstable : (prefixWord ++ tailWord_5490712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490712).length < 2 ^ (prefixWord ++ tailWord_5490712).sum := by decide
  have hdescent : baseEnd_5490712 < baseStart_5490712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490736 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 1, 4]
def baseStart_5490736 : Nat := 118140960795 + 5490736 * 2 ^ 59
def prefixEnd_5490736 : Nat := 4983230072969 + 3 ^ 40 * 5490736 * 2
def baseEnd_5490736 : Nat := 939795571648444901282857

theorem tailTrace_5490736 : CollatzResearch.WordTrace tailWord_5490736 prefixEnd_5490736 939795571648444901282857 := by
  unfold tailWord_5490736
  simp only [CollatzResearch.WordTrace]
  refine ⟨100131797118004344948186031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133509062824005793264248041 100131797118004344948186031)
  ·
    refine ⟨150197695677006517422279047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100131797118004344948186031 150197695677006517422279047)
    ·
      refine ⟨225296543515509776133418571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150197695677006517422279047 225296543515509776133418571)
      ·
        refine ⟨337944815273264664200127857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225296543515509776133418571 337944815273264664200127857)
        ·
          refine ⟨253458611454948498150095893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337944815273264664200127857 253458611454948498150095893)
          ·
            refine ⟨11880872411950710850785745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253458611454948498150095893 11880872411950710850785745)
            ·
              refine ⟨8910654308963033138089309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11880872411950710850785745 8910654308963033138089309)
              ·
                refine ⟨3341495365861137426783491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8910654308963033138089309 3341495365861137426783491)
                ·
                  refine ⟨5012243048791706140175237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341495365861137426783491 5012243048791706140175237)
                  ·
                    refine ⟨939795571648444901282857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012243048791706140175237 939795571648444901282857)
                    ·
                      rfl

theorem cell23_5490736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 4].length) (baseStart_5490736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490736 prefixEnd_5490736 := by exact prefixLift 5490736
  have htrace : WordTrace (prefixWord ++ tailWord_5490736) baseStart_5490736 baseEnd_5490736 := by
    simpa [prefixWord, tailWord_5490736, baseEnd_5490736] using wordTrace_append hprefix tailTrace_5490736
  have hstable : (prefixWord ++ tailWord_5490736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490736).length < 2 ^ (prefixWord ++ tailWord_5490736).sum := by decide
  have hdescent : baseEnd_5490736 < baseStart_5490736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490755 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_5490755 : Nat := 118140960795 + 5490755 * 2 ^ 59
def prefixEnd_5490755 : Nat := 4983230072969 + 3 ^ 40 * 5490755 * 2
def baseEnd_5490755 : Nat := 2819396471077770129510983

theorem tailTrace_5490755 : CollatzResearch.WordTrace tailWord_5490755 prefixEnd_5490755 2819396471077770129510983 := by
  unfold tailWord_5490755
  simp only [CollatzResearch.WordTrace]
  refine ⟨200264287222939856141313719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133509524815293237427542479 200264287222939856141313719)
  ·
    refine ⟨300396430834409784211970579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200264287222939856141313719 300396430834409784211970579)
    ·
      refine ⟨450594646251614676317955869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300396430834409784211970579 450594646251614676317955869)
      ·
        refine ⟨168972992344355503619233451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450594646251614676317955869 168972992344355503619233451)
        ·
          refine ⟨253459488516533255428850177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168972992344355503619233451 253459488516533255428850177)
          ·
            refine ⟨190094616387399941571637633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253459488516533255428850177 190094616387399941571637633)
            ·
              refine ⟨142570962290549956178728225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190094616387399941571637633 142570962290549956178728225)
              ·
                refine ⟨106928221717912467134046169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142570962290549956178728225 106928221717912467134046169)
                ·
                  refine ⟨80196166288434350350534627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106928221717912467134046169 80196166288434350350534627)
                  ·
                    refine ⟨120294249432651525525801941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80196166288434350350534627 120294249432651525525801941)
                    ·
                      refine ⟨2819396471077770129510983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120294249432651525525801941 2819396471077770129510983)
                      ·
                        rfl

theorem cell23_5490755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_5490755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490755 prefixEnd_5490755 := by exact prefixLift 5490755
  have htrace : WordTrace (prefixWord ++ tailWord_5490755) baseStart_5490755 baseEnd_5490755 := by
    simpa [prefixWord, tailWord_5490755, baseEnd_5490755] using wordTrace_append hprefix tailTrace_5490755
  have hstable : (prefixWord ++ tailWord_5490755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490755).length < 2 ^ (prefixWord ++ tailWord_5490755).sum := by decide
  have hdescent : baseEnd_5490755 < baseStart_5490755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490799 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_5490799 : Nat := 118140960795 + 5490799 * 2 ^ 59
def prefixEnd_5490799 : Nat := 4983230072969 + 3 ^ 40 * 5490799 * 2
def baseEnd_5490799 : Nat := 2819419064226567957360781

theorem tailTrace_5490799 : CollatzResearch.WordTrace tailWord_5490799 prefixEnd_5490799 2819419064226567957360781 := by
  unfold tailWord_5490799
  simp only [CollatzResearch.WordTrace]
  refine ⟨200265892034780451655915451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133510594689853634437276967 200265892034780451655915451)
  ·
    refine ⟨300398838052170677483873177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200265892034780451655915451 300398838052170677483873177)
    ·
      refine ⟨225299128539128008112904883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300398838052170677483873177 225299128539128008112904883)
      ·
        refine ⟨337948692808692012169357325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225299128539128008112904883 337948692808692012169357325)
        ·
          refine ⟨126730759803259504563508997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337948692808692012169357325 126730759803259504563508997)
          ·
            refine ⟨23762017463111157105657937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126730759803259504563508997 23762017463111157105657937)
            ·
              refine ⟨17821513097333367829243453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23762017463111157105657937 17821513097333367829243453)
              ·
                refine ⟨6683067411500012935966295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17821513097333367829243453 6683067411500012935966295)
                ·
                  refine ⟨10024601117250019403949443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683067411500012935966295 10024601117250019403949443)
                  ·
                    refine ⟨15036901675875029105924165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10024601117250019403949443 15036901675875029105924165)
                    ·
                      refine ⟨2819419064226567957360781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15036901675875029105924165 2819419064226567957360781)
                      ·
                        rfl

theorem cell23_5490799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_5490799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490799 prefixEnd_5490799 := by exact prefixLift 5490799
  have htrace : WordTrace (prefixWord ++ tailWord_5490799) baseStart_5490799 baseEnd_5490799 := by
    simpa [prefixWord, tailWord_5490799, baseEnd_5490799] using wordTrace_append hprefix tailTrace_5490799
  have hstable : (prefixWord ++ tailWord_5490799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490799).length < 2 ^ (prefixWord ++ tailWord_5490799).sum := by decide
  have hdescent : baseEnd_5490799 < baseStart_5490799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490809 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_5490809 : Nat := 118140960795 + 5490809 * 2 ^ 59
def prefixEnd_5490809 : Nat := 4983230072969 + 3 ^ 40 * 5490809 * 2
def baseEnd_5490809 : Nat := 939808066344370972745245

theorem tailTrace_5490809 : CollatzResearch.WordTrace tailWord_5490809 prefixEnd_5490809 939808066344370972745245 := by
  unfold tailWord_5490809
  simp only [CollatzResearch.WordTrace]
  refine ⟨200266256764744223363779481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133510837843162815575852987 200266256764744223363779481)
  ·
    refine ⟨150199692573558167522834611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200266256764744223363779481 150199692573558167522834611)
    ·
      refine ⟨225299538860337251284251917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150199692573558167522834611 225299538860337251284251917)
      ·
        refine ⟨84487327072626469231594469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225299538860337251284251917 84487327072626469231594469)
        ·
          refine ⟨15841373826117462980923963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84487327072626469231594469 15841373826117462980923963)
          ·
            refine ⟨23762060739176194471385945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15841373826117462980923963 23762060739176194471385945)
            ·
              refine ⟨17821545554382145853539459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23762060739176194471385945 17821545554382145853539459)
              ·
                refine ⟨26732318331573218780309189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17821545554382145853539459 26732318331573218780309189)
                ·
                  refine ⟨5012309687169978521307973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26732318331573218780309189 5012309687169978521307973)
                  ·
                    refine ⟨939808066344370972745245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012309687169978521307973 939808066344370972745245)
                    ·
                      rfl

theorem cell23_5490809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_5490809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490809 prefixEnd_5490809 := by exact prefixLift 5490809
  have htrace : WordTrace (prefixWord ++ tailWord_5490809) baseStart_5490809 baseEnd_5490809 := by
    simpa [prefixWord, tailWord_5490809, baseEnd_5490809] using wordTrace_append hprefix tailTrace_5490809
  have hstable : (prefixWord ++ tailWord_5490809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490809).length < 2 ^ (prefixWord ++ tailWord_5490809).sum := by decide
  have hdescent : baseEnd_5490809 < baseStart_5490809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490812 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_5490812 : Nat := 118140960795 + 5490812 * 2 ^ 59
def prefixEnd_5490812 : Nat := 4983230072969 + 3 ^ 40 * 5490812 * 2
def baseEnd_5490812 : Nat := 2819425739475076406498221

theorem tailTrace_5490812 : CollatzResearch.WordTrace tailWord_5490812 prefixEnd_5490812 2819425739475076406498221 := by
  unfold tailWord_5490812
  simp only [CollatzResearch.WordTrace]
  refine ⟨100133183091866677438069345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133510910789155569917425793 100133183091866677438069345)
  ·
    refine ⟨75099887318900008078552009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100133183091866677438069345 75099887318900008078552009)
    ·
      refine ⟨56324915489175006058914007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75099887318900008078552009 56324915489175006058914007)
      ·
        refine ⟨84487373233762509088371011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56324915489175006058914007 84487373233762509088371011)
        ·
          refine ⟨126731059850643763632556517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84487373233762509088371011 126731059850643763632556517)
          ·
            refine ⟨23762073721995705681104347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126731059850643763632556517 23762073721995705681104347)
            ·
              refine ⟨35643110582993558521656521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23762073721995705681104347 35643110582993558521656521)
              ·
                refine ⟨26732332937245168891242391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35643110582993558521656521 26732332937245168891242391)
                ·
                  refine ⟨40098499405867753336863587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26732332937245168891242391 40098499405867753336863587)
                  ·
                    refine ⟨60147749108801630005295381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40098499405867753336863587 60147749108801630005295381)
                    ·
                      refine ⟨2819425739475076406498221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60147749108801630005295381 2819425739475076406498221)
                      ·
                        rfl

theorem cell23_5490812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_5490812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490812 prefixEnd_5490812 := by exact prefixLift 5490812
  have htrace : WordTrace (prefixWord ++ tailWord_5490812) baseStart_5490812 baseEnd_5490812 := by
    simpa [prefixWord, tailWord_5490812, baseEnd_5490812] using wordTrace_append hprefix tailTrace_5490812
  have hstable : (prefixWord ++ tailWord_5490812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490812).length < 2 ^ (prefixWord ++ tailWord_5490812).sum := by decide
  have hdescent : baseEnd_5490812 < baseStart_5490812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490826 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_5490826 : Nat := 118140960795 + 5490826 * 2 ^ 59
def prefixEnd_5490826 : Nat := 4983230072969 + 3 ^ 40 * 5490826 * 2
def baseEnd_5490826 : Nat := 939810976068079783907719

theorem tailTrace_5490826 : CollatzResearch.WordTrace tailWord_5490826 prefixEnd_5490826 939810976068079783907719 := by
  unfold tailWord_5490826
  simp only [CollatzResearch.WordTrace]
  refine ⟨50066719201420658816787083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133511251203788423511432221 50066719201420658816787083)
  ·
    refine ⟨75100078802130988225180625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50066719201420658816787083 75100078802130988225180625)
    ·
      refine ⟨56325059101598241168885469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75100078802130988225180625 56325059101598241168885469)
      ·
        refine ⟨21121897163099340438332051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56325059101598241168885469 21121897163099340438332051)
        ·
          refine ⟨31682845744649010657498077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21121897163099340438332051 31682845744649010657498077)
          ·
            refine ⟨11881067154243378996561779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31682845744649010657498077 11881067154243378996561779)
            ·
              refine ⟨17821600731365068494842669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881067154243378996561779 17821600731365068494842669)
              ·
                refine ⟨6683100274261900685566001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17821600731365068494842669 6683100274261900685566001)
                ·
                  refine ⟨5012325205696425514174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6683100274261900685566001 5012325205696425514174501)
                  ·
                    refine ⟨939810976068079783907719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012325205696425514174501 939810976068079783907719)
                    ·
                      rfl

theorem cell23_5490826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_5490826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490826 prefixEnd_5490826 := by exact prefixLift 5490826
  have htrace : WordTrace (prefixWord ++ tailWord_5490826) baseStart_5490826 baseEnd_5490826 := by
    simpa [prefixWord, tailWord_5490826, baseEnd_5490826] using wordTrace_append hprefix tailTrace_5490826
  have hstable : (prefixWord ++ tailWord_5490826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490826).length < 2 ^ (prefixWord ++ tailWord_5490826).sum := by decide
  have hdescent : baseEnd_5490826 < baseStart_5490826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490849 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5490849 : Nat := 118140960795 + 5490849 * 2 ^ 59
def prefixEnd_5490849 : Nat := 4983230072969 + 3 ^ 40 * 5490849 * 2
def baseEnd_5490849 : Nat := 2819444738259292761735551

theorem tailTrace_5490849 : CollatzResearch.WordTrace tailWord_5490849 prefixEnd_5490849 2819444738259292761735551 := by
  unfold tailWord_5490849
  simp only [CollatzResearch.WordTrace]
  refine ⟨200267715684599310195235601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133511810456399540130157067 200267715684599310195235601)
  ·
    refine ⟨150200786763449482646426701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200267715684599310195235601 150200786763449482646426701)
    ·
      refine ⟨56325295036293555992410013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150200786763449482646426701 56325295036293555992410013)
      ·
        refine ⟨21121985638610083497153755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56325295036293555992410013 21121985638610083497153755)
        ·
          refine ⟨31682978457915125245730633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21121985638610083497153755 31682978457915125245730633)
          ·
            refine ⟨23762233843436343934297975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31682978457915125245730633 23762233843436343934297975)
            ·
              refine ⟨35643350765154515901446963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23762233843436343934297975 35643350765154515901446963)
              ·
                refine ⟨53465026147731773852170445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35643350765154515901446963 53465026147731773852170445)
                ·
                  refine ⟨20049384805399415194563917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53465026147731773852170445 20049384805399415194563917)
                  ·
                    refine ⟨7518519302024780697961469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20049384805399415194563917 7518519302024780697961469)
                    ·
                      refine ⟨2819444738259292761735551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7518519302024780697961469 2819444738259292761735551)
                      ·
                        rfl

theorem cell23_5490849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5490849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490849 prefixEnd_5490849 := by exact prefixLift 5490849
  have htrace : WordTrace (prefixWord ++ tailWord_5490849) baseStart_5490849 baseEnd_5490849 := by
    simpa [prefixWord, tailWord_5490849, baseEnd_5490849] using wordTrace_append hprefix tailTrace_5490849
  have hstable : (prefixWord ++ tailWord_5490849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490849).length < 2 ^ (prefixWord ++ tailWord_5490849).sum := by decide
  have hdescent : baseEnd_5490849 < baseStart_5490849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490872 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_5490872 : Nat := 118140960795 + 5490872 * 2 ^ 59
def prefixEnd_5490872 : Nat := 4983230072969 + 3 ^ 40 * 5490872 * 2
def baseEnd_5490872 : Nat := 2819456548314346171747945

theorem tailTrace_5490872 : CollatzResearch.WordTrace tailWord_5490872 prefixEnd_5490872 2819456548314346171747945 := by
  unfold tailWord_5490872
  simp only [CollatzResearch.WordTrace]
  refine ⟨100134277281757992561661435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133512369709010656748881913 100134277281757992561661435)
  ·
    refine ⟨150201415922636988842492153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100134277281757992561661435 150201415922636988842492153)
    ·
      refine ⟨112651061941977741631869115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150201415922636988842492153 112651061941977741631869115)
      ·
        refine ⟨168976592912966612447803673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112651061941977741631869115 168976592912966612447803673)
        ·
          refine ⟨126732444684724959335852755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168976592912966612447803673 126732444684724959335852755)
          ·
            refine ⟨190098667027087439003779133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126732444684724959335852755 190098667027087439003779133)
            ·
              refine ⟨71287000135157789626417175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190098667027087439003779133 71287000135157789626417175)
              ·
                refine ⟨106930500202736684439625763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71287000135157789626417175 106930500202736684439625763)
                ·
                  refine ⟨160395750304105026659438645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106930500202736684439625763 160395750304105026659438645)
                  ·
                    refine ⟨15037101591009846249322373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160395750304105026659438645 15037101591009846249322373)
                    ·
                      refine ⟨2819456548314346171747945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15037101591009846249322373 2819456548314346171747945)
                      ·
                        rfl

theorem cell23_5490872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_5490872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490872 prefixEnd_5490872 := by exact prefixLift 5490872
  have htrace : WordTrace (prefixWord ++ tailWord_5490872) baseStart_5490872 baseEnd_5490872 := by
    simpa [prefixWord, tailWord_5490872, baseEnd_5490872] using wordTrace_append hprefix tailTrace_5490872
  have hstable : (prefixWord ++ tailWord_5490872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490872).length < 2 ^ (prefixWord ++ tailWord_5490872).sum := by decide
  have hdescent : baseEnd_5490872 < baseStart_5490872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490906 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_5490906 : Nat := 118140960795 + 5490906 * 2 ^ 59
def prefixEnd_5490906 : Nat := 4983230072969 + 3 ^ 40 * 5490906 * 2
def baseEnd_5490906 : Nat := 2819474006656599038722789

theorem tailTrace_5490906 : CollatzResearch.WordTrace tailWord_5490906 prefixEnd_5490906 2819474006656599038722789 := by
  unfold tailWord_5490906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50067448661348202232515143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133513196430261872620040381 50067448661348202232515143)
  ·
    refine ⟨75101172992022303348772715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50067448661348202232515143 75101172992022303348772715)
    ·
      refine ⟨112651759488033455023159073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75101172992022303348772715 112651759488033455023159073)
      ·
        refine ⟨84488819616025091267369305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112651759488033455023159073 84488819616025091267369305)
        ·
          refine ⟨63366614712018818450526979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84488819616025091267369305 63366614712018818450526979)
          ·
            refine ⟨95049922068028227675790469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63366614712018818450526979 95049922068028227675790469)
            ·
              refine ⟨17821860387755292689210713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95049922068028227675790469 17821860387755292689210713)
              ·
                refine ⟨13366395290816469516908035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17821860387755292689210713 13366395290816469516908035)
                ·
                  refine ⟨20049592936224704275362053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13366395290816469516908035 20049592936224704275362053)
                  ·
                    refine ⟨3759298675542132051630385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20049592936224704275362053 3759298675542132051630385)
                    ·
                      refine ⟨2819474006656599038722789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759298675542132051630385 2819474006656599038722789)
                      ·
                        rfl

theorem cell23_5490906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_5490906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490906 prefixEnd_5490906 := by exact prefixLift 5490906
  have htrace : WordTrace (prefixWord ++ tailWord_5490906) baseStart_5490906 baseEnd_5490906 := by
    simpa [prefixWord, tailWord_5490906, baseEnd_5490906] using wordTrace_append hprefix tailTrace_5490906
  have hstable : (prefixWord ++ tailWord_5490906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490906).length < 2 ^ (prefixWord ++ tailWord_5490906).sum := by decide
  have hdescent : baseEnd_5490906 < baseStart_5490906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490912 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 9]
def baseStart_5490912 : Nat := 118140960795 + 5490912 * 2 ^ 59
def prefixEnd_5490912 : Nat := 4983230072969 + 3 ^ 40 * 5490912 * 2
def baseEnd_5490912 : Nat := 313275231948947335027529

theorem tailTrace_5490912 : CollatzResearch.WordTrace tailWord_5490912 prefixEnd_5490912 313275231948947335027529 := by
  unfold tailWord_5490912
  simp only [CollatzResearch.WordTrace]
  refine ⟨100135006741685535977389495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133513342322247381303185993 100135006741685535977389495)
  ·
    refine ⟨150202510112528303966084243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100135006741685535977389495 150202510112528303966084243)
    ·
      refine ⟨225303765168792455949126365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150202510112528303966084243 225303765168792455949126365)
      ·
        refine ⟨84488911938297170980922387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225303765168792455949126365 84488911938297170980922387)
        ·
          refine ⟨126733367907445756471383581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84488911938297170980922387 126733367907445756471383581)
          ·
            refine ⟨47525012965292158676768843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126733367907445756471383581 47525012965292158676768843)
            ·
              refine ⟨71287519447938238015153265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47525012965292158676768843 71287519447938238015153265)
              ·
                refine ⟨53465639585953678511364949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71287519447938238015153265 53465639585953678511364949)
                ·
                  refine ⟨313275231948947335027529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53465639585953678511364949 313275231948947335027529)
                  ·
                    rfl

theorem cell23_5490912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_5490912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490912 prefixEnd_5490912 := by exact prefixLift 5490912
  have htrace : WordTrace (prefixWord ++ tailWord_5490912) baseStart_5490912 baseEnd_5490912 := by
    simpa [prefixWord, tailWord_5490912, baseEnd_5490912] using wordTrace_append hprefix tailTrace_5490912
  have hstable : (prefixWord ++ tailWord_5490912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490912).length < 2 ^ (prefixWord ++ tailWord_5490912).sum := by decide
  have hdescent : baseEnd_5490912 < baseStart_5490912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490946 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_5490946 : Nat := 118140960795 + 5490946 * 2 ^ 59
def prefixEnd_5490946 : Nat := 4983230072969 + 3 ^ 40 * 5490946 * 2
def baseEnd_5490946 : Nat := 313277171764753209135845

theorem tailTrace_5490946 : CollatzResearch.WordTrace tailWord_5490946 prefixEnd_5490946 313277171764753209135845 := by
  unfold tailWord_5490946
  simp only [CollatzResearch.WordTrace]
  refine ⟨50067813391311973940379173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133514169043498597174344461 50067813391311973940379173)
  ·
    refine ⟨9387715010870995113821095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50067813391311973940379173 9387715010870995113821095)
    ·
      refine ⟨14081572516306492670731643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9387715010870995113821095 14081572516306492670731643)
      ·
        refine ⟨21122358774459739006097465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14081572516306492670731643 21122358774459739006097465)
        ·
          refine ⟨15841769080844804254573099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21122358774459739006097465 15841769080844804254573099)
          ·
            refine ⟨23762653621267206381859649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15841769080844804254573099 23762653621267206381859649)
            ·
              refine ⟨17821990215950404786394737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23762653621267206381859649 17821990215950404786394737)
              ·
                refine ⟨13366492661962803589796053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17821990215950404786394737 13366492661962803589796053)
                ·
                  refine ⟨313277171764753209135845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13366492661962803589796053 313277171764753209135845)
                  ·
                    rfl

theorem cell23_5490946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_5490946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490946 prefixEnd_5490946 := by exact prefixLift 5490946
  have htrace : WordTrace (prefixWord ++ tailWord_5490946) baseStart_5490946 baseEnd_5490946 := by
    simpa [prefixWord, tailWord_5490946, baseEnd_5490946] using wordTrace_append hprefix tailTrace_5490946
  have hstable : (prefixWord ++ tailWord_5490946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490946).length < 2 ^ (prefixWord ++ tailWord_5490946).sum := by decide
  have hdescent : baseEnd_5490946 < baseStart_5490946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490976 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_5490976 : Nat := 118140960795 + 5490976 * 2 ^ 59
def prefixEnd_5490976 : Nat := 4983230072969 + 3 ^ 40 * 5490976 * 2
def baseEnd_5490976 : Nat := 939836650100804588282489

theorem tailTrace_5490976 : CollatzResearch.WordTrace tailWord_5490976 prefixEnd_5490976 939836650100804588282489 := by
  unfold tailWord_5490976
  simp only [CollatzResearch.WordTrace]
  refine ⟨100136173877569605442554391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133514898503426140590072521 100136173877569605442554391)
  ·
    refine ⟨150204260816354408163831587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100136173877569605442554391 150204260816354408163831587)
    ·
      refine ⟨225306391224531612245747381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150204260816354408163831587 225306391224531612245747381)
      ·
        refine ⟨21122474177299838648038817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225306391224531612245747381 21122474177299838648038817)
        ·
          refine ⟨15841855632974878986029113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21122474177299838648038817 15841855632974878986029113)
          ·
            refine ⟨11881391724731159239521835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15841855632974878986029113 11881391724731159239521835)
            ·
              refine ⟨17822087587096738859282753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881391724731159239521835 17822087587096738859282753)
              ·
                refine ⟨13366565690322554144462065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17822087587096738859282753 13366565690322554144462065)
                ·
                  refine ⟨10024924267741915608346549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13366565690322554144462065 10024924267741915608346549)
                  ·
                    refine ⟨939836650100804588282489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10024924267741915608346549 939836650100804588282489)
                    ·
                      rfl

theorem cell23_5490976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_5490976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490976 prefixEnd_5490976 := by exact prefixLift 5490976
  have htrace : WordTrace (prefixWord ++ tailWord_5490976) baseStart_5490976 baseEnd_5490976 := by
    simpa [prefixWord, tailWord_5490976, baseEnd_5490976] using wordTrace_append hprefix tailTrace_5490976
  have hstable : (prefixWord ++ tailWord_5490976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490976).length < 2 ^ (prefixWord ++ tailWord_5490976).sum := by decide
  have hdescent : baseEnd_5490976 < baseStart_5490976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5490999 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_5490999 : Nat := 118140960795 + 5490999 * 2 ^ 59
def prefixEnd_5490999 : Nat := 4983230072969 + 3 ^ 40 * 5490999 * 2
def baseEnd_5490999 : Nat := 2819521760357467174859861

theorem tailTrace_5490999 : CollatzResearch.WordTrace tailWord_5490999 prefixEnd_5490999 2819521760357467174859861 := by
  unfold tailWord_5490999
  simp only [CollatzResearch.WordTrace]
  refine ⟨200273186634055885813196051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133515457756037257208797367 200273186634055885813196051)
  ·
    refine ⟨300409779951083828719794077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200273186634055885813196051 300409779951083828719794077)
    ·
      refine ⟨112653667481656435769922779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300409779951083828719794077 112653667481656435769922779)
      ·
        refine ⟨168980501222484653654884169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112653667481656435769922779 168980501222484653654884169)
        ·
          refine ⟨126735375916863490241163127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168980501222484653654884169 126735375916863490241163127)
          ·
            refine ⟨190103063875295235361744691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126735375916863490241163127 190103063875295235361744691)
            ·
              refine ⟨285154595812942853042617037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190103063875295235361744691 285154595812942853042617037)
              ·
                refine ⟨106932973429853569890981389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285154595812942853042617037 106932973429853569890981389)
                ·
                  refine ⟨40099865036195088709118021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106932973429853569890981389 40099865036195088709118021)
                  ·
                    refine ⟨7518724694286579132959629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40099865036195088709118021 7518724694286579132959629)
                    ·
                      refine ⟨2819521760357467174859861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7518724694286579132959629 2819521760357467174859861)
                      ·
                        rfl

theorem cell23_5490999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_5490999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5490999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5490999 prefixEnd_5490999 := by exact prefixLift 5490999
  have htrace : WordTrace (prefixWord ++ tailWord_5490999) baseStart_5490999 baseEnd_5490999 := by
    simpa [prefixWord, tailWord_5490999, baseEnd_5490999] using wordTrace_append hprefix tailTrace_5490999
  have hstable : (prefixWord ++ tailWord_5490999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5490999).length < 2 ^ (prefixWord ++ tailWord_5490999).sum := by decide
  have hdescent : baseEnd_5490999 < baseStart_5490999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5490999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491016 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_5491016 : Nat := 118140960795 + 5491016 * 2 ^ 59
def prefixEnd_5491016 : Nat := 4983230072969 + 3 ^ 40 * 5491016 * 2
def baseEnd_5491016 : Nat := 2819530489528593608347283

theorem tailTrace_5491016 : CollatzResearch.WordTrace tailWord_5491016 prefixEnd_5491016 2819530489528593608347283 := by
  unfold tailWord_5491016
  simp only [CollatzResearch.WordTrace]
  refine ⟨100136903337497148858282451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133515871116662865144376601 100136903337497148858282451)
  ·
    refine ⟨150205355006245723287423677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100136903337497148858282451 150205355006245723287423677)
    ·
      refine ⟨56327008127342146232783879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150205355006245723287423677 56327008127342146232783879)
      ·
        refine ⟨84490512191013219349175819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56327008127342146232783879 84490512191013219349175819)
        ·
          refine ⟨126735768286519829023763729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84490512191013219349175819 126735768286519829023763729)
          ·
            refine ⟨95051826214889871767822797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126735768286519829023763729 95051826214889871767822797)
            ·
              refine ⟨35644434830583701912933549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95051826214889871767822797 35644434830583701912933549)
              ·
                refine ⟨13366663061468888217350081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35644434830583701912933549 13366663061468888217350081)
                ·
                  refine ⟨10024997296101666163012561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13366663061468888217350081 10024997296101666163012561)
                  ·
                    refine ⟨7518747972076249622259421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10024997296101666163012561 7518747972076249622259421)
                    ·
                      refine ⟨2819530489528593608347283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7518747972076249622259421 2819530489528593608347283)
                      ·
                        rfl

theorem cell23_5491016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_5491016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491016 prefixEnd_5491016 := by exact prefixLift 5491016
  have htrace : WordTrace (prefixWord ++ tailWord_5491016) baseStart_5491016 baseEnd_5491016 := by
    simpa [prefixWord, tailWord_5491016, baseEnd_5491016] using wordTrace_append hprefix tailTrace_5491016
  have hstable : (prefixWord ++ tailWord_5491016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491016).length < 2 ^ (prefixWord ++ tailWord_5491016).sum := by decide
  have hdescent : baseEnd_5491016 < baseStart_5491016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491040 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 1, 4]
def baseStart_5491040 : Nat := 118140960795 + 5491040 * 2 ^ 59
def prefixEnd_5491040 : Nat := 4983230072969 + 3 ^ 40 * 5491040 * 2
def baseEnd_5491040 : Nat := 939847604354767171482391

theorem tailTrace_5491040 : CollatzResearch.WordTrace tailWord_5491040 prefixEnd_5491040 939847604354767171482391 := by
  unfold tailWord_5491040
  simp only [CollatzResearch.WordTrace]
  refine ⟨100137341013453674907719287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133516454684604899876959049 100137341013453674907719287)
  ·
    refine ⟨150206011520180512361578931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100137341013453674907719287 150206011520180512361578931)
    ·
      refine ⟨225309017280270768542368397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150206011520180512361578931 225309017280270768542368397)
      ·
        refine ⟨84490881480101538203388149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225309017280270768542368397 84490881480101538203388149)
        ·
          refine ⟨7921020138759519206567639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84490881480101538203388149 7921020138759519206567639)
          ·
            refine ⟨11881530208139278809851459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921020138759519206567639 11881530208139278809851459)
            ·
              refine ⟨17822295312208918214777189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881530208139278809851459 17822295312208918214777189)
              ·
                refine ⟨3341680371039172165270723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17822295312208918214777189 3341680371039172165270723)
                ·
                  refine ⟨5012520556558758247906085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341680371039172165270723 5012520556558758247906085)
                  ·
                    refine ⟨939847604354767171482391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012520556558758247906085 939847604354767171482391)
                    ·
                      rfl

theorem cell23_5491040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 4].length) (baseStart_5491040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491040 prefixEnd_5491040 := by exact prefixLift 5491040
  have htrace : WordTrace (prefixWord ++ tailWord_5491040) baseStart_5491040 baseEnd_5491040 := by
    simpa [prefixWord, tailWord_5491040, baseEnd_5491040] using wordTrace_append hprefix tailTrace_5491040
  have hstable : (prefixWord ++ tailWord_5491040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491040).length < 2 ^ (prefixWord ++ tailWord_5491040).sum := by decide
  have hdescent : baseEnd_5491040 < baseStart_5491040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491049 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_5491049 : Nat := 118140960795 + 5491049 * 2 ^ 59
def prefixEnd_5491049 : Nat := 4983230072969 + 3 ^ 40 * 5491049 * 2
def baseEnd_5491049 : Nat := 939849144796730659744877

theorem tailTrace_5491049 : CollatzResearch.WordTrace tailWord_5491049 prefixEnd_5491049 939849144796730659744877 := by
  unfold tailWord_5491049
  simp only [CollatzResearch.WordTrace]
  refine ⟨200275010283874744352516201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133516673522583162901677467 200275010283874744352516201)
  ·
    refine ⟨150206257712906058264387151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200275010283874744352516201 150206257712906058264387151)
    ·
      refine ⟨225309386569359087396580727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150206257712906058264387151 225309386569359087396580727)
      ·
        refine ⟨337964079854038631094871091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225309386569359087396580727 337964079854038631094871091)
        ·
          refine ⟨506946119781057946642306637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337964079854038631094871091 506946119781057946642306637)
          ·
            refine ⟨190104794917896729990864989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506946119781057946642306637 190104794917896729990864989)
            ·
              refine ⟨71289298094211273746574371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190104794917896729990864989 71289298094211273746574371)
              ·
                refine ⟨106933947141316910619861557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71289298094211273746574371 106933947141316910619861557)
                ·
                  refine ⟨10025057544498460370612021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106933947141316910619861557 10025057544498460370612021)
                  ·
                    refine ⟨939849144796730659744877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10025057544498460370612021 939849144796730659744877)
                    ·
                      rfl

theorem cell23_5491049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_5491049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491049 prefixEnd_5491049 := by exact prefixLift 5491049
  have htrace : WordTrace (prefixWord ++ tailWord_5491049) baseStart_5491049 baseEnd_5491049 := by
    simpa [prefixWord, tailWord_5491049, baseEnd_5491049] using wordTrace_append hprefix tailTrace_5491049
  have hstable : (prefixWord ++ tailWord_5491049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491049).length < 2 ^ (prefixWord ++ tailWord_5491049).sum := by decide
  have hdescent : baseEnd_5491049 < baseStart_5491049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491074 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5491074 : Nat := 118140960795 + 5491074 * 2 ^ 59
def prefixEnd_5491074 : Nat := 4983230072969 + 3 ^ 40 * 5491074 * 2
def baseEnd_5491074 : Nat := 939853423802184793807339

theorem tailTrace_5491074 : CollatzResearch.WordTrace tailWord_5491074 prefixEnd_5491074 939853423802184793807339 := by
  unfold tailWord_5491074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50068980527196043405544069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133517281405856115748117517 50068980527196043405544069)
  ·
    refine ⟨9387933848849258138539513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50068980527196043405544069 9387933848849258138539513)
    ·
      refine ⟨7040950386636943603904635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9387933848849258138539513 7040950386636943603904635)
      ·
        refine ⟨10561425579955415405856953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7040950386636943603904635 10561425579955415405856953)
        ·
          refine ⟨7921069184966561554392715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10561425579955415405856953 7921069184966561554392715)
          ·
            refine ⟨11881603777449842331589073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921069184966561554392715 11881603777449842331589073)
            ·
              refine ⟨8911202833087381748691805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11881603777449842331589073 8911202833087381748691805)
              ·
                refine ⟨3341701062407768155759427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8911202833087381748691805 3341701062407768155759427)
                ·
                  refine ⟨5012551593611652233639141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341701062407768155759427 5012551593611652233639141)
                  ·
                    refine ⟨939853423802184793807339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012551593611652233639141 939853423802184793807339)
                    ·
                      rfl

theorem cell23_5491074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5491074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491074 prefixEnd_5491074 := by exact prefixLift 5491074
  have htrace : WordTrace (prefixWord ++ tailWord_5491074) baseStart_5491074 baseEnd_5491074 := by
    simpa [prefixWord, tailWord_5491074, baseEnd_5491074] using wordTrace_append hprefix tailTrace_5491074
  have hstable : (prefixWord ++ tailWord_5491074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491074).length < 2 ^ (prefixWord ++ tailWord_5491074).sum := by decide
  have hdescent : baseEnd_5491074 < baseStart_5491074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491083 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 1, 5]
def baseStart_5491083 : Nat := 118140960795 + 5491083 * 2 ^ 59
def prefixEnd_5491083 : Nat := 4983230072969 + 3 ^ 40 * 5491083 * 2
def baseEnd_5491083 : Nat := 939854964244148282069825

theorem tailTrace_5491083 : CollatzResearch.WordTrace tailWord_5491083 prefixEnd_5491083 939854964244148282069825 := by
  unfold tailWord_5491083
  simp only [CollatzResearch.WordTrace]
  refine ⟨200276250365751568159253903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133517500243834378772835935 200276250365751568159253903)
  ·
    refine ⟨300414375548627352238880855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200276250365751568159253903 300414375548627352238880855)
    ·
      refine ⟨450621563322941028358321283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300414375548627352238880855 450621563322941028358321283)
      ·
        refine ⟨675932344984411542537481925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450621563322941028358321283 675932344984411542537481925)
        ·
          refine ⟨126737314684577164225777861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 675932344984411542537481925 126737314684577164225777861)
          ·
            refine ⟨23763246503358218292333349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126737314684577164225777861 23763246503358218292333349)
            ·
              refine ⟨4455608719379665929812503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23763246503358218292333349 4455608719379665929812503)
              ·
                refine ⟨6683413079069498894718755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455608719379665929812503 6683413079069498894718755)
                ·
                  refine ⟨10025119618604248342078133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683413079069498894718755 10025119618604248342078133)
                  ·
                    refine ⟨939854964244148282069825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10025119618604248342078133 939854964244148282069825)
                    ·
                      rfl

theorem cell23_5491083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 5].length) (baseStart_5491083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491083 prefixEnd_5491083 := by exact prefixLift 5491083
  have htrace : WordTrace (prefixWord ++ tailWord_5491083) baseStart_5491083 baseEnd_5491083 := by
    simpa [prefixWord, tailWord_5491083, baseEnd_5491083] using wordTrace_append hprefix tailTrace_5491083
  have hstable : (prefixWord ++ tailWord_5491083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491083).length < 2 ^ (prefixWord ++ tailWord_5491083).sum := by decide
  have hdescent : baseEnd_5491083 < baseStart_5491083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491109 : List Nat := [1, 3, 1, 2, 1, 1, 4, 10]
def baseStart_5491109 : Nat := 118140960795 + 5491109 * 2 ^ 59
def prefixEnd_5491109 : Nat := 4983230072969 + 3 ^ 40 * 5491109 * 2
def baseEnd_5491109 : Nat := 104428823823313397943865

theorem tailTrace_5491109 : CollatzResearch.WordTrace tailWord_5491109 prefixEnd_5491109 104428823823313397943865 := by
  unfold tailWord_5491109
  simp only [CollatzResearch.WordTrace]
  refine ⟨200277198663657374599700381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133518132442438249733133587 200277198663657374599700381)
  ·
    refine ⟨75103949498871515474887643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200277198663657374599700381 75103949498871515474887643)
    ·
      refine ⟨112655924248307273212331465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75103949498871515474887643 112655924248307273212331465)
      ·
        refine ⟨84491943186230454909248599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112655924248307273212331465 84491943186230454909248599)
        ·
          refine ⟨126737914779345682363872899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84491943186230454909248599 126737914779345682363872899)
          ·
            refine ⟨190106872169018523545809349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126737914779345682363872899 190106872169018523545809349)
            ·
              refine ⟨35645038531690973164839253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190106872169018523545809349 35645038531690973164839253)
              ·
                refine ⟨104428823823313397943865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35645038531690973164839253 104428823823313397943865)
                ·
                  rfl

theorem cell23_5491109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 10].length) (baseStart_5491109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491109 prefixEnd_5491109 := by exact prefixLift 5491109
  have htrace : WordTrace (prefixWord ++ tailWord_5491109) baseStart_5491109 baseEnd_5491109 := by
    simpa [prefixWord, tailWord_5491109, baseEnd_5491109] using wordTrace_append hprefix tailTrace_5491109
  have hstable : (prefixWord ++ tailWord_5491109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491109).length < 2 ^ (prefixWord ++ tailWord_5491109).sum := by decide
  have hdescent : baseEnd_5491109 < baseStart_5491109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491136 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_5491136 : Nat := 118140960795 + 5491136 * 2 ^ 59
def prefixEnd_5491136 : Nat := 4983230072969 + 3 ^ 40 * 5491136 * 2
def baseEnd_5491136 : Nat := 2819592107207133138846731

theorem tailTrace_5491136 : CollatzResearch.WordTrace tailWord_5491136 prefixEnd_5491136 2819592107207133138846731 := by
  unfold tailWord_5491136
  simp only [CollatzResearch.WordTrace]
  refine ⟨100139091717279779105466631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133518788956373038807288841 100139091717279779105466631)
  ·
    refine ⟨150208637575919668658199947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100139091717279779105466631 150208637575919668658199947)
    ·
      refine ⟨225312956363879502987299921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150208637575919668658199947 225312956363879502987299921)
      ·
        refine ⟨168984717272909627240474941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225312956363879502987299921 168984717272909627240474941)
        ·
          refine ⟨63369268977341110215178103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168984717272909627240474941 63369268977341110215178103)
          ·
            refine ⟨95053903466011665322767155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63369268977341110215178103 95053903466011665322767155)
            ·
              refine ⟨142580855199017497984150733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95053903466011665322767155 142580855199017497984150733)
              ·
                refine ⟨53467820699631561744056525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142580855199017497984150733 53467820699631561744056525)
                ·
                  refine ⟨20050432762361835654021197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53467820699631561744056525 20050432762361835654021197)
                  ·
                    refine ⟨7518912285885688370257949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20050432762361835654021197 7518912285885688370257949)
                    ·
                      refine ⟨2819592107207133138846731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7518912285885688370257949 2819592107207133138846731)
                      ·
                        rfl

theorem cell23_5491136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_5491136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491136 prefixEnd_5491136 := by exact prefixLift 5491136
  have htrace : WordTrace (prefixWord ++ tailWord_5491136) baseStart_5491136 baseEnd_5491136 := by
    simpa [prefixWord, tailWord_5491136, baseEnd_5491136] using wordTrace_append hprefix tailTrace_5491136
  have hstable : (prefixWord ++ tailWord_5491136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491136).length < 2 ^ (prefixWord ++ tailWord_5491136).sum := by decide
  have hdescent : baseEnd_5491136 < baseStart_5491136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491139 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 9]
def baseStart_5491139 : Nat := 118140960795 + 5491139 * 2 ^ 59
def prefixEnd_5491139 : Nat := 4983230072969 + 3 ^ 40 * 5491139 * 2
def baseEnd_5491139 : Nat := 939864549216365542369739

theorem tailTrace_5491139 : CollatzResearch.WordTrace tailWord_5491139 prefixEnd_5491139 939864549216365542369739 := by
  unfold tailWord_5491139
  simp only [CollatzResearch.WordTrace]
  refine ⟨200278292853548689723292471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133518861902365793148861647 200278292853548689723292471)
  ·
    refine ⟨300417439280323034584938707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200278292853548689723292471 300417439280323034584938707)
    ·
      refine ⟨450626158920484551877408061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300417439280323034584938707 450626158920484551877408061)
      ·
        refine ⟨168984809595181706954028023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450626158920484551877408061 168984809595181706954028023)
        ·
          refine ⟨253477214392772560431042035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168984809595181706954028023 253477214392772560431042035)
          ·
            refine ⟨380215821589158840646563053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253477214392772560431042035 380215821589158840646563053)
            ·
              refine ⟨142580933095934565242461145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380215821589158840646563053 142580933095934565242461145)
              ·
                refine ⟨106935699821950923931845859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142580933095934565242461145 106935699821950923931845859)
                ·
                  refine ⟨160403549732926385897768789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106935699821950923931845859 160403549732926385897768789)
                  ·
                    refine ⟨939864549216365542369739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 160403549732926385897768789 939864549216365542369739)
                    ·
                      rfl

theorem cell23_5491139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_5491139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491139 prefixEnd_5491139 := by exact prefixLift 5491139
  have htrace : WordTrace (prefixWord ++ tailWord_5491139) baseStart_5491139 baseEnd_5491139 := by
    simpa [prefixWord, tailWord_5491139, baseEnd_5491139] using wordTrace_append hprefix tailTrace_5491139
  have hstable : (prefixWord ++ tailWord_5491139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491139).length < 2 ^ (prefixWord ++ tailWord_5491139).sum := by decide
  have hdescent : baseEnd_5491139 < baseStart_5491139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491140 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5491140 : Nat := 118140960795 + 5491140 * 2 ^ 59
def prefixEnd_5491140 : Nat := 4983230072969 + 3 ^ 40 * 5491140 * 2
def baseEnd_5491140 : Nat := 2819594161129751123196713

theorem tailTrace_5491140 : CollatzResearch.WordTrace tailWord_5491140 prefixEnd_5491140 2819594161129751123196713 := by
  unfold tailWord_5491140
  simp only [CollatzResearch.WordTrace]
  refine ⟨100139164663272533447039437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133518886217696711262719249 100139164663272533447039437)
  ·
    refine ⟨37552186748727200042639789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100139164663272533447039437 37552186748727200042639789)
    ·
      refine ⟨14082070030772700015989921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37552186748727200042639789 14082070030772700015989921)
      ·
        refine ⟨10561552523079525011992441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14082070030772700015989921 10561552523079525011992441)
        ·
          refine ⟨7921164392309643758994331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10561552523079525011992441 7921164392309643758994331)
          ·
            refine ⟨11881746588464465638491497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921164392309643758994331 11881746588464465638491497)
            ·
              refine ⟨8911309941348349228868623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11881746588464465638491497 8911309941348349228868623)
              ·
                refine ⟨13366964912022523843302935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911309941348349228868623 13366964912022523843302935)
                ·
                  refine ⟨20050447368033785764954403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13366964912022523843302935 20050447368033785764954403)
                  ·
                    refine ⟨30075671052050678647431605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20050447368033785764954403 30075671052050678647431605)
                    ·
                      refine ⟨2819594161129751123196713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30075671052050678647431605 2819594161129751123196713)
                      ·
                        rfl

theorem cell23_5491140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5491140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491140 prefixEnd_5491140 := by exact prefixLift 5491140
  have htrace : WordTrace (prefixWord ++ tailWord_5491140) baseStart_5491140 baseEnd_5491140 := by
    simpa [prefixWord, tailWord_5491140, baseEnd_5491140] using wordTrace_append hprefix tailTrace_5491140
  have hstable : (prefixWord ++ tailWord_5491140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491140).length < 2 ^ (prefixWord ++ tailWord_5491140).sum := by decide
  have hdescent : baseEnd_5491140 < baseStart_5491140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491193 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 3, 4, 2]
def baseStart_5491193 : Nat := 118140960795 + 5491193 * 2 ^ 59
def prefixEnd_5491193 : Nat := 4983230072969 + 3 ^ 40 * 5491193 * 2
def baseEnd_5491193 : Nat := 2819621375604439415833969

theorem tailTrace_5491193 : CollatzResearch.WordTrace tailWord_5491193 prefixEnd_5491193 2819621375604439415833969 := by
  unfold tailWord_5491193
  simp only [CollatzResearch.WordTrace]
  refine ⟨200280262395353056945758233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133520174930235371297172155 200280262395353056945758233)
  ·
    refine ⟨150210196796514792709318675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200280262395353056945758233 150210196796514792709318675)
    ·
      refine ⟨225315295194772189063978013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150210196796514792709318675 225315295194772189063978013)
      ·
        refine ⟨84493235698039570898991755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225315295194772189063978013 84493235698039570898991755)
        ·
          refine ⟨126739853547059356348487633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84493235698039570898991755 126739853547059356348487633)
          ·
            refine ⟨95054890160294517261365725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126739853547059356348487633 95054890160294517261365725)
            ·
              refine ⟨35645583810110443973012147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95054890160294517261365725 35645583810110443973012147)
              ·
                refine ⟨53468375715165665959518221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35645583810110443973012147 53468375715165665959518221)
                ·
                  refine ⟨20050640893187124734819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53468375715165665959518221 20050640893187124734819333)
                  ·
                    refine ⟨3759495167472585887778625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20050640893187124734819333 3759495167472585887778625)
                    ·
                      refine ⟨2819621375604439415833969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759495167472585887778625 2819621375604439415833969)
                      ·
                        rfl

theorem cell23_5491193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_5491193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491193 prefixEnd_5491193 := by exact prefixLift 5491193
  have htrace : WordTrace (prefixWord ++ tailWord_5491193) baseStart_5491193 baseEnd_5491193 := by
    simpa [prefixWord, tailWord_5491193, baseEnd_5491193] using wordTrace_append hprefix tailTrace_5491193
  have hstable : (prefixWord ++ tailWord_5491193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491193).length < 2 ^ (prefixWord ++ tailWord_5491193).sum := by decide
  have hdescent : baseEnd_5491193 < baseStart_5491193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491197 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_5491197 : Nat := 118140960795 + 5491197 * 2 ^ 59
def prefixEnd_5491197 : Nat := 4983230072969 + 3 ^ 40 * 5491197 * 2
def baseEnd_5491197 : Nat := 2819623429527057400183951

theorem tailTrace_5491197 : CollatzResearch.WordTrace tailWord_5491197 prefixEnd_5491197 2819623429527057400183951 := by
  unfold tailWord_5491197
  simp only [CollatzResearch.WordTrace]
  refine ⟨200280408287338565628903845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133520272191559043752602563 200280408287338565628903845)
  ·
    refine ⟨37552576553875981055419471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200280408287338565628903845 37552576553875981055419471)
    ·
      refine ⟨56328864830813971583129207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37552576553875981055419471 56328864830813971583129207)
      ·
        refine ⟨84493297246220957374693811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56328864830813971583129207 84493297246220957374693811)
        ·
          refine ⟨126739945869331436062040717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84493297246220957374693811 126739945869331436062040717)
          ·
            refine ⟨47527479700999288523265269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126739945869331436062040717 47527479700999288523265269)
            ·
              refine ⟨4455701221968683299056119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47527479700999288523265269 4455701221968683299056119)
              ·
                refine ⟨6683551832953024948584179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455701221968683299056119 6683551832953024948584179)
                ·
                  refine ⟨10025327749429537422876269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683551832953024948584179 10025327749429537422876269)
                  ·
                    refine ⟨3759497906036076533578601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10025327749429537422876269 3759497906036076533578601)
                    ·
                      refine ⟨2819623429527057400183951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759497906036076533578601 2819623429527057400183951)
                      ·
                        rfl

theorem cell23_5491197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_5491197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491197 prefixEnd_5491197 := by exact prefixLift 5491197
  have htrace : WordTrace (prefixWord ++ tailWord_5491197) baseStart_5491197 baseEnd_5491197 := by
    simpa [prefixWord, tailWord_5491197, baseEnd_5491197] using wordTrace_append hprefix tailTrace_5491197
  have hstable : (prefixWord ++ tailWord_5491197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491197).length < 2 ^ (prefixWord ++ tailWord_5491197).sum := by decide
  have hdescent : baseEnd_5491197 < baseStart_5491197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491220 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5491220 : Nat := 118140960795 + 5491220 * 2 ^ 59
def prefixEnd_5491220 : Nat := 4983230072969 + 3 ^ 40 * 5491220 * 2
def baseEnd_5491220 : Nat := 939878413194036936732115

theorem tailTrace_5491220 : CollatzResearch.WordTrace tailWord_5491220 prefixEnd_5491220 939878413194036936732115 := by
  unfold tailWord_5491220
  simp only [CollatzResearch.WordTrace]
  refine ⟨100140623583127620278495557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133520831444170160371327409 100140623583127620278495557)
  ·
    refine ⟨18776366921836428802217917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100140623583127620278495557 18776366921836428802217917)
    ·
      refine ⟨7041137595688660800831719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18776366921836428802217917 7041137595688660800831719)
      ·
        refine ⟨10561706393532991201247579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041137595688660800831719 10561706393532991201247579)
        ·
          refine ⟨15842559590299486801871369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561706393532991201247579 15842559590299486801871369)
          ·
            refine ⟨11881919692724615101403527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15842559590299486801871369 11881919692724615101403527)
            ·
              refine ⟨17822879539086922652105291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881919692724615101403527 17822879539086922652105291)
              ·
                refine ⟨26734319308630383978157937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17822879539086922652105291 26734319308630383978157937)
                ·
                  refine ⟨20050739481472787983618453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26734319308630383978157937 20050739481472787983618453)
                  ·
                    refine ⟨939878413194036936732115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20050739481472787983618453 939878413194036936732115)
                    ·
                      rfl

theorem cell23_5491220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5491220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491220 prefixEnd_5491220 := by exact prefixLift 5491220
  have htrace : WordTrace (prefixWord ++ tailWord_5491220) baseStart_5491220 baseEnd_5491220 := by
    simpa [prefixWord, tailWord_5491220, baseEnd_5491220] using wordTrace_append hprefix tailTrace_5491220
  have hstable : (prefixWord ++ tailWord_5491220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491220).length < 2 ^ (prefixWord ++ tailWord_5491220).sum := by decide
  have hdescent : baseEnd_5491220 < baseStart_5491220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491317 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5491317 : Nat := 118140960795 + 5491317 * 2 ^ 59
def prefixEnd_5491317 : Nat := 4983230072969 + 3 ^ 40 * 5491317 * 2
def baseEnd_5491317 : Nat := 2819685047205596930683399

theorem tailTrace_5491317 : CollatzResearch.WordTrace tailWord_5491317 prefixEnd_5491317 2819685047205596930683399 := by
  unfold tailWord_5491317
  simp only [CollatzResearch.WordTrace]
  refine ⟨200284785046903826123272205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133523190031269217415514803 200284785046903826123272205)
  ·
    refine ⟨75106794392588934796227077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200284785046903826123272205 75106794392588934796227077)
    ·
      refine ⟨14082523948610425274292577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75106794392588934796227077 14082523948610425274292577)
      ·
        refine ⟨10561892961457818955719433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14082523948610425274292577 10561892961457818955719433)
        ·
          refine ⟨7921419721093364216789575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10561892961457818955719433 7921419721093364216789575)
          ·
            refine ⟨11882129581640046325184363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921419721093364216789575 11882129581640046325184363)
            ·
              refine ⟨17823194372460069487776545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11882129581640046325184363 17823194372460069487776545)
              ·
                refine ⟨13367395779345052115832409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17823194372460069487776545 13367395779345052115832409)
                ·
                  refine ⟨10025546834508789086874307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13367395779345052115832409 10025546834508789086874307)
                  ·
                    refine ⟨15038320251763183630311461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10025546834508789086874307 15038320251763183630311461)
                    ·
                      refine ⟨2819685047205596930683399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15038320251763183630311461 2819685047205596930683399)
                      ·
                        rfl

theorem cell23_5491317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5491317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491317 prefixEnd_5491317 := by exact prefixLift 5491317
  have htrace : WordTrace (prefixWord ++ tailWord_5491317) baseStart_5491317 baseEnd_5491317 := by
    simpa [prefixWord, tailWord_5491317, baseEnd_5491317] using wordTrace_append hprefix tailTrace_5491317
  have hstable : (prefixWord ++ tailWord_5491317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491317).length < 2 ^ (prefixWord ++ tailWord_5491317).sum := by decide
  have hdescent : baseEnd_5491317 < baseStart_5491317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491353 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_5491353 : Nat := 118140960795 + 5491353 * 2 ^ 59
def prefixEnd_5491353 : Nat := 4983230072969 + 3 ^ 40 * 5491353 * 2
def baseEnd_5491353 : Nat := 939901177503052929944411

theorem tailTrace_5491353 : CollatzResearch.WordTrace tailWord_5491353 prefixEnd_5491353 939901177503052929944411 := by
  unfold tailWord_5491353
  simp only [CollatzResearch.WordTrace]
  refine ⟨200286098074773404271582713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133524065383182269514388475 200286098074773404271582713)
  ·
    refine ⟨150214573556080053203687035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200286098074773404271582713 150214573556080053203687035)
    ·
      refine ⟨225321860334120079805530553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150214573556080053203687035 225321860334120079805530553)
      ·
        refine ⟨168991395250590059854147915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225321860334120079805530553 168991395250590059854147915)
        ·
          refine ⟨253487092875885089781221873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168991395250590059854147915 253487092875885089781221873)
          ·
            refine ⟨190115319656913817335916405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253487092875885089781221873 190115319656913817335916405)
            ·
              refine ⟨17823311217835670375242163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 190115319656913817335916405 17823311217835670375242163)
              ·
                refine ⟨26734966826753505562863245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17823311217835670375242163 26734966826753505562863245)
                ·
                  refine ⟨10025612560032564586073717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26734966826753505562863245 10025612560032564586073717)
                  ·
                    refine ⟨939901177503052929944411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10025612560032564586073717 939901177503052929944411)
                    ·
                      rfl

theorem cell23_5491353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_5491353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491353 prefixEnd_5491353 := by exact prefixLift 5491353
  have htrace : WordTrace (prefixWord ++ tailWord_5491353) baseStart_5491353 baseEnd_5491353 := by
    simpa [prefixWord, tailWord_5491353, baseEnd_5491353] using wordTrace_append hprefix tailTrace_5491353
  have hstable : (prefixWord ++ tailWord_5491353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491353).length < 2 ^ (prefixWord ++ tailWord_5491353).sum := by decide
  have hdescent : baseEnd_5491353 < baseStart_5491353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491354 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5491354 : Nat := 118140960795 + 5491354 * 2 ^ 59
def prefixEnd_5491354 : Nat := 4983230072969 + 3 ^ 40 * 5491354 * 2
def baseEnd_5491354 : Nat := 2819704045989813285920729

theorem tailTrace_5491354 : CollatzResearch.WordTrace tailWord_5491354 prefixEnd_5491354 2819704045989813285920729 := by
  unfold tailWord_5491354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50071533636942445360592279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133524089698513187628246077 50071533636942445360592279)
  ·
    refine ⟨75107300455413668040888419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50071533636942445360592279 75107300455413668040888419)
    ·
      refine ⟨112660950683120502061332629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75107300455413668040888419 112660950683120502061332629)
      ·
        refine ⟨5280982063271273534124967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112660950683120502061332629 5280982063271273534124967)
        ·
          refine ⟨7921473094906910301187451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280982063271273534124967 7921473094906910301187451)
          ·
            refine ⟨11882209642360365451781177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921473094906910301187451 11882209642360365451781177)
            ·
              refine ⟨8911657231770274088835883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11882209642360365451781177 8911657231770274088835883)
              ·
                refine ⟨13367485847655411133253825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911657231770274088835883 13367485847655411133253825)
                ·
                  refine ⟨10025614385741558349940369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13367485847655411133253825 10025614385741558349940369)
                  ·
                    refine ⟨7519210789306168762455277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10025614385741558349940369 7519210789306168762455277)
                    ·
                      refine ⟨2819704045989813285920729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7519210789306168762455277 2819704045989813285920729)
                      ·
                        rfl

theorem cell23_5491354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5491354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491354 prefixEnd_5491354 := by exact prefixLift 5491354
  have htrace : WordTrace (prefixWord ++ tailWord_5491354) baseStart_5491354 baseEnd_5491354 := by
    simpa [prefixWord, tailWord_5491354, baseEnd_5491354] using wordTrace_append hprefix tailTrace_5491354
  have hstable : (prefixWord ++ tailWord_5491354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491354).length < 2 ^ (prefixWord ++ tailWord_5491354).sum := by decide
  have hdescent : baseEnd_5491354 < baseStart_5491354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491390 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5491390 : Nat := 118140960795 + 5491390 * 2 ^ 59
def prefixEnd_5491390 : Nat := 4983230072969 + 3 ^ 40 * 5491390 * 2
def baseEnd_5491390 : Nat := 2819722531293375145070563

theorem tailTrace_5491390 : CollatzResearch.WordTrace tailWord_5491390 prefixEnd_5491390 2819722531293375145070563 := by
  unfold tailWord_5491390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25035930946954919948834953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133524965050426239727119749 25035930946954919948834953)
  ·
    refine ⟨18776948210216189961626215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25035930946954919948834953 18776948210216189961626215)
    ·
      refine ⟨28165422315324284942439323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18776948210216189961626215 28165422315324284942439323)
      ·
        refine ⟨42248133472986427413658985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28165422315324284942439323 42248133472986427413658985)
        ·
          refine ⟨31686100104739820560244239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42248133472986427413658985 31686100104739820560244239)
          ·
            refine ⟨47529150157109730840366359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31686100104739820560244239 47529150157109730840366359)
            ·
              refine ⟨71293725235664596260549539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47529150157109730840366359 71293725235664596260549539)
              ·
                refine ⟨106940587853496894390824309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71293725235664596260549539 106940587853496894390824309)
                ·
                  refine ⟨10025680111265333849139779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106940587853496894390824309 10025680111265333849139779)
                  ·
                    refine ⟨15038520166898000773709669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10025680111265333849139779 15038520166898000773709669)
                    ·
                      refine ⟨2819722531293375145070563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15038520166898000773709669 2819722531293375145070563)
                      ·
                        rfl

theorem cell23_5491390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5491390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491390 prefixEnd_5491390 := by exact prefixLift 5491390
  have htrace : WordTrace (prefixWord ++ tailWord_5491390) baseStart_5491390 baseEnd_5491390 := by
    simpa [prefixWord, tailWord_5491390, baseEnd_5491390] using wordTrace_append hprefix tailTrace_5491390
  have hstable : (prefixWord ++ tailWord_5491390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491390).length < 2 ^ (prefixWord ++ tailWord_5491390).sum := by decide
  have hdescent : baseEnd_5491390 < baseStart_5491390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491400 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_5491400 : Nat := 118140960795 + 5491400 * 2 ^ 59
def prefixEnd_5491400 : Nat := 4983230072969 + 3 ^ 40 * 5491400 * 2
def baseEnd_5491400 : Nat := 939909222033306701981839

theorem tailTrace_5491400 : CollatzResearch.WordTrace tailWord_5491400 prefixEnd_5491400 939909222033306701981839 := by
  unfold tailWord_5491400
  simp only [CollatzResearch.WordTrace]
  refine ⟨100143906152801565649271827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133525208203735420865695769 100143906152801565649271827)
  ·
    refine ⟨150215859229202348473907741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100143906152801565649271827 150215859229202348473907741)
    ·
      refine ⟨56330947210950880677715403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150215859229202348473907741 56330947210950880677715403)
      ·
        refine ⟨84496420816426321016573105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56330947210950880677715403 84496420816426321016573105)
        ·
          refine ⟨63372315612319740762429829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84496420816426321016573105 63372315612319740762429829)
          ·
            refine ⟨11882309177309951392955593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63372315612319740762429829 11882309177309951392955593)
            ·
              refine ⟨8911731882982463544716695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11882309177309951392955593 8911731882982463544716695)
              ·
                refine ⟨13367597824473695317075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911731882982463544716695 13367597824473695317075043)
                ·
                  refine ⟨20051396736710542975612565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13367597824473695317075043 20051396736710542975612565)
                  ·
                    refine ⟨939909222033306701981839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20051396736710542975612565 939909222033306701981839)
                    ·
                      rfl

theorem cell23_5491400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_5491400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491400 prefixEnd_5491400 := by exact prefixLift 5491400
  have htrace : WordTrace (prefixWord ++ tailWord_5491400) baseStart_5491400 baseEnd_5491400 := by
    simpa [prefixWord, tailWord_5491400, baseEnd_5491400] using wordTrace_append hprefix tailTrace_5491400
  have hstable : (prefixWord ++ tailWord_5491400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491400).length < 2 ^ (prefixWord ++ tailWord_5491400).sum := by decide
  have hdescent : baseEnd_5491400 < baseStart_5491400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491454 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5491454 : Nat := 118140960795 + 5491454 * 2 ^ 59
def prefixEnd_5491454 : Nat := 4983230072969 + 3 ^ 40 * 5491454 * 2
def baseEnd_5491454 : Nat := 2819755394055262894670269

theorem tailTrace_5491454 : CollatzResearch.WordTrace tailWord_5491454 prefixEnd_5491454 2819755394055262894670269 := by
  unfold tailWord_5491454
  simp only [CollatzResearch.WordTrace]
  refine ⟨25036222730925937315126177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133526521231604999014006277 25036222730925937315126177)
  ·
    refine ⟨18777167048194452986344633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25036222730925937315126177 18777167048194452986344633)
    ·
      refine ⟨14082875286145839739758475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18777167048194452986344633 14082875286145839739758475)
      ·
        refine ⟨21124312929218759609637713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14082875286145839739758475 21124312929218759609637713)
        ·
          refine ⟨15843234696914069707228285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21124312929218759609637713 15843234696914069707228285)
          ·
            refine ⟨5941213011342776140210607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15843234696914069707228285 5941213011342776140210607)
            ·
              refine ⟨8911819517014164210315911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941213011342776140210607 8911819517014164210315911)
              ·
                refine ⟨13367729275521246315473867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911819517014164210315911 13367729275521246315473867)
                ·
                  refine ⟨20051593913281869473210801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13367729275521246315473867 20051593913281869473210801)
                  ·
                    refine ⟨15038695434961402104908101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20051593913281869473210801 15038695434961402104908101)
                    ·
                      refine ⟨2819755394055262894670269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15038695434961402104908101 2819755394055262894670269)
                      ·
                        rfl

theorem cell23_5491454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5491454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491454 prefixEnd_5491454 := by exact prefixLift 5491454
  have htrace : WordTrace (prefixWord ++ tailWord_5491454) baseStart_5491454 baseEnd_5491454 := by
    simpa [prefixWord, tailWord_5491454, baseEnd_5491454] using wordTrace_append hprefix tailTrace_5491454
  have hstable : (prefixWord ++ tailWord_5491454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491454).length < 2 ^ (prefixWord ++ tailWord_5491454).sum := by decide
  have hdescent : baseEnd_5491454 < baseStart_5491454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491473 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_5491473 : Nat := 118140960795 + 5491473 * 2 ^ 59
def prefixEnd_5491473 : Nat := 4983230072969 + 3 ^ 40 * 5491473 * 2
def baseEnd_5491473 : Nat := 939921716729232773444227

theorem tailTrace_5491473 : CollatzResearch.WordTrace tailWord_5491473 prefixEnd_5491473 939921716729232773444227 := by
  unfold tailWord_5491473
  simp only [CollatzResearch.WordTrace]
  refine ⟨200290474834338664765951073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133526983222892443177300715 200290474834338664765951073)
  ·
    refine ⟨150217856125753998574463305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200290474834338664765951073 150217856125753998574463305)
    ·
      refine ⟨112663392094315498930847479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150217856125753998574463305 112663392094315498930847479)
      ·
        refine ⟨168995088141473248396271219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112663392094315498930847479 168995088141473248396271219)
        ·
          refine ⟨253492632212209872594406829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168995088141473248396271219 253492632212209872594406829)
          ·
            refine ⟨95059737079578702222902561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253492632212209872594406829 95059737079578702222902561)
            ·
              refine ⟨71294802809684026667176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95059737079578702222902561 71294802809684026667176921)
              ·
                refine ⟨53471102107263020000382691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71294802809684026667176921 53471102107263020000382691)
                ·
                  refine ⟨80206653160894530000574037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53471102107263020000382691 80206653160894530000574037)
                  ·
                    refine ⟨939921716729232773444227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80206653160894530000574037 939921716729232773444227)
                    ·
                      rfl

theorem cell23_5491473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_5491473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491473 prefixEnd_5491473 := by exact prefixLift 5491473
  have htrace : WordTrace (prefixWord ++ tailWord_5491473) baseStart_5491473 baseEnd_5491473 := by
    simpa [prefixWord, tailWord_5491473, baseEnd_5491473] using wordTrace_append hprefix tailTrace_5491473
  have hstable : (prefixWord ++ tailWord_5491473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491473).length < 2 ^ (prefixWord ++ tailWord_5491473).sum := by decide
  have hdescent : baseEnd_5491473 < baseStart_5491473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491484 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_5491484 : Nat := 118140960795 + 5491484 * 2 ^ 59
def prefixEnd_5491484 : Nat := 4983230072969 + 3 ^ 40 * 5491484 * 2
def baseEnd_5491484 : Nat := 2819770798474897777295131

theorem tailTrace_5491484 : CollatzResearch.WordTrace tailWord_5491484 prefixEnd_5491484 2819770798474897777295131 := by
  unfold tailWord_5491484
  simp only [CollatzResearch.WordTrace]
  refine ⟨100145438018649406822300753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133527250691532542429734337 100145438018649406822300753)
  ·
    refine ⟨75109078513987055116725565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100145438018649406822300753 75109078513987055116725565)
    ·
      refine ⟨28165904442745145668772087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75109078513987055116725565 28165904442745145668772087)
      ·
        refine ⟨42248856664117718503158131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28165904442745145668772087 42248856664117718503158131)
        ·
          refine ⟨63373284996176577754737197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42248856664117718503158131 63373284996176577754737197)
          ·
            refine ⟨23764981873566216658026449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63373284996176577754737197 23764981873566216658026449)
            ·
              refine ⟨17823736405174662493519837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23764981873566216658026449 17823736405174662493519837)
              ·
                refine ⟨6683901151940498435069939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17823736405174662493519837 6683901151940498435069939)
                ·
                  refine ⟨10025851727910747652604909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683901151940498435069939 10025851727910747652604909)
                  ·
                    refine ⟨3759694397966530369726841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10025851727910747652604909 3759694397966530369726841)
                    ·
                      refine ⟨2819770798474897777295131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759694397966530369726841 2819770798474897777295131)
                      ·
                        rfl

theorem cell23_5491484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_5491484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491484 prefixEnd_5491484 := by exact prefixLift 5491484
  have htrace : WordTrace (prefixWord ++ tailWord_5491484) baseStart_5491484 baseEnd_5491484 := by
    simpa [prefixWord, tailWord_5491484, baseEnd_5491484] using wordTrace_append hprefix tailTrace_5491484
  have hstable : (prefixWord ++ tailWord_5491484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491484).length < 2 ^ (prefixWord ++ tailWord_5491484).sum := by decide
  have hdescent : baseEnd_5491484 < baseStart_5491484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491500 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_5491500 : Nat := 118140960795 + 5491500 * 2 ^ 59
def prefixEnd_5491500 : Nat := 4983230072969 + 3 ^ 40 * 5491500 * 2
def baseEnd_5491500 : Nat := 2819779014165369714695057

theorem tailTrace_5491500 : CollatzResearch.WordTrace tailWord_5491500 prefixEnd_5491500 2819779014165369714695057 := by
  unfold tailWord_5491500
  simp only [CollatzResearch.WordTrace]
  refine ⟨100145729802620424188591977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133527639736827232251455969 100145729802620424188591977)
  ·
    refine ⟨75109297351965318141443983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100145729802620424188591977 75109297351965318141443983)
    ·
      refine ⟨112663946027947977212165975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75109297351965318141443983 112663946027947977212165975)
      ·
        refine ⟨168995919041921965818248963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112663946027947977212165975 168995919041921965818248963)
        ·
          refine ⟨253493878562882948727373445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168995919041921965818248963 253493878562882948727373445)
          ·
            refine ⟨47530102230540552886382521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253493878562882948727373445 47530102230540552886382521)
            ·
              refine ⟨35647576672905414664786891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47530102230540552886382521 35647576672905414664786891)
              ·
                refine ⟨53471365009358121997180337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35647576672905414664786891 53471365009358121997180337)
                ·
                  refine ⟨40103523757018591497885253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53471365009358121997180337 40103523757018591497885253)
                  ·
                    refine ⟨7519410704440985905853485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40103523757018591497885253 7519410704440985905853485)
                    ·
                      refine ⟨2819779014165369714695057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7519410704440985905853485 2819779014165369714695057)
                      ·
                        rfl

theorem cell23_5491500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_5491500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491500 prefixEnd_5491500 := by exact prefixLift 5491500
  have htrace : WordTrace (prefixWord ++ tailWord_5491500) baseStart_5491500 baseEnd_5491500 := by
    simpa [prefixWord, tailWord_5491500, baseEnd_5491500] using wordTrace_append hprefix tailTrace_5491500
  have hstable : (prefixWord ++ tailWord_5491500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491500).length < 2 ^ (prefixWord ++ tailWord_5491500).sum := by decide
  have hdescent : baseEnd_5491500 < baseStart_5491500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491518 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_5491518 : Nat := 118140960795 + 5491518 * 2 ^ 59
def prefixEnd_5491518 : Nat := 4983230072969 + 3 ^ 40 * 5491518 * 2
def baseEnd_5491518 : Nat := 2819788256817150644269975

theorem tailTrace_5491518 : CollatzResearch.WordTrace tailWord_5491518 prefixEnd_5491518 2819788256817150644269975 := by
  unfold tailWord_5491518
  simp only [CollatzResearch.WordTrace]
  refine ⟨25036514514896954681417401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133528077412783758300892805 25036514514896954681417401)
  ·
    refine ⟨18777385886172716011063051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25036514514896954681417401 18777385886172716011063051)
    ·
      refine ⟨28166078829259074016594577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18777385886172716011063051 28166078829259074016594577)
      ·
        refine ⟨21124559121944305512445933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28166078829259074016594577 21124559121944305512445933)
        ·
          refine ⟨7921709670729114567167225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21124559121944305512445933 7921709670729114567167225)
          ·
            refine ⟨5941282253046835925375419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7921709670729114567167225 5941282253046835925375419)
            ·
              refine ⟨8911923379570253888063129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941282253046835925375419 8911923379570253888063129)
              ·
                refine ⟨6683942534677690416047347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8911923379570253888063129 6683942534677690416047347)
                ·
                  refine ⟨10025913802016535624071021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683942534677690416047347 10025913802016535624071021)
                  ·
                    refine ⟨3759717675756200859026633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10025913802016535624071021 3759717675756200859026633)
                    ·
                      refine ⟨2819788256817150644269975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759717675756200859026633 2819788256817150644269975)
                      ·
                        rfl

theorem cell23_5491518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_5491518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491518 prefixEnd_5491518 := by exact prefixLift 5491518
  have htrace : WordTrace (prefixWord ++ tailWord_5491518) baseStart_5491518 baseEnd_5491518 := by
    simpa [prefixWord, tailWord_5491518, baseEnd_5491518] using wordTrace_append hprefix tailTrace_5491518
  have hstable : (prefixWord ++ tailWord_5491518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491518).length < 2 ^ (prefixWord ++ tailWord_5491518).sum := by decide
  have hdescent : baseEnd_5491518 < baseStart_5491518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491530 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_5491530 : Nat := 118140960795 + 5491530 * 2 ^ 59
def prefixEnd_5491530 : Nat := 4983230072969 + 3 ^ 40 * 5491530 * 2
def baseEnd_5491530 : Nat := 2819794418585004597319919

theorem tailTrace_5491530 : CollatzResearch.WordTrace tailWord_5491530 prefixEnd_5491530 2819794418585004597319919 := by
  unfold tailWord_5491530
  simp only [CollatzResearch.WordTrace]
  refine ⟨50073138448783040875194011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133528369196754775667184029 50073138448783040875194011)
  ·
    refine ⟨75109707673174561312791017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50073138448783040875194011 75109707673174561312791017)
    ·
      refine ⟨56332280754880920984593263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75109707673174561312791017 56332280754880920984593263)
      ·
        refine ⟨84498421132321381476889895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56332280754880920984593263 84498421132321381476889895)
        ·
          refine ⟨126747631698482072215334843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84498421132321381476889895 126747631698482072215334843)
          ·
            refine ⟨190121447547723108323002265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126747631698482072215334843 190121447547723108323002265)
            ·
              refine ⟨142591085660792331242251699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190121447547723108323002265 142591085660792331242251699)
              ·
                refine ⟨213886628491188496863377549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142591085660792331242251699 213886628491188496863377549)
                ·
                  refine ⟨80207485684195686323766581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213886628491188496863377549 80207485684195686323766581)
                  ·
                    refine ⟨7519451782893345592853117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80207485684195686323766581 7519451782893345592853117)
                    ·
                      refine ⟨2819794418585004597319919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7519451782893345592853117 2819794418585004597319919)
                      ·
                        rfl

theorem cell23_5491530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_5491530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491530 prefixEnd_5491530 := by exact prefixLift 5491530
  have htrace : WordTrace (prefixWord ++ tailWord_5491530) baseStart_5491530 baseEnd_5491530 := by
    simpa [prefixWord, tailWord_5491530, baseEnd_5491530] using wordTrace_append hprefix tailTrace_5491530
  have hstable : (prefixWord ++ tailWord_5491530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491530).length < 2 ^ (prefixWord ++ tailWord_5491530).sum := by decide
  have hdescent : baseEnd_5491530 < baseStart_5491530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491548 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5491548 : Nat := 118140960795 + 5491548 * 2 ^ 59
def prefixEnd_5491548 : Nat := 4983230072969 + 3 ^ 40 * 5491548 * 2
def baseEnd_5491548 : Nat := 2819803661236785526894837

theorem tailTrace_5491548 : CollatzResearch.WordTrace tailWord_5491548 prefixEnd_5491548 2819803661236785526894837 := by
  unfold tailWord_5491548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100146605154533476287465649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133528806872711301716620865 100146605154533476287465649)
  ·
    refine ⟨75109953865900107215599237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100146605154533476287465649 75109953865900107215599237)
    ·
      refine ⟨14083116349856270102924857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75109953865900107215599237 14083116349856270102924857)
      ·
        refine ⟨10562337262392202577193643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14083116349856270102924857 10562337262392202577193643)
        ·
          refine ⟨15843505893588303865790465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562337262392202577193643 15843505893588303865790465)
          ·
            refine ⟨11882629420191227899342849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15843505893588303865790465 11882629420191227899342849)
            ·
              refine ⟨8911972065143420924507137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11882629420191227899342849 8911972065143420924507137)
              ·
                refine ⟨6683979048857565693380353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8911972065143420924507137 6683979048857565693380353)
                ·
                  refine ⟨5012984286643174270035265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6683979048857565693380353 5012984286643174270035265)
                  ·
                    refine ⟨3759738214982380702526449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5012984286643174270035265 3759738214982380702526449)
                    ·
                      refine ⟨2819803661236785526894837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759738214982380702526449 2819803661236785526894837)
                      ·
                        rfl

theorem cell23_5491548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5491548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491548 prefixEnd_5491548 := by exact prefixLift 5491548
  have htrace : WordTrace (prefixWord ++ tailWord_5491548) baseStart_5491548 baseEnd_5491548 := by
    simpa [prefixWord, tailWord_5491548, baseEnd_5491548] using wordTrace_append hprefix tailTrace_5491548
  have hstable : (prefixWord ++ tailWord_5491548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491548).length < 2 ^ (prefixWord ++ tailWord_5491548).sum := by decide
  have hdescent : baseEnd_5491548 < baseStart_5491548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491557 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 5, 2]
def baseStart_5491557 : Nat := 118140960795 + 5491557 * 2 ^ 59
def prefixEnd_5491557 : Nat := 4983230072969 + 3 ^ 40 * 5491557 * 2
def baseEnd_5491557 : Nat := 2819808282562675991682295

theorem tailTrace_5491557 : CollatzResearch.WordTrace tailWord_5491557 prefixEnd_5491557 2819808282562675991682295 := by
  unfold tailWord_5491557
  simp only [CollatzResearch.WordTrace]
  refine ⟨200293538566034347112008925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133529025710689564741339283 200293538566034347112008925)
  ·
    refine ⟨75110076962262880167003347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200293538566034347112008925 75110076962262880167003347)
    ·
      refine ⟨112665115443394320250505021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75110076962262880167003347 112665115443394320250505021)
      ·
        refine ⟨42249418291272870093939383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112665115443394320250505021 42249418291272870093939383)
        ·
          refine ⟨63374127436909305140909075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42249418291272870093939383 63374127436909305140909075)
          ·
            refine ⟨95061191155363957711363613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63374127436909305140909075 95061191155363957711363613)
            ·
              refine ⟨35647946683261484141761355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95061191155363957711363613 35647946683261484141761355)
              ·
                refine ⟨53471920024892226212642033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35647946683261484141761355 53471920024892226212642033)
                ·
                  refine ⟨40103940018669169659481525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53471920024892226212642033 40103940018669169659481525)
                  ·
                    refine ⟨3759744376750234655576393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40103940018669169659481525 3759744376750234655576393)
                    ·
                      refine ⟨2819808282562675991682295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759744376750234655576393 2819808282562675991682295)
                      ·
                        rfl

theorem cell23_5491557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_5491557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491557 prefixEnd_5491557 := by exact prefixLift 5491557
  have htrace : WordTrace (prefixWord ++ tailWord_5491557) baseStart_5491557 baseEnd_5491557 := by
    simpa [prefixWord, tailWord_5491557, baseEnd_5491557] using wordTrace_append hprefix tailTrace_5491557
  have hstable : (prefixWord ++ tailWord_5491557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491557).length < 2 ^ (prefixWord ++ tailWord_5491557).sum := by decide
  have hdescent : baseEnd_5491557 < baseStart_5491557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491587 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 6, 2]
def baseStart_5491587 : Nat := 118140960795 + 5491587 * 2 ^ 59
def prefixEnd_5491587 : Nat := 4983230072969 + 3 ^ 40 * 5491587 * 2
def baseEnd_5491587 : Nat := 2819823686982310874307157

theorem tailTrace_5491587 : CollatzResearch.WordTrace tailWord_5491587 prefixEnd_5491587 2819823686982310874307157 := by
  unfold tailWord_5491587
  simp only [CollatzResearch.WordTrace]
  refine ⟨200294632755925662235601015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133529755170617108157067343 200294632755925662235601015)
  ·
    refine ⟨300441949133888493353401523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200294632755925662235601015 300441949133888493353401523)
    ·
      refine ⟨450662923700832740030102285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300441949133888493353401523 450662923700832740030102285)
      ·
        refine ⟨168998596387812277511288357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450662923700832740030102285 168998596387812277511288357)
        ·
          refine ⟨31687236822714802033366567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168998596387812277511288357 31687236822714802033366567)
          ·
            refine ⟨47530855234072203050049851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31687236822714802033366567 47530855234072203050049851)
            ·
              refine ⟨71296282851108304575074777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47530855234072203050049851 71296282851108304575074777)
              ·
                refine ⟨53472212138331228431306083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71296282851108304575074777 53472212138331228431306083)
                ·
                  refine ⟨80208318207496842646959125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53472212138331228431306083 80208318207496842646959125)
                  ·
                    refine ⟨3759764915976414499076209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80208318207496842646959125 3759764915976414499076209)
                    ·
                      refine ⟨2819823686982310874307157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759764915976414499076209 2819823686982310874307157)
                      ·
                        rfl

theorem cell23_5491587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_5491587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491587 prefixEnd_5491587 := by exact prefixLift 5491587
  have htrace : WordTrace (prefixWord ++ tailWord_5491587) baseStart_5491587 baseEnd_5491587 := by
    simpa [prefixWord, tailWord_5491587, baseEnd_5491587] using wordTrace_append hprefix tailTrace_5491587
  have hstable : (prefixWord ++ tailWord_5491587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491587).length < 2 ^ (prefixWord ++ tailWord_5491587).sum := by decide
  have hdescent : baseEnd_5491587 < baseStart_5491587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491604 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5491604 : Nat := 118140960795 + 5491604 * 2 ^ 59
def prefixEnd_5491604 : Nat := 4983230072969 + 3 ^ 40 * 5491604 * 2
def baseEnd_5491604 : Nat := 2819832416153437307794579

theorem tailTrace_5491604 : CollatzResearch.WordTrace tailWord_5491604 prefixEnd_5491604 2819832416153437307794579 := by
  unfold tailWord_5491604
  simp only [CollatzResearch.WordTrace]
  refine ⟨100147626398432037069484933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133530168531242716092646577 100147626398432037069484933)
  ·
    refine ⟨18777679949706006950528425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100147626398432037069484933 18777679949706006950528425)
    ·
      refine ⟨14083259962279505212896319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18777679949706006950528425 14083259962279505212896319)
      ·
        refine ⟨21124889943419257819344479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14083259962279505212896319 21124889943419257819344479)
        ·
          refine ⟨31687334915128886729016719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21124889943419257819344479 31687334915128886729016719)
          ·
            refine ⟨47531002372693330093525079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31687334915128886729016719 47531002372693330093525079)
            ·
              refine ⟨71296503559039995140287619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47531002372693330093525079 71296503559039995140287619)
              ·
                refine ⟨106944755338559992710431429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71296503559039995140287619 106944755338559992710431429)
                ·
                  refine ⟨20052141625979998633205893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106944755338559992710431429 20052141625979998633205893)
                  ·
                    refine ⟨3759776554871249743726105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20052141625979998633205893 3759776554871249743726105)
                    ·
                      refine ⟨2819832416153437307794579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759776554871249743726105 2819832416153437307794579)
                      ·
                        rfl

theorem cell23_5491604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5491604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491604 prefixEnd_5491604 := by exact prefixLift 5491604
  have htrace : WordTrace (prefixWord ++ tailWord_5491604) baseStart_5491604 baseEnd_5491604 := by
    simpa [prefixWord, tailWord_5491604, baseEnd_5491604] using wordTrace_append hprefix tailTrace_5491604
  have hstable : (prefixWord ++ tailWord_5491604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491604).length < 2 ^ (prefixWord ++ tailWord_5491604).sum := by decide
  have hdescent : baseEnd_5491604 < baseStart_5491604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491607 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_5491607 : Nat := 118140960795 + 5491607 * 2 ^ 59
def prefixEnd_5491607 : Nat := 4983230072969 + 3 ^ 40 * 5491607 * 2
def baseEnd_5491607 : Nat := 2819833956595400796057065

theorem tailTrace_5491607 : CollatzResearch.WordTrace tailWord_5491607 prefixEnd_5491607 2819833956595400796057065 := by
  unfold tailWord_5491607
  simp only [CollatzResearch.WordTrace]
  refine ⟨200295362215853205651329075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133530241477235470434219383 200295362215853205651329075)
  ·
    refine ⟨300443043323779808476993613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200295362215853205651329075 300443043323779808476993613)
    ·
      refine ⟨112666141246417428178872605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300443043323779808476993613 112666141246417428178872605)
      ·
        refine ⟨42249802967406535567077227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112666141246417428178872605 42249802967406535567077227)
        ·
          refine ⟨63374704451109803350615841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42249802967406535567077227 63374704451109803350615841)
          ·
            refine ⟨47531028338332352512961881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63374704451109803350615841 47531028338332352512961881)
            ·
              refine ⟨35648271253749264384721411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47531028338332352512961881 35648271253749264384721411)
              ·
                refine ⟨53472406880623896577082117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35648271253749264384721411 53472406880623896577082117)
                ·
                  refine ⟨10026076290116980608202897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53472406880623896577082117 10026076290116980608202897)
                  ·
                    refine ⟨7519557217587735456152173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10026076290116980608202897 7519557217587735456152173)
                    ·
                      refine ⟨2819833956595400796057065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7519557217587735456152173 2819833956595400796057065)
                      ·
                        rfl

theorem cell23_5491607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_5491607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491607 prefixEnd_5491607 := by exact prefixLift 5491607
  have htrace : WordTrace (prefixWord ++ tailWord_5491607) baseStart_5491607 baseEnd_5491607 := by
    simpa [prefixWord, tailWord_5491607, baseEnd_5491607] using wordTrace_append hprefix tailTrace_5491607
  have hstable : (prefixWord ++ tailWord_5491607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491607).length < 2 ^ (prefixWord ++ tailWord_5491607).sum := by decide
  have hdescent : baseEnd_5491607 < baseStart_5491607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491637 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_5491637 : Nat := 118140960795 + 5491637 * 2 ^ 59
def prefixEnd_5491637 : Nat := 4983230072969 + 3 ^ 40 * 5491637 * 2
def baseEnd_5491637 : Nat := 2819849361015035678681927

theorem tailTrace_5491637 : CollatzResearch.WordTrace tailWord_5491637 prefixEnd_5491637 2819849361015035678681927 := by
  unfold tailWord_5491637
  simp only [CollatzResearch.WordTrace]
  refine ⟨200296456405744520774921165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133530970937163013849947443 200296456405744520774921165)
  ·
    refine ⟨75111171152154195290595437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200296456405744520774921165 75111171152154195290595437)
    ·
      refine ⟨28166689182057823233973289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75111171152154195290595437 28166689182057823233973289)
      ·
        refine ⟨21125016886543367425479967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28166689182057823233973289 21125016886543367425479967)
        ·
          refine ⟨31687525329815051138219951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21125016886543367425479967 31687525329815051138219951)
          ·
            refine ⟨47531287994722576707329927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31687525329815051138219951 47531287994722576707329927)
            ·
              refine ⟨71296931992083865060994891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47531287994722576707329927 71296931992083865060994891)
              ·
                refine ⟨106945397988125797591492337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71296931992083865060994891 106945397988125797591492337)
                ·
                  refine ⟨80209048491094348193619253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106945397988125797591492337 80209048491094348193619253)
                  ·
                    refine ⟨7519598296040095143151805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80209048491094348193619253 7519598296040095143151805)
                    ·
                      refine ⟨2819849361015035678681927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7519598296040095143151805 2819849361015035678681927)
                      ·
                        rfl

theorem cell23_5491637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_5491637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491637 prefixEnd_5491637 := by exact prefixLift 5491637
  have htrace : WordTrace (prefixWord ++ tailWord_5491637) baseStart_5491637 baseEnd_5491637 := by
    simpa [prefixWord, tailWord_5491637, baseEnd_5491637] using wordTrace_append hprefix tailTrace_5491637
  have hstable : (prefixWord ++ tailWord_5491637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491637).length < 2 ^ (prefixWord ++ tailWord_5491637).sum := by decide
  have hdescent : baseEnd_5491637 < baseStart_5491637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491741 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_5491741 : Nat := 118140960795 + 5491741 * 2 ^ 59
def prefixEnd_5491741 : Nat := 4983230072969 + 3 ^ 40 * 5491741 * 2
def baseEnd_5491741 : Nat := 2819902763003103271781449

theorem tailTrace_5491741 : CollatzResearch.WordTrace tailWord_5491741 prefixEnd_5491741 2819902763003103271781449 := by
  unfold tailWord_5491741
  simp only [CollatzResearch.WordTrace]
  refine ⟨200300249597367746536707077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133533499731578497691138051 200300249597367746536707077)
  ·
    refine ⟨37556296799506452475632577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200300249597367746536707077 37556296799506452475632577)
    ·
      refine ⟨28167222599629839356724433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37556296799506452475632577 28167222599629839356724433)
      ·
        refine ⟨21125416949722379517543325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28167222599629839356724433 21125416949722379517543325)
        ·
          refine ⟨7922031356145892319078747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21125416949722379517543325 7922031356145892319078747)
          ·
            refine ⟨11883047034218838478618121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922031356145892319078747 11883047034218838478618121)
            ·
              refine ⟨8912285275664128858963591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11883047034218838478618121 8912285275664128858963591)
              ·
                refine ⟨13368427913496193288445387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8912285275664128858963591 13368427913496193288445387)
                ·
                  refine ⟨20052641870244289932668081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13368427913496193288445387 20052641870244289932668081)
                  ·
                    refine ⟨15039481402683217449501061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20052641870244289932668081 15039481402683217449501061)
                    ·
                      refine ⟨2819902763003103271781449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15039481402683217449501061 2819902763003103271781449)
                      ·
                        rfl

theorem cell23_5491741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_5491741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491741 prefixEnd_5491741 := by exact prefixLift 5491741
  have htrace : WordTrace (prefixWord ++ tailWord_5491741) baseStart_5491741 baseEnd_5491741 := by
    simpa [prefixWord, tailWord_5491741, baseEnd_5491741] using wordTrace_append hprefix tailTrace_5491741
  have hstable : (prefixWord ++ tailWord_5491741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491741).length < 2 ^ (prefixWord ++ tailWord_5491741).sum := by decide
  have hdescent : baseEnd_5491741 < baseStart_5491741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491751 : List Nat := [1, 1, 7, 1, 1, 2, 3, 7]
def baseStart_5491751 : Nat := 118140960795 + 5491751 * 2 ^ 59
def prefixEnd_5491751 : Nat := 4983230072969 + 3 ^ 40 * 5491751 * 2
def baseEnd_5491751 : Nat := 104441033252209193802089

theorem tailTrace_5491751 : CollatzResearch.WordTrace tailWord_5491751 prefixEnd_5491751 104441033252209193802089 := by
  unfold tailWord_5491751
  simp only [CollatzResearch.WordTrace]
  refine ⟨200300614327331518244571107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133533742884887678829714071 200300614327331518244571107)
  ·
    refine ⟨300450921490997277366856661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200300614327331518244571107 300450921490997277366856661)
    ·
      refine ⟨7041818472445248688285703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 300450921490997277366856661 7041818472445248688285703)
      ·
        refine ⟨10562727708667873032428555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041818472445248688285703 10562727708667873032428555)
        ·
          refine ⟨15844091563001809548642833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10562727708667873032428555 15844091563001809548642833)
          ·
            refine ⟨11883068672251357161482125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15844091563001809548642833 11883068672251357161482125)
            ·
              refine ⟨4456150752094258935555797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11883068672251357161482125 4456150752094258935555797)
              ·
                refine ⟨104441033252209193802089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4456150752094258935555797 104441033252209193802089)
                ·
                  rfl

theorem cell23_5491751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 7].length) (baseStart_5491751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491751 prefixEnd_5491751 := by exact prefixLift 5491751
  have htrace : WordTrace (prefixWord ++ tailWord_5491751) baseStart_5491751 baseEnd_5491751 := by
    simpa [prefixWord, tailWord_5491751, baseEnd_5491751] using wordTrace_append hprefix tailTrace_5491751
  have hstable : (prefixWord ++ tailWord_5491751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491751).length < 2 ^ (prefixWord ++ tailWord_5491751).sum := by decide
  have hdescent : baseEnd_5491751 < baseStart_5491751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491794 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5491794 : Nat := 118140960795 + 5491794 * 2 ^ 59
def prefixEnd_5491794 : Nat := 4983230072969 + 3 ^ 40 * 5491794 * 2
def baseEnd_5491794 : Nat := 939976659159263854806235

theorem tailTrace_5491794 : CollatzResearch.WordTrace tailWord_5491794 prefixEnd_5491794 939976659159263854806235 := by
  unfold tailWord_5491794
  simp only [CollatzResearch.WordTrace]
  refine ⟨50075545666543934147096609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133534788444117157725590957 50075545666543934147096609)
  ·
    refine ⟨37556659249907950610322457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50075545666543934147096609 37556659249907950610322457)
    ·
      refine ⟨28167494437430962957741843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37556659249907950610322457 28167494437430962957741843)
      ·
        refine ⟨42251241656146444436612765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28167494437430962957741843 42251241656146444436612765)
        ·
          refine ⟨15844215621054916663729787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42251241656146444436612765 15844215621054916663729787)
          ·
            refine ⟨23766323431582374995594681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15844215621054916663729787 23766323431582374995594681)
            ·
              refine ⟨17824742573686781246696011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23766323431582374995594681 17824742573686781246696011)
              ·
                refine ⟨26737113860530171870044017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17824742573686781246696011 26737113860530171870044017)
                ·
                  refine ⟨20052835395397628902533013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26737113860530171870044017 20052835395397628902533013)
                  ·
                    refine ⟨939976659159263854806235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20052835395397628902533013 939976659159263854806235)
                    ·
                      rfl

theorem cell23_5491794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5491794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491794 prefixEnd_5491794 := by exact prefixLift 5491794
  have htrace : WordTrace (prefixWord ++ tailWord_5491794) baseStart_5491794 baseEnd_5491794 := by
    simpa [prefixWord, tailWord_5491794, baseEnd_5491794] using wordTrace_append hprefix tailTrace_5491794
  have hstable : (prefixWord ++ tailWord_5491794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491794).length < 2 ^ (prefixWord ++ tailWord_5491794).sum := by decide
  have hdescent : baseEnd_5491794 < baseStart_5491794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491804 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5491804 : Nat := 118140960795 + 5491804 * 2 ^ 59
def prefixEnd_5491804 : Nat := 4983230072969 + 3 ^ 40 * 5491804 * 2
def baseEnd_5491804 : Nat := 2819935112284336525293659

theorem tailTrace_5491804 : CollatzResearch.WordTrace tailWord_5491804 prefixEnd_5491804 2819935112284336525293659 := by
  unfold tailWord_5491804
  simp only [CollatzResearch.WordTrace]
  refine ⟨100151273698069754148125233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133535031597426338864166977 100151273698069754148125233)
  ·
    refine ⟨75113455273552315611093925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100151273698069754148125233 75113455273552315611093925)
    ·
      refine ⟨14083772863791059177080111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75113455273552315611093925 14083772863791059177080111)
      ·
        refine ⟨21125659295686588765620167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14083772863791059177080111 21125659295686588765620167)
        ·
          refine ⟨31688488943529883148430251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21125659295686588765620167 31688488943529883148430251)
          ·
            refine ⟨47532733415294824722645377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31688488943529883148430251 47532733415294824722645377)
            ·
              refine ⟨35649550061471118541984033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47532733415294824722645377 35649550061471118541984033)
              ·
                refine ⟨26737162546103338906488025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35649550061471118541984033 26737162546103338906488025)
                ·
                  refine ⟨20052871909577504179866019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26737162546103338906488025 20052871909577504179866019)
                  ·
                    refine ⟨30079307864366256269799029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20052871909577504179866019 30079307864366256269799029)
                    ·
                      refine ⟨2819935112284336525293659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30079307864366256269799029 2819935112284336525293659)
                      ·
                        rfl

theorem cell23_5491804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5491804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491804 prefixEnd_5491804 := by exact prefixLift 5491804
  have htrace : WordTrace (prefixWord ++ tailWord_5491804) baseStart_5491804 baseEnd_5491804 := by
    simpa [prefixWord, tailWord_5491804, baseEnd_5491804] using wordTrace_append hprefix tailTrace_5491804
  have hstable : (prefixWord ++ tailWord_5491804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491804).length < 2 ^ (prefixWord ++ tailWord_5491804).sum := by decide
  have hdescent : baseEnd_5491804 < baseStart_5491804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491807 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 7]
def baseStart_5491807 : Nat := 118140960795 + 5491807 * 2 ^ 59
def prefixEnd_5491807 : Nat := 4983230072969 + 3 ^ 40 * 5491807 * 2
def baseEnd_5491807 : Nat := 313326294747366668172905

theorem tailTrace_5491807 : CollatzResearch.WordTrace tailWord_5491807 prefixEnd_5491807 313326294747366668172905 := by
  unfold tailWord_5491807
  simp only [CollatzResearch.WordTrace]
  refine ⟨200302656815128639808609675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133535104543419093205739783 200302656815128639808609675)
  ·
    refine ⟨300453985222692959712914513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200302656815128639808609675 300453985222692959712914513)
    ·
      refine ⟨225340488917019719784685885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300453985222692959712914513 225340488917019719784685885)
      ·
        refine ⟨84502683343882394919257207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225340488917019719784685885 84502683343882394919257207)
        ·
          refine ⟨126754025015823592378885811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84502683343882394919257207 126754025015823592378885811)
          ·
            refine ⟨190131037523735388568328717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126754025015823592378885811 190131037523735388568328717)
            ·
              refine ⟨71299139071400770713123269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190131037523735388568328717 71299139071400770713123269)
              ·
                refine ⟨13368588575887644508710613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71299139071400770713123269 13368588575887644508710613)
                ·
                  refine ⟨313326294747366668172905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13368588575887644508710613 313326294747366668172905)
                  ·
                    rfl

theorem cell23_5491807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 7].length) (baseStart_5491807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491807 prefixEnd_5491807 := by exact prefixLift 5491807
  have htrace : WordTrace (prefixWord ++ tailWord_5491807) baseStart_5491807 baseEnd_5491807 := by
    simpa [prefixWord, tailWord_5491807, baseEnd_5491807] using wordTrace_append hprefix tailTrace_5491807
  have hstable : (prefixWord ++ tailWord_5491807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491807).length < 2 ^ (prefixWord ++ tailWord_5491807).sum := by decide
  have hdescent : baseEnd_5491807 < baseStart_5491807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491818 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_5491818 : Nat := 118140960795 + 5491818 * 2 ^ 59
def prefixEnd_5491818 : Nat := 4983230072969 + 3 ^ 40 * 5491818 * 2
def baseEnd_5491818 : Nat := 2819942301013499470518595

theorem tailTrace_5491818 : CollatzResearch.WordTrace tailWord_5491818 prefixEnd_5491818 2819942301013499470518595 := by
  unfold tailWord_5491818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50075764504522197171815027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133535372012059192458173405 50075764504522197171815027)
  ·
    refine ⟨75113646756783295757722541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50075764504522197171815027 75113646756783295757722541)
    ·
      refine ⟨28167617533793735909145953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75113646756783295757722541 28167617533793735909145953)
      ·
        refine ⟨21125713150345301931859465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28167617533793735909145953 21125713150345301931859465)
        ·
          refine ⟨15844284862758976448894599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21125713150345301931859465 15844284862758976448894599)
          ·
            refine ⟨23766427294138464673341899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15844284862758976448894599 23766427294138464673341899)
            ·
              refine ⟨35649640941207697010012849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23766427294138464673341899 35649640941207697010012849)
              ·
                refine ⟨26737230705905772757509637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35649640941207697010012849 26737230705905772757509637)
                ·
                  refine ⟨5013230757357332392033057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26737230705905772757509637 5013230757357332392033057)
                  ·
                    refine ⟨3759923068017999294024793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5013230757357332392033057 3759923068017999294024793)
                    ·
                      refine ⟨2819942301013499470518595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3759923068017999294024793 2819942301013499470518595)
                      ·
                        rfl

theorem cell23_5491818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_5491818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491818 prefixEnd_5491818 := by exact prefixLift 5491818
  have htrace : WordTrace (prefixWord ++ tailWord_5491818) baseStart_5491818 baseEnd_5491818 := by
    simpa [prefixWord, tailWord_5491818, baseEnd_5491818] using wordTrace_append hprefix tailTrace_5491818
  have hstable : (prefixWord ++ tailWord_5491818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491818).length < 2 ^ (prefixWord ++ tailWord_5491818).sum := by decide
  have hdescent : baseEnd_5491818 < baseStart_5491818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491841 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 7]
def baseStart_5491841 : Nat := 118140960795 + 5491841 * 2 ^ 59
def prefixEnd_5491841 : Nat := 4983230072969 + 3 ^ 40 * 5491841 * 2
def baseEnd_5491841 : Nat := 313328234563172542281221

theorem tailTrace_5491841 : CollatzResearch.WordTrace tailWord_5491841 prefixEnd_5491841 313328234563172542281221 := by
  unfold tailWord_5491841
  simp only [CollatzResearch.WordTrace]
  refine ⟨200303896897005463615347377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133535931264670309076898251 200303896897005463615347377)
  ·
    refine ⟨150227922672754097711510533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200303896897005463615347377 150227922672754097711510533)
    ·
      refine ⟨28167735501141393320908225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150227922672754097711510533 28167735501141393320908225)
      ·
        refine ⟨21125801625856044990681169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28167735501141393320908225 21125801625856044990681169)
        ·
          refine ⟨15844351219392033743010877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21125801625856044990681169 15844351219392033743010877)
          ·
            refine ⟨5941631707272012653629079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15844351219392033743010877 5941631707272012653629079)
            ·
              refine ⟨8912447560908018980443619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941631707272012653629079 8912447560908018980443619)
              ·
                refine ⟨13368671341362028470665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8912447560908018980443619 13368671341362028470665429)
                ·
                  refine ⟨313328234563172542281221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13368671341362028470665429 313328234563172542281221)
                  ·
                    rfl

theorem cell23_5491841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_5491841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491841 prefixEnd_5491841 := by exact prefixLift 5491841
  have htrace : WordTrace (prefixWord ++ tailWord_5491841) baseStart_5491841 baseEnd_5491841 := by
    simpa [prefixWord, tailWord_5491841, baseEnd_5491841] using wordTrace_append hprefix tailTrace_5491841
  have hstable : (prefixWord ++ tailWord_5491841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491841).length < 2 ^ (prefixWord ++ tailWord_5491841).sum := by decide
  have hdescent : baseEnd_5491841 < baseStart_5491841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491884 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_5491884 : Nat := 118140960795 + 5491884 * 2 ^ 59
def prefixEnd_5491884 : Nat := 4983230072969 + 3 ^ 40 * 5491884 * 2
def baseEnd_5491884 : Nat := 939992063578898737431097

theorem tailTrace_5491884 : CollatzResearch.WordTrace tailWord_5491884 prefixEnd_5491884 939992063578898737431097 := by
  unfold tailWord_5491884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100152732617924840979581353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133536976823899787972775137 100152732617924840979581353)
  ·
    refine ⟨75114549463443630734686015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100152732617924840979581353 75114549463443630734686015)
    ·
      refine ⟨112671824195165446102029023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75114549463443630734686015 112671824195165446102029023)
      ·
        refine ⟨169007736292748169153043535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112671824195165446102029023 169007736292748169153043535)
        ·
          refine ⟨253511604439122253729565303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169007736292748169153043535 253511604439122253729565303)
          ·
            refine ⟨380267406658683380594347955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253511604439122253729565303 380267406658683380594347955)
            ·
              refine ⟨570401109988025070891521933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380267406658683380594347955 570401109988025070891521933)
              ·
                refine ⟨213900416245509401584320725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570401109988025070891521933 213900416245509401584320725)
                ·
                  refine ⟨5013291005754126599632517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213900416245509401584320725 5013291005754126599632517)
                  ·
                    refine ⟨939992063578898737431097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013291005754126599632517 939992063578898737431097)
                    ·
                      rfl

theorem cell23_5491884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_5491884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491884 prefixEnd_5491884 := by exact prefixLift 5491884
  have htrace : WordTrace (prefixWord ++ tailWord_5491884) baseStart_5491884 baseEnd_5491884 := by
    simpa [prefixWord, tailWord_5491884, baseEnd_5491884] using wordTrace_append hprefix tailTrace_5491884
  have hstable : (prefixWord ++ tailWord_5491884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491884).length < 2 ^ (prefixWord ++ tailWord_5491884).sum := by decide
  have hdescent : baseEnd_5491884 < baseStart_5491884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491918 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_5491918 : Nat := 118140960795 + 5491918 * 2 ^ 59
def prefixEnd_5491918 : Nat := 4983230072969 + 3 ^ 40 * 5491918 * 2
def baseEnd_5491918 : Nat := 939997883026316359756045

theorem tailTrace_5491918 : CollatzResearch.WordTrace tailWord_5491918 prefixEnd_5491918 939997883026316359756045 := by
  unfold tailWord_5491918
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038338164715813220737551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133537803545151003843933605 25038338164715813220737551)
  ·
    refine ⟨37557507247073719831106327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25038338164715813220737551 37557507247073719831106327)
    ·
      refine ⟨56336260870610579746659491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37557507247073719831106327 56336260870610579746659491)
      ·
        refine ⟨84504391305915869619989237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56336260870610579746659491 84504391305915869619989237)
        ·
          refine ⟨7922286684929612776873991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84504391305915869619989237 7922286684929612776873991)
          ·
            refine ⟨11883430027394419165310987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922286684929612776873991 11883430027394419165310987)
            ·
              refine ⟨17825145041091628747966481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11883430027394419165310987 17825145041091628747966481)
              ·
                refine ⟨13368858780818721560974861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17825145041091628747966481 13368858780818721560974861)
                ·
                  refine ⟨5013322042807020585365573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13368858780818721560974861 5013322042807020585365573)
                  ·
                    refine ⟨939997883026316359756045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013322042807020585365573 939997883026316359756045)
                    ·
                      rfl

theorem cell23_5491918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_5491918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491918 prefixEnd_5491918 := by exact prefixLift 5491918
  have htrace : WordTrace (prefixWord ++ tailWord_5491918) baseStart_5491918 baseEnd_5491918 := by
    simpa [prefixWord, tailWord_5491918, baseEnd_5491918] using wordTrace_append hprefix tailTrace_5491918
  have hstable : (prefixWord ++ tailWord_5491918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491918).length < 2 ^ (prefixWord ++ tailWord_5491918).sum := by decide
  have hdescent : baseEnd_5491918 < baseStart_5491918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491986 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5491986 : Nat := 118140960795 + 5491986 * 2 ^ 59
def prefixEnd_5491986 : Nat := 4983230072969 + 3 ^ 40 * 5491986 * 2
def baseEnd_5491986 : Nat := 940009521921151604405941

theorem tailTrace_5491986 : CollatzResearch.WordTrace tailWord_5491986 prefixEnd_5491986 940009521921151604405941 := by
  unfold tailWord_5491986
  simp only [CollatzResearch.WordTrace]
  refine ⟨50077296370370038344843953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133539456987653435586250541 50077296370370038344843953)
  ·
    refine ⟨37557972277777528758632965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50077296370370038344843953 37557972277777528758632965)
    ·
      refine ⟨7042119802083286642243681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37557972277777528758632965 7042119802083286642243681)
      ·
        refine ⟨5281589851562464981682761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7042119802083286642243681 5281589851562464981682761)
        ·
          refine ⟨3961192388671848736262071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5281589851562464981682761 3961192388671848736262071)
          ·
            refine ⟨5941788583007773104393107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961192388671848736262071 5941788583007773104393107)
            ·
              refine ⟨8912682874511659656589661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941788583007773104393107 8912682874511659656589661)
              ·
                refine ⟨3342256077941872371221123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8912682874511659656589661 3342256077941872371221123)
                ·
                  refine ⟨5013384116912808556831685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342256077941872371221123 5013384116912808556831685)
                  ·
                    refine ⟨940009521921151604405941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013384116912808556831685 940009521921151604405941)
                    ·
                      rfl

theorem cell23_5491986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5491986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491986 prefixEnd_5491986 := by exact prefixLift 5491986
  have htrace : WordTrace (prefixWord ++ tailWord_5491986) baseStart_5491986 baseEnd_5491986 := by
    simpa [prefixWord, tailWord_5491986, baseEnd_5491986] using wordTrace_append hprefix tailTrace_5491986
  have hstable : (prefixWord ++ tailWord_5491986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491986).length < 2 ^ (prefixWord ++ tailWord_5491986).sum := by decide
  have hdescent : baseEnd_5491986 < baseStart_5491986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491991 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 6, 4]
def baseStart_5491991 : Nat := 118140960795 + 5491991 * 2 ^ 59
def prefixEnd_5491991 : Nat := 4983230072969 + 3 ^ 40 * 5491991 * 2
def baseEnd_5491991 : Nat := 940010377722242431218433

theorem tailTrace_5491991 : CollatzResearch.WordTrace tailWord_5491991 prefixEnd_5491991 940010377722242431218433 := by
  unfold tailWord_5491991
  simp only [CollatzResearch.WordTrace]
  refine ⟨200309367846462039233307827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133539578564308026155538551 200309367846462039233307827)
  ·
    refine ⟨300464051769693058849961741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200309367846462039233307827 300464051769693058849961741)
    ·
      refine ⟨112674019413634897068735653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300464051769693058849961741 112674019413634897068735653)
      ·
        refine ⟨21126378640056543200387935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112674019413634897068735653 21126378640056543200387935)
        ·
          refine ⟨31689567960084814800581903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21126378640056543200387935 31689567960084814800581903)
          ·
            refine ⟨47534351940127222200872855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31689567960084814800581903 47534351940127222200872855)
            ·
              refine ⟨71301527910190833301309283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47534351940127222200872855 71301527910190833301309283)
              ·
                refine ⟨106952291865286249951963925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71301527910190833301309283 106952291865286249951963925)
                ·
                  refine ⟨5013388681185292966498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106952291865286249951963925 5013388681185292966498309)
                  ·
                    refine ⟨940010377722242431218433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013388681185292966498309 940010377722242431218433)
                    ·
                      rfl

theorem cell23_5491991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_5491991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491991 prefixEnd_5491991 := by exact prefixLift 5491991
  have htrace : WordTrace (prefixWord ++ tailWord_5491991) baseStart_5491991 baseEnd_5491991 := by
    simpa [prefixWord, tailWord_5491991, baseEnd_5491991] using wordTrace_append hprefix tailTrace_5491991
  have hstable : (prefixWord ++ tailWord_5491991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491991).length < 2 ^ (prefixWord ++ tailWord_5491991).sum := by decide
  have hdescent : baseEnd_5491991 < baseStart_5491991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5491992 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 1, 1, 3]
def baseStart_5491992 : Nat := 118140960795 + 5491992 * 2 ^ 59
def prefixEnd_5491992 : Nat := 4983230072969 + 3 ^ 40 * 5491992 * 2
def baseEnd_5491992 : Nat := 2820031646647381789742795

theorem tailTrace_5491992 : CollatzResearch.WordTrace tailWord_5491992 prefixEnd_5491992 2820031646647381789742795 := by
  unfold tailWord_5491992
  simp only [CollatzResearch.WordTrace]
  refine ⟨100154702159729208202047115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133539602879638944269396153 100154702159729208202047115)
  ·
    refine ⟨150232053239593812303070673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100154702159729208202047115 150232053239593812303070673)
    ·
      refine ⟨112674039929695359227303005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150232053239593812303070673 112674039929695359227303005)
      ·
        refine ⟨42252764973635759710238627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112674039929695359227303005 42252764973635759710238627)
        ·
          refine ⟨63379147460453639565357941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42252764973635759710238627 63379147460453639565357941)
          ·
            refine ⟨5941795074417528709252307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63379147460453639565357941 5941795074417528709252307)
            ·
              refine ⟨8912692611626293063878461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941795074417528709252307 8912692611626293063878461)
              ·
                refine ⟨3342259729359859898954423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8912692611626293063878461 3342259729359859898954423)
                ·
                  refine ⟨5013389594039789848431635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342259729359859898954423 5013389594039789848431635)
                  ·
                    refine ⟨7520084391059684772647453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5013389594039789848431635 7520084391059684772647453)
                    ·
                      refine ⟨2820031646647381789742795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7520084391059684772647453 2820031646647381789742795)
                      ·
                        rfl

theorem cell23_5491992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_5491992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5491992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5491992 prefixEnd_5491992 := by exact prefixLift 5491992
  have htrace : WordTrace (prefixWord ++ tailWord_5491992) baseStart_5491992 baseEnd_5491992 := by
    simpa [prefixWord, tailWord_5491992, baseEnd_5491992] using wordTrace_append hprefix tailTrace_5491992
  have hstable : (prefixWord ++ tailWord_5491992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5491992).length < 2 ^ (prefixWord ++ tailWord_5491992).sum := by decide
  have hdescent : baseEnd_5491992 < baseStart_5491992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5491992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492001 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5492001 : Nat := 118140960795 + 5492001 * 2 ^ 59
def prefixEnd_5492001 : Nat := 4983230072969 + 3 ^ 40 * 5492001 * 2
def baseEnd_5492001 : Nat := 2820036267973272254530253

theorem tailTrace_5492001 : CollatzResearch.WordTrace tailWord_5492001 prefixEnd_5492001 2820036267973272254530253 := by
  unfold tailWord_5492001
  simp only [CollatzResearch.WordTrace]
  refine ⟨200309732576425810941171857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133539821717617207294114571 200309732576425810941171857)
  ·
    refine ⟨150232299432319358205878893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200309732576425810941171857 150232299432319358205878893)
    ·
      refine ⟨56337112287119759327204585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150232299432319358205878893 56337112287119759327204585)
      ·
        refine ⟨42252834215339819495403439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56337112287119759327204585 42252834215339819495403439)
        ·
          refine ⟨63379251323009729243105159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42252834215339819495403439 63379251323009729243105159)
          ·
            refine ⟨95068876984514593864657739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63379251323009729243105159 95068876984514593864657739)
            ·
              refine ⟨142603315476771890796986609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95068876984514593864657739 142603315476771890796986609)
              ·
                refine ⟨106952486607578918097739957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142603315476771890796986609 106952486607578918097739957)
                ·
                  refine ⟨10026795619460523571663121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106952486607578918097739957 10026795619460523571663121)
                  ·
                    refine ⟨7520096714595392678747341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10026795619460523571663121 7520096714595392678747341)
                    ·
                      refine ⟨2820036267973272254530253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7520096714595392678747341 2820036267973272254530253)
                      ·
                        rfl

theorem cell23_5492001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5492001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492001 prefixEnd_5492001 := by exact prefixLift 5492001
  have htrace : WordTrace (prefixWord ++ tailWord_5492001) baseStart_5492001 baseEnd_5492001 := by
    simpa [prefixWord, tailWord_5492001, baseEnd_5492001] using wordTrace_append hprefix tailTrace_5492001
  have hstable : (prefixWord ++ tailWord_5492001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492001).length < 2 ^ (prefixWord ++ tailWord_5492001).sum := by decide
  have hdescent : baseEnd_5492001 < baseStart_5492001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492008 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5492008 : Nat := 118140960795 + 5492008 * 2 ^ 59
def prefixEnd_5492008 : Nat := 4983230072969 + 3 ^ 40 * 5492008 * 2
def baseEnd_5492008 : Nat := 940013287445951242380907

theorem tailTrace_5492008 : CollatzResearch.WordTrace tailWord_5492008 prefixEnd_5492008 940013287445951242380907 := by
  unfold tailWord_5492008
  simp only [CollatzResearch.WordTrace]
  refine ⟨100154993943700225568338339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133539991924933634091117785 100154993943700225568338339)
  ·
    refine ⟨150232490915550338352507509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100154993943700225568338339 150232490915550338352507509)
    ·
      refine ⟨14084296023332844220547579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150232490915550338352507509 14084296023332844220547579)
      ·
        refine ⟨21126444034999266330821369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14084296023332844220547579 21126444034999266330821369)
        ·
          refine ⟨15844833026249449748116027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21126444034999266330821369 15844833026249449748116027)
          ·
            refine ⟨23767249539374174622174041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15844833026249449748116027 23767249539374174622174041)
            ·
              refine ⟨17825437154530630966630531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23767249539374174622174041 17825437154530630966630531)
              ·
                refine ⟨26738155731795946449945797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17825437154530630966630531 26738155731795946449945797)
                ·
                  refine ⟨5013404199711739959364837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26738155731795946449945797 5013404199711739959364837)
                  ·
                    refine ⟨940013287445951242380907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013404199711739959364837 940013287445951242380907)
                    ·
                      rfl

theorem cell23_5492008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5492008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492008 prefixEnd_5492008 := by exact prefixLift 5492008
  have htrace : WordTrace (prefixWord ++ tailWord_5492008) baseStart_5492008 baseEnd_5492008 := by
    simpa [prefixWord, tailWord_5492008, baseEnd_5492008] using wordTrace_append hprefix tailTrace_5492008
  have hstable : (prefixWord ++ tailWord_5492008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492008).length < 2 ^ (prefixWord ++ tailWord_5492008).sum := by decide
  have hdescent : baseEnd_5492008 < baseStart_5492008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492021 : List Nat := [1, 3, 3, 1, 2, 3, 2, 8]
def baseStart_5492021 : Nat := 118140960795 + 5492021 * 2 ^ 59
def prefixEnd_5492021 : Nat := 4983230072969 + 3 ^ 40 * 5492021 * 2
def baseEnd_5492021 : Nat := 104446168058754154677043

theorem tailTrace_5492021 : CollatzResearch.WordTrace tailWord_5492021 prefixEnd_5492021 104446168058754154677043 := by
  unfold tailWord_5492021
  simp only [CollatzResearch.WordTrace]
  refine ⟨200310462036353354356899917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133540308024235569571266611 200310462036353354356899917)
  ·
    refine ⟨75116423263632507883837469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200310462036353354356899917 75116423263632507883837469)
    ·
      refine ⟨28168658723862190456439051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75116423263632507883837469 28168658723862190456439051)
      ·
        refine ⟨42252988085793285684658577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28168658723862190456439051 42252988085793285684658577)
        ·
          refine ⟨31689741064344964263493933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42252988085793285684658577 31689741064344964263493933)
          ·
            refine ⟨11883652899129361598810225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31689741064344964263493933 11883652899129361598810225)
            ·
              refine ⟨8912739674347021199107669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11883652899129361598810225 8912739674347021199107669)
              ·
                refine ⟨104446168058754154677043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8912739674347021199107669 104446168058754154677043)
                ·
                  rfl

theorem cell23_5492021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 8].length) (baseStart_5492021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492021 prefixEnd_5492021 := by exact prefixLift 5492021
  have htrace : WordTrace (prefixWord ++ tailWord_5492021) baseStart_5492021 baseEnd_5492021 := by
    simpa [prefixWord, tailWord_5492021, baseEnd_5492021] using wordTrace_append hprefix tailTrace_5492021
  have hstable : (prefixWord ++ tailWord_5492021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492021).length < 2 ^ (prefixWord ++ tailWord_5492021).sum := by decide
  have hdescent : baseEnd_5492021 < baseStart_5492021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_5492024 : Nat := 118140960795 + 5492024 * 2 ^ 59
def prefixEnd_5492024 : Nat := 4983230072969 + 3 ^ 40 * 5492024 * 2
def baseEnd_5492024 : Nat := 2820048078028325664542647

theorem tailTrace_5492024 : CollatzResearch.WordTrace tailWord_5492024 prefixEnd_5492024 2820048078028325664542647 := by
  unfold tailWord_5492024
  simp only [CollatzResearch.WordTrace]
  refine ⟨100155285727671242934629563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133540380970228323912839417 100155285727671242934629563)
  ·
    refine ⟨150232928591506864401944345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100155285727671242934629563 150232928591506864401944345)
    ·
      refine ⟨112674696443630148301458259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150232928591506864401944345 112674696443630148301458259)
      ·
        refine ⟨169012044665445222452187389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112674696443630148301458259 169012044665445222452187389)
        ·
          refine ⟨63379516749541958419570271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169012044665445222452187389 63379516749541958419570271)
          ·
            refine ⟨95069275124312937629355407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63379516749541958419570271 95069275124312937629355407)
            ·
              refine ⟨142603912686469406444033111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95069275124312937629355407 142603912686469406444033111)
              ·
                refine ⟨213905869029704109666049667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142603912686469406444033111 213905869029704109666049667)
                ·
                  refine ⟨320858803544556164499074501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213905869029704109666049667 320858803544556164499074501)
                  ·
                    refine ⟨60161025664604280843576469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320858803544556164499074501 60161025664604280843576469)
                    ·
                      refine ⟨2820048078028325664542647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60161025664604280843576469 2820048078028325664542647)
                      ·
                        rfl

theorem cell23_5492024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_5492024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492024 prefixEnd_5492024 := by exact prefixLift 5492024
  have htrace : WordTrace (prefixWord ++ tailWord_5492024) baseStart_5492024 baseEnd_5492024 := by
    simpa [prefixWord, tailWord_5492024, baseEnd_5492024] using wordTrace_append hprefix tailTrace_5492024
  have hstable : (prefixWord ++ tailWord_5492024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492024).length < 2 ^ (prefixWord ++ tailWord_5492024).sum := by decide
  have hdescent : baseEnd_5492024 < baseStart_5492024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492025 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_5492025 : Nat := 118140960795 + 5492025 * 2 ^ 59
def prefixEnd_5492025 : Nat := 4983230072969 + 3 ^ 40 * 5492025 * 2
def baseEnd_5492025 : Nat := 940016197169660053543381

theorem tailTrace_5492025 : CollatzResearch.WordTrace tailWord_5492025 prefixEnd_5492025 940016197169660053543381 := by
  unfold tailWord_5492025
  simp only [CollatzResearch.WordTrace]
  refine ⟨200310607928338863040045529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133540405285559242026697019 200310607928338863040045529)
  ·
    refine ⟨150232955946254147280034147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200310607928338863040045529 150232955946254147280034147)
    ·
      refine ⟨225349433919381220920051221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150232955946254147280034147 225349433919381220920051221)
      ·
        refine ⟨10563254714970994730627401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 225349433919381220920051221 10563254714970994730627401)
        ·
          refine ⟨7922441036228246047970551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10563254714970994730627401 7922441036228246047970551)
          ·
            refine ⟨11883661554342369071955827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922441036228246047970551 11883661554342369071955827)
            ·
              refine ⟨17825492331513553607933741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11883661554342369071955827 17825492331513553607933741)
              ·
                refine ⟨6684559624317582602975153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17825492331513553607933741 6684559624317582602975153)
                ·
                  refine ⟨5013419718238186952231365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6684559624317582602975153 5013419718238186952231365)
                  ·
                    refine ⟨940016197169660053543381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013419718238186952231365 940016197169660053543381)
                    ·
                      rfl

theorem cell23_5492025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_5492025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492025 prefixEnd_5492025 := by exact prefixLift 5492025
  have htrace : WordTrace (prefixWord ++ tailWord_5492025) baseStart_5492025 baseEnd_5492025 := by
    simpa [prefixWord, tailWord_5492025, baseEnd_5492025] using wordTrace_append hprefix tailTrace_5492025
  have hstable : (prefixWord ++ tailWord_5492025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492025).length < 2 ^ (prefixWord ++ tailWord_5492025).sum := by decide
  have hdescent : baseEnd_5492025 < baseStart_5492025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492091 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3]
def baseStart_5492091 : Nat := 118140960795 + 5492091 * 2 ^ 59
def prefixEnd_5492091 : Nat := 4983230072969 + 3 ^ 40 * 5492091 * 2
def baseEnd_5492091 : Nat := 2820082481232176902404839

theorem tailTrace_5492091 : CollatzResearch.WordTrace tailWord_5492091 prefixEnd_5492091 2820082481232176902404839 := by
  unfold tailWord_5492091
  simp only [CollatzResearch.WordTrace]
  refine ⟨200313015146099756311948127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133542010097399837541298751 200313015146099756311948127)
  ·
    refine ⟨300469522719149634467922191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200313015146099756311948127 300469522719149634467922191)
    ·
      refine ⟨450704284078724451701883287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300469522719149634467922191 450704284078724451701883287)
      ·
        refine ⟨676056426118086677552824931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450704284078724451701883287 676056426118086677552824931)
        ·
          refine ⟨1014084639177130016329237397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676056426118086677552824931 1014084639177130016329237397)
          ·
            refine ⟨47535217461427969515433003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1014084639177130016329237397 47535217461427969515433003)
            ·
              refine ⟨71302826192141954273149505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47535217461427969515433003 71302826192141954273149505)
              ·
                refine ⟨53477119644106465704862129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71302826192141954273149505 53477119644106465704862129)
                ·
                  refine ⟨40107839733079849278646597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53477119644106465704862129 40107839733079849278646597)
                  ·
                    refine ⟨7520219949952471739746237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40107839733079849278646597 7520219949952471739746237)
                    ·
                      refine ⟨2820082481232176902404839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7520219949952471739746237 2820082481232176902404839)
                      ·
                        rfl

theorem cell23_5492091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3].length) (baseStart_5492091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492091 prefixEnd_5492091 := by exact prefixLift 5492091
  have htrace : WordTrace (prefixWord ++ tailWord_5492091) baseStart_5492091 baseEnd_5492091 := by
    simpa [prefixWord, tailWord_5492091, baseEnd_5492091] using wordTrace_append hprefix tailTrace_5492091
  have hstable : (prefixWord ++ tailWord_5492091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492091).length < 2 ^ (prefixWord ++ tailWord_5492091).sum := by decide
  have hdescent : baseEnd_5492091 < baseStart_5492091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492128 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 5]
def baseStart_5492128 : Nat := 118140960795 + 5492128 * 2 ^ 59
def prefixEnd_5492128 : Nat := 4983230072969 + 3 ^ 40 * 5492128 * 2
def baseEnd_5492128 : Nat := 313344608890710361960241

theorem tailTrace_5492128 : CollatzResearch.WordTrace tailWord_5492128 prefixEnd_5492128 313344608890710361960241 := by
  unfold tailWord_5492128
  simp only [CollatzResearch.WordTrace]
  refine ⟨100157182323482855815522519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133542909764643807754030025 100157182323482855815522519)
  ·
    refine ⟨150235773485224283723283779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100157182323482855815522519 150235773485224283723283779)
    ·
      refine ⟨225353660227836425584925669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150235773485224283723283779 225353660227836425584925669)
      ·
        refine ⟨42253811292719329797173563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225353660227836425584925669 42253811292719329797173563)
        ·
          refine ⟨63380716939078994695760345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42253811292719329797173563 63380716939078994695760345)
          ·
            refine ⟨47535537704309246021820259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63380716939078994695760345 47535537704309246021820259)
            ·
              refine ⟨71303306556463869032730389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47535537704309246021820259 71303306556463869032730389)
              ·
                refine ⟨3342342494834243860909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71303306556463869032730389 3342342494834243860909237)
                ·
                  refine ⟨313344608890710361960241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342342494834243860909237 313344608890710361960241)
                  ·
                    rfl

theorem cell23_5492128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 5].length) (baseStart_5492128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492128 prefixEnd_5492128 := by exact prefixLift 5492128
  have htrace : WordTrace (prefixWord ++ tailWord_5492128) baseStart_5492128 baseEnd_5492128 := by
    simpa [prefixWord, tailWord_5492128, baseEnd_5492128] using wordTrace_append hprefix tailTrace_5492128
  have hstable : (prefixWord ++ tailWord_5492128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492128).length < 2 ^ (prefixWord ++ tailWord_5492128).sum := by decide
  have hdescent : baseEnd_5492128 < baseStart_5492128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492158 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_5492158 : Nat := 118140960795 + 5492158 * 2 ^ 59
def prefixEnd_5492158 : Nat := 4983230072969 + 3 ^ 40 * 5492158 * 2
def baseEnd_5492158 : Nat := 940038961478676046755677

theorem tailTrace_5492158 : CollatzResearch.WordTrace tailWord_5492158 prefixEnd_5492158 940038961478676046755677 := by
  unfold tailWord_5492158
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039432354607128344329641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133543639224571351169758085 25039432354607128344329641)
  ·
    refine ⟨18779574265955346258247231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25039432354607128344329641 18779574265955346258247231)
    ·
      refine ⟨28169361398933019387370847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18779574265955346258247231 28169361398933019387370847)
      ·
        refine ⟨42254042098399529081056271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28169361398933019387370847 42254042098399529081056271)
        ·
          refine ⟨63381063147599293621584407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42254042098399529081056271 63381063147599293621584407)
          ·
            refine ⟨95071594721398940432376611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63381063147599293621584407 95071594721398940432376611)
            ·
              refine ⟨142607392082098410648564917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95071594721398940432376611 142607392082098410648564917)
              ·
                refine ⟨13369443007696725998302961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142607392082098410648564917 13369443007696725998302961)
                ·
                  refine ⟨10027082255772544498727221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13369443007696725998302961 10027082255772544498727221)
                  ·
                    refine ⟨940038961478676046755677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10027082255772544498727221 940038961478676046755677)
                    ·
                      rfl

theorem cell23_5492158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_5492158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492158 prefixEnd_5492158 := by exact prefixLift 5492158
  have htrace : WordTrace (prefixWord ++ tailWord_5492158) baseStart_5492158 baseEnd_5492158 := by
    simpa [prefixWord, tailWord_5492158, baseEnd_5492158] using wordTrace_append hprefix tailTrace_5492158
  have hstable : (prefixWord ++ tailWord_5492158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492158).length < 2 ^ (prefixWord ++ tailWord_5492158).sum := by decide
  have hdescent : baseEnd_5492158 < baseStart_5492158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492230 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5492230 : Nat := 118140960795 + 5492230 * 2 ^ 59
def prefixEnd_5492230 : Nat := 4983230072969 + 3 ^ 40 * 5492230 * 2
def baseEnd_5492230 : Nat := 313350428338127984285189

theorem tailTrace_5492230 : CollatzResearch.WordTrace tailWord_5492230 prefixEnd_5492230 313350428338127984285189 := by
  unfold tailWord_5492230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259940152893630720351817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133545389928397455367505429 6259940152893630720351817)
  ·
    refine ⟨4694955114670223040263863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6259940152893630720351817 4694955114670223040263863)
    ·
      refine ⟨7042432672005334560395795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694955114670223040263863 7042432672005334560395795)
      ·
        refine ⟨10563649008008001840593693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042432672005334560395795 10563649008008001840593693)
        ·
          refine ⟨3961368378003000690222635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10563649008008001840593693 3961368378003000690222635)
          ·
            refine ⟨5942052567004501035333953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961368378003000690222635 5942052567004501035333953)
            ·
              refine ⟨4456539425253375776500465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5942052567004501035333953 4456539425253375776500465)
              ·
                refine ⟨3342404568940031832375349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456539425253375776500465 3342404568940031832375349)
                ·
                  refine ⟨313350428338127984285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342404568940031832375349 313350428338127984285189)
                  ·
                    rfl

theorem cell23_5492230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5492230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492230 prefixEnd_5492230 := by exact prefixLift 5492230
  have htrace : WordTrace (prefixWord ++ tailWord_5492230) baseStart_5492230 baseEnd_5492230 := by
    simpa [prefixWord, tailWord_5492230, baseEnd_5492230] using wordTrace_append hprefix tailTrace_5492230
  have hstable : (prefixWord ++ tailWord_5492230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492230).length < 2 ^ (prefixWord ++ tailWord_5492230).sum := by decide
  have hdescent : baseEnd_5492230 < baseStart_5492230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492235 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 6]
def baseStart_5492235 : Nat := 118140960795 + 5492235 * 2 ^ 59
def prefixEnd_5492235 : Nat := 4983230072969 + 3 ^ 40 * 5492235 * 2
def baseEnd_5492235 : Nat := 313350713605158259889353

theorem tailTrace_5492235 : CollatzResearch.WordTrace tailWord_5492235 prefixEnd_5492235 313350713605158259889353 := by
  unfold tailWord_5492235
  simp only [CollatzResearch.WordTrace]
  refine ⟨200318267257578068905190159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133545511505052045936793439 200318267257578068905190159)
  ·
    refine ⟨300477400886367103357785239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200318267257578068905190159 300477400886367103357785239)
    ·
      refine ⟨450716101329550655036677859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300477400886367103357785239 450716101329550655036677859)
      ·
        refine ⟨676074151994325982555016789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450716101329550655036677859 676074151994325982555016789)
        ·
          refine ⟨7922743968683507608066603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 676074151994325982555016789 7922743968683507608066603)
          ·
            refine ⟨11884115953025261412099905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922743968683507608066603 11884115953025261412099905)
            ·
              refine ⟨8913086964768946059074929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11884115953025261412099905 8913086964768946059074929)
              ·
                refine ⟨6684815223576709544306197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8913086964768946059074929 6684815223576709544306197)
                ·
                  refine ⟨313350713605158259889353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6684815223576709544306197 313350713605158259889353)
                  ·
                    rfl

theorem cell23_5492235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 6].length) (baseStart_5492235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492235 prefixEnd_5492235 := by exact prefixLift 5492235
  have htrace : WordTrace (prefixWord ++ tailWord_5492235) baseStart_5492235 baseEnd_5492235 := by
    simpa [prefixWord, tailWord_5492235, baseEnd_5492235] using wordTrace_append hprefix tailTrace_5492235
  have hstable : (prefixWord ++ tailWord_5492235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492235).length < 2 ^ (prefixWord ++ tailWord_5492235).sum := by decide
  have hdescent : baseEnd_5492235 < baseStart_5492235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492255 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 4, 3, 2]
def baseStart_5492255 : Nat := 118140960795 + 5492255 * 2 ^ 59
def prefixEnd_5492255 : Nat := 4983230072969 + 3 ^ 40 * 5492255 * 2
def baseEnd_5492255 : Nat := 2820166692059514260754085

theorem tailTrace_5492255 : CollatzResearch.WordTrace tailWord_5492255 prefixEnd_5492255 2820166692059514260754085 := by
  unfold tailWord_5492255
  simp only [CollatzResearch.WordTrace]
  refine ⟨200318996717505612320918219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133545997811670408213945479 200318996717505612320918219)
  ·
    refine ⟨300478495076258418481377329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200318996717505612320918219 300478495076258418481377329)
    ·
      refine ⟨225358871307193813861032997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300478495076258418481377329 225358871307193813861032997)
      ·
        refine ⟨42254788370098840098943687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225358871307193813861032997 42254788370098840098943687)
        ·
          refine ⟨63382182555148260148415531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42254788370098840098943687 63382182555148260148415531)
          ·
            refine ⟨95073273832722390222623297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63382182555148260148415531 95073273832722390222623297)
            ·
              refine ⟨71304955374541792666967473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95073273832722390222623297 71304955374541792666967473)
              ·
                refine ⟨53478716530906344500225605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71304955374541792666967473 53478716530906344500225605)
                ·
                  refine ⟨10027259349544939593792301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53478716530906344500225605 10027259349544939593792301)
                  ·
                    refine ⟨3760222256079352347672113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10027259349544939593792301 3760222256079352347672113)
                    ·
                      refine ⟨2820166692059514260754085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760222256079352347672113 2820166692059514260754085)
                      ·
                        rfl

theorem cell23_5492255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_5492255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492255 prefixEnd_5492255 := by exact prefixLift 5492255
  have htrace : WordTrace (prefixWord ++ tailWord_5492255) baseStart_5492255 baseEnd_5492255 := by
    simpa [prefixWord, tailWord_5492255, baseEnd_5492255] using wordTrace_append hprefix tailTrace_5492255
  have hstable : (prefixWord ++ tailWord_5492255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492255).length < 2 ^ (prefixWord ++ tailWord_5492255).sum := by decide
  have hdescent : baseEnd_5492255 < baseStart_5492255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492279 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 1, 1, 3]
def baseStart_5492279 : Nat := 118140960795 + 5492279 * 2 ^ 59
def prefixEnd_5492279 : Nat := 4983230072969 + 3 ^ 40 * 5492279 * 2
def baseEnd_5492279 : Nat := 2820179015595222166853975

theorem tailTrace_5492279 : CollatzResearch.WordTrace tailWord_5492279 prefixEnd_5492279 2820179015595222166853975 := by
  unfold tailWord_5492279
  simp only [CollatzResearch.WordTrace]
  refine ⟨200319872069418664419791891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133546581379612442946527927 200319872069418664419791891)
  ·
    refine ⟨300479808104127996629687837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200319872069418664419791891 300479808104127996629687837)
    ·
      refine ⟨112679928039047998736132939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300479808104127996629687837 112679928039047998736132939)
      ·
        refine ⟨169019892058571998104199409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112679928039047998736132939 169019892058571998104199409)
        ·
          refine ⟨126764919043928998578149557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169019892058571998104199409 126764919043928998578149557)
          ·
            refine ⟨11884211160368343616701521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126764919043928998578149557 11884211160368343616701521)
            ·
              refine ⟨8913158370276257712526141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11884211160368343616701521 8913158370276257712526141)
              ·
                refine ⟨3342434388853596642197303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8913158370276257712526141 3342434388853596642197303)
                ·
                  refine ⟨5013651583280394963295955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342434388853596642197303 5013651583280394963295955)
                  ·
                    refine ⟨7520477374920592444943933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5013651583280394963295955 7520477374920592444943933)
                    ·
                      refine ⟨2820179015595222166853975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7520477374920592444943933 2820179015595222166853975)
                      ·
                        rfl

theorem cell23_5492279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_5492279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492279 prefixEnd_5492279 := by exact prefixLift 5492279
  have htrace : WordTrace (prefixWord ++ tailWord_5492279) baseStart_5492279 baseEnd_5492279 := by
    simpa [prefixWord, tailWord_5492279, baseEnd_5492279] using wordTrace_append hprefix tailTrace_5492279
  have hstable : (prefixWord ++ tailWord_5492279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492279).length < 2 ^ (prefixWord ++ tailWord_5492279).sum := by decide
  have hdescent : baseEnd_5492279 < baseStart_5492279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492288 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_5492288 : Nat := 118140960795 + 5492288 * 2 ^ 59
def prefixEnd_5492288 : Nat := 4983230072969 + 3 ^ 40 * 5492288 * 2
def baseEnd_5492288 : Nat := 2820183636921112631641433

theorem tailTrace_5492288 : CollatzResearch.WordTrace tailWord_5492288 prefixEnd_5492288 2820183636921112631641433 := by
  unfold tailWord_5492288
  simp only [CollatzResearch.WordTrace]
  refine ⟨100160100163193029478434759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133546800217590705971246345 100160100163193029478434759)
  ·
    refine ⟨150240150244789544217652139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100160100163193029478434759 150240150244789544217652139)
    ·
      refine ⟨225360225367184316326478209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150240150244789544217652139 225360225367184316326478209)
      ·
        refine ⟨169020169025388237244858657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225360225367184316326478209 169020169025388237244858657)
        ·
          refine ⟨126765126769041177933643993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169020169025388237244858657 126765126769041177933643993)
          ·
            refine ⟨95073845076780883450232995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126765126769041177933643993 95073845076780883450232995)
            ·
              refine ⟨142610767615171325175349493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95073845076780883450232995 142610767615171325175349493)
              ·
                refine ⟨13369759463922311735189015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142610767615171325175349493 13369759463922311735189015)
                ·
                  refine ⟨20054639195883467602783523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13369759463922311735189015 20054639195883467602783523)
                  ·
                    refine ⟨30081958793825201404175285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20054639195883467602783523 30081958793825201404175285)
                    ·
                      refine ⟨2820183636921112631641433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30081958793825201404175285 2820183636921112631641433)
                      ·
                        rfl

theorem cell23_5492288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_5492288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492288 prefixEnd_5492288 := by exact prefixLift 5492288
  have htrace : WordTrace (prefixWord ++ tailWord_5492288) baseStart_5492288 baseEnd_5492288 := by
    simpa [prefixWord, tailWord_5492288, baseEnd_5492288] using wordTrace_append hprefix tailTrace_5492288
  have hstable : (prefixWord ++ tailWord_5492288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492288).length < 2 ^ (prefixWord ++ tailWord_5492288).sum := by decide
  have hdescent : baseEnd_5492288 < baseStart_5492288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492298 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_5492298 : Nat := 118140960795 + 5492298 * 2 ^ 59
def prefixEnd_5492298 : Nat := 4983230072969 + 3 ^ 40 * 5492298 * 2
def baseEnd_5492298 : Nat := 2820188771727657592516387

theorem tailTrace_5492298 : CollatzResearch.WordTrace tailWord_5492298 prefixEnd_5492298 2820188771727657592516387 := by
  unfold tailWord_5492298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50080141264087457666183387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133547043370899887109822365 50080141264087457666183387)
  ·
    refine ⟨75120211896131186499275081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50080141264087457666183387 75120211896131186499275081)
    ·
      refine ⟨56340158922098389874456311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75120211896131186499275081 56340158922098389874456311)
      ·
        refine ⟨84510238383147584811684467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56340158922098389874456311 84510238383147584811684467)
        ·
          refine ⟨126765357574721377217526701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84510238383147584811684467 126765357574721377217526701)
          ·
            refine ⟨47537009090520516456572513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126765357574721377217526701 47537009090520516456572513)
            ·
              refine ⟨35652756817890387342429385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47537009090520516456572513 35652756817890387342429385)
              ·
                refine ⟨26739567613417790506822039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35652756817890387342429385 26739567613417790506822039)
                ·
                  refine ⟨40109351420126685760233059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26739567613417790506822039 40109351420126685760233059)
                  ·
                    refine ⟨60164027130190028640349589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40109351420126685760233059 60164027130190028640349589)
                    ·
                      refine ⟨2820188771727657592516387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60164027130190028640349589 2820188771727657592516387)
                      ·
                        rfl

theorem cell23_5492298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_5492298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492298 prefixEnd_5492298 := by exact prefixLift 5492298
  have htrace : WordTrace (prefixWord ++ tailWord_5492298) baseStart_5492298 baseEnd_5492298 := by
    simpa [prefixWord, tailWord_5492298, baseEnd_5492298] using wordTrace_append hprefix tailTrace_5492298
  have hstable : (prefixWord ++ tailWord_5492298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492298).length < 2 ^ (prefixWord ++ tailWord_5492298).sum := by decide
  have hdescent : baseEnd_5492298 < baseStart_5492298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492308 : List Nat := [2, 4, 1, 1, 1, 2, 2, 10]
def baseStart_5492308 : Nat := 118140960795 + 5492308 * 2 ^ 59
def prefixEnd_5492308 : Nat := 4983230072969 + 3 ^ 40 * 5492308 * 2
def baseEnd_5492308 : Nat := 104451626167933427903383

theorem tailTrace_5492308 : CollatzResearch.WordTrace tailWord_5492308 prefixEnd_5492308 104451626167933427903383 := by
  unfold tailWord_5492308
  simp only [CollatzResearch.WordTrace]
  refine ⟨100160464893156801186298789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133547286524209068248398385 100160464893156801186298789)
  ·
    refine ⟨18780087167466900222431023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100160464893156801186298789 18780087167466900222431023)
    ·
      refine ⟨28170130751200350333646535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18780087167466900222431023 28170130751200350333646535)
      ·
        refine ⟨42255196126800525500469803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28170130751200350333646535 42255196126800525500469803)
        ·
          refine ⟨63382794190200788250704705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42255196126800525500469803 63382794190200788250704705)
          ·
            refine ⟨47537095642650591188028529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63382794190200788250704705 47537095642650591188028529)
            ·
              refine ⟨35652821731987943391021397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47537095642650591188028529 35652821731987943391021397)
              ·
                refine ⟨104451626167933427903383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35652821731987943391021397 104451626167933427903383)
                ·
                  rfl

theorem cell23_5492308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 10].length) (baseStart_5492308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492308 prefixEnd_5492308 := by exact prefixLift 5492308
  have htrace : WordTrace (prefixWord ++ tailWord_5492308) baseStart_5492308 baseEnd_5492308 := by
    simpa [prefixWord, tailWord_5492308, baseEnd_5492308] using wordTrace_append hprefix tailTrace_5492308
  have hstable : (prefixWord ++ tailWord_5492308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492308).length < 2 ^ (prefixWord ++ tailWord_5492308).sum := by decide
  have hdescent : baseEnd_5492308 < baseStart_5492308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492325 : List Nat := [1, 3, 1, 3, 3, 1, 4, 7]
def baseStart_5492325 : Nat := 118140960795 + 5492325 * 2 ^ 59
def prefixEnd_5492325 : Nat := 4983230072969 + 3 ^ 40 * 5492325 * 2
def baseEnd_5492325 : Nat := 104451949470567740254769

theorem tailTrace_5492325 : CollatzResearch.WordTrace tailWord_5492325 prefixEnd_5492325 104451949470567740254769 := by
  unfold tailWord_5492325
  simp only [CollatzResearch.WordTrace]
  refine ⟨200321549827252014275966429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133547699884834676183977619 200321549827252014275966429)
  ·
    refine ⟨75120581185219505353487411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200321549827252014275966429 75120581185219505353487411)
    ·
      refine ⟨112680871777829258030231117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75120581185219505353487411 112680871777829258030231117)
      ·
        refine ⟨42255326916685971761336669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112680871777829258030231117 42255326916685971761336669)
        ·
          refine ⟨15845747593757239410501251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42255326916685971761336669 15845747593757239410501251)
          ·
            refine ⟨23768621390635859115751877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15845747593757239410501251 23768621390635859115751877)
            ·
              refine ⟨4456616510744223584203477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23768621390635859115751877 4456616510744223584203477)
              ·
                refine ⟨104451949470567740254769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4456616510744223584203477 104451949470567740254769)
                ·
                  rfl

theorem cell23_5492325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 7].length) (baseStart_5492325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492325 prefixEnd_5492325 := by exact prefixLift 5492325
  have htrace : WordTrace (prefixWord ++ tailWord_5492325) baseStart_5492325 baseEnd_5492325 := by
    simpa [prefixWord, tailWord_5492325, baseEnd_5492325] using wordTrace_append hprefix tailTrace_5492325
  have hstable : (prefixWord ++ tailWord_5492325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492325).length < 2 ^ (prefixWord ++ tailWord_5492325).sum := by decide
  have hdescent : baseEnd_5492325 < baseStart_5492325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492336 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 1, 2, 2]
def baseStart_5492336 : Nat := 118140960795 + 5492336 * 2 ^ 59
def prefixEnd_5492336 : Nat := 4983230072969 + 3 ^ 40 * 5492336 * 2
def baseEnd_5492336 : Nat := 2820208283992528443841213

theorem tailTrace_5492336 : CollatzResearch.WordTrace tailWord_5492336 prefixEnd_5492336 2820208283992528443841213 := by
  unfold tailWord_5492336
  simp only [CollatzResearch.WordTrace]
  refine ⟨100160975515106081577308431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133547967353474775436411241 100160975515106081577308431)
  ·
    refine ⟨150241463272659122365962647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100160975515106081577308431 150241463272659122365962647)
    ·
      refine ⟨225362194908988683548943971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150241463272659122365962647 225362194908988683548943971)
      ·
        refine ⟨338043292363483025323415957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225362194908988683548943971 338043292363483025323415957)
        ·
          refine ⟨15845779329538266812035123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 338043292363483025323415957 15845779329538266812035123)
          ·
            refine ⟨23768668994307400218052685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15845779329538266812035123 23768668994307400218052685)
            ·
              refine ⟨8913250872865275081769757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23768668994307400218052685 8913250872865275081769757)
              ·
                refine ⟨3342469077324478155663659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8913250872865275081769757 3342469077324478155663659)
                ·
                  refine ⟨5013703615986717233495489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342469077324478155663659 5013703615986717233495489)
                  ·
                    refine ⟨3760277711990037925121617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5013703615986717233495489 3760277711990037925121617)
                    ·
                      refine ⟨2820208283992528443841213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760277711990037925121617 2820208283992528443841213)
                      ·
                        rfl

theorem cell23_5492336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 2, 2].length) (baseStart_5492336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492336 prefixEnd_5492336 := by exact prefixLift 5492336
  have htrace : WordTrace (prefixWord ++ tailWord_5492336) baseStart_5492336 baseEnd_5492336 := by
    simpa [prefixWord, tailWord_5492336, baseEnd_5492336] using wordTrace_append hprefix tailTrace_5492336
  have hstable : (prefixWord ++ tailWord_5492336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492336).length < 2 ^ (prefixWord ++ tailWord_5492336).sum := by decide
  have hdescent : baseEnd_5492336 < baseStart_5492336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492348 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_5492348 : Nat := 118140960795 + 5492348 * 2 ^ 59
def prefixEnd_5492348 : Nat := 4983230072969 + 3 ^ 40 * 5492348 * 2
def baseEnd_5492348 : Nat := 2820214445760382396891157

theorem tailTrace_5492348 : CollatzResearch.WordTrace tailWord_5492348 prefixEnd_5492348 2820214445760382396891157 := by
  unfold tailWord_5492348
  simp only [CollatzResearch.WordTrace]
  refine ⟨100161194353084344602026849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133548259137445792802702465 100161194353084344602026849)
  ·
    refine ⟨75120895764813258451520137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100161194353084344602026849 75120895764813258451520137)
    ·
      refine ⟨56340671823609943838640103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75120895764813258451520137 56340671823609943838640103)
      ·
        refine ⟨84511007735414915757960155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56340671823609943838640103 84511007735414915757960155)
        ·
          refine ⟨126766511603122373636940233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84511007735414915757960155 126766511603122373636940233)
          ·
            refine ⟨95074883702341780227705175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126766511603122373636940233 95074883702341780227705175)
            ·
              refine ⟨142612325553512670341557763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95074883702341780227705175 142612325553512670341557763)
              ·
                refine ⟨213918488330269005512336645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142612325553512670341557763 213918488330269005512336645)
                ·
                  refine ⟨40109716561925438533563121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213918488330269005512336645 40109716561925438533563121)
                  ·
                    refine ⟨30082287421444078900172341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40109716561925438533563121 30082287421444078900172341)
                    ·
                      refine ⟨2820214445760382396891157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30082287421444078900172341 2820214445760382396891157)
                      ·
                        rfl

theorem cell23_5492348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_5492348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492348 prefixEnd_5492348 := by exact prefixLift 5492348
  have htrace : WordTrace (prefixWord ++ tailWord_5492348) baseStart_5492348 baseEnd_5492348 := by
    simpa [prefixWord, tailWord_5492348, baseEnd_5492348] using wordTrace_append hprefix tailTrace_5492348
  have hstable : (prefixWord ++ tailWord_5492348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492348).length < 2 ^ (prefixWord ++ tailWord_5492348).sum := by decide
  have hdescent : baseEnd_5492348 < baseStart_5492348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492352 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3]
def baseStart_5492352 : Nat := 118140960795 + 5492352 * 2 ^ 59
def prefixEnd_5492352 : Nat := 4983230072969 + 3 ^ 40 * 5492352 * 2
def baseEnd_5492352 : Nat := 2820216499683000381241139

theorem tailTrace_5492352 : CollatzResearch.WordTrace tailWord_5492352 prefixEnd_5492352 2820216499683000381241139 := by
  unfold tailWord_5492352
  simp only [CollatzResearch.WordTrace]
  refine ⟨100161267299077098943599655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133548356398769465258132873 100161267299077098943599655)
  ·
    refine ⟨150241900948615648415399483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100161267299077098943599655 150241900948615648415399483)
    ·
      refine ⟨225362851422923472623099225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150241900948615648415399483 225362851422923472623099225)
      ·
        refine ⟨169022138567192604467324419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225362851422923472623099225 169022138567192604467324419)
        ·
          refine ⟨253533207850788906700986629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169022138567192604467324419 253533207850788906700986629)
          ·
            refine ⟨47537476472022920006434993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253533207850788906700986629 47537476472022920006434993)
            ·
              refine ⟨35653107354017190004826245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47537476472022920006434993 35653107354017190004826245)
              ·
                refine ⟨6684957628878223125904921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35653107354017190004826245 6684957628878223125904921)
                ·
                  refine ⟨5013718221658667344428691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6684957628878223125904921 5013718221658667344428691)
                  ·
                    refine ⟨7520577332488001016643037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5013718221658667344428691 7520577332488001016643037)
                    ·
                      refine ⟨2820216499683000381241139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7520577332488001016643037 2820216499683000381241139)
                      ·
                        rfl

theorem cell23_5492352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_5492352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492352 prefixEnd_5492352 := by exact prefixLift 5492352
  have htrace : WordTrace (prefixWord ++ tailWord_5492352) baseStart_5492352 baseEnd_5492352 := by
    simpa [prefixWord, tailWord_5492352, baseEnd_5492352] using wordTrace_append hprefix tailTrace_5492352
  have hstable : (prefixWord ++ tailWord_5492352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492352).length < 2 ^ (prefixWord ++ tailWord_5492352).sum := by decide
  have hdescent : baseEnd_5492352 < baseStart_5492352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492353 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_5492353 : Nat := 118140960795 + 5492353 * 2 ^ 59
def prefixEnd_5492353 : Nat := 4983230072969 + 3 ^ 40 * 5492353 * 2
def baseEnd_5492353 : Nat := 2820217013163654877328635

theorem tailTrace_5492353 : CollatzResearch.WordTrace tailWord_5492353 prefixEnd_5492353 2820217013163654877328635 := by
  unfold tailWord_5492353
  simp only [CollatzResearch.WordTrace]
  refine ⟨200322571071150575057985713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133548380714100383371990475 200322571071150575057985713)
  ·
    refine ⟨150241928303362931293489285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200322571071150575057985713 150241928303362931293489285)
    ·
      refine ⟨28170361556880549617529241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150241928303362931293489285 28170361556880549617529241)
      ·
        refine ⟨21127771167660412213146931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28170361556880549617529241 21127771167660412213146931)
        ·
          refine ⟨31691656751490618319720397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21127771167660412213146931 31691656751490618319720397)
          ·
            refine ⟨11884371281808981869895149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31691656751490618319720397 11884371281808981869895149)
            ·
              refine ⟨4456639230678368201210681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11884371281808981869895149 4456639230678368201210681)
              ·
                refine ⟨3342479423008776150908011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456639230678368201210681 3342479423008776150908011)
                ·
                  refine ⟨5013719134513164226362017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342479423008776150908011 5013719134513164226362017)
                  ·
                    refine ⟨3760289350884873169771513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5013719134513164226362017 3760289350884873169771513)
                    ·
                      refine ⟨2820217013163654877328635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760289350884873169771513 2820217013163654877328635)
                      ·
                        rfl

theorem cell23_5492353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_5492353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492353 prefixEnd_5492353 := by exact prefixLift 5492353
  have htrace : WordTrace (prefixWord ++ tailWord_5492353) baseStart_5492353 baseEnd_5492353 := by
    simpa [prefixWord, tailWord_5492353, baseEnd_5492353] using wordTrace_append hprefix tailTrace_5492353
  have hstable : (prefixWord ++ tailWord_5492353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492353).length < 2 ^ (prefixWord ++ tailWord_5492353).sum := by decide
  have hdescent : baseEnd_5492353 < baseStart_5492353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492368 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_5492368 : Nat := 118140960795 + 5492368 * 2 ^ 59
def prefixEnd_5492368 : Nat := 4983230072969 + 3 ^ 40 * 5492368 * 2
def baseEnd_5492368 : Nat := 940074905124490772880355

theorem tailTrace_5492368 : CollatzResearch.WordTrace tailWord_5492368 prefixEnd_5492368 940074905124490772880355 := by
  unfold tailWord_5492368
  simp only [CollatzResearch.WordTrace]
  refine ⟨100161559083048116309890879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133548745444064155079854505 100161559083048116309890879)
  ·
    refine ⟨150242338624572174464836319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100161559083048116309890879 150242338624572174464836319)
    ·
      refine ⟨225363507936858261697254479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150242338624572174464836319 225363507936858261697254479)
      ·
        refine ⟨338045261905287392545881719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225363507936858261697254479 338045261905287392545881719)
        ·
          refine ⟨507067892857931088818822579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338045261905287392545881719 507067892857931088818822579)
          ·
            refine ⟨760601839286896633228233869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507067892857931088818822579 760601839286896633228233869)
            ·
              refine ⟨285225689732586237460587701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 760601839286896633228233869 285225689732586237460587701)
              ·
                refine ⟨26739908412429959761930097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285225689732586237460587701 26739908412429959761930097)
                ·
                  refine ⟨20054931309322469821447573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26739908412429959761930097 20054931309322469821447573)
                  ·
                    refine ⟨940074905124490772880355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20054931309322469821447573 940074905124490772880355)
                    ·
                      rfl

theorem cell23_5492368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_5492368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492368 prefixEnd_5492368 := by exact prefixLift 5492368
  have htrace : WordTrace (prefixWord ++ tailWord_5492368) baseStart_5492368 baseEnd_5492368 := by
    simpa [prefixWord, tailWord_5492368, baseEnd_5492368] using wordTrace_append hprefix tailTrace_5492368
  have hstable : (prefixWord ++ tailWord_5492368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492368).length < 2 ^ (prefixWord ++ tailWord_5492368).sum := by decide
  have hdescent : baseEnd_5492368 < baseStart_5492368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492408 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_5492408 : Nat := 118140960795 + 5492408 * 2 ^ 59
def prefixEnd_5492408 : Nat := 4983230072969 + 3 ^ 40 * 5492408 * 2
def baseEnd_5492408 : Nat := 2820245254599652162140881

theorem tailTrace_5492408 : CollatzResearch.WordTrace tailWord_5492408 prefixEnd_5492408 2820245254599652162140881 := by
  unfold tailWord_5492408
  simp only [CollatzResearch.WordTrace]
  refine ⟨100162288542975659725618939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133549718057300879634158585 100162288542975659725618939)
  ·
    refine ⟨150243432814463489588428409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100162288542975659725618939 150243432814463489588428409)
    ·
      refine ⟨112682574610847617191321307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150243432814463489588428409 112682574610847617191321307)
      ·
        refine ⟨169023861916271425786981961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112682574610847617191321307 169023861916271425786981961)
        ·
          refine ⟨126767896437203569340236471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169023861916271425786981961 126767896437203569340236471)
          ·
            refine ⟨190151844655805354010354707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126767896437203569340236471 190151844655805354010354707)
            ·
              refine ⟨285227766983708031015532061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190151844655805354010354707 285227766983708031015532061)
              ·
                refine ⟨106960412618890511630824523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285227766983708031015532061 106960412618890511630824523)
                ·
                  refine ⟨160440618928335767446236785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106960412618890511630824523 160440618928335767446236785)
                  ·
                    refine ⟨120330464196251825584677589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160440618928335767446236785 120330464196251825584677589)
                    ·
                      refine ⟨2820245254599652162140881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120330464196251825584677589 2820245254599652162140881)
                      ·
                        rfl

theorem cell23_5492408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5492408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492408 prefixEnd_5492408 := by exact prefixLift 5492408
  have htrace : WordTrace (prefixWord ++ tailWord_5492408) baseStart_5492408 baseEnd_5492408 := by
    simpa [prefixWord, tailWord_5492408, baseEnd_5492408] using wordTrace_append hprefix tailTrace_5492408
  have hstable : (prefixWord ++ tailWord_5492408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492408).length < 2 ^ (prefixWord ++ tailWord_5492408).sum := by decide
  have hdescent : baseEnd_5492408 < baseStart_5492408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492409 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5492409 : Nat := 118140960795 + 5492409 * 2 ^ 59
def prefixEnd_5492409 : Nat := 4983230072969 + 3 ^ 40 * 5492409 * 2
def baseEnd_5492409 : Nat := 2820245768080306658228377

theorem tailTrace_5492409 : CollatzResearch.WordTrace tailWord_5492409 prefixEnd_5492409 2820245768080306658228377 := by
  unfold tailWord_5492409
  simp only [CollatzResearch.WordTrace]
  refine ⟨200324613558947696622024281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133549742372631797748016187 200324613558947696622024281)
  ·
    refine ⟨150243460169210772466518211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200324613558947696622024281 150243460169210772466518211)
    ·
      refine ⟨225365190253816158699777317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150243460169210772466518211 225365190253816158699777317)
      ·
        refine ⟨42255973172590529756208247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225365190253816158699777317 42255973172590529756208247)
        ·
          refine ⟨63383959758885794634312371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42255973172590529756208247 63383959758885794634312371)
          ·
            refine ⟨95075939638328691951468557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63383959758885794634312371 95075939638328691951468557)
            ·
              refine ⟨35653477364373259481800709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95075939638328691951468557 35653477364373259481800709)
              ·
                refine ⟨6685027005819986152837633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35653477364373259481800709 6685027005819986152837633)
                ·
                  refine ⟨5013770254364989614628225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6685027005819986152837633 5013770254364989614628225)
                  ·
                    refine ⟨3760327690773742210971169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5013770254364989614628225 3760327690773742210971169)
                    ·
                      refine ⟨2820245768080306658228377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760327690773742210971169 2820245768080306658228377)
                      ·
                        rfl

theorem cell23_5492409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5492409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492409 prefixEnd_5492409 := by exact prefixLift 5492409
  have htrace : WordTrace (prefixWord ++ tailWord_5492409) baseStart_5492409 baseEnd_5492409 := by
    simpa [prefixWord, tailWord_5492409, baseEnd_5492409] using wordTrace_append hprefix tailTrace_5492409
  have hstable : (prefixWord ++ tailWord_5492409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492409).length < 2 ^ (prefixWord ++ tailWord_5492409).sum := by decide
  have hdescent : baseEnd_5492409 < baseStart_5492409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492449 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 5]
def baseStart_5492449 : Nat := 118140960795 + 5492449 * 2 ^ 59
def prefixEnd_5492449 : Nat := 4983230072969 + 3 ^ 40 * 5492449 * 2
def baseEnd_5492449 : Nat := 313362923034054055747577

theorem tailTrace_5492449 : CollatzResearch.WordTrace tailWord_5492449 prefixEnd_5492449 313362923034054055747577 := by
  unfold tailWord_5492449
  simp only [CollatzResearch.WordTrace]
  refine ⟨200326072478802783453480401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133550714985868522302320267 200326072478802783453480401)
  ·
    refine ⟨150244554359102087590110301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200326072478802783453480401 150244554359102087590110301)
    ·
      refine ⟨56341707884663282846291363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150244554359102087590110301 56341707884663282846291363)
      ·
        refine ⟨84512561826994924269437045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56341707884663282846291363 84512561826994924269437045)
        ·
          refine ⟨7923052671280774150259723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84512561826994924269437045 7923052671280774150259723)
          ·
            refine ⟨11884579006921161225389585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7923052671280774150259723 11884579006921161225389585)
            ·
              refine ⟨8913434255190870919042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11884579006921161225389585 8913434255190870919042189)
              ·
                refine ⟨3342537845696576594640821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8913434255190870919042189 3342537845696576594640821)
                ·
                  refine ⟨313362923034054055747577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342537845696576594640821 313362923034054055747577)
                  ·
                    rfl

theorem cell23_5492449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 5].length) (baseStart_5492449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492449 prefixEnd_5492449 := by exact prefixLift 5492449
  have htrace : WordTrace (prefixWord ++ tailWord_5492449) baseStart_5492449 baseEnd_5492449 := by
    simpa [prefixWord, tailWord_5492449, baseEnd_5492449] using wordTrace_append hprefix tailTrace_5492449
  have hstable : (prefixWord ++ tailWord_5492449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492449).length < 2 ^ (prefixWord ++ tailWord_5492449).sum := by decide
  have hdescent : baseEnd_5492449 < baseStart_5492449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492482 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5492482 : Nat := 118140960795 + 5492482 * 2 ^ 59
def prefixEnd_5492482 : Nat := 4983230072969 + 3 ^ 40 * 5492482 * 2
def baseEnd_5492482 : Nat := 2820283252168084872615541

theorem tailTrace_5492482 : CollatzResearch.WordTrace tailWord_5492482 prefixEnd_5492482 2820283252168084872615541 := by
  unfold tailWord_5492482
  simp only [CollatzResearch.WordTrace]
  refine ⟨50081819021920807522357925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133551517391788820059621133 50081819021920807522357925)
  ·
    refine ⟨9390341066610151410442111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50081819021920807522357925 9390341066610151410442111)
    ·
      refine ⟨14085511599915227115663167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390341066610151410442111 14085511599915227115663167)
      ·
        refine ⟨21128267399872840673494751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14085511599915227115663167 21128267399872840673494751)
        ·
          refine ⟨31692401099809261010242127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21128267399872840673494751 31692401099809261010242127)
          ·
            refine ⟨47538601649713891515363191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31692401099809261010242127 47538601649713891515363191)
            ·
              refine ⟨71307902474570837273044787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47538601649713891515363191 71307902474570837273044787)
              ·
                refine ⟨106961853711856255909567181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71307902474570837273044787 106961853711856255909567181)
                ·
                  refine ⟨40110695141946095966087693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106961853711856255909567181 40110695141946095966087693)
                  ·
                    refine ⟨15041510678229785987282885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40110695141946095966087693 15041510678229785987282885)
                    ·
                      refine ⟨2820283252168084872615541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15041510678229785987282885 2820283252168084872615541)
                      ·
                        rfl

theorem cell23_5492482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5492482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492482 prefixEnd_5492482 := by exact prefixLift 5492482
  have htrace : WordTrace (prefixWord ++ tailWord_5492482) baseStart_5492482 baseEnd_5492482 := by
    simpa [prefixWord, tailWord_5492482, baseEnd_5492482] using wordTrace_append hprefix tailTrace_5492482
  have hstable : (prefixWord ++ tailWord_5492482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492482).length < 2 ^ (prefixWord ++ tailWord_5492482).sum := by decide
  have hdescent : baseEnd_5492482 < baseStart_5492482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492492 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_5492492 : Nat := 118140960795 + 5492492 * 2 ^ 59
def prefixEnd_5492492 : Nat := 4983230072969 + 3 ^ 40 * 5492492 * 2
def baseEnd_5492492 : Nat := 940096128991543277830165

theorem tailTrace_5492492 : CollatzResearch.WordTrace tailWord_5492492 prefixEnd_5492492 940096128991543277830165 := by
  unfold tailWord_5492492
  simp only [CollatzResearch.WordTrace]
  refine ⟨100163820408823500898647865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133551760545098001198197153 100163820408823500898647865)
  ·
    refine ⟨75122865306617625673985899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100163820408823500898647865 75122865306617625673985899)
    ·
      refine ⟨112684297959926438510978849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75122865306617625673985899 112684297959926438510978849)
      ·
        refine ⟨84513223469944828883234137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112684297959926438510978849 84513223469944828883234137)
        ·
          refine ⟨63384917602458621662425603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84513223469944828883234137 63384917602458621662425603)
          ·
            refine ⟨95077376403687932493638405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63384917602458621662425603 95077376403687932493638405)
            ·
              refine ⟨17827008075691487342557201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95077376403687932493638405 17827008075691487342557201)
              ·
                refine ⟨13370256056768615506917901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17827008075691487342557201 13370256056768615506917901)
                ·
                  refine ⟨5013846021288230815094213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13370256056768615506917901 5013846021288230815094213)
                  ·
                    refine ⟨940096128991543277830165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013846021288230815094213 940096128991543277830165)
                    ·
                      rfl

theorem cell23_5492492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_5492492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492492 prefixEnd_5492492 := by exact prefixLift 5492492
  have htrace : WordTrace (prefixWord ++ tailWord_5492492) baseStart_5492492 baseEnd_5492492 := by
    simpa [prefixWord, tailWord_5492492, baseEnd_5492492] using wordTrace_append hprefix tailTrace_5492492
  have hstable : (prefixWord ++ tailWord_5492492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492492).length < 2 ^ (prefixWord ++ tailWord_5492492).sum := by decide
  have hdescent : baseEnd_5492492 < baseStart_5492492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492500 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 5]
def baseStart_5492500 : Nat := 118140960795 + 5492500 * 2 ^ 59
def prefixEnd_5492500 : Nat := 4983230072969 + 3 ^ 40 * 5492500 * 2
def baseEnd_5492500 : Nat := 313365832757762866910051

theorem tailTrace_5492500 : CollatzResearch.WordTrace tailWord_5492500 prefixEnd_5492500 313365832757762866910051 := by
  unfold tailWord_5492500
  simp only [CollatzResearch.WordTrace]
  refine ⟨100163966300809009581793477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133551955067745346109057969 100163966300809009581793477)
  ·
    refine ⟨18780743681401689296586277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100163966300809009581793477 18780743681401689296586277)
    ·
      refine ⟨3521389440262816743109927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18780743681401689296586277 3521389440262816743109927)
      ·
        refine ⟨5282084160394225114664891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521389440262816743109927 5282084160394225114664891)
        ·
          refine ⟨7923126240591337671997337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282084160394225114664891 7923126240591337671997337)
          ·
            refine ⟨5942344680443503253998003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7923126240591337671997337 5942344680443503253998003)
            ·
              refine ⟨8913517020665254880997005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942344680443503253998003 8913517020665254880997005)
              ·
                refine ⟨3342568882749470580373877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8913517020665254880997005 3342568882749470580373877)
                ·
                  refine ⟨313365832757762866910051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342568882749470580373877 313365832757762866910051)
                  ·
                    rfl

theorem cell23_5492500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_5492500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492500 prefixEnd_5492500 := by exact prefixLift 5492500
  have htrace : WordTrace (prefixWord ++ tailWord_5492500) baseStart_5492500 baseEnd_5492500 := by
    simpa [prefixWord, tailWord_5492500, baseEnd_5492500] using wordTrace_append hprefix tailTrace_5492500
  have hstable : (prefixWord ++ tailWord_5492500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492500).length < 2 ^ (prefixWord ++ tailWord_5492500).sum := by decide
  have hdescent : baseEnd_5492500 < baseStart_5492500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492552 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_5492552 : Nat := 118140960795 + 5492552 * 2 ^ 59
def prefixEnd_5492552 : Nat := 4983230072969 + 3 ^ 40 * 5492552 * 2
def baseEnd_5492552 : Nat := 940106398604633199580073

theorem tailTrace_5492552 : CollatzResearch.WordTrace tailWord_5492552 prefixEnd_5492552 940106398604633199580073 := by
  unfold tailWord_5492552
  simp only [CollatzResearch.WordTrace]
  refine ⟨100164914598714816022239955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133553219464953088029653273 100164914598714816022239955)
  ·
    refine ⟨150247371898072224033359933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100164914598714816022239955 150247371898072224033359933)
    ·
      refine ⟨56342764461777084012509975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150247371898072224033359933 56342764461777084012509975)
      ·
        refine ⟨84514146692665626018764963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56342764461777084012509975 84514146692665626018764963)
        ·
          refine ⟨126771220038998439028147445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84514146692665626018764963 126771220038998439028147445)
          ·
            refine ⟨11884801878656103658888823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126771220038998439028147445 11884801878656103658888823)
            ·
              refine ⟨17827202817984155488333235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11884801878656103658888823 17827202817984155488333235)
              ·
                refine ⟨26740804226976233232499853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17827202817984155488333235 26740804226976233232499853)
                ·
                  refine ⟨10027801585116087462187445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26740804226976233232499853 10027801585116087462187445)
                  ·
                    refine ⟨940106398604633199580073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10027801585116087462187445 940106398604633199580073)
                    ·
                      rfl

theorem cell23_5492552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_5492552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492552 prefixEnd_5492552 := by exact prefixLift 5492552
  have htrace : WordTrace (prefixWord ++ tailWord_5492552) baseStart_5492552 baseEnd_5492552 := by
    simpa [prefixWord, tailWord_5492552, baseEnd_5492552] using wordTrace_append hprefix tailTrace_5492552
  have hstable : (prefixWord ++ tailWord_5492552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492552).length < 2 ^ (prefixWord ++ tailWord_5492552).sum := by decide
  have hdescent : baseEnd_5492552 < baseStart_5492552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492569 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 1, 5]
def baseStart_5492569 : Nat := 118140960795 + 5492569 * 2 ^ 59
def prefixEnd_5492569 : Nat := 4983230072969 + 3 ^ 40 * 5492569 * 2
def baseEnd_5492569 : Nat := 940109308328342010742547

theorem tailTrace_5492569 : CollatzResearch.WordTrace tailWord_5492569 prefixEnd_5492569 940109308328342010742547 := by
  unfold tailWord_5492569
  simp only [CollatzResearch.WordTrace]
  refine ⟨200330449238368043947848761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133553632825578695965232507 200330449238368043947848761)
  ·
    refine ⟨150247836928776032960886571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200330449238368043947848761 150247836928776032960886571)
    ·
      refine ⟨225371755393164049441329857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150247836928776032960886571 225371755393164049441329857)
      ·
        refine ⟨169028816544873037080997393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225371755393164049441329857 169028816544873037080997393)
        ·
          refine ⟨126771612408654777810748045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169028816544873037080997393 126771612408654777810748045)
          ·
            refine ⟨47539354653245541679030517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126771612408654777810748045 47539354653245541679030517)
            ·
              refine ⟨4456814498741769532409111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47539354653245541679030517 4456814498741769532409111)
              ·
                refine ⟨6685221748112654298613667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456814498741769532409111 6685221748112654298613667)
                ·
                  refine ⟨10027832622168981447920501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685221748112654298613667 10027832622168981447920501)
                  ·
                    refine ⟨940109308328342010742547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10027832622168981447920501 940109308328342010742547)
                    ·
                      rfl

theorem cell23_5492569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_5492569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492569 prefixEnd_5492569 := by exact prefixLift 5492569
  have htrace : WordTrace (prefixWord ++ tailWord_5492569) baseStart_5492569 baseEnd_5492569 := by
    simpa [prefixWord, tailWord_5492569, baseEnd_5492569] using wordTrace_append hprefix tailTrace_5492569
  have hstable : (prefixWord ++ tailWord_5492569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492569).length < 2 ^ (prefixWord ++ tailWord_5492569).sum := by decide
  have hdescent : baseEnd_5492569 < baseStart_5492569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492585 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_5492585 : Nat := 118140960795 + 5492585 * 2 ^ 59
def prefixEnd_5492585 : Nat := 4983230072969 + 3 ^ 40 * 5492585 * 2
def baseEnd_5492585 : Nat := 2820336140675497969627567

theorem tailTrace_5492585 : CollatzResearch.WordTrace tailWord_5492585 prefixEnd_5492585 2820336140675497969627567 := by
  unfold tailWord_5492585
  simp only [CollatzResearch.WordTrace]
  refine ⟨200331032806310078680431209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133554021870873385786954139 200331032806310078680431209)
  ·
    refine ⟨150248274604732559010323407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200331032806310078680431209 150248274604732559010323407)
    ·
      refine ⟨225372411907098838515485111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150248274604732559010323407 225372411907098838515485111)
      ·
        refine ⟨338058617860648257773227667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225372411907098838515485111 338058617860648257773227667)
        ·
          refine ⟨507087926790972386659841501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338058617860648257773227667 507087926790972386659841501)
          ·
            refine ⟨190157972546614644997440563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507087926790972386659841501 190157972546614644997440563)
            ·
              refine ⟨285236958819921967496160845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190157972546614644997440563 285236958819921967496160845)
              ·
                refine ⟨106963859557470737811060317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285236958819921967496160845 106963859557470737811060317)
                ·
                  refine ⟨40111447334051526679147619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106963859557470737811060317 40111447334051526679147619)
                  ·
                    refine ⟨60167171001077290018721429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40111447334051526679147619 60167171001077290018721429)
                    ·
                      refine ⟨2820336140675497969627567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60167171001077290018721429 2820336140675497969627567)
                      ·
                        rfl

theorem cell23_5492585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_5492585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492585 prefixEnd_5492585 := by exact prefixLift 5492585
  have htrace : WordTrace (prefixWord ++ tailWord_5492585) baseStart_5492585 baseEnd_5492585 := by
    simpa [prefixWord, tailWord_5492585, baseEnd_5492585] using wordTrace_append hprefix tailTrace_5492585
  have hstable : (prefixWord ++ tailWord_5492585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492585).length < 2 ^ (prefixWord ++ tailWord_5492585).sum := by decide
  have hdescent : baseEnd_5492585 < baseStart_5492585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492602 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_5492602 : Nat := 118140960795 + 5492602 * 2 ^ 59
def prefixEnd_5492602 : Nat := 4983230072969 + 3 ^ 40 * 5492602 * 2
def baseEnd_5492602 : Nat := 2820344869846624403114989

theorem tailTrace_5492602 : CollatzResearch.WordTrace tailWord_5492602 prefixEnd_5492602 2820344869846624403114989 := by
  unfold tailWord_5492602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50082913211812122645950015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133554435231498993722533373 50082913211812122645950015)
  ·
    refine ⟨75124369817718183968925023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50082913211812122645950015 75124369817718183968925023)
    ·
      refine ⟨112686554726577275953387535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75124369817718183968925023 112686554726577275953387535)
      ·
        refine ⟨169029832089865913930081303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112686554726577275953387535 169029832089865913930081303)
        ·
          refine ⟨253544748134798870895121955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169029832089865913930081303 253544748134798870895121955)
          ·
            refine ⟨380317122202198306342682933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253544748134798870895121955 380317122202198306342682933)
            ·
              refine ⟨35654730206456091219626525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 380317122202198306342682933 35654730206456091219626525)
              ·
                refine ⟨13370523827421034207359947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35654730206456091219626525 13370523827421034207359947)
                ·
                  refine ⟨20055785741131551311039921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13370523827421034207359947 20055785741131551311039921)
                  ·
                    refine ⟨15041839305848663483279941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20055785741131551311039921 15041839305848663483279941)
                    ·
                      refine ⟨2820344869846624403114989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15041839305848663483279941 2820344869846624403114989)
                      ·
                        rfl

theorem cell23_5492602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_5492602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492602 prefixEnd_5492602 := by exact prefixLift 5492602
  have htrace : WordTrace (prefixWord ++ tailWord_5492602) baseStart_5492602 baseEnd_5492602 := by
    simpa [prefixWord, tailWord_5492602, baseEnd_5492602] using wordTrace_append hprefix tailTrace_5492602
  have hstable : (prefixWord ++ tailWord_5492602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492602).length < 2 ^ (prefixWord ++ tailWord_5492602).sum := by decide
  have hdescent : baseEnd_5492602 < baseStart_5492602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492606 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5492606 : Nat := 118140960795 + 5492606 * 2 ^ 59
def prefixEnd_5492606 : Nat := 4983230072969 + 3 ^ 40 * 5492606 * 2
def baseEnd_5492606 : Nat := 2820346923769242387464971

theorem tailTrace_5492606 : CollatzResearch.WordTrace tailWord_5492606 prefixEnd_5492606 2820346923769242387464971 := by
  unfold tailWord_5492606
  simp only [CollatzResearch.WordTrace]
  refine ⟨25041474842404249908368209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133554532492822666177963781 25041474842404249908368209)
  ·
    refine ⟨18781106131803187431276157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25041474842404249908368209 18781106131803187431276157)
    ·
      refine ⟨7042914799426195286728559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18781106131803187431276157 7042914799426195286728559)
      ·
        refine ⟨10564372199139292930092839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042914799426195286728559 10564372199139292930092839)
        ·
          refine ⟨15846558298708939395139259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564372199139292930092839 15846558298708939395139259)
          ·
            refine ⟨23769837448063409092708889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15846558298708939395139259 23769837448063409092708889)
            ·
              refine ⟨17827378086047556819531667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23769837448063409092708889 17827378086047556819531667)
              ·
                refine ⟨26741067129071335229297501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17827378086047556819531667 26741067129071335229297501)
                ·
                  refine ⟨10027900173401750710986563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26741067129071335229297501 10027900173401750710986563)
                  ·
                    refine ⟨15041850260102626066479845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10027900173401750710986563 15041850260102626066479845)
                    ·
                      refine ⟨2820346923769242387464971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15041850260102626066479845 2820346923769242387464971)
                      ·
                        rfl

theorem cell23_5492606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5492606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492606 prefixEnd_5492606 := by exact prefixLift 5492606
  have htrace : WordTrace (prefixWord ++ tailWord_5492606) baseStart_5492606 baseEnd_5492606 := by
    simpa [prefixWord, tailWord_5492606, baseEnd_5492606] using wordTrace_append hprefix tailTrace_5492606
  have hstable : (prefixWord ++ tailWord_5492606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492606).length < 2 ^ (prefixWord ++ tailWord_5492606).sum := by decide
  have hdescent : baseEnd_5492606 < baseStart_5492606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492649 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 3, 3, 2]
def baseStart_5492649 : Nat := 118140960795 + 5492649 * 2 ^ 59
def prefixEnd_5492649 : Nat := 4983230072969 + 3 ^ 40 * 5492649 * 2
def baseEnd_5492649 : Nat := 2820369003437385719227273

theorem tailTrace_5492649 : CollatzResearch.WordTrace tailWord_5492649 prefixEnd_5492649 2820369003437385719227273 := by
  unfold tailWord_5492649
  simp only [CollatzResearch.WordTrace]
  refine ⟨200333367078078217610761001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133555578052052145073840667 200333367078078217610761001)
  ·
    refine ⟨150250025308558663208070751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200333367078078217610761001 150250025308558663208070751)
    ·
      refine ⟨225375037962837994812106127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150250025308558663208070751 225375037962837994812106127)
      ·
        refine ⟨338062556944256992218159191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225375037962837994812106127 338062556944256992218159191)
        ·
          refine ⟨507093835416385488327238787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338062556944256992218159191 507093835416385488327238787)
          ·
            refine ⟨760640753124578232490858181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507093835416385488327238787 760640753124578232490858181)
            ·
              refine ⟨142620141210858418592035909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 760640753124578232490858181 142620141210858418592035909)
              ·
                refine ⟨26741276477035953486006733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142620141210858418592035909 26741276477035953486006733)
                ·
                  refine ⟨10027978678888482557252525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26741276477035953486006733 10027978678888482557252525)
                  ·
                    refine ⟨3760492004583180958969697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10027978678888482557252525 3760492004583180958969697)
                    ·
                      refine ⟨2820369003437385719227273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760492004583180958969697 2820369003437385719227273)
                      ·
                        rfl

theorem cell23_5492649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3, 2].length) (baseStart_5492649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492649 prefixEnd_5492649 := by exact prefixLift 5492649
  have htrace : WordTrace (prefixWord ++ tailWord_5492649) baseStart_5492649 baseEnd_5492649 := by
    simpa [prefixWord, tailWord_5492649, baseEnd_5492649] using wordTrace_append hprefix tailTrace_5492649
  have hstable : (prefixWord ++ tailWord_5492649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492649).length < 2 ^ (prefixWord ++ tailWord_5492649).sum := by decide
  have hdescent : baseEnd_5492649 < baseStart_5492649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492660 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5492660 : Nat := 118140960795 + 5492660 * 2 ^ 59
def prefixEnd_5492660 : Nat := 4983230072969 + 3 ^ 40 * 5492660 * 2
def baseEnd_5492660 : Nat := 2820374651724585176189723

theorem tailTrace_5492660 : CollatzResearch.WordTrace tailWord_5492660 prefixEnd_5492660 2820374651724585176189723 := by
  unfold tailWord_5492660
  simp only [CollatzResearch.WordTrace]
  refine ⟨100166884140519183244705717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133555845520692244326274289 100166884140519183244705717)
  ·
    refine ⟨9390645388173673429191161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100166884140519183244705717 9390645388173673429191161)
    ·
      refine ⟨7042984041130255071893371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9390645388173673429191161 7042984041130255071893371)
      ·
        refine ⟨10564476061695382607840057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042984041130255071893371 10564476061695382607840057)
        ·
          refine ⟨7923357046271536955880043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10564476061695382607840057 7923357046271536955880043)
          ·
            refine ⟨11885035569407305433820065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7923357046271536955880043 11885035569407305433820065)
            ·
              refine ⟨8913776677055479075365049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11885035569407305433820065 8913776677055479075365049)
              ·
                refine ⟨6685332507791609306523787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8913776677055479075365049 6685332507791609306523787)
                ·
                  refine ⟨10027998761687413959785681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685332507791609306523787 10027998761687413959785681)
                  ·
                    refine ⟨7520999071265560469839261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10027998761687413959785681 7520999071265560469839261)
                    ·
                      refine ⟨2820374651724585176189723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7520999071265560469839261 2820374651724585176189723)
                      ·
                        rfl

theorem cell23_5492660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5492660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492660 prefixEnd_5492660 := by exact prefixLift 5492660
  have htrace : WordTrace (prefixWord ++ tailWord_5492660) baseStart_5492660 baseEnd_5492660 := by
    simpa [prefixWord, tailWord_5492660, baseEnd_5492660] using wordTrace_append hprefix tailTrace_5492660
  have hstable : (prefixWord ++ tailWord_5492660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492660).length < 2 ^ (prefixWord ++ tailWord_5492660).sum := by decide
  have hdescent : baseEnd_5492660 < baseStart_5492660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492679 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_5492679 : Nat := 118140960795 + 5492679 * 2 ^ 59
def prefixEnd_5492679 : Nat := 4983230072969 + 3 ^ 40 * 5492679 * 2
def baseEnd_5492679 : Nat := 2820384407857020601852135

theorem tailTrace_5492679 : CollatzResearch.WordTrace tailWord_5492679 prefixEnd_5492679 2820384407857020601852135 := by
  unfold tailWord_5492679
  simp only [CollatzResearch.WordTrace]
  refine ⟨200334461267969532734353091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133556307511979688489568727 200334461267969532734353091)
  ·
    refine ⟨300501691901954299101529637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200334461267969532734353091 300501691901954299101529637)
    ·
      refine ⟨56344067231616431081536807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300501691901954299101529637 56344067231616431081536807)
      ·
        refine ⟨84516100847424646622305211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56344067231616431081536807 84516100847424646622305211)
        ·
          refine ⟨126774151271136969933457817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84516100847424646622305211 126774151271136969933457817)
          ·
            refine ⟨95080613453352727450093363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126774151271136969933457817 95080613453352727450093363)
            ·
              refine ⟨142620920180029091175140045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95080613453352727450093363 142620920180029091175140045)
              ·
                refine ⟨53482845067510909190677517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142620920180029091175140045 53482845067510909190677517)
                ·
                  refine ⟨20056066900316590946504069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53482845067510909190677517 20056066900316590946504069)
                  ·
                    refine ⟨3760512543809360802469513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20056066900316590946504069 3760512543809360802469513)
                    ·
                      refine ⟨2820384407857020601852135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760512543809360802469513 2820384407857020601852135)
                      ·
                        rfl

theorem cell23_5492679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_5492679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492679 prefixEnd_5492679 := by exact prefixLift 5492679
  have htrace : WordTrace (prefixWord ++ tailWord_5492679) baseStart_5492679 baseEnd_5492679 := by
    simpa [prefixWord, tailWord_5492679, baseEnd_5492679] using wordTrace_append hprefix tailTrace_5492679
  have hstable : (prefixWord ++ tailWord_5492679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492679).length < 2 ^ (prefixWord ++ tailWord_5492679).sum := by decide
  have hdescent : baseEnd_5492679 < baseStart_5492679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492682 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_5492682 : Nat := 118140960795 + 5492682 * 2 ^ 59
def prefixEnd_5492682 : Nat := 4983230072969 + 3 ^ 40 * 5492682 * 2
def baseEnd_5492682 : Nat := 2820385948298984090114621

theorem tailTrace_5492682 : CollatzResearch.WordTrace tailWord_5492682 prefixEnd_5492682 2820385948298984090114621 := by
  unfold tailWord_5492682
  simp only [CollatzResearch.WordTrace]
  refine ⟨50083642671739666061678075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133556380457972442831141533 50083642671739666061678075)
  ·
    refine ⟨75125464007609499092517113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50083642671739666061678075 75125464007609499092517113)
    ·
      refine ⟨56344098005707124319387835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75125464007609499092517113 56344098005707124319387835)
      ·
        refine ⟨84516147008560686479081753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56344098005707124319387835 84516147008560686479081753)
        ·
          refine ⟨63387110256420514859311315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84516147008560686479081753 63387110256420514859311315)
          ·
            refine ⟨95080665384630772288966973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63387110256420514859311315 95080665384630772288966973)
            ·
              refine ⟨35655249519236539608362615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95080665384630772288966973 35655249519236539608362615)
              ·
                refine ⟨53482874278854809412543923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35655249519236539608362615 53482874278854809412543923)
                ·
                  refine ⟨80224311418282214118815885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53482874278854809412543923 80224311418282214118815885)
                  ·
                    refine ⟨30084116781855830294555957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80224311418282214118815885 30084116781855830294555957)
                    ·
                      refine ⟨2820385948298984090114621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30084116781855830294555957 2820385948298984090114621)
                      ·
                        rfl

theorem cell23_5492682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_5492682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492682 prefixEnd_5492682 := by exact prefixLift 5492682
  have htrace : WordTrace (prefixWord ++ tailWord_5492682) baseStart_5492682 baseEnd_5492682 := by
    simpa [prefixWord, tailWord_5492682, baseEnd_5492682] using wordTrace_append hprefix tailTrace_5492682
  have hstable : (prefixWord ++ tailWord_5492682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492682).length < 2 ^ (prefixWord ++ tailWord_5492682).sum := by decide
  have hdescent : baseEnd_5492682 < baseStart_5492682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492696 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_5492696 : Nat := 118140960795 + 5492696 * 2 ^ 59
def prefixEnd_5492696 : Nat := 4983230072969 + 3 ^ 40 * 5492696 * 2
def baseEnd_5492696 : Nat := 2820393137028147035339557

theorem tailTrace_5492696 : CollatzResearch.WordTrace tailWord_5492696 prefixEnd_5492696 2820393137028147035339557 := by
  unfold tailWord_5492696
  simp only [CollatzResearch.WordTrace]
  refine ⟨100167540654453972318860971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133556720872605296425147961 100167540654453972318860971)
  ·
    refine ⟨150251310981680958478291457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100167540654453972318860971 150251310981680958478291457)
    ·
      refine ⟨112688483236260718858718593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150251310981680958478291457 112688483236260718858718593)
      ·
        refine ⟨84516362427195539144038945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112688483236260718858718593 84516362427195539144038945)
        ·
          refine ⟨63387271820396654358029209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84516362427195539144038945 63387271820396654358029209)
          ·
            refine ⟨47540453865297490768521907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63387271820396654358029209 47540453865297490768521907)
            ·
              refine ⟨71310680797946236152782861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47540453865297490768521907 71310680797946236152782861)
              ·
                refine ⟨26741505299229838557293573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71310680797946236152782861 26741505299229838557293573)
                ·
                  refine ⟨5014032243605594729492545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26741505299229838557293573 5014032243605594729492545)
                  ·
                    refine ⟨3760524182704196047119409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5014032243605594729492545 3760524182704196047119409)
                    ·
                      refine ⟨2820393137028147035339557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760524182704196047119409 2820393137028147035339557)
                      ·
                        rfl

theorem cell23_5492696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_5492696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492696 prefixEnd_5492696 := by exact prefixLift 5492696
  have htrace : WordTrace (prefixWord ++ tailWord_5492696) baseStart_5492696 baseEnd_5492696 := by
    simpa [prefixWord, tailWord_5492696, baseEnd_5492696] using wordTrace_append hprefix tailTrace_5492696
  have hstable : (prefixWord ++ tailWord_5492696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492696).length < 2 ^ (prefixWord ++ tailWord_5492696).sum := by decide
  have hdescent : baseEnd_5492696 < baseStart_5492696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492717 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5492717 : Nat := 118140960795 + 5492717 * 2 ^ 59
def prefixEnd_5492717 : Nat := 4983230072969 + 3 ^ 40 * 5492717 * 2
def baseEnd_5492717 : Nat := 2820403920121891453176961

theorem tailTrace_5492717 : CollatzResearch.WordTrace tailWord_5492717 prefixEnd_5492717 2820403920121891453176961 := by
  unfold tailWord_5492717
  simp only [CollatzResearch.WordTrace]
  refine ⟨200335847241831865224236405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133557231494554576816157603 200335847241831865224236405)
  ·
    refine ⟨18781485678921737364772163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200335847241831865224236405 18781485678921737364772163)
    ·
      refine ⟨28172228518382606047158245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18781485678921737364772163 28172228518382606047158245)
      ·
        refine ⟨5282292847196738633842171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28172228518382606047158245 5282292847196738633842171)
        ·
          refine ⟨7923439270795107950763257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282292847196738633842171 7923439270795107950763257)
          ·
            refine ⟨5942579453096330963072443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7923439270795107950763257 5942579453096330963072443)
            ·
              refine ⟨8913869179644496444608665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5942579453096330963072443 8913869179644496444608665)
              ·
                refine ⟨6685401884733372333456499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8913869179644496444608665 6685401884733372333456499)
                ·
                  refine ⟨10028102827100058500184749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6685401884733372333456499 10028102827100058500184749)
                  ·
                    refine ⟨3760538560162521937569281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10028102827100058500184749 3760538560162521937569281)
                    ·
                      refine ⟨2820403920121891453176961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760538560162521937569281 2820403920121891453176961)
                      ·
                        rfl

theorem cell23_5492717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5492717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492717 prefixEnd_5492717 := by exact prefixLift 5492717
  have htrace : WordTrace (prefixWord ++ tailWord_5492717) baseStart_5492717 baseEnd_5492717 := by
    simpa [prefixWord, tailWord_5492717, baseEnd_5492717] using wordTrace_append hprefix tailTrace_5492717
  have hstable : (prefixWord ++ tailWord_5492717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492717).length < 2 ^ (prefixWord ++ tailWord_5492717).sum := by decide
  have hdescent : baseEnd_5492717 < baseStart_5492717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492739 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 5, 2]
def baseStart_5492739 : Nat := 118140960795 + 5492739 * 2 ^ 59
def prefixEnd_5492739 : Nat := 4983230072969 + 3 ^ 40 * 5492739 * 2
def baseEnd_5492739 : Nat := 2820415216696290367101859

theorem tailTrace_5492739 : CollatzResearch.WordTrace tailWord_5492739 prefixEnd_5492739 2820415216696290367101859 := by
  unfold tailWord_5492739
  simp only [CollatzResearch.WordTrace]
  refine ⟨200336649647752162981537271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133557766431834775321024847 200336649647752162981537271)
  ·
    refine ⟨300504974471628244472305907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200336649647752162981537271 300504974471628244472305907)
    ·
      refine ⟨450757461707442366708458861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300504974471628244472305907 450757461707442366708458861)
      ·
        refine ⟨169034048140290887515672073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450757461707442366708458861 169034048140290887515672073)
        ·
          refine ⟨126775536105218165636754055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169034048140290887515672073 126775536105218165636754055)
          ·
            refine ⟨190163304157827248455131083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126775536105218165636754055 190163304157827248455131083)
            ·
              refine ⟨285244956236740872682696625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190163304157827248455131083 285244956236740872682696625)
              ·
                refine ⟨213933717177555654512022469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285244956236740872682696625 213933717177555654512022469)
                ·
                  refine ⟨40112571970791685221004213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213933717177555654512022469 40112571970791685221004213)
                  ·
                    refine ⟨3760553622261720489469145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40112571970791685221004213 3760553622261720489469145)
                    ·
                      refine ⟨2820415216696290367101859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3760553622261720489469145 2820415216696290367101859)
                      ·
                        rfl

theorem cell23_5492739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_5492739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492739 prefixEnd_5492739 := by exact prefixLift 5492739
  have htrace : WordTrace (prefixWord ++ tailWord_5492739) baseStart_5492739 baseEnd_5492739 := by
    simpa [prefixWord, tailWord_5492739, baseEnd_5492739] using wordTrace_append hprefix tailTrace_5492739
  have hstable : (prefixWord ++ tailWord_5492739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492739).length < 2 ^ (prefixWord ++ tailWord_5492739).sum := by decide
  have hdescent : baseEnd_5492739 < baseStart_5492739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492786 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_5492786 : Nat := 118140960795 + 5492786 * 2 ^ 59
def prefixEnd_5492786 : Nat := 4983230072969 + 3 ^ 40 * 5492786 * 2
def baseEnd_5492786 : Nat := 2820439350287051683214143

theorem tailTrace_5492786 : CollatzResearch.WordTrace tailWord_5492786 prefixEnd_5492786 2820439350287051683214143 := by
  unfold tailWord_5492786
  simp only [CollatzResearch.WordTrace]
  refine ⟨50084590969645472502124553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133558909252387926672332141 50084590969645472502124553)
  ·
    refine ⟨37563443227234104376593415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50084590969645472502124553 37563443227234104376593415)
    ·
      refine ⟨56345164840851156564890123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37563443227234104376593415 56345164840851156564890123)
      ·
        refine ⟨84517747261276734847335185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56345164840851156564890123 84517747261276734847335185)
        ·
          refine ⟨63388310445957551135501389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84517747261276734847335185 63388310445957551135501389)
          ·
            refine ⟨23770616417234081675813021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63388310445957551135501389 23770616417234081675813021)
            ·
              refine ⟨8913981156462780628429883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23770616417234081675813021 8913981156462780628429883)
              ·
                refine ⟨13370971734694170942644825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8913981156462780628429883 13370971734694170942644825)
                ·
                  refine ⟨10028228801020628206983619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13370971734694170942644825 10028228801020628206983619)
                  ·
                    refine ⟨15042343201530942310475429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10028228801020628206983619 15042343201530942310475429)
                    ·
                      refine ⟨2820439350287051683214143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15042343201530942310475429 2820439350287051683214143)
                      ·
                        rfl

theorem cell23_5492786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_5492786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492786 prefixEnd_5492786 := by exact prefixLift 5492786
  have htrace : WordTrace (prefixWord ++ tailWord_5492786) baseStart_5492786 baseEnd_5492786 := by
    simpa [prefixWord, tailWord_5492786, baseEnd_5492786] using wordTrace_append hprefix tailTrace_5492786
  have hstable : (prefixWord ++ tailWord_5492786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492786).length < 2 ^ (prefixWord ++ tailWord_5492786).sum := by decide
  have hdescent : baseEnd_5492786 < baseStart_5492786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5492813 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5492813 : Nat := 118140960795 + 5492813 * 2 ^ 59
def prefixEnd_5492813 : Nat := 4983230072969 + 3 ^ 40 * 5492813 * 2
def baseEnd_5492813 : Nat := 940151071421574359192173

theorem tailTrace_5492813 : CollatzResearch.WordTrace tailWord_5492813 prefixEnd_5492813 940151071421574359192173 := by
  unfold tailWord_5492813
  simp only [CollatzResearch.WordTrace]
  refine ⟨200339348649484073619731093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133559565766322715746487395 200339348649484073619731093)
  ·
    refine ⟨9390906967944565950924895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 200339348649484073619731093 9390906967944565950924895)
    ·
      refine ⟨14086360451916848926387343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390906967944565950924895 14086360451916848926387343)
      ·
        refine ⟨21129540677875273389581015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14086360451916848926387343 21129540677875273389581015)
        ·
          refine ⟨31694311016812910084371523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21129540677875273389581015 31694311016812910084371523)
          ·
            refine ⟨47541466525219365126557285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31694311016812910084371523 47541466525219365126557285)
            ·
              refine ⟨8914024973478630961229491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47541466525219365126557285 8914024973478630961229491)
              ·
                refine ⟨13371037460217946441844237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8914024973478630961229491 13371037460217946441844237)
                ·
                  refine ⟨5014139047581729915691589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13371037460217946441844237 5014139047581729915691589)
                  ·
                    refine ⟨940151071421574359192173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014139047581729915691589 940151071421574359192173)
                    ·
                      rfl

theorem cell23_5492813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5492813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5492813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5492813 prefixEnd_5492813 := by exact prefixLift 5492813
  have htrace : WordTrace (prefixWord ++ tailWord_5492813) baseStart_5492813 baseEnd_5492813 := by
    simpa [prefixWord, tailWord_5492813, baseEnd_5492813] using wordTrace_append hprefix tailTrace_5492813
  have hstable : (prefixWord ++ tailWord_5492813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5492813).length < 2 ^ (prefixWord ++ tailWord_5492813).sum := by decide
  have hdescent : baseEnd_5492813 < baseStart_5492813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5492813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
