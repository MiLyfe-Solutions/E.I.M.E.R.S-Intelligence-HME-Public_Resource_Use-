import V185TrunkScan23Chunk0850

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5036872 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_5036872 : Nat := 118140960795 + 5036872 * 2 ^ 59
def prefixEnd_5036872 : Nat := 4983230072969 + 3 ^ 40 * 5036872 * 2
def baseEnd_5036872 : Nat := 2586336331173122448835853

theorem tailTrace_5036872 : CollatzResearch.WordTrace tailWord_5036872 prefixEnd_5036872 2586336331173122448835853 := by
  unfold tailWord_5036872
  simp only [CollatzResearch.WordTrace]
  refine ⟨91854907104140224048180435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122473209472186965397573913 91854907104140224048180435)
  ·
    refine ⟨137782360656210336072270653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91854907104140224048180435 137782360656210336072270653)
    ·
      refine ⟨51668385246078876027101495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137782360656210336072270653 51668385246078876027101495)
      ·
        refine ⟨77502577869118314040652243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51668385246078876027101495 77502577869118314040652243)
        ·
          refine ⟨116253866803677471060978365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77502577869118314040652243 116253866803677471060978365)
          ·
            refine ⟨43595200051379051647866887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116253866803677471060978365 43595200051379051647866887)
            ·
              refine ⟨65392800077068577471800331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43595200051379051647866887 65392800077068577471800331)
              ·
                refine ⟨98089200115602866207700497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65392800077068577471800331 98089200115602866207700497)
                ·
                  refine ⟨73566900086702149655775373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98089200115602866207700497 73566900086702149655775373)
                  ·
                    refine ⟨27587587532513306120915765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73566900086702149655775373 27587587532513306120915765)
                    ·
                      refine ⟨2586336331173122448835853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27587587532513306120915765 2586336331173122448835853)
                      ·
                        rfl

theorem cell23_5036872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_5036872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036872 prefixEnd_5036872 := by exact prefixLift 5036872
  have htrace : WordTrace (prefixWord ++ tailWord_5036872) baseStart_5036872 baseEnd_5036872 := by
    simpa [prefixWord, tailWord_5036872, baseEnd_5036872] using wordTrace_append hprefix tailTrace_5036872
  have hstable : (prefixWord ++ tailWord_5036872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036872).length < 2 ^ (prefixWord ++ tailWord_5036872).sum := by decide
  have hdescent : baseEnd_5036872 < baseStart_5036872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036913 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 1, 4]
def baseStart_5036913 : Nat := 118140960795 + 5036913 * 2 ^ 59
def prefixEnd_5036913 : Nat := 4983230072969 + 3 ^ 40 * 5036913 * 2
def baseEnd_5036913 : Nat := 862119127959985596141055

theorem tailTrace_5036913 : CollatzResearch.WordTrace tailWord_5036913 prefixEnd_5036913 862119127959985596141055 := by
  unfold tailWord_5036913
  simp only [CollatzResearch.WordTrace]
  refine ⟨183711309601131912098603393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122474206400754608065735595 183711309601131912098603393)
  ·
    refine ⟨137783482200848934073952545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183711309601131912098603393 137783482200848934073952545)
    ·
      refine ⟨103337611650636700555464409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137783482200848934073952545 103337611650636700555464409)
      ·
        refine ⟨77503208737977525416598307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103337611650636700555464409 77503208737977525416598307)
        ·
          refine ⟨116254813106966288124897461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77503208737977525416598307 116254813106966288124897461)
          ·
            refine ⟨10898888728778089511709137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116254813106966288124897461 10898888728778089511709137)
            ·
              refine ⟨8174166546583567133781853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10898888728778089511709137 8174166546583567133781853)
              ·
                refine ⟨3065312454968837675168195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8174166546583567133781853 3065312454968837675168195)
                ·
                  refine ⟨4597968682453256512752293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065312454968837675168195 4597968682453256512752293)
                  ·
                    refine ⟨862119127959985596141055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597968682453256512752293 862119127959985596141055)
                    ·
                      rfl

theorem cell23_5036913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_5036913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036913 prefixEnd_5036913 := by exact prefixLift 5036913
  have htrace : WordTrace (prefixWord ++ tailWord_5036913) baseStart_5036913 baseEnd_5036913 := by
    simpa [prefixWord, tailWord_5036913, baseEnd_5036913] using wordTrace_append hprefix tailTrace_5036913
  have hstable : (prefixWord ++ tailWord_5036913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036913).length < 2 ^ (prefixWord ++ tailWord_5036913).sum := by decide
  have hdescent : baseEnd_5036913 < baseStart_5036913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036969 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_5036969 : Nat := 118140960795 + 5036969 * 2 ^ 59
def prefixEnd_5036969 : Nat := 4983230072969 + 3 ^ 40 * 5036969 * 2
def baseEnd_5036969 : Nat := 862128712932202856440969

theorem tailTrace_5036969 : CollatzResearch.WordTrace tailWord_5036969 prefixEnd_5036969 862128712932202856440969 := by
  unfold tailWord_5036969
  simp only [CollatzResearch.WordTrace]
  refine ⟨183713352088929033662641961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122475568059286022441761307 183713352088929033662641961)
  ·
    refine ⟨137785014066696775246981471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183713352088929033662641961 137785014066696775246981471)
    ·
      refine ⟨206677521100045162870472207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137785014066696775246981471 206677521100045162870472207)
      ·
        refine ⟨310016281650067744305708311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206677521100045162870472207 310016281650067744305708311)
        ·
          refine ⟨465024422475101616458562467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310016281650067744305708311 465024422475101616458562467)
          ·
            refine ⟨697536633712652424687843701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465024422475101616458562467 697536633712652424687843701)
            ·
              refine ⟨65394059410561164814485347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 697536633712652424687843701 65394059410561164814485347)
              ·
                refine ⟨98091089115841747221728021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65394059410561164814485347 98091089115841747221728021)
                ·
                  refine ⟨4598019802305081901018501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98091089115841747221728021 4598019802305081901018501)
                  ·
                    refine ⟨862128712932202856440969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598019802305081901018501 862128712932202856440969)
                    ·
                      rfl

theorem cell23_5036969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_5036969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036969 prefixEnd_5036969 := by exact prefixLift 5036969
  have htrace : WordTrace (prefixWord ++ tailWord_5036969) baseStart_5036969 baseEnd_5036969 := by
    simpa [prefixWord, tailWord_5036969, baseEnd_5036969] using wordTrace_append hprefix tailTrace_5036969
  have hstable : (prefixWord ++ tailWord_5036969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036969).length < 2 ^ (prefixWord ++ tailWord_5036969).sum := by decide
  have hdescent : baseEnd_5036969 < baseStart_5036969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036980 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5036980 : Nat := 118140960795 + 5036980 * 2 ^ 59
def prefixEnd_5036980 : Nat := 4983230072969 + 3 ^ 40 * 5036980 * 2
def baseEnd_5036980 : Nat := 2586391787083808026285357

theorem tailTrace_5036980 : CollatzResearch.WordTrace tailWord_5036980 prefixEnd_5036980 2586391787083808026285357 := by
  unfold tailWord_5036980
  simp only [CollatzResearch.WordTrace]
  refine ⟨91856876645944591270646197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122475835527926121694194929 91856876645944591270646197)
  ·
    refine ⟨8611582185557305431623081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91856876645944591270646197 8611582185557305431623081)
    ·
      refine ⟨6458686639167979073717311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8611582185557305431623081 6458686639167979073717311)
      ·
        refine ⟨9688029958751968610575967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458686639167979073717311 9688029958751968610575967)
        ·
          refine ⟨14532044938127952915863951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9688029958751968610575967 14532044938127952915863951)
          ·
            refine ⟨21798067407191929373795927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14532044938127952915863951 21798067407191929373795927)
            ·
              refine ⟨32697101110787894060693891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21798067407191929373795927 32697101110787894060693891)
              ·
                refine ⟨49045651666181841091040837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32697101110787894060693891 49045651666181841091040837)
                ·
                  refine ⟨9196059687409095204570157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49045651666181841091040837 9196059687409095204570157)
                  ·
                    refine ⟨3448522382778410701713809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9196059687409095204570157 3448522382778410701713809)
                    ·
                      refine ⟨2586391787083808026285357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448522382778410701713809 2586391787083808026285357)
                      ·
                        rfl

theorem cell23_5036980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5036980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036980 prefixEnd_5036980 := by exact prefixLift 5036980
  have htrace : WordTrace (prefixWord ++ tailWord_5036980) baseStart_5036980 baseEnd_5036980 := by
    simpa [prefixWord, tailWord_5036980, baseEnd_5036980] using wordTrace_append hprefix tailTrace_5036980
  have hstable : (prefixWord ++ tailWord_5036980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036980).length < 2 ^ (prefixWord ++ tailWord_5036980).sum := by decide
  have hdescent : baseEnd_5036980 < baseStart_5036980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036986 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_5036986 : Nat := 118140960795 + 5036986 * 2 ^ 59
def prefixEnd_5036986 : Nat := 4983230072969 + 3 ^ 40 * 5036986 * 2
def baseEnd_5036986 : Nat := 862131622655911667603443

theorem tailTrace_5036986 : CollatzResearch.WordTrace tailWord_5036986 prefixEnd_5036986 862131622655911667603443 := by
  unfold tailWord_5036986
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928493032466861391502703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122475981419911630377340541 45928493032466861391502703)
  ·
    refine ⟨68892739548700292087254055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45928493032466861391502703 68892739548700292087254055)
    ·
      refine ⟨103339109323050438130881083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68892739548700292087254055 103339109323050438130881083)
      ·
        refine ⟨155008663984575657196321625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103339109323050438130881083 155008663984575657196321625)
        ·
          refine ⟨116256497988431742897241219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155008663984575657196321625 116256497988431742897241219)
          ·
            refine ⟨174384746982647614345861829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116256497988431742897241219 174384746982647614345861829)
            ·
              refine ⟨32697140059246427689849093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174384746982647614345861829 32697140059246427689849093)
              ·
                refine ⟨6130713761108705191846705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32697140059246427689849093 6130713761108705191846705)
                ·
                  refine ⟨4598035320831528893885029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130713761108705191846705 4598035320831528893885029)
                  ·
                    refine ⟨862131622655911667603443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598035320831528893885029 862131622655911667603443)
                    ·
                      rfl

theorem cell23_5036986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_5036986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036986 prefixEnd_5036986 := by exact prefixLift 5036986
  have htrace : WordTrace (prefixWord ++ tailWord_5036986) baseStart_5036986 baseEnd_5036986 := by
    simpa [prefixWord, tailWord_5036986, baseEnd_5036986] using wordTrace_append hprefix tailTrace_5036986
  have hstable : (prefixWord ++ tailWord_5036986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036986).length < 2 ^ (prefixWord ++ tailWord_5036986).sum := by decide
  have hdescent : baseEnd_5036986 < baseStart_5036986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037003 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 2, 4]
def baseStart_5037003 : Nat := 118140960795 + 5037003 * 2 ^ 59
def prefixEnd_5037003 : Nat := 4983230072969 + 3 ^ 40 * 5037003 * 2
def baseEnd_5037003 : Nat := 862134532379620478765917

theorem tailTrace_5037003 : CollatzResearch.WordTrace tailWord_5037003 prefixEnd_5037003 862134532379620478765917 := by
  unfold tailWord_5037003
  simp only [CollatzResearch.WordTrace]
  refine ⟨183714592170805857469379663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122476394780537238312919775 183714592170805857469379663)
  ·
    refine ⟨275571888256208786204069495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183714592170805857469379663 275571888256208786204069495)
    ·
      refine ⟨413357832384313179306104243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275571888256208786204069495 413357832384313179306104243)
      ·
        refine ⟨620036748576469768959156365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413357832384313179306104243 620036748576469768959156365)
        ·
          refine ⟨232513780716176163359683637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 620036748576469768959156365 232513780716176163359683637)
          ·
            refine ⟨21798166942141515314970341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232513780716176163359683637 21798166942141515314970341)
            ·
              refine ⟨4087156301651534121556939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21798166942141515314970341 4087156301651534121556939)
              ·
                refine ⟨6130734452477301182335409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087156301651534121556939 6130734452477301182335409)
                ·
                  refine ⟨4598050839357975886751557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130734452477301182335409 4598050839357975886751557)
                  ·
                    refine ⟨862134532379620478765917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598050839357975886751557 862134532379620478765917)
                    ·
                      rfl

theorem cell23_5037003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 4].length) (baseStart_5037003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037003 prefixEnd_5037003 := by exact prefixLift 5037003
  have htrace : WordTrace (prefixWord ++ tailWord_5037003) baseStart_5037003 baseEnd_5037003 := by
    simpa [prefixWord, tailWord_5037003, baseEnd_5037003] using wordTrace_append hprefix tailTrace_5037003
  have hstable : (prefixWord ++ tailWord_5037003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037003).length < 2 ^ (prefixWord ++ tailWord_5037003).sum := by decide
  have hdescent : baseEnd_5037003 < baseStart_5037003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037010 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5037010 : Nat := 118140960795 + 5037010 * 2 ^ 59
def prefixEnd_5037010 : Nat := 4983230072969 + 3 ^ 40 * 5037010 * 2
def baseEnd_5037010 : Nat := 2586407191503442908910219

theorem tailTrace_5037010 : CollatzResearch.WordTrace tailWord_5037010 prefixEnd_5037010 2586407191503442908910219 := by
  unfold tailWord_5037010
  simp only [CollatzResearch.WordTrace]
  refine ⟨45928711870445124416221121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122476564987853665109922989 45928711870445124416221121)
  ·
    refine ⟨34446533902833843312165841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45928711870445124416221121 34446533902833843312165841)
    ·
      refine ⟨25834900427125382484124381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34446533902833843312165841 25834900427125382484124381)
      ·
        refine ⟨9688087660172018431546643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25834900427125382484124381 9688087660172018431546643)
        ·
          refine ⟨14532131490258027647319965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9688087660172018431546643 14532131490258027647319965)
          ·
            refine ⟨5449549308846760367744987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14532131490258027647319965 5449549308846760367744987)
            ·
              refine ⟨8174323963270140551617481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449549308846760367744987 8174323963270140551617481)
              ·
                refine ⟨6130742972452605413713111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8174323963270140551617481 6130742972452605413713111)
                ·
                  refine ⟨9196114458678908120569667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6130742972452605413713111 9196114458678908120569667)
                  ·
                    refine ⟨13794171688018362180854501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9196114458678908120569667 13794171688018362180854501)
                    ·
                      refine ⟨2586407191503442908910219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13794171688018362180854501 2586407191503442908910219)
                      ·
                        rfl

theorem cell23_5037010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5037010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037010 prefixEnd_5037010 := by exact prefixLift 5037010
  have htrace : WordTrace (prefixWord ++ tailWord_5037010) baseStart_5037010 baseEnd_5037010 := by
    simpa [prefixWord, tailWord_5037010, baseEnd_5037010] using wordTrace_append hprefix tailTrace_5037010
  have hstable : (prefixWord ++ tailWord_5037010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037010).length < 2 ^ (prefixWord ++ tailWord_5037010).sum := by decide
  have hdescent : baseEnd_5037010 < baseStart_5037010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037013 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_5037013 : Nat := 118140960795 + 5037013 * 2 ^ 59
def prefixEnd_5037013 : Nat := 4983230072969 + 3 ^ 40 * 5037013 * 2
def baseEnd_5037013 : Nat := 2586408731945406397172705

theorem tailTrace_5037013 : CollatzResearch.WordTrace tailWord_5037013 prefixEnd_5037013 2586408731945406397172705 := by
  unfold tailWord_5037013
  simp only [CollatzResearch.WordTrace]
  refine ⟨183714956900769629177243693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122476637933846419451495795 183714956900769629177243693)
  ·
    refine ⟨68893108837788610941466385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183714956900769629177243693 68893108837788610941466385)
    ·
      refine ⟨51669831628341458206099789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68893108837788610941466385 51669831628341458206099789)
      ·
        refine ⟨19376186860628046827287421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51669831628341458206099789 19376186860628046827287421)
        ·
          refine ⟨7266070072735517560232783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19376186860628046827287421 7266070072735517560232783)
          ·
            refine ⟨10899105109103276340349175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266070072735517560232783 10899105109103276340349175)
            ·
              refine ⟨16348657663654914510523763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10899105109103276340349175 16348657663654914510523763)
              ·
                refine ⟨24522986495482371765785645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16348657663654914510523763 24522986495482371765785645)
                ·
                  refine ⟨9196119935805889412169617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24522986495482371765785645 9196119935805889412169617)
                  ·
                    refine ⟨6897089951854417059127213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9196119935805889412169617 6897089951854417059127213)
                    ·
                      refine ⟨2586408731945406397172705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897089951854417059127213 2586408731945406397172705)
                      ·
                        rfl

theorem cell23_5037013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_5037013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037013 prefixEnd_5037013 := by exact prefixLift 5037013
  have htrace : WordTrace (prefixWord ++ tailWord_5037013) baseStart_5037013 baseEnd_5037013 := by
    simpa [prefixWord, tailWord_5037013, baseEnd_5037013] using wordTrace_append hprefix tailTrace_5037013
  have hstable : (prefixWord ++ tailWord_5037013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037013).length < 2 ^ (prefixWord ++ tailWord_5037013).sum := by decide
  have hdescent : baseEnd_5037013 < baseStart_5037013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037046 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_5037046 : Nat := 118140960795 + 5037046 * 2 ^ 59
def prefixEnd_5037046 : Nat := 4983230072969 + 3 ^ 40 * 5037046 * 2
def baseEnd_5037046 : Nat := 862141892269001589353351

theorem tailTrace_5037046 : CollatzResearch.WordTrace tailWord_5037046 prefixEnd_5037046 862141892269001589353351 := by
  unfold tailWord_5037046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482260031853129738324687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122477440339766717208796661 11482260031853129738324687)
  ·
    refine ⟨17223390047779694607487031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11482260031853129738324687 17223390047779694607487031)
    ·
      refine ⟨25835085071669541911230547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17223390047779694607487031 25835085071669541911230547)
      ·
        refine ⟨38752627607504312866845821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25835085071669541911230547 38752627607504312866845821)
        ·
          refine ⟨14532235352814117325067183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38752627607504312866845821 14532235352814117325067183)
          ·
            refine ⟨21798353029221175987600775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14532235352814117325067183 21798353029221175987600775)
            ·
              refine ⟨32697529543831763981401163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21798353029221175987600775 32697529543831763981401163)
              ·
                refine ⟨49046294315747645972101745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32697529543831763981401163 49046294315747645972101745)
                ·
                  refine ⟨36784720736810734479076309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49046294315747645972101745 36784720736810734479076309)
                  ·
                    refine ⟨862141892269001589353351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36784720736810734479076309 862141892269001589353351)
                    ·
                      rfl

theorem cell23_5037046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_5037046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037046 prefixEnd_5037046 := by exact prefixLift 5037046
  have htrace : WordTrace (prefixWord ++ tailWord_5037046) baseStart_5037046 baseEnd_5037046 := by
    simpa [prefixWord, tailWord_5037046, baseEnd_5037046] using wordTrace_append hprefix tailTrace_5037046
  have hstable : (prefixWord ++ tailWord_5037046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037046).length < 2 ^ (prefixWord ++ tailWord_5037046).sum := by decide
  have hdescent : baseEnd_5037046 < baseStart_5037046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037049 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_5037049 : Nat := 118140960795 + 5037049 * 2 ^ 59
def prefixEnd_5037049 : Nat := 4983230072969 + 3 ^ 40 * 5037049 * 2
def baseEnd_5037049 : Nat := 2586427217248968256322539

theorem tailTrace_5037049 : CollatzResearch.WordTrace tailWord_5037049 prefixEnd_5037049 2586427217248968256322539 := by
  unfold tailWord_5037049
  simp only [CollatzResearch.WordTrace]
  refine ⟨183716269928639207325554201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122477513285759471550369467 183716269928639207325554201)
  ·
    refine ⟨137787202446479405494165651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183716269928639207325554201 137787202446479405494165651)
    ·
      refine ⟨206680803669719108241248477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137787202446479405494165651 206680803669719108241248477)
      ·
        refine ⟨77505301376144665590468179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206680803669719108241248477 77505301376144665590468179)
        ·
          refine ⟨116257952064216998385702269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77505301376144665590468179 116257952064216998385702269)
          ·
            refine ⟨43596732024081374394638351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116257952064216998385702269 43596732024081374394638351)
            ·
              refine ⟨65395098036122061591957527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43596732024081374394638351 65395098036122061591957527)
              ·
                refine ⟨98092647054183092387936291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65395098036122061591957527 98092647054183092387936291)
                ·
                  refine ⟨147138970581274638581904437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98092647054183092387936291 147138970581274638581904437)
                  ·
                    refine ⟨13794278491994497367053541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147138970581274638581904437 13794278491994497367053541)
                    ·
                      refine ⟨2586427217248968256322539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13794278491994497367053541 2586427217248968256322539)
                      ·
                        rfl

theorem cell23_5037049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_5037049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037049 prefixEnd_5037049 := by exact prefixLift 5037049
  have htrace : WordTrace (prefixWord ++ tailWord_5037049) baseStart_5037049 baseEnd_5037049 := by
    simpa [prefixWord, tailWord_5037049, baseEnd_5037049] using wordTrace_append hprefix tailTrace_5037049
  have hstable : (prefixWord ++ tailWord_5037049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037049).length < 2 ^ (prefixWord ++ tailWord_5037049).sum := by decide
  have hdescent : baseEnd_5037049 < baseStart_5037049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037087 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 1, 3, 2]
def baseStart_5037087 : Nat := 118140960795 + 5037087 * 2 ^ 59
def prefixEnd_5037087 : Nat := 4983230072969 + 3 ^ 40 * 5037087 * 2
def baseEnd_5037087 : Nat := 2586446729513839107647365

theorem tailTrace_5037087 : CollatzResearch.WordTrace tailWord_5037087 prefixEnd_5037087 2586446729513839107647365 := by
  unfold tailWord_5037087
  simp only [CollatzResearch.WordTrace]
  refine ⟨183717655902501539815437515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122478437268334359876958343 183717655902501539815437515)
  ·
    refine ⟨275576483853752309723156273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183717655902501539815437515 275576483853752309723156273)
    ·
      refine ⟨206682362890314232292367205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275576483853752309723156273 206682362890314232292367205)
      ·
        refine ⟨38752943041933918554818851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206682362890314232292367205 38752943041933918554818851)
        ·
          refine ⟨58129414562900877832228277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38752943041933918554818851 58129414562900877832228277)
          ·
            refine ⟨5449632615271957296771401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58129414562900877832228277 5449632615271957296771401)
            ·
              refine ⟨4087224461453967972578551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449632615271957296771401 4087224461453967972578551)
              ·
                refine ⟨6130836692180951958867827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087224461453967972578551 6130836692180951958867827)
                ·
                  refine ⟨9196255038271427938301741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6130836692180951958867827 9196255038271427938301741)
                  ·
                    refine ⟨3448595639351785476863153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9196255038271427938301741 3448595639351785476863153)
                    ·
                      refine ⟨2586446729513839107647365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448595639351785476863153 2586446729513839107647365)
                      ·
                        rfl

theorem cell23_5037087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_5037087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037087 prefixEnd_5037087 := by exact prefixLift 5037087
  have htrace : WordTrace (prefixWord ++ tailWord_5037087) baseStart_5037087 baseEnd_5037087 := by
    simpa [prefixWord, tailWord_5037087, baseEnd_5037087] using wordTrace_append hprefix tailTrace_5037087
  have hstable : (prefixWord ++ tailWord_5037087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037087).length < 2 ^ (prefixWord ++ tailWord_5037087).sum := by decide
  have hdescent : baseEnd_5037087 < baseStart_5037087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037106 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_5037106 : Nat := 118140960795 + 5037106 * 2 ^ 59
def prefixEnd_5037106 : Nat := 4983230072969 + 3 ^ 40 * 5037106 * 2
def baseEnd_5037106 : Nat := 287384053960697170367753

theorem tailTrace_5037106 : CollatzResearch.WordTrace tailWord_5037106 prefixEnd_5037106 287384053960697170367753 := by
  unfold tailWord_5037106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45929587222358176515094793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122478899259621804040252781 45929587222358176515094793)
  ·
    refine ⟨34447190416768632386321095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45929587222358176515094793 34447190416768632386321095)
    ·
      refine ⟨51670785625152948579481643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34447190416768632386321095 51670785625152948579481643)
      ·
        refine ⟨77506178437729422869222465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51670785625152948579481643 77506178437729422869222465)
        ·
          refine ⟨58129633828297067151916849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77506178437729422869222465 58129633828297067151916849)
          ·
            refine ⟨43597225371222800363937637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58129633828297067151916849 43597225371222800363937637)
            ·
              refine ⟨8174479757104275068238307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43597225371222800363937637 8174479757104275068238307)
              ·
                refine ⟨12261719635656412602357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8174479757104275068238307 12261719635656412602357461)
                ·
                  refine ⟨287384053960697170367753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12261719635656412602357461 287384053960697170367753)
                  ·
                    rfl

theorem cell23_5037106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_5037106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037106 prefixEnd_5037106 := by exact prefixLift 5037106
  have htrace : WordTrace (prefixWord ++ tailWord_5037106) baseStart_5037106 baseEnd_5037106 := by
    simpa [prefixWord, tailWord_5037106, baseEnd_5037106] using wordTrace_append hprefix tailTrace_5037106
  have hstable : (prefixWord ++ tailWord_5037106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037106).length < 2 ^ (prefixWord ++ tailWord_5037106).sum := by decide
  have hdescent : baseEnd_5037106 < baseStart_5037106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037129 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_5037129 : Nat := 118140960795 + 5037129 * 2 ^ 59
def prefixEnd_5037129 : Nat := 4983230072969 + 3 ^ 40 * 5037129 * 2
def baseEnd_5037129 : Nat := 2586468295701327943322171

theorem tailTrace_5037129 : CollatzResearch.WordTrace tailWord_5037129 prefixEnd_5037129 2586468295701327943322171 := by
  unfold tailWord_5037129
  simp only [CollatzResearch.WordTrace]
  refine ⟨183719187768349380988466441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122479458512232920658977627 183719187768349380988466441)
  ·
    refine ⟨137789390826262035741349831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183719187768349380988466441 137789390826262035741349831)
    ·
      refine ⟨206684086239393053612024747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137789390826262035741349831 206684086239393053612024747)
      ·
        refine ⟨310026129359089580418037121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206684086239393053612024747 310026129359089580418037121)
        ·
          refine ⟨232519597019317185313527841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310026129359089580418037121 232519597019317185313527841)
          ·
            refine ⟨174389697764487888985145881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232519597019317185313527841 174389697764487888985145881)
            ·
              refine ⟨130792273323365916738859411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174389697764487888985145881 130792273323365916738859411)
              ·
                refine ⟨196188409985048875108289117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130792273323365916738859411 196188409985048875108289117)
                ·
                  refine ⟨73570653744393328165608419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196188409985048875108289117 73570653744393328165608419)
                  ·
                    refine ⟨110355980616589992248412629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73570653744393328165608419 110355980616589992248412629)
                    ·
                      refine ⟨2586468295701327943322171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110355980616589992248412629 2586468295701327943322171)
                      ·
                        rfl

theorem cell23_5037129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_5037129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037129 prefixEnd_5037129 := by exact prefixLift 5037129
  have htrace : WordTrace (prefixWord ++ tailWord_5037129) baseStart_5037129 baseEnd_5037129 := by
    simpa [prefixWord, tailWord_5037129, baseEnd_5037129] using wordTrace_append hprefix tailTrace_5037129
  have hstable : (prefixWord ++ tailWord_5037129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037129).length < 2 ^ (prefixWord ++ tailWord_5037129).sum := by decide
  have hdescent : baseEnd_5037129 < baseStart_5037129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037176 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_5037176 : Nat := 118140960795 + 5037176 * 2 ^ 59
def prefixEnd_5037176 : Nat := 4983230072969 + 3 ^ 40 * 5037176 * 2
def baseEnd_5037176 : Nat := 2586492429292089259434455

theorem tailTrace_5037176 : CollatzResearch.WordTrace tailWord_5037176 prefixEnd_5037176 2586492429292089259434455 := by
  unfold tailWord_5037176
  simp only [CollatzResearch.WordTrace]
  refine ⟨91860450999589554007713691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122480601332786072010284921 91860450999589554007713691)
  ·
    refine ⟨137790676499384331011570537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91860450999589554007713691 137790676499384331011570537)
    ·
      refine ⟨103343007374538248258677903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137790676499384331011570537 103343007374538248258677903)
      ·
        refine ⟨155014511061807372388016855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103343007374538248258677903 155014511061807372388016855)
        ·
          refine ⟨232521766592711058582025283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155014511061807372388016855 232521766592711058582025283)
          ·
            refine ⟨348782649889066587873037925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232521766592711058582025283 348782649889066587873037925)
            ·
              refine ⟨65396746854199985226194611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348782649889066587873037925 65396746854199985226194611)
              ·
                refine ⟨98095120281299977839291917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65396746854199985226194611 98095120281299977839291917)
                ·
                  refine ⟨36785670105487491689734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98095120281299977839291917 36785670105487491689734469)
                  ·
                    refine ⟨6897313144778904691825213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36785670105487491689734469 6897313144778904691825213)
                    ·
                      refine ⟨2586492429292089259434455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897313144778904691825213 2586492429292089259434455)
                      ·
                        rfl

theorem cell23_5037176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_5037176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037176 prefixEnd_5037176 := by exact prefixLift 5037176
  have htrace : WordTrace (prefixWord ++ tailWord_5037176) baseStart_5037176 baseEnd_5037176 := by
    simpa [prefixWord, tailWord_5037176, baseEnd_5037176] using wordTrace_append hprefix tailTrace_5037176
  have hstable : (prefixWord ++ tailWord_5037176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037176).length < 2 ^ (prefixWord ++ tailWord_5037176).sum := by decide
  have hdescent : baseEnd_5037176 < baseStart_5037176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037193 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_5037193 : Nat := 118140960795 + 5037193 * 2 ^ 59
def prefixEnd_5037193 : Nat := 4983230072969 + 3 ^ 40 * 5037193 * 2
def baseEnd_5037193 : Nat := 2586501158463215692921877

theorem tailTrace_5037193 : CollatzResearch.WordTrace tailWord_5037193 prefixEnd_5037193 2586501158463215692921877 := by
  unfold tailWord_5037193
  simp only [CollatzResearch.WordTrace]
  refine ⟨183721522040117519918796233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122481014693411679945864155 183721522040117519918796233)
  ·
    refine ⟨137791141530088139939097175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183721522040117519918796233 137791141530088139939097175)
    ·
      refine ⟨206686712295132209908645763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137791141530088139939097175 206686712295132209908645763)
      ·
        refine ⟨310030068442698314862968645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206686712295132209908645763 310030068442698314862968645)
        ·
          refine ⟨58130637833005934036806621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310030068442698314862968645 58130637833005934036806621)
          ·
            refine ⟨21798989187377225263802483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58130637833005934036806621 21798989187377225263802483)
            ·
              refine ⟨32698483781065837895703725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21798989187377225263802483 32698483781065837895703725)
              ·
                refine ⟨12261931417899689210888897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32698483781065837895703725 12261931417899689210888897)
                ·
                  refine ⟨9196448563424766908166673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12261931417899689210888897 9196448563424766908166673)
                  ·
                    refine ⟨6897336422568575181125005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9196448563424766908166673 6897336422568575181125005)
                    ·
                      refine ⟨2586501158463215692921877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897336422568575181125005 2586501158463215692921877)
                      ·
                        rfl

theorem cell23_5037193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_5037193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037193 prefixEnd_5037193 := by exact prefixLift 5037193
  have htrace : WordTrace (prefixWord ++ tailWord_5037193) baseStart_5037193 baseEnd_5037193 := by
    simpa [prefixWord, tailWord_5037193, baseEnd_5037193] using wordTrace_append hprefix tailTrace_5037193
  have hstable : (prefixWord ++ tailWord_5037193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037193).length < 2 ^ (prefixWord ++ tailWord_5037193).sum := by decide
  have hdescent : baseEnd_5037193 < baseStart_5037193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037210 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5037210 : Nat := 118140960795 + 5037210 * 2 ^ 59
def prefixEnd_5037210 : Nat := 4983230072969 + 3 ^ 40 * 5037210 * 2
def baseEnd_5037210 : Nat := 2586509887634342126409299

theorem tailTrace_5037210 : CollatzResearch.WordTrace tailWord_5037210 prefixEnd_5037210 2586509887634342126409299 := by
  unfold tailWord_5037210
  simp only [CollatzResearch.WordTrace]
  refine ⟨45930535520263982955541271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122481428054037287881443389 45930535520263982955541271)
  ·
    refine ⟨68895803280395974433311907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45930535520263982955541271 68895803280395974433311907)
    ·
      refine ⟨103343704920593961649967861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68895803280395974433311907 103343704920593961649967861)
      ·
        refine ⟨9688472336305683904684487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103343704920593961649967861 9688472336305683904684487)
        ·
          refine ⟨14532708504458525857026731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9688472336305683904684487 14532708504458525857026731)
          ·
            refine ⟨21799062756687788785540097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14532708504458525857026731 21799062756687788785540097)
            ·
              refine ⟨16349297067515841589155073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21799062756687788785540097 16349297067515841589155073)
              ·
                refine ⟨12261972800636881191866305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16349297067515841589155073 12261972800636881191866305)
                ·
                  refine ⟨9196479600477660893899729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12261972800636881191866305 9196479600477660893899729)
                  ·
                    refine ⟨6897359700358245670424797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9196479600477660893899729 6897359700358245670424797)
                    ·
                      refine ⟨2586509887634342126409299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897359700358245670424797 2586509887634342126409299)
                      ·
                        rfl

theorem cell23_5037210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5037210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037210 prefixEnd_5037210 := by exact prefixLift 5037210
  have htrace : WordTrace (prefixWord ++ tailWord_5037210) baseStart_5037210 baseEnd_5037210 := by
    simpa [prefixWord, tailWord_5037210, baseEnd_5037210] using wordTrace_append hprefix tailTrace_5037210
  have hstable : (prefixWord ++ tailWord_5037210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037210).length < 2 ^ (prefixWord ++ tailWord_5037210).sum := by decide
  have hdescent : baseEnd_5037210 < baseStart_5037210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037213 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 6]
def baseStart_5037213 : Nat := 118140960795 + 5037213 * 2 ^ 59
def prefixEnd_5037213 : Nat := 4983230072969 + 3 ^ 40 * 5037213 * 2
def baseEnd_5037213 : Nat := 287390158675145068296865

theorem tailTrace_5037213 : CollatzResearch.WordTrace tailWord_5037213 prefixEnd_5037213 287390158675145068296865 := by
  unfold tailWord_5037213
  simp only [CollatzResearch.WordTrace]
  refine ⟨183722251500045063334524293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122481501000030042223016195 183722251500045063334524293)
  ·
    refine ⟨34447922156258449375223305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183722251500045063334524293 34447922156258449375223305)
    ·
      refine ⟨25835941617193837031417479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34447922156258449375223305 25835941617193837031417479)
      ·
        refine ⟨38753912425790755547126219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25835941617193837031417479 38753912425790755547126219)
        ·
          refine ⟨58130868638686133320689329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38753912425790755547126219 58130868638686133320689329)
          ·
            refine ⟨43598151479014599990516997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58130868638686133320689329 43598151479014599990516997)
            ·
              refine ⟨8174653402315237498221937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43598151479014599990516997 8174653402315237498221937)
              ·
                refine ⟨6130990051736428123666453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8174653402315237498221937 6130990051736428123666453)
                ·
                  refine ⟨287390158675145068296865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6130990051736428123666453 287390158675145068296865)
                  ·
                    rfl

theorem cell23_5037213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_5037213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037213 prefixEnd_5037213 := by exact prefixLift 5037213
  have htrace : WordTrace (prefixWord ++ tailWord_5037213) baseStart_5037213 baseEnd_5037213 := by
    simpa [prefixWord, tailWord_5037213, baseEnd_5037213] using wordTrace_append hprefix tailTrace_5037213
  have hstable : (prefixWord ++ tailWord_5037213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037213).length < 2 ^ (prefixWord ++ tailWord_5037213).sum := by decide
  have hdescent : baseEnd_5037213 < baseStart_5037213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037216 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5037216 : Nat := 118140960795 + 5037216 * 2 ^ 59
def prefixEnd_5037216 : Nat := 4983230072969 + 3 ^ 40 * 5037216 * 2
def baseEnd_5037216 : Nat := 2586512968518269102934271

theorem tailTrace_5037216 : CollatzResearch.WordTrace tailWord_5037216 prefixEnd_5037216 2586512968518269102934271 := by
  unfold tailWord_5037216
  simp only [CollatzResearch.WordTrace]
  refine ⟨91861180459517097423441751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122481573946022796564589001 91861180459517097423441751)
  ·
    refine ⟨137791770689275646135162627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91861180459517097423441751 137791770689275646135162627)
    ·
      refine ⟨206687656033913469202743941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137791770689275646135162627 206687656033913469202743941)
      ·
        refine ⟨38753935506358775475514489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206687656033913469202743941 38753935506358775475514489)
        ·
          refine ⟨29065451629769081606635867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38753935506358775475514489 29065451629769081606635867)
          ·
            refine ⟨43598177444653622409953801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29065451629769081606635867 43598177444653622409953801)
            ·
              refine ⟨32698633083490216807465351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43598177444653622409953801 32698633083490216807465351)
              ·
                refine ⟨49047949625235325211198027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32698633083490216807465351 49047949625235325211198027)
                ·
                  refine ⟨73571924437852987816797041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49047949625235325211198027 73571924437852987816797041)
                  ·
                    refine ⟨55178943328389740862597781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73571924437852987816797041 55178943328389740862597781)
                    ·
                      refine ⟨2586512968518269102934271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55178943328389740862597781 2586512968518269102934271)
                      ·
                        rfl

theorem cell23_5037216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5037216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037216 prefixEnd_5037216 := by exact prefixLift 5037216
  have htrace : WordTrace (prefixWord ++ tailWord_5037216) baseStart_5037216 baseEnd_5037216 := by
    simpa [prefixWord, tailWord_5037216, baseEnd_5037216] using wordTrace_append hprefix tailTrace_5037216
  have hstable : (prefixWord ++ tailWord_5037216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037216).length < 2 ^ (prefixWord ++ tailWord_5037216).sum := by decide
  have hdescent : baseEnd_5037216 < baseStart_5037216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037290 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_5037290 : Nat := 118140960795 + 5037290 * 2 ^ 59
def prefixEnd_5037290 : Nat := 4983230072969 + 3 ^ 40 * 5037290 * 2
def baseEnd_5037290 : Nat := 862183655362233937802977

theorem tailTrace_5037290 : CollatzResearch.WordTrace tailWord_5037290 prefixEnd_5037290 862183655362233937802977 := by
  unfold tailWord_5037290
  simp only [CollatzResearch.WordTrace]
  refine ⟨45931264980191526371269331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122483373280510736990051549 45931264980191526371269331)
  ·
    refine ⟨68896897470287289556903997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45931264980191526371269331 68896897470287289556903997)
    ·
      refine ⟨25836336551357733583838999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68896897470287289556903997 25836336551357733583838999)
      ·
        refine ⟨38754504827036600375758499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25836336551357733583838999 38754504827036600375758499)
        ·
          refine ⟨58131757240554900563637749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38754504827036600375758499 58131757240554900563637749)
          ·
            refine ⟨5449852241302021927841039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58131757240554900563637749 5449852241302021927841039)
            ·
              refine ⟨8174778361953032891761559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449852241302021927841039 8174778361953032891761559)
              ·
                refine ⟨12262167542929549337642339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8174778361953032891761559 12262167542929549337642339)
                ·
                  refine ⟨18393251314394324006463509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12262167542929549337642339 18393251314394324006463509)
                  ·
                    refine ⟨862183655362233937802977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18393251314394324006463509 862183655362233937802977)
                    ·
                      rfl

theorem cell23_5037290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_5037290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037290 prefixEnd_5037290 := by exact prefixLift 5037290
  have htrace : WordTrace (prefixWord ++ tailWord_5037290) baseStart_5037290 baseEnd_5037290 := by
    simpa [prefixWord, tailWord_5037290, baseEnd_5037290] using wordTrace_append hprefix tailTrace_5037290
  have hstable : (prefixWord ++ tailWord_5037290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037290).length < 2 ^ (prefixWord ++ tailWord_5037290).sum := by decide
  have hdescent : baseEnd_5037290 < baseStart_5037290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037320 : List Nat := [2, 1, 3, 2, 5, 1, 9]
def baseStart_5037320 : Nat := 118140960795 + 5037320 * 2 ^ 59
def prefixEnd_5037320 : Nat := 4983230072969 + 3 ^ 40 * 5037320 * 2
def baseEnd_5037320 : Nat := 31932918154399218469553

theorem tailTrace_5037320 : CollatzResearch.WordTrace tailWord_5037320 prefixEnd_5037320 31932918154399218469553 := by
  unfold tailWord_5037320
  simp only [CollatzResearch.WordTrace]
  refine ⟨91863077055328710304334707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122484102740438280405779609 91863077055328710304334707)
  ·
    refine ⟨137794615582993065456502061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91863077055328710304334707 137794615582993065456502061)
    ·
      refine ⟨51672980843622399546188273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137794615582993065456502061 51672980843622399546188273)
      ·
        refine ⟨38754735632716799659641205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51672980843622399546188273 38754735632716799659641205)
        ·
          refine ⟨3633256465567199968091363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38754735632716799659641205 3633256465567199968091363)
          ·
            refine ⟨5449884698350799952137045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633256465567199968091363 5449884698350799952137045)
            ·
              refine ⟨31932918154399218469553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5449884698350799952137045 31932918154399218469553)
              ·
                rfl

theorem cell23_5037320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 9].length) (baseStart_5037320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037320 prefixEnd_5037320 := by exact prefixLift 5037320
  have htrace : WordTrace (prefixWord ++ tailWord_5037320) baseStart_5037320 baseEnd_5037320 := by
    simpa [prefixWord, tailWord_5037320, baseEnd_5037320] using wordTrace_append hprefix tailTrace_5037320
  have hstable : (prefixWord ++ tailWord_5037320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037320).length < 2 ^ (prefixWord ++ tailWord_5037320).sum := by decide
  have hdescent : baseEnd_5037320 < baseStart_5037320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037347 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 3]
def baseStart_5037347 : Nat := 118140960795 + 5037347 * 2 ^ 59
def prefixEnd_5037347 : Nat := 4983230072969 + 3 ^ 40 * 5037347 * 2
def baseEnd_5037347 : Nat := 2586580234484008090396169

theorem tailTrace_5037347 : CollatzResearch.WordTrace tailWord_5037347 prefixEnd_5037347 2586580234484008090396169 := by
  unfold tailWord_5037347
  simp only [CollatzResearch.WordTrace]
  refine ⟨183727138881559604219902295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122484759254373069479934863 183727138881559604219902295)
  ·
    refine ⟨275590708322339406329853443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183727138881559604219902295 275590708322339406329853443)
    ·
      refine ⟨413386062483509109494780165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275590708322339406329853443 413386062483509109494780165)
      ·
        refine ⟨77509886715657958030271281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 413386062483509109494780165 77509886715657958030271281)
        ·
          refine ⟨58132415036743468522703461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77509886715657958030271281 58132415036743468522703461)
          ·
            refine ⟨10899827819389400348006899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58132415036743468522703461 10899827819389400348006899)
            ·
              refine ⟨16349741729084100522010349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10899827819389400348006899 16349741729084100522010349)
              ·
                refine ⟨6131153148406537695753881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16349741729084100522010349 6131153148406537695753881)
                ·
                  refine ⟨4598364861304903271815411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131153148406537695753881 4598364861304903271815411)
                  ·
                    refine ⟨6897547291957354907723117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4598364861304903271815411 6897547291957354907723117)
                    ·
                      refine ⟨2586580234484008090396169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897547291957354907723117 2586580234484008090396169)
                      ·
                        rfl

theorem cell23_5037347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_5037347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037347 prefixEnd_5037347 := by exact prefixLift 5037347
  have htrace : WordTrace (prefixWord ++ tailWord_5037347) baseStart_5037347 baseEnd_5037347 := by
    simpa [prefixWord, tailWord_5037347, baseEnd_5037347] using wordTrace_append hprefix tailTrace_5037347
  have hstable : (prefixWord ++ tailWord_5037347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037347).length < 2 ^ (prefixWord ++ tailWord_5037347).sum := by decide
  have hdescent : baseEnd_5037347 < baseStart_5037347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037393 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 7]
def baseStart_5037393 : Nat := 118140960795 + 5037393 * 2 ^ 59
def prefixEnd_5037393 : Nat := 4983230072969 + 3 ^ 40 * 5037393 * 2
def baseEnd_5037393 : Nat := 287400428288234990046773

theorem tailTrace_5037393 : CollatzResearch.WordTrace tailWord_5037393 prefixEnd_5037393 287400428288234990046773 := by
  unfold tailWord_5037393
  simp only [CollatzResearch.WordTrace]
  refine ⟨183728816639392954076076833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122485877759595302717384555 183728816639392954076076833)
  ·
    refine ⟨137796612479544715557057625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183728816639392954076076833 137796612479544715557057625)
    ·
      refine ⟨103347459359658536667793219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137796612479544715557057625 103347459359658536667793219)
      ·
        refine ⟨155021189039487805001689829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103347459359658536667793219 155021189039487805001689829)
        ·
          refine ⟨29066472944903963437816843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155021189039487805001689829 29066472944903963437816843)
          ·
            refine ⟨43599709417355945156725265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29066472944903963437816843 43599709417355945156725265)
            ·
              refine ⟨32699782063016958867543949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43599709417355945156725265 32699782063016958867543949)
              ·
                refine ⟨12262418273631359575328981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32699782063016958867543949 12262418273631359575328981)
                ·
                  refine ⟨287400428288234990046773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12262418273631359575328981 287400428288234990046773)
                  ·
                    rfl

theorem cell23_5037393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_5037393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037393 prefixEnd_5037393 := by exact prefixLift 5037393
  have htrace : WordTrace (prefixWord ++ tailWord_5037393) baseStart_5037393 baseEnd_5037393 := by
    simpa [prefixWord, tailWord_5037393, baseEnd_5037393] using wordTrace_append hprefix tailTrace_5037393
  have hstable : (prefixWord ++ tailWord_5037393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037393).length < 2 ^ (prefixWord ++ tailWord_5037393).sum := by decide
  have hdescent : baseEnd_5037393 < baseStart_5037393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037398 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5037398 : Nat := 118140960795 + 5037398 * 2 ^ 59
def prefixEnd_5037398 : Nat := 4983230072969 + 3 ^ 40 * 5037398 * 2
def baseEnd_5037398 : Nat := 2586606421997387390858435

theorem tailTrace_5037398 : CollatzResearch.WordTrace tailWord_5037398 prefixEnd_5037398 2586606421997387390858435 := by
  unfold tailWord_5037398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483062437773427495625553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122485999336249893286672565 11483062437773427495625553)
  ·
    refine ⟨8612296828330070621719165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11483062437773427495625553 8612296828330070621719165)
    ·
      refine ⟨3229611310623776483144687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8612296828330070621719165 3229611310623776483144687)
      ·
        refine ⟨4844416965935664724717031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229611310623776483144687 4844416965935664724717031)
        ·
          refine ⟨7266625448903497087075547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844416965935664724717031 7266625448903497087075547)
          ·
            refine ⟨10899938173355245630613321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266625448903497087075547 10899938173355245630613321)
            ·
              refine ⟨8174953630016434222959991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10899938173355245630613321 8174953630016434222959991)
              ·
                refine ⟨12262430445024651334439987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8174953630016434222959991 12262430445024651334439987)
                ·
                  refine ⟨18393645667536977001659981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12262430445024651334439987 18393645667536977001659981)
                  ·
                    refine ⟨6897617125326366375622493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18393645667536977001659981 6897617125326366375622493)
                    ·
                      refine ⟨2586606421997387390858435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897617125326366375622493 2586606421997387390858435)
                      ·
                        rfl

theorem cell23_5037398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5037398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037398 prefixEnd_5037398 := by exact prefixLift 5037398
  have htrace : WordTrace (prefixWord ++ tailWord_5037398) baseStart_5037398 baseEnd_5037398 := by
    simpa [prefixWord, tailWord_5037398, baseEnd_5037398] using wordTrace_append hprefix tailTrace_5037398
  have hstable : (prefixWord ++ tailWord_5037398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037398).length < 2 ^ (prefixWord ++ tailWord_5037398).sum := by decide
  have hdescent : baseEnd_5037398 < baseStart_5037398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037410 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_5037410 : Nat := 118140960795 + 5037410 * 2 ^ 59
def prefixEnd_5037410 : Nat := 4983230072969 + 3 ^ 40 * 5037410 * 2
def baseEnd_5037410 : Nat := 287401398196137927100931

theorem tailTrace_5037410 : CollatzResearch.WordTrace tailWord_5037410 prefixEnd_5037410 287401398196137927100931 := by
  unfold tailWord_5037410
  simp only [CollatzResearch.WordTrace]
  refine ⟨45932359170082841494861421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122486291120220910652963789 45932359170082841494861421)
  ·
    refine ⟨17224634688781065560573033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45932359170082841494861421 17224634688781065560573033)
    ·
      refine ⟨12918476016585799170429775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17224634688781065560573033 12918476016585799170429775)
      ·
        refine ⟨19377714024878698755644663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12918476016585799170429775 19377714024878698755644663)
        ·
          refine ⟨29066571037318048133466995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19377714024878698755644663 29066571037318048133466995)
          ·
            refine ⟨43599856555977072200200493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29066571037318048133466995 43599856555977072200200493)
            ·
              refine ⟨16349946208491402075075185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43599856555977072200200493 16349946208491402075075185)
              ·
                refine ⟨12262459656368551556306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16349946208491402075075185 12262459656368551556306389)
                ·
                  refine ⟨287401398196137927100931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12262459656368551556306389 287401398196137927100931)
                  ·
                    rfl

theorem cell23_5037410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_5037410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037410 prefixEnd_5037410 := by exact prefixLift 5037410
  have htrace : WordTrace (prefixWord ++ tailWord_5037410) baseStart_5037410 baseEnd_5037410 := by
    simpa [prefixWord, tailWord_5037410, baseEnd_5037410] using wordTrace_append hprefix tailTrace_5037410
  have hstable : (prefixWord ++ tailWord_5037410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037410).length < 2 ^ (prefixWord ++ tailWord_5037410).sum := by decide
  have hdescent : baseEnd_5037410 < baseStart_5037410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037423 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 7]
def baseStart_5037423 : Nat := 118140960795 + 5037423 * 2 ^ 59
def prefixEnd_5037423 : Nat := 4983230072969 + 3 ^ 40 * 5037423 * 2
def baseEnd_5037423 : Nat := 862206419671249931015273

theorem tailTrace_5037423 : CollatzResearch.WordTrace tailWord_5037423 prefixEnd_5037423 862206419671249931015273 := by
  unfold tailWord_5037423
  simp only [CollatzResearch.WordTrace]
  refine ⟨183729910829284269199668923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122486607219522846133112615 183729910829284269199668923)
  ·
    refine ⟨275594866243926403799503385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183729910829284269199668923 275594866243926403799503385)
    ·
      refine ⟨206696149682944802849627539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275594866243926403799503385 206696149682944802849627539)
      ·
        refine ⟨310044224524417204274441309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206696149682944802849627539 310044224524417204274441309)
        ·
          refine ⟨116266584196656451602915491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310044224524417204274441309 116266584196656451602915491)
          ·
            refine ⟨174399876294984677404373237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116266584196656451602915491 174399876294984677404373237)
            ·
              refine ⟨16349988402654813506659991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174399876294984677404373237 16349988402654813506659991)
              ·
                refine ⟨24524982603982220259989987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16349988402654813506659991 24524982603982220259989987)
                ·
                  refine ⟨36787473905973330389984981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24524982603982220259989987 36787473905973330389984981)
                  ·
                    refine ⟨862206419671249931015273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36787473905973330389984981 862206419671249931015273)
                    ·
                      rfl

theorem cell23_5037423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_5037423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037423 prefixEnd_5037423 := by exact prefixLift 5037423
  have htrace : WordTrace (prefixWord ++ tailWord_5037423) baseStart_5037423 baseEnd_5037423 := by
    simpa [prefixWord, tailWord_5037423, baseEnd_5037423] using wordTrace_append hprefix tailTrace_5037423
  have hstable : (prefixWord ++ tailWord_5037423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037423).length < 2 ^ (prefixWord ++ tailWord_5037423).sum := by decide
  have hdescent : baseEnd_5037423 < baseStart_5037423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037433 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_5037433 : Nat := 118140960795 + 5037433 * 2 ^ 59
def prefixEnd_5037433 : Nat := 4983230072969 + 3 ^ 40 * 5037433 * 2
def baseEnd_5037433 : Nat := 2586624393820294753920773

theorem tailTrace_5037433 : CollatzResearch.WordTrace tailWord_5037433 prefixEnd_5037433 2586624393820294753920773 := by
  unfold tailWord_5037433
  simp only [CollatzResearch.WordTrace]
  refine ⟨183730275559248040907532953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122486850372832027271688635 183730275559248040907532953)
  ·
    refine ⟨137797706669436030680649715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183730275559248040907532953 137797706669436030680649715)
    ·
      refine ⟨206696560004154046020974573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137797706669436030680649715 206696560004154046020974573)
      ·
        refine ⟨77511210001557767257865465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206696560004154046020974573 77511210001557767257865465)
        ·
          refine ⟨58133407501168325443399099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77511210001557767257865465 58133407501168325443399099)
          ·
            refine ⟨87200111251752488165098649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58133407501168325443399099 87200111251752488165098649)
            ·
              refine ⟨65400083438814366123823987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87200111251752488165098649 65400083438814366123823987)
              ·
                refine ⟨98100125158221549185735981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65400083438814366123823987 98100125158221549185735981)
                ·
                  refine ⟨36787546934333080944650993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98100125158221549185735981 36787546934333080944650993)
                  ·
                    refine ⟨27590660200749810708488245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36787546934333080944650993 27590660200749810708488245)
                    ·
                      refine ⟨2586624393820294753920773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27590660200749810708488245 2586624393820294753920773)
                      ·
                        rfl

theorem cell23_5037433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_5037433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037433 prefixEnd_5037433 := by exact prefixLift 5037433
  have htrace : WordTrace (prefixWord ++ tailWord_5037433) baseStart_5037433 baseEnd_5037433 := by
    simpa [prefixWord, tailWord_5037433, baseEnd_5037433] using wordTrace_append hprefix tailTrace_5037433
  have hstable : (prefixWord ++ tailWord_5037433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037433).length < 2 ^ (prefixWord ++ tailWord_5037433).sum := by decide
  have hdescent : baseEnd_5037433 < baseStart_5037433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037438 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5037438 : Nat := 118140960795 + 5037438 * 2 ^ 59
def prefixEnd_5037438 : Nat := 4983230072969 + 3 ^ 40 * 5037438 * 2
def baseEnd_5037438 : Nat := 2586626961223567234358251

theorem tailTrace_5037438 : CollatzResearch.WordTrace tailWord_5037438 prefixEnd_5037438 2586626961223567234358251 := by
  unfold tailWord_5037438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22966307240528740845183121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122486971949486617840976645 22966307240528740845183121)
  ·
    refine ⟨17224730430396555633887341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22966307240528740845183121 17224730430396555633887341)
    ·
      refine ⟨6459273911398708362707753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17224730430396555633887341 6459273911398708362707753)
      ·
        refine ⟨4844455433549031272030815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6459273911398708362707753 4844455433549031272030815)
        ·
          refine ⟨7266683150323546908046223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844455433549031272030815 7266683150323546908046223)
          ·
            refine ⟨10900024725485320362069335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266683150323546908046223 10900024725485320362069335)
            ·
              refine ⟨16350037088227980543104003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10900024725485320362069335 16350037088227980543104003)
              ·
                refine ⟨24525055632341970814656005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16350037088227980543104003 24525055632341970814656005)
                ·
                  refine ⟨4598447931064119527748001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24525055632341970814656005 4598447931064119527748001)
                  ·
                    refine ⟨3448835948298089645811001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4598447931064119527748001 3448835948298089645811001)
                    ·
                      refine ⟨2586626961223567234358251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448835948298089645811001 2586626961223567234358251)
                      ·
                        rfl

theorem cell23_5037438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5037438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037438 prefixEnd_5037438 := by exact prefixLift 5037438
  have htrace : WordTrace (prefixWord ++ tailWord_5037438) baseStart_5037438 baseEnd_5037438 := by
    simpa [prefixWord, tailWord_5037438, baseEnd_5037438] using wordTrace_append hprefix tailTrace_5037438
  have hstable : (prefixWord ++ tailWord_5037438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037438).length < 2 ^ (prefixWord ++ tailWord_5037438).sum := by decide
  have hdescent : baseEnd_5037438 < baseStart_5037438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037503 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_5037503 : Nat := 118140960795 + 5037503 * 2 ^ 59
def prefixEnd_5037503 : Nat := 4983230072969 + 3 ^ 40 * 5037503 * 2
def baseEnd_5037503 : Nat := 2586660337466109480045451

theorem tailTrace_5037503 : CollatzResearch.WordTrace tailWord_5037503 prefixEnd_5037503 2586660337466109480045451 := by
  unfold tailWord_5037503
  simp only [CollatzResearch.WordTrace]
  refine ⟨183732828668994442862581163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122488552445996295241720775 183732828668994442862581163)
  ·
    refine ⟨275599243003491664293871745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183732828668994442862581163 275599243003491664293871745)
    ·
      refine ⟨206699432252618748220403809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275599243003491664293871745 206699432252618748220403809)
      ·
        refine ⟨155024574189464061165302857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206699432252618748220403809 155024574189464061165302857)
        ·
          refine ⟨116268430642098045873977143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155024574189464061165302857 116268430642098045873977143)
          ·
            refine ⟨174402645963147068810965715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116268430642098045873977143 174402645963147068810965715)
            ·
              refine ⟨261603968944720603216448573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174402645963147068810965715 261603968944720603216448573)
              ·
                refine ⟨98101488354270226206168215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261603968944720603216448573 98101488354270226206168215)
                ·
                  refine ⟨147152232531405339309252323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98101488354270226206168215 147152232531405339309252323)
                  ·
                    refine ⟨220728348797108008963878485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147152232531405339309252323 220728348797108008963878485)
                    ·
                      refine ⟨2586660337466109480045451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220728348797108008963878485 2586660337466109480045451)
                      ·
                        rfl

theorem cell23_5037503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_5037503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037503 prefixEnd_5037503 := by exact prefixLift 5037503
  have htrace : WordTrace (prefixWord ++ tailWord_5037503) baseStart_5037503 baseEnd_5037503 := by
    simpa [prefixWord, tailWord_5037503, baseEnd_5037503] using wordTrace_append hprefix tailTrace_5037503
  have hstable : (prefixWord ++ tailWord_5037503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037503).length < 2 ^ (prefixWord ++ tailWord_5037503).sum := by decide
  have hdescent : baseEnd_5037503 < baseStart_5037503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037506 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5037506 : Nat := 118140960795 + 5037506 * 2 ^ 59
def prefixEnd_5037506 : Nat := 4983230072969 + 3 ^ 40 * 5037506 * 2
def baseEnd_5037506 : Nat := 2586661877908072968307939

theorem tailTrace_5037506 : CollatzResearch.WordTrace tailWord_5037506 prefixEnd_5037506 2586661877908072968307939 := by
  unfold tailWord_5037506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45933234521995893593735093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122488625391989049583293581 45933234521995893593735093)
  ·
    refine ⟨4306240736437115024412665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45933234521995893593735093 4306240736437115024412665)
    ·
      refine ⟨3229680552327836268309499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4306240736437115024412665 3229680552327836268309499)
      ·
        refine ⟨4844520828491754402464249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229680552327836268309499 4844520828491754402464249)
        ·
          refine ⟨3633390621368815801848187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844520828491754402464249 3633390621368815801848187)
          ·
            refine ⟨5450085932053223702772281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633390621368815801848187 5450085932053223702772281)
            ·
              refine ⟨4087564449039917777079211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5450085932053223702772281 4087564449039917777079211)
              ·
                refine ⟨6131346673559876665618817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087564449039917777079211 6131346673559876665618817)
                ·
                  refine ⟨4598510005169907499214113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131346673559876665618817 4598510005169907499214113)
                  ·
                    refine ⟨3448882503877430624410585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4598510005169907499214113 3448882503877430624410585)
                    ·
                      refine ⟨2586661877908072968307939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448882503877430624410585 2586661877908072968307939)
                      ·
                        rfl

theorem cell23_5037506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5037506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037506 prefixEnd_5037506 := by exact prefixLift 5037506
  have htrace : WordTrace (prefixWord ++ tailWord_5037506) baseStart_5037506 baseEnd_5037506 := by
    simpa [prefixWord, tailWord_5037506, baseEnd_5037506] using wordTrace_append hprefix tailTrace_5037506
  have hstable : (prefixWord ++ tailWord_5037506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037506).length < 2 ^ (prefixWord ++ tailWord_5037506).sum := by decide
  have hdescent : baseEnd_5037506 < baseStart_5037506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037513 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_5037513 : Nat := 118140960795 + 5037513 * 2 ^ 59
def prefixEnd_5037513 : Nat := 4983230072969 + 3 ^ 40 * 5037513 * 2
def baseEnd_5037513 : Nat := 862221824090884813640135

theorem tailTrace_5037513 : CollatzResearch.WordTrace tailWord_5037513 prefixEnd_5037513 862221824090884813640135 := by
  unfold tailWord_5037513
  simp only [CollatzResearch.WordTrace]
  refine ⟨183733193398958214570445193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122488795599305476380296795 183733193398958214570445193)
  ·
    refine ⟨137799895049218660927833895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183733193398958214570445193 137799895049218660927833895)
    ·
      refine ⟨206699842573827991391750843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137799895049218660927833895 206699842573827991391750843)
      ·
        refine ⟨310049763860741987087626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206699842573827991391750843 310049763860741987087626265)
        ·
          refine ⟨232537322895556490315719699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310049763860741987087626265 232537322895556490315719699)
          ·
            refine ⟨348805984343334735473579549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232537322895556490315719699 348805984343334735473579549)
            ·
              refine ⟨130802244128750525802592331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348805984343334735473579549 130802244128750525802592331)
              ·
                refine ⟨196203366193125788703888497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130802244128750525802592331 196203366193125788703888497)
                ·
                  refine ⟨147152524644844341527916373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196203366193125788703888497 147152524644844341527916373)
                  ·
                    refine ⟨862221824090884813640135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147152524644844341527916373 862221824090884813640135)
                    ·
                      rfl

theorem cell23_5037513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_5037513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037513 prefixEnd_5037513 := by exact prefixLift 5037513
  have htrace : WordTrace (prefixWord ++ tailWord_5037513) baseStart_5037513 baseEnd_5037513 := by
    simpa [prefixWord, tailWord_5037513, baseEnd_5037513] using wordTrace_append hprefix tailTrace_5037513
  have hstable : (prefixWord ++ tailWord_5037513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037513).length < 2 ^ (prefixWord ++ tailWord_5037513).sum := by decide
  have hdescent : baseEnd_5037513 < baseStart_5037513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037527 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_5037527 : Nat := 118140960795 + 5037527 * 2 ^ 59
def prefixEnd_5037527 : Nat := 4983230072969 + 3 ^ 40 * 5037527 * 2
def baseEnd_5037527 : Nat := 2586672661001817386145341

theorem tailTrace_5037527 : CollatzResearch.WordTrace tailWord_5037527 prefixEnd_5037527 2586672661001817386145341 := by
  unfold tailWord_5037527
  simp only [CollatzResearch.WordTrace]
  refine ⟨183733704020907494961454835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122489136013938329974303223 183733704020907494961454835)
  ·
    refine ⟨275600556031361242442182253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183733704020907494961454835 275600556031361242442182253)
    ·
      refine ⟨103350208511760465915818345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275600556031361242442182253 103350208511760465915818345)
      ·
        refine ⟨77512656383820349436863759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103350208511760465915818345 77512656383820349436863759)
        ·
          refine ⟨116268984575730524155295639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77512656383820349436863759 116268984575730524155295639)
          ·
            refine ⟨174403476863595786232943459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116268984575730524155295639 174403476863595786232943459)
            ·
              refine ⟨261605215295393679349415189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174403476863595786232943459 261605215295393679349415189)
              ·
                refine ⟨12262744466971578719503837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261605215295393679349415189 12262744466971578719503837)
                ·
                  refine ⟨4598529175114342019813939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12262744466971578719503837 4598529175114342019813939)
                  ·
                    refine ⟨6897793762671513029720909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4598529175114342019813939 6897793762671513029720909)
                    ·
                      refine ⟨2586672661001817386145341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897793762671513029720909 2586672661001817386145341)
                      ·
                        rfl

theorem cell23_5037527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_5037527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037527 prefixEnd_5037527 := by exact prefixLift 5037527
  have htrace : WordTrace (prefixWord ++ tailWord_5037527) baseStart_5037527 baseEnd_5037527 := by
    simpa [prefixWord, tailWord_5037527, baseEnd_5037527] using wordTrace_append hprefix tailTrace_5037527
  have hstable : (prefixWord ++ tailWord_5037527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037527).length < 2 ^ (prefixWord ++ tailWord_5037527).sum := by decide
  have hdescent : baseEnd_5037527 < baseStart_5037527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037577 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_5037577 : Nat := 118140960795 + 5037577 * 2 ^ 59
def prefixEnd_5037577 : Nat := 4983230072969 + 3 ^ 40 * 5037577 * 2
def baseEnd_5037577 : Nat := 862232778344847396840037

theorem tailTrace_5037577 : CollatzResearch.WordTrace tailWord_5037577 prefixEnd_5037577 862232778344847396840037 := by
  unfold tailWord_5037577
  simp only [CollatzResearch.WordTrace]
  refine ⟨183735527670726353500774985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122490351780484235667183323 183735527670726353500774985)
  ·
    refine ⟨137801645753044765125581239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183735527670726353500774985 137801645753044765125581239)
    ·
      refine ⟨206702468629567147688371859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137801645753044765125581239 206702468629567147688371859)
      ·
        refine ⟨310053702944350721532557789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206702468629567147688371859 310053702944350721532557789)
        ·
          refine ⟨116270138604131520574709171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310053702944350721532557789 116270138604131520574709171)
          ·
            refine ⟨174405207906197280862063757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116270138604131520574709171 174405207906197280862063757)
            ·
              refine ⟨65401952964823980323273909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174405207906197280862063757 65401952964823980323273909)
              ·
                refine ⟨6131433090452248155306929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65401952964823980323273909 6131433090452248155306929)
                ·
                  refine ⟨4598574817839186116480197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131433090452248155306929 4598574817839186116480197)
                  ·
                    refine ⟨862232778344847396840037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598574817839186116480197 862232778344847396840037)
                    ·
                      rfl

theorem cell23_5037577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_5037577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037577 prefixEnd_5037577 := by exact prefixLift 5037577
  have htrace : WordTrace (prefixWord ++ tailWord_5037577) baseStart_5037577 baseEnd_5037577 := by
    simpa [prefixWord, tailWord_5037577, baseEnd_5037577] using wordTrace_append hprefix tailTrace_5037577
  have hstable : (prefixWord ++ tailWord_5037577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037577).length < 2 ^ (prefixWord ++ tailWord_5037577).sum := by decide
  have hdescent : baseEnd_5037577 < baseStart_5037577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037587 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3]
def baseStart_5037587 : Nat := 118140960795 + 5037587 * 2 ^ 59
def prefixEnd_5037587 : Nat := 4983230072969 + 3 ^ 40 * 5037587 * 2
def baseEnd_5037587 : Nat := 2586703469841087151395065

theorem tailTrace_5037587 : CollatzResearch.WordTrace tailWord_5037587 prefixEnd_5037587 2586703469841087151395065 := by
  unfold tailWord_5037587
  simp only [CollatzResearch.WordTrace]
  refine ⟨183735892400690125208639015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122490594933793416805759343 183735892400690125208639015)
  ·
    refine ⟨275603838601035187812958523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183735892400690125208639015 275603838601035187812958523)
    ·
      refine ⟨413405757901552781719437785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275603838601035187812958523 413405757901552781719437785)
      ·
        refine ⟨310054318426164586289578339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413405757901552781719437785 310054318426164586289578339)
        ·
          refine ⟨465081477639246879434367509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310054318426164586289578339 465081477639246879434367509)
          ·
            refine ⟨21800694264339697473485977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 465081477639246879434367509 21800694264339697473485977)
            ·
              refine ⟨16350520698254773105114483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21800694264339697473485977 16350520698254773105114483)
              ·
                refine ⟨24525781047382159657671725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16350520698254773105114483 24525781047382159657671725)
                ·
                  refine ⟨9197167892768309871626897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24525781047382159657671725 9197167892768309871626897)
                  ·
                    refine ⟨6897875919576232403720173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9197167892768309871626897 6897875919576232403720173)
                    ·
                      refine ⟨2586703469841087151395065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6897875919576232403720173 2586703469841087151395065)
                      ·
                        rfl

theorem cell23_5037587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_5037587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037587 prefixEnd_5037587 := by exact prefixLift 5037587
  have htrace : WordTrace (prefixWord ++ tailWord_5037587) baseStart_5037587 baseEnd_5037587 := by
    simpa [prefixWord, tailWord_5037587, baseEnd_5037587] using wordTrace_append hprefix tailTrace_5037587
  have hstable : (prefixWord ++ tailWord_5037587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037587).length < 2 ^ (prefixWord ++ tailWord_5037587).sum := by decide
  have hdescent : baseEnd_5037587 < baseStart_5037587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037597 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5037597 : Nat := 118140960795 + 5037597 * 2 ^ 59
def prefixEnd_5037597 : Nat := 4983230072969 + 3 ^ 40 * 5037597 * 2
def baseEnd_5037597 : Nat := 2586708604647632112270019

theorem tailTrace_5037597 : CollatzResearch.WordTrace tailWord_5037597 prefixEnd_5037597 2586708604647632112270019 := by
  unfold tailWord_5037597
  simp only [CollatzResearch.WordTrace]
  refine ⟨183736257130653896916503045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122490838087102597944335363 183736257130653896916503045)
  ·
    refine ⟨34450548211997605671844321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183736257130653896916503045 34450548211997605671844321)
    ·
      refine ⟨25837911158998204253883241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34450548211997605671844321 25837911158998204253883241)
      ·
        refine ⟨19378433369248653190412431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25837911158998204253883241 19378433369248653190412431)
        ·
          refine ⟨29067650053872979785618647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19378433369248653190412431 29067650053872979785618647)
          ·
            refine ⟨43601475080809469678427971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29067650053872979785618647 43601475080809469678427971)
            ·
              refine ⟨65402212621214204517641957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43601475080809469678427971 65402212621214204517641957)
              ·
                refine ⟨12262914866477663347057867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65402212621214204517641957 12262914866477663347057867)
                ·
                  refine ⟨18394372299716495020586801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12262914866477663347057867 18394372299716495020586801)
                  ·
                    refine ⟨13795779224787371265440101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18394372299716495020586801 13795779224787371265440101)
                    ·
                      refine ⟨2586708604647632112270019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13795779224787371265440101 2586708604647632112270019)
                      ·
                        rfl

theorem cell23_5037597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5037597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037597 prefixEnd_5037597 := by exact prefixLift 5037597
  have htrace : WordTrace (prefixWord ++ tailWord_5037597) baseStart_5037597 baseEnd_5037597 := by
    simpa [prefixWord, tailWord_5037597, baseEnd_5037597] using wordTrace_append hprefix tailTrace_5037597
  have hstable : (prefixWord ++ tailWord_5037597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037597).length < 2 ^ (prefixWord ++ tailWord_5037597).sum := by decide
  have hdescent : baseEnd_5037597 < baseStart_5037597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037601 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5037601 : Nat := 118140960795 + 5037601 * 2 ^ 59
def prefixEnd_5037601 : Nat := 4983230072969 + 3 ^ 40 * 5037601 * 2
def baseEnd_5037601 : Nat := 2586710658570250096620001

theorem tailTrace_5037601 : CollatzResearch.WordTrace tailWord_5037601 prefixEnd_5037601 2586710658570250096620001 := by
  unfold tailWord_5037601
  simp only [CollatzResearch.WordTrace]
  refine ⟨183736403022639405599648657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122490935348426270399765771 183736403022639405599648657)
  ·
    refine ⟨137802302266979554199736493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183736403022639405599648657 137802302266979554199736493)
    ·
      refine ⟨51675863350117332824901185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137802302266979554199736493 51675863350117332824901185)
      ·
        refine ⟨38756897512587999618675889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51675863350117332824901185 38756897512587999618675889)
        ·
          refine ⟨29067673134440999714006917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38756897512587999618675889 29067673134440999714006917)
          ·
            refine ⟨5450188712707687446376297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29067673134440999714006917 5450188712707687446376297)
            ·
              refine ⟨4087641534530765584782223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5450188712707687446376297 4087641534530765584782223)
              ·
                refine ⟨6131462301796148377173335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087641534530765584782223 6131462301796148377173335)
                ·
                  refine ⟨9197193452694222565760003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6131462301796148377173335 9197193452694222565760003)
                  ·
                    refine ⟨13795790179041333848640005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9197193452694222565760003 13795790179041333848640005)
                    ·
                      refine ⟨2586710658570250096620001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13795790179041333848640005 2586710658570250096620001)
                      ·
                        rfl

theorem cell23_5037601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5037601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037601 prefixEnd_5037601 := by exact prefixLift 5037601
  have htrace : WordTrace (prefixWord ++ tailWord_5037601) baseStart_5037601 baseEnd_5037601 := by
    simpa [prefixWord, tailWord_5037601, baseEnd_5037601] using wordTrace_append hprefix tailTrace_5037601
  have hstable : (prefixWord ++ tailWord_5037601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037601).length < 2 ^ (prefixWord ++ tailWord_5037601).sum := by decide
  have hdescent : baseEnd_5037601 < baseStart_5037601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037685 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5037685 : Nat := 118140960795 + 5037685 * 2 ^ 59
def prefixEnd_5037685 : Nat := 4983230072969 + 3 ^ 40 * 5037685 * 2
def baseEnd_5037685 : Nat := 2586753790945227767969615

theorem tailTrace_5037685 : CollatzResearch.WordTrace tailWord_5037685 prefixEnd_5037685 2586753790945227767969615 := by
  unfold tailWord_5037685
  simp only [CollatzResearch.WordTrace]
  refine ⟨183739466754335087945706509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122492977836223391963804339 183739466754335087945706509)
  ·
    refine ⟨68902300032875657979639941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183739466754335087945706509 68902300032875657979639941)
    ·
      refine ⟨12919181256164185871182489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68902300032875657979639941 12919181256164185871182489)
      ·
        refine ⟨9689385942123139403386867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12919181256164185871182489 9689385942123139403386867)
        ·
          refine ⟨14534078913184709105080301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9689385942123139403386867 14534078913184709105080301)
          ·
            refine ⟨5450279592444265914405113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14534078913184709105080301 5450279592444265914405113)
            ·
              refine ⟨4087709694333199435803835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5450279592444265914405113 4087709694333199435803835)
              ·
                refine ⟨6131564541499799153705753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087709694333199435803835 6131564541499799153705753)
                ·
                  refine ⟨4598673406124849365279315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131564541499799153705753 4598673406124849365279315)
                  ·
                    refine ⟨6898010109187274047918973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4598673406124849365279315 6898010109187274047918973)
                    ·
                      refine ⟨2586753790945227767969615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898010109187274047918973 2586753790945227767969615)
                      ·
                        rfl

theorem cell23_5037685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5037685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037685 prefixEnd_5037685 := by exact prefixLift 5037685
  have htrace : WordTrace (prefixWord ++ tailWord_5037685) baseStart_5037685 baseEnd_5037685 := by
    simpa [prefixWord, tailWord_5037685, baseEnd_5037685] using wordTrace_append hprefix tailTrace_5037685
  have hstable : (prefixWord ++ tailWord_5037685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037685).length < 2 ^ (prefixWord ++ tailWord_5037685).sum := by decide
  have hdescent : baseEnd_5037685 < baseStart_5037685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037691 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 2, 2, 2]
def baseStart_5037691 : Nat := 118140960795 + 5037691 * 2 ^ 59
def prefixEnd_5037691 : Nat := 4983230072969 + 3 ^ 40 * 5037691 * 2
def baseEnd_5037691 : Nat := 2586756871829154744494587

theorem tailTrace_5037691 : CollatzResearch.WordTrace tailWord_5037691 prefixEnd_5037691 2586756871829154744494587 := by
  unfold tailWord_5037691
  simp only [CollatzResearch.WordTrace]
  refine ⟨183739685592313350970424927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122493123728208900646949951 183739685592313350970424927)
  ·
    refine ⟨275609528388470026455637391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183739685592313350970424927 275609528388470026455637391)
    ·
      refine ⟨413414292582705039683456087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275609528388470026455637391 413414292582705039683456087)
      ·
        refine ⟨620121438874057559525184131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413414292582705039683456087 620121438874057559525184131)
        ·
          refine ⟨930182158311086339287776197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620121438874057559525184131 930182158311086339287776197)
          ·
            refine ⟨174409154683328688616458037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 930182158311086339287776197 174409154683328688616458037)
            ·
              refine ⟨16350858251562064557792941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174409154683328688616458037 16350858251562064557792941)
              ·
                refine ⟨6131571844335774209172353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16350858251562064557792941 6131571844335774209172353)
                ·
                  refine ⟨4598678883251830656879265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131571844335774209172353 4598678883251830656879265)
                  ·
                    refine ⟨3449009162438872992659449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4598678883251830656879265 3449009162438872992659449)
                    ·
                      refine ⟨2586756871829154744494587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449009162438872992659449 2586756871829154744494587)
                      ·
                        rfl

theorem cell23_5037691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2, 2].length) (baseStart_5037691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037691 prefixEnd_5037691 := by exact prefixLift 5037691
  have htrace : WordTrace (prefixWord ++ tailWord_5037691) baseStart_5037691 baseEnd_5037691 := by
    simpa [prefixWord, tailWord_5037691, baseEnd_5037691] using wordTrace_append hprefix tailTrace_5037691
  have hstable : (prefixWord ++ tailWord_5037691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037691).length < 2 ^ (prefixWord ++ tailWord_5037691).sum := by decide
  have hdescent : baseEnd_5037691 < baseStart_5037691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037747 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4]
def baseStart_5037747 : Nat := 118140960795 + 5037747 * 2 ^ 59
def prefixEnd_5037747 : Nat := 4983230072969 + 3 ^ 40 * 5037747 * 2
def baseEnd_5037747 : Nat := 2586785626745806525394329

theorem tailTrace_5037747 : CollatzResearch.WordTrace tailWord_5037747 prefixEnd_5037747 2586785626745806525394329 := by
  unfold tailWord_5037747
  simp only [CollatzResearch.WordTrace]
  refine ⟨183741728080110472534463495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122494485386740315022975663 183741728080110472534463495)
  ·
    refine ⟨275612592120165708801695243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183741728080110472534463495 275612592120165708801695243)
    ·
      refine ⟨413418888180248563202542865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275612592120165708801695243 413418888180248563202542865)
      ·
        refine ⟨310064166135186422401907149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413418888180248563202542865 310064166135186422401907149)
        ·
          refine ⟨116274062300694908400715181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310064166135186422401907149 116274062300694908400715181)
          ·
            refine ⟨43602773362760590650268193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116274062300694908400715181 43602773362760590650268193)
            ·
              refine ⟨32702080022070442987701145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43602773362760590650268193 32702080022070442987701145)
              ·
                refine ⟨24526560016552832240775859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32702080022070442987701145 24526560016552832240775859)
                ·
                  refine ⟨36789840024829248361163789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24526560016552832240775859 36789840024829248361163789)
                  ·
                    refine ⟨13796190009310968135436421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36789840024829248361163789 13796190009310968135436421)
                    ·
                      refine ⟨2586785626745806525394329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13796190009310968135436421 2586785626745806525394329)
                      ·
                        rfl

theorem cell23_5037747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_5037747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037747 prefixEnd_5037747 := by exact prefixLift 5037747
  have htrace : WordTrace (prefixWord ++ tailWord_5037747) baseStart_5037747 baseEnd_5037747 := by
    simpa [prefixWord, tailWord_5037747, baseEnd_5037747] using wordTrace_append hprefix tailTrace_5037747
  have hstable : (prefixWord ++ tailWord_5037747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037747).length < 2 ^ (prefixWord ++ tailWord_5037747).sum := by decide
  have hdescent : baseEnd_5037747 < baseStart_5037747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037764 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5037764 : Nat := 118140960795 + 5037764 * 2 ^ 59
def prefixEnd_5037764 : Nat := 4983230072969 + 3 ^ 40 * 5037764 * 2
def baseEnd_5037764 : Nat := 2586794355916932958881751

theorem tailTrace_5037764 : CollatzResearch.WordTrace tailWord_5037764 prefixEnd_5037764 2586794355916932958881751 := by
  unfold tailWord_5037764
  simp only [CollatzResearch.WordTrace]
  refine ⟨91871174060524442218916173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122494898747365922958554897 91871174060524442218916173)
  ·
    refine ⟨34451690272696665832093565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91871174060524442218916173 34451690272696665832093565)
    ·
      refine ⟨12919383852261249687035087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34451690272696665832093565 12919383852261249687035087)
      ·
        refine ⟨19379075778391874530552631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12919383852261249687035087 19379075778391874530552631)
        ·
          refine ⟨29068613667587811795828947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19379075778391874530552631 29068613667587811795828947)
          ·
            refine ⟨43602920501381717693743421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068613667587811795828947 43602920501381717693743421)
            ·
              refine ⟨16351095188018144135153783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43602920501381717693743421 16351095188018144135153783)
              ·
                refine ⟨24526642782027216202730675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16351095188018144135153783 24526642782027216202730675)
                ·
                  refine ⟨36789964173040824304096013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24526642782027216202730675 36789964173040824304096013)
                  ·
                    refine ⟨13796236564890309114036005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36789964173040824304096013 13796236564890309114036005)
                    ·
                      refine ⟨2586794355916932958881751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13796236564890309114036005 2586794355916932958881751)
                      ·
                        rfl

theorem cell23_5037764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5037764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037764 prefixEnd_5037764 := by exact prefixLift 5037764
  have htrace : WordTrace (prefixWord ++ tailWord_5037764) baseStart_5037764 baseEnd_5037764 := by
    simpa [prefixWord, tailWord_5037764, baseEnd_5037764] using wordTrace_append hprefix tailTrace_5037764
  have hstable : (prefixWord ++ tailWord_5037764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037764).length < 2 ^ (prefixWord ++ tailWord_5037764).sum := by decide
  have hdescent : baseEnd_5037764 < baseStart_5037764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037774 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_5037774 : Nat := 118140960795 + 5037774 * 2 ^ 59
def prefixEnd_5037774 : Nat := 4983230072969 + 3 ^ 40 * 5037774 * 2
def baseEnd_5037774 : Nat := 862266496907825973252235

theorem tailTrace_5037774 : CollatzResearch.WordTrace tailWord_5037774 prefixEnd_5037774 862266496907825973252235 := by
  unfold tailWord_5037774
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967839106376582018212047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122495141900675104097130917 22967839106376582018212047)
  ·
    refine ⟨34451758659564873027318071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22967839106376582018212047 34451758659564873027318071)
    ·
      refine ⟨51677637989347309540977107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34451758659564873027318071 51677637989347309540977107)
      ·
        refine ⟨77516456984020964311465661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51677637989347309540977107 77516456984020964311465661)
        ·
          refine ⟨29068671369007861616799623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77516456984020964311465661 29068671369007861616799623)
          ·
            refine ⟨43603007053511792425199435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068671369007861616799623 43603007053511792425199435)
            ·
              refine ⟨65404510580267688637799153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43603007053511792425199435 65404510580267688637799153)
              ·
                refine ⟨49053382935200766478349365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65404510580267688637799153 49053382935200766478349365)
                ·
                  refine ⟨4598754650175071857345253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49053382935200766478349365 4598754650175071857345253)
                  ·
                    refine ⟨862266496907825973252235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598754650175071857345253 862266496907825973252235)
                    ·
                      rfl

theorem cell23_5037774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_5037774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037774 prefixEnd_5037774 := by exact prefixLift 5037774
  have htrace : WordTrace (prefixWord ++ tailWord_5037774) baseStart_5037774 baseEnd_5037774 := by
    simpa [prefixWord, tailWord_5037774, baseEnd_5037774] using wordTrace_append hprefix tailTrace_5037774
  have hstable : (prefixWord ++ tailWord_5037774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037774).length < 2 ^ (prefixWord ++ tailWord_5037774).sum := by decide
  have hdescent : baseEnd_5037774 < baseStart_5037774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037777 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_5037777 : Nat := 118140960795 + 5037777 * 2 ^ 59
def prefixEnd_5037777 : Nat := 4983230072969 + 3 ^ 40 * 5037777 * 2
def baseEnd_5037777 : Nat := 2586801031165441408019191

theorem tailTrace_5037777 : CollatzResearch.WordTrace tailWord_5037777 prefixEnd_5037777 2586801031165441408019191 := by
  unfold tailWord_5037777
  simp only [CollatzResearch.WordTrace]
  refine ⟨183742822270001787658055585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122495214846667858438703723 183742822270001787658055585)
  ·
    refine ⟨137807116702501340743541689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183742822270001787658055585 137807116702501340743541689)
    ·
      refine ⟨103355337526876005557656267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137807116702501340743541689 103355337526876005557656267)
      ·
        refine ⟨155033006290314008336484401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103355337526876005557656267 155033006290314008336484401)
        ·
          refine ⟨116274754717735506252363301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155033006290314008336484401 116274754717735506252363301)
          ·
            refine ⟨21801516509575407422318119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116274754717735506252363301 21801516509575407422318119)
            ·
              refine ⟨32702274764363111133477179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21801516509575407422318119 32702274764363111133477179)
              ·
                refine ⟨49053412146544666700215769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32702274764363111133477179 49053412146544666700215769)
                ·
                  refine ⟨36790059109908500025161827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49053412146544666700215769 36790059109908500025161827)
                  ·
                    refine ⟨55185088664862750037742741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36790059109908500025161827 55185088664862750037742741)
                    ·
                      refine ⟨2586801031165441408019191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55185088664862750037742741 2586801031165441408019191)
                      ·
                        rfl

theorem cell23_5037777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_5037777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037777 prefixEnd_5037777 := by exact prefixLift 5037777
  have htrace : WordTrace (prefixWord ++ tailWord_5037777) baseStart_5037777 baseEnd_5037777 := by
    simpa [prefixWord, tailWord_5037777, baseEnd_5037777] using wordTrace_append hprefix tailTrace_5037777
  have hstable : (prefixWord ++ tailWord_5037777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037777).length < 2 ^ (prefixWord ++ tailWord_5037777).sum := by decide
  have hdescent : baseEnd_5037777 < baseStart_5037777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037784 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_5037784 : Nat := 118140960795 + 5037784 * 2 ^ 59
def prefixEnd_5037784 : Nat := 4983230072969 + 3 ^ 40 * 5037784 * 2
def baseEnd_5037784 : Nat := 2586804625530022880631659

theorem tailTrace_5037784 : CollatzResearch.WordTrace tailWord_5037784 prefixEnd_5037784 2586804625530022880631659 := by
  unfold tailWord_5037784
  simp only [CollatzResearch.WordTrace]
  refine ⟨91871538790488213926780203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122495385053984285235706937 91871538790488213926780203)
  ·
    refine ⟨137807308185732320890170305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91871538790488213926780203 137807308185732320890170305)
    ·
      refine ⟨103355481139299240667627729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137807308185732320890170305 103355481139299240667627729)
      ·
        refine ⟨77516610854474430500720797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103355481139299240667627729 77516610854474430500720797)
        ·
          refine ⟨29068729070427911437770299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77516610854474430500720797 29068729070427911437770299)
          ·
            refine ⟨43603093605641867156655449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068729070427911437770299 43603093605641867156655449)
            ·
              refine ⟨32702320204231400367491587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43603093605641867156655449 32702320204231400367491587)
              ·
                refine ⟨49053480306347100551237381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32702320204231400367491587 49053480306347100551237381)
                ·
                  refine ⟨9197527557440081353357009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49053480306347100551237381 9197527557440081353357009)
                  ·
                    refine ⟨6898145668080061015017757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9197527557440081353357009 6898145668080061015017757)
                    ·
                      refine ⟨2586804625530022880631659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898145668080061015017757 2586804625530022880631659)
                      ·
                        rfl

theorem cell23_5037784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_5037784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037784 prefixEnd_5037784 := by exact prefixLift 5037784
  have htrace : WordTrace (prefixWord ++ tailWord_5037784) baseStart_5037784 baseEnd_5037784 := by
    simpa [prefixWord, tailWord_5037784, baseEnd_5037784] using wordTrace_append hprefix tailTrace_5037784
  have hstable : (prefixWord ++ tailWord_5037784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037784).length < 2 ^ (prefixWord ++ tailWord_5037784).sum := by decide
  have hdescent : baseEnd_5037784 < baseStart_5037784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037791 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 1, 4]
def baseStart_5037791 : Nat := 118140960795 + 5037791 * 2 ^ 59
def prefixEnd_5037791 : Nat := 4983230072969 + 3 ^ 40 * 5037791 * 2
def baseEnd_5037791 : Nat := 862269406631534784414709

theorem tailTrace_5037791 : CollatzResearch.WordTrace tailWord_5037791 prefixEnd_5037791 862269406631534784414709 := by
  unfold tailWord_5037791
  simp only [CollatzResearch.WordTrace]
  refine ⟨183743332891951068049065227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122495555261300712032710151 183743332891951068049065227)
  ·
    refine ⟨275614999337926602073597841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183743332891951068049065227 275614999337926602073597841)
    ·
      refine ⟨206711249503444951555198381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275614999337926602073597841 206711249503444951555198381)
      ·
        refine ⟨77516718563791856833199393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206711249503444951555198381 77516718563791856833199393)
        ·
          refine ⟨58137538922843892624899545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77516718563791856833199393 58137538922843892624899545)
          ·
            refine ⟨43603154192132919468674659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58137538922843892624899545 43603154192132919468674659)
            ·
              refine ⟨65404731288199379203011989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43603154192132919468674659 65404731288199379203011989)
              ·
                refine ⟨3065846779134345900141187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65404731288199379203011989 3065846779134345900141187)
                ·
                  refine ⟨4598770168701518850211781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065846779134345900141187 4598770168701518850211781)
                  ·
                    refine ⟨862269406631534784414709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598770168701518850211781 862269406631534784414709)
                    ·
                      rfl

theorem cell23_5037791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 4].length) (baseStart_5037791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037791 prefixEnd_5037791 := by exact prefixLift 5037791
  have htrace : WordTrace (prefixWord ++ tailWord_5037791) baseStart_5037791 baseEnd_5037791 := by
    simpa [prefixWord, tailWord_5037791, baseEnd_5037791] using wordTrace_append hprefix tailTrace_5037791
  have hstable : (prefixWord ++ tailWord_5037791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037791).length < 2 ^ (prefixWord ++ tailWord_5037791).sum := by decide
  have hdescent : baseEnd_5037791 < baseStart_5037791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037807 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_5037807 : Nat := 118140960795 + 5037807 * 2 ^ 59
def prefixEnd_5037807 : Nat := 4983230072969 + 3 ^ 40 * 5037807 * 2
def baseEnd_5037807 : Nat := 2586816435585076290644053

theorem tailTrace_5037807 : CollatzResearch.WordTrace tailWord_5037807 prefixEnd_5037807 2586816435585076290644053 := by
  unfold tailWord_5037807
  simp only [CollatzResearch.WordTrace]
  refine ⟨183743916459893102781647675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122495944306595401854431783 183743916459893102781647675)
  ·
    refine ⟨275615874689839654172471513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183743916459893102781647675 275615874689839654172471513)
    ·
      refine ⟨206711906017379740629353635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275615874689839654172471513 206711906017379740629353635)
      ·
        refine ⟨310067859026069610944030453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206711906017379740629353635 310067859026069610944030453)
        ·
          refine ⟨29068861783694026026002855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310067859026069610944030453 29068861783694026026002855)
          ·
            refine ⟨43603292675541039039004283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29068861783694026026002855 43603292675541039039004283)
            ·
              refine ⟨65404939013311558558506425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43603292675541039039004283 65404939013311558558506425)
              ·
                refine ⟨49053704259983668918879819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65404939013311558558506425 49053704259983668918879819)
                ·
                  refine ⟨73580556389975503378319729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49053704259983668918879819 73580556389975503378319729)
                  ·
                    refine ⟨55185417292481627533739797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73580556389975503378319729 55185417292481627533739797)
                    ·
                      refine ⟨2586816435585076290644053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55185417292481627533739797 2586816435585076290644053)
                      ·
                        rfl

theorem cell23_5037807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_5037807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037807 prefixEnd_5037807 := by exact prefixLift 5037807
  have htrace : WordTrace (prefixWord ++ tailWord_5037807) baseStart_5037807 baseEnd_5037807 := by
    simpa [prefixWord, tailWord_5037807, baseEnd_5037807] using wordTrace_append hprefix tailTrace_5037807
  have hstable : (prefixWord ++ tailWord_5037807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037807).length < 2 ^ (prefixWord ++ tailWord_5037807).sum := by decide
  have hdescent : baseEnd_5037807 < baseStart_5037807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037842 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5037842 : Nat := 118140960795 + 5037842 * 2 ^ 59
def prefixEnd_5037842 : Nat := 4983230072969 + 3 ^ 40 * 5037842 * 2
def baseEnd_5037842 : Nat := 862278135802661217902131

theorem tailTrace_5037842 : CollatzResearch.WordTrace tailWord_5037842 prefixEnd_5037842 862278135802661217902131 := by
  unfold tailWord_5037842
  simp only [CollatzResearch.WordTrace]
  refine ⟨45936298253691575939792945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122496795343177535839447853 45936298253691575939792945)
  ·
    refine ⟨34452223690268681954844709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45936298253691575939792945 34452223690268681954844709)
    ·
      refine ⟨6459791941925377866533383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34452223690268681954844709 6459791941925377866533383)
      ·
        refine ⟨9689687912888066799800075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459791941925377866533383 9689687912888066799800075)
        ·
          refine ⟨14534531869332100199700113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9689687912888066799800075 14534531869332100199700113)
          ·
            refine ⟨10900898901999075149775085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14534531869332100199700113 10900898901999075149775085)
            ·
              refine ⟨4087837088249653181165657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10900898901999075149775085 4087837088249653181165657)
              ·
                refine ⟨3065877816187239885874243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087837088249653181165657 3065877816187239885874243)
                ·
                  refine ⟨4598816724280859828811365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065877816187239885874243 4598816724280859828811365)
                  ·
                    refine ⟨862278135802661217902131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4598816724280859828811365 862278135802661217902131)
                    ·
                      rfl

theorem cell23_5037842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5037842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037842 prefixEnd_5037842 := by exact prefixLift 5037842
  have htrace : WordTrace (prefixWord ++ tailWord_5037842) baseStart_5037842 baseEnd_5037842 := by
    simpa [prefixWord, tailWord_5037842, baseEnd_5037842] using wordTrace_append hprefix tailTrace_5037842
  have hstable : (prefixWord ++ tailWord_5037842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037842).length < 2 ^ (prefixWord ++ tailWord_5037842).sum := by decide
  have hdescent : baseEnd_5037842 < baseStart_5037842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037848 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5037848 : Nat := 118140960795 + 5037848 * 2 ^ 59
def prefixEnd_5037848 : Nat := 4983230072969 + 3 ^ 40 * 5037848 * 2
def baseEnd_5037848 : Nat := 2586837488291910630231365

theorem tailTrace_5037848 : CollatzResearch.WordTrace tailWord_5037848 prefixEnd_5037848 2586837488291910630231365 := by
  unfold tailWord_5037848
  simp only [CollatzResearch.WordTrace]
  refine ⟨91872705926372283391945099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122496941235163044522593465 91872705926372283391945099)
  ·
    refine ⟨137809058889558425087917649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91872705926372283391945099 137809058889558425087917649)
    ·
      refine ⟨103356794167168818815938237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137809058889558425087917649 103356794167168818815938237)
      ·
        refine ⟨38758797812688307055976839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103356794167168818815938237 38758797812688307055976839)
        ·
          refine ⟨58138196719032460583965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38758797812688307055976839 58138196719032460583965259)
          ·
            refine ⟨87207295078548690875947889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58138196719032460583965259 87207295078548690875947889)
            ·
              refine ⟨65405471308911518156960917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87207295078548690875947889 65405471308911518156960917)
              ·
                refine ⟨3065881467605227413607543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65405471308911518156960917 3065881467605227413607543)
                ·
                  refine ⟨4598822201407841120411315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065881467605227413607543 4598822201407841120411315)
                  ·
                    refine ⟨6898233302111761680616973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4598822201407841120411315 6898233302111761680616973)
                    ·
                      refine ⟨2586837488291910630231365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898233302111761680616973 2586837488291910630231365)
                      ·
                        rfl

theorem cell23_5037848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5037848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037848 prefixEnd_5037848 := by exact prefixLift 5037848
  have htrace : WordTrace (prefixWord ++ tailWord_5037848) baseStart_5037848 baseEnd_5037848 := by
    simpa [prefixWord, tailWord_5037848, baseEnd_5037848] using wordTrace_append hprefix tailTrace_5037848
  have hstable : (prefixWord ++ tailWord_5037848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037848).length < 2 ^ (prefixWord ++ tailWord_5037848).sum := by decide
  have hdescent : baseEnd_5037848 < baseStart_5037848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6]
def baseStart_5037867 : Nat := 118140960795 + 5037867 * 2 ^ 59
def prefixEnd_5037867 : Nat := 4983230072969 + 3 ^ 40 * 5037867 * 2
def baseEnd_5037867 : Nat := 2586847244424346055893777

theorem tailTrace_5037867 : CollatzResearch.WordTrace tailWord_5037867 prefixEnd_5037867 2586847244424346055893777 := by
  unfold tailWord_5037867
  simp only [CollatzResearch.WordTrace]
  refine ⟨183746104839675733028831855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122497403226450488685887903 183746104839675733028831855)
  ·
    refine ⟨275619157259513599543247783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183746104839675733028831855 275619157259513599543247783)
    ·
      refine ⟨413428735889270399314871675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275619157259513599543247783 413428735889270399314871675)
      ·
        refine ⟨620143103833905598972307513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413428735889270399314871675 620143103833905598972307513)
        ·
          refine ⟨465107327875429199229230635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620143103833905598972307513 465107327875429199229230635)
          ·
            refine ⟨697660991813143798843845953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465107327875429199229230635 697660991813143798843845953)
            ·
              refine ⟨523245743859857849132884465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697660991813143798843845953 523245743859857849132884465)
              ·
                refine ⟨392434307894893386849663349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523245743859857849132884465 392434307894893386849663349)
                ·
                  refine ⟨36790716365146255017155939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392434307894893386849663349 36790716365146255017155939)
                  ·
                    refine ⟨55186074547719382525733909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36790716365146255017155939 55186074547719382525733909)
                    ·
                      refine ⟨2586847244424346055893777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55186074547719382525733909 2586847244424346055893777)
                      ·
                        rfl

theorem cell23_5037867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_5037867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037867 prefixEnd_5037867 := by exact prefixLift 5037867
  have htrace : WordTrace (prefixWord ++ tailWord_5037867) baseStart_5037867 baseEnd_5037867 := by
    simpa [prefixWord, tailWord_5037867, baseEnd_5037867] using wordTrace_append hprefix tailTrace_5037867
  have hstable : (prefixWord ++ tailWord_5037867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037867).length < 2 ^ (prefixWord ++ tailWord_5037867).sum := by decide
  have hdescent : baseEnd_5037867 < baseStart_5037867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037884 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_5037884 : Nat := 118140960795 + 5037884 * 2 ^ 59
def prefixEnd_5037884 : Nat := 4983230072969 + 3 ^ 40 * 5037884 * 2
def baseEnd_5037884 : Nat := 2586855973595472489381199

theorem tailTrace_5037884 : CollatzResearch.WordTrace tailWord_5037884 prefixEnd_5037884 2586855973595472489381199 := by
  unfold tailWord_5037884
  simp only [CollatzResearch.WordTrace]
  refine ⟨91873362440307072466100353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122497816587076096621467137 91873362440307072466100353)
  ·
    refine ⟨68905021830230304349575265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91873362440307072466100353 68905021830230304349575265)
    ·
      refine ⟨51678766372672728262181449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68905021830230304349575265 51678766372672728262181449)
      ·
        refine ⟨38759074779504546196636087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51678766372672728262181449 38759074779504546196636087)
        ·
          refine ⟨58138612169256819294954131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38759074779504546196636087 58138612169256819294954131)
          ·
            refine ⟨87207918253885228942431197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58138612169256819294954131 87207918253885228942431197)
            ·
              refine ⟨32702969345206960853411699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87207918253885228942431197 32702969345206960853411699)
              ·
                refine ⟨49054454017810441280117549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32702969345206960853411699 49054454017810441280117549)
                ·
                  refine ⟨18395420256678915480044081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49054454017810441280117549 18395420256678915480044081)
                  ·
                    refine ⟨13796565192509186610033061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18395420256678915480044081 13796565192509186610033061)
                    ·
                      refine ⟨2586855973595472489381199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13796565192509186610033061 2586855973595472489381199)
                      ·
                        rfl

theorem cell23_5037884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_5037884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037884 prefixEnd_5037884 := by exact prefixLift 5037884
  have htrace : WordTrace (prefixWord ++ tailWord_5037884) baseStart_5037884 baseEnd_5037884 := by
    simpa [prefixWord, tailWord_5037884, baseEnd_5037884] using wordTrace_append hprefix tailTrace_5037884
  have hstable : (prefixWord ++ tailWord_5037884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037884).length < 2 ^ (prefixWord ++ tailWord_5037884).sum := by decide
  have hdescent : baseEnd_5037884 < baseStart_5037884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037891 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 5]
def baseStart_5037891 : Nat := 118140960795 + 5037891 * 2 ^ 59
def prefixEnd_5037891 : Nat := 4983230072969 + 3 ^ 40 * 5037891 * 2
def baseEnd_5037891 : Nat := 2586859567960053961993667

theorem tailTrace_5037891 : CollatzResearch.WordTrace tailWord_5037891 prefixEnd_5037891 2586859567960053961993667 := by
  unfold tailWord_5037891
  simp only [CollatzResearch.WordTrace]
  refine ⟨183746980191588785127705527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122497986794392523418470351 183746980191588785127705527)
  ·
    refine ⟨275620470287383177691558291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183746980191588785127705527 275620470287383177691558291)
    ·
      refine ⟨413430705431074766537337437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275620470287383177691558291 413430705431074766537337437)
      ·
        refine ⟨155036514536653037451501539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413430705431074766537337437 155036514536653037451501539)
        ·
          refine ⟨232554771804979556177252309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155036514536653037451501539 232554771804979556177252309)
          ·
            refine ⟨5450502464179208347904351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 232554771804979556177252309 5450502464179208347904351)
            ·
              refine ⟨8175753696268812521856527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450502464179208347904351 8175753696268812521856527)
              ·
                refine ⟨12263630544403218782784791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175753696268812521856527 12263630544403218782784791)
                ·
                  refine ⟨18395445816604828174177187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12263630544403218782784791 18395445816604828174177187)
                  ·
                    refine ⟨27593168724907242261265781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18395445816604828174177187 27593168724907242261265781)
                    ·
                      refine ⟨2586859567960053961993667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27593168724907242261265781 2586859567960053961993667)
                      ·
                        rfl

theorem cell23_5037891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_5037891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037891 prefixEnd_5037891 := by exact prefixLift 5037891
  have htrace : WordTrace (prefixWord ++ tailWord_5037891) baseStart_5037891 baseEnd_5037891 := by
    simpa [prefixWord, tailWord_5037891, baseEnd_5037891] using wordTrace_append hprefix tailTrace_5037891
  have hstable : (prefixWord ++ tailWord_5037891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037891).length < 2 ^ (prefixWord ++ tailWord_5037891).sum := by decide
  have hdescent : baseEnd_5037891 < baseStart_5037891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037904 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_5037904 : Nat := 118140960795 + 5037904 * 2 ^ 59
def prefixEnd_5037904 : Nat := 4983230072969 + 3 ^ 40 * 5037904 * 2
def baseEnd_5037904 : Nat := 2586866243208562411131107

theorem tailTrace_5037904 : CollatzResearch.WordTrace tailWord_5037904 prefixEnd_5037904 2586866243208562411131107 := by
  unfold tailWord_5037904
  simp only [CollatzResearch.WordTrace]
  refine ⟨91873727170270844173964383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122498302893694458898619177 91873727170270844173964383)
  ·
    refine ⟨137810590755406266260946575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91873727170270844173964383 137810590755406266260946575)
    ·
      refine ⟨206715886133109399391419863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137810590755406266260946575 206715886133109399391419863)
      ·
        refine ⟨310073829199664099087129795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206715886133109399391419863 310073829199664099087129795)
        ·
          refine ⟨465110743799496148630694693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310073829199664099087129795 465110743799496148630694693)
          ·
            refine ⟨87208264462405527868255255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 465110743799496148630694693 87208264462405527868255255)
            ·
              refine ⟨130812396693608291802382883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87208264462405527868255255 130812396693608291802382883)
              ·
                refine ⟨196218595040412437703574325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130812396693608291802382883 196218595040412437703574325)
                ·
                  refine ⟨18395493285038666034710093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196218595040412437703574325 18395493285038666034710093)
                  ·
                    refine ⟨6898309981889499763016285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18395493285038666034710093 6898309981889499763016285)
                    ·
                      refine ⟨2586866243208562411131107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898309981889499763016285 2586866243208562411131107)
                      ·
                        rfl

theorem cell23_5037904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_5037904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037904 prefixEnd_5037904 := by exact prefixLift 5037904
  have htrace : WordTrace (prefixWord ++ tailWord_5037904) baseStart_5037904 baseEnd_5037904 := by
    simpa [prefixWord, tailWord_5037904, baseEnd_5037904] using wordTrace_append hprefix tailTrace_5037904
  have hstable : (prefixWord ++ tailWord_5037904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037904).length < 2 ^ (prefixWord ++ tailWord_5037904).sum := by decide
  have hdescent : baseEnd_5037904 < baseStart_5037904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037911 : List Nat := [1, 1, 3, 2, 5, 2, 1, 8]
def baseStart_5037911 : Nat := 118140960795 + 5037911 * 2 ^ 59
def prefixEnd_5037911 : Nat := 4983230072969 + 3 ^ 40 * 5037911 * 2
def baseEnd_5037911 : Nat := 95809993984190514212725

theorem tailTrace_5037911 : CollatzResearch.WordTrace tailWord_5037911 prefixEnd_5037911 95809993984190514212725 := by
  unfold tailWord_5037911
  simp only [CollatzResearch.WordTrace]
  refine ⟨183747709651516328543433587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122498473101010885695622391 183747709651516328543433587)
  ·
    refine ⟨275621564477274492815150381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183747709651516328543433587 275621564477274492815150381)
    ·
      refine ⟨103358086678977934805681393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275621564477274492815150381 103358086678977934805681393)
      ·
        refine ⟨77518565009233451104261045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103358086678977934805681393 77518565009233451104261045)
        ·
          refine ⟨7267365469615636041024473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77518565009233451104261045 7267365469615636041024473)
          ·
            refine ⟨5450524102211727030768355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7267365469615636041024473 5450524102211727030768355)
            ·
              refine ⟨8175786153317590546152533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450524102211727030768355 8175786153317590546152533)
              ·
                refine ⟨95809993984190514212725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8175786153317590546152533 95809993984190514212725)
                ·
                  rfl

theorem cell23_5037911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 8].length) (baseStart_5037911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037911 prefixEnd_5037911 := by exact prefixLift 5037911
  have htrace : WordTrace (prefixWord ++ tailWord_5037911) baseStart_5037911 baseEnd_5037911 := by
    simpa [prefixWord, tailWord_5037911, baseEnd_5037911] using wordTrace_append hprefix tailTrace_5037911
  have hstable : (prefixWord ++ tailWord_5037911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037911).length < 2 ^ (prefixWord ++ tailWord_5037911).sum := by decide
  have hdescent : baseEnd_5037911 < baseStart_5037911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037921 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_5037921 : Nat := 118140960795 + 5037921 * 2 ^ 59
def prefixEnd_5037921 : Nat := 4983230072969 + 3 ^ 40 * 5037921 * 2
def baseEnd_5037921 : Nat := 2586874972379688844618529

theorem tailTrace_5037921 : CollatzResearch.WordTrace tailWord_5037921 prefixEnd_5037921 2586874972379688844618529 := by
  unfold tailWord_5037921
  simp only [CollatzResearch.WordTrace]
  refine ⟨183748074381480100251297617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122498716254320066834198411 183748074381480100251297617)
  ·
    refine ⟨137811055786110075188473213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183748074381480100251297617 137811055786110075188473213)
    ·
      refine ⟨51679145919791278195677455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137811055786110075188473213 51679145919791278195677455)
      ·
        refine ⟨77518718879686917293516183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51679145919791278195677455 77518718879686917293516183)
        ·
          refine ⟨116278078319530375940274275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77518718879686917293516183 116278078319530375940274275)
          ·
            refine ⟨174417117479295563910411413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116278078319530375940274275 174417117479295563910411413)
            ·
              refine ⟨8175802381841979558300535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174417117479295563910411413 8175802381841979558300535)
              ·
                refine ⟨12263703572762969337450803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8175802381841979558300535 12263703572762969337450803)
                ·
                  refine ⟨18395555359144454006176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12263703572762969337450803 18395555359144454006176205)
                  ·
                    refine ⟨6898333259679170252316077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18395555359144454006176205 6898333259679170252316077)
                    ·
                      refine ⟨2586874972379688844618529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898333259679170252316077 2586874972379688844618529)
                      ·
                        rfl

theorem cell23_5037921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_5037921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037921 prefixEnd_5037921 := by exact prefixLift 5037921
  have htrace : WordTrace (prefixWord ++ tailWord_5037921) baseStart_5037921 baseEnd_5037921 := by
    simpa [prefixWord, tailWord_5037921, baseEnd_5037921] using wordTrace_append hprefix tailTrace_5037921
  have hstable : (prefixWord ++ tailWord_5037921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037921).length < 2 ^ (prefixWord ++ tailWord_5037921).sum := by decide
  have hdescent : baseEnd_5037921 < baseStart_5037921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037955 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 3]
def baseStart_5037955 : Nat := 118140960795 + 5037955 * 2 ^ 59
def prefixEnd_5037955 : Nat := 4983230072969 + 3 ^ 40 * 5037955 * 2
def baseEnd_5037955 : Nat := 2586892430721941711593373

theorem tailTrace_5037955 : CollatzResearch.WordTrace tailWord_5037955 prefixEnd_5037955 2586892430721941711593373 := by
  unfold tailWord_5037955
  simp only [CollatzResearch.WordTrace]
  refine ⟨183749314463356924058035319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122499542975571282705356879 183749314463356924058035319)
  ·
    refine ⟨275623971695035386087052979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183749314463356924058035319 275623971695035386087052979)
    ·
      refine ⟨413435957542553079130579469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275623971695035386087052979 413435957542553079130579469)
      ·
        refine ⟨155038484078457404673967301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413435957542553079130579469 155038484078457404673967301)
        ·
          refine ⟨29069715764710763376368869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155038484078457404673967301 29069715764710763376368869)
          ·
            refine ⟨5450571705883268133069163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29069715764710763376368869 5450571705883268133069163)
            ·
              refine ⟨8175857558824902199603745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450571705883268133069163 8175857558824902199603745)
              ·
                refine ⟨6131893169118676649702809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8175857558824902199603745 6131893169118676649702809)
                ·
                  refine ⟨4598919876839007487277107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131893169118676649702809 4598919876839007487277107)
                  ·
                    refine ⟨6898379815258511230915661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4598919876839007487277107 6898379815258511230915661)
                    ·
                      refine ⟨2586892430721941711593373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898379815258511230915661 2586892430721941711593373)
                      ·
                        rfl

theorem cell23_5037955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_5037955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037955 prefixEnd_5037955 := by exact prefixLift 5037955
  have htrace : WordTrace (prefixWord ++ tailWord_5037955) baseStart_5037955 baseEnd_5037955 := by
    simpa [prefixWord, tailWord_5037955, baseEnd_5037955] using wordTrace_append hprefix tailTrace_5037955
  have hstable : (prefixWord ++ tailWord_5037955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037955).length < 2 ^ (prefixWord ++ tailWord_5037955).sum := by decide
  have hdescent : baseEnd_5037955 < baseStart_5037955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037964 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_5037964 : Nat := 118140960795 + 5037964 * 2 ^ 59
def prefixEnd_5037964 : Nat := 4983230072969 + 3 ^ 40 * 5037964 * 2
def baseEnd_5037964 : Nat := 2586897052047832176380831

theorem tailTrace_5037964 : CollatzResearch.WordTrace tailWord_5037964 prefixEnd_5037964 2586897052047832176380831 := by
  unfold tailWord_5037964
  simp only [CollatzResearch.WordTrace]
  refine ⟨91874821360162159297556473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122499761813549545730075297 91874821360162159297556473)
  ·
    refine ⟨68906116020121619473167355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91874821360162159297556473 68906116020121619473167355)
    ·
      refine ⟨103359174030182429209751033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68906116020121619473167355 103359174030182429209751033)
      ·
        refine ⟨77519380522636821907313275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103359174030182429209751033 77519380522636821907313275)
        ·
          refine ⟨116279070783955232860969913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77519380522636821907313275 116279070783955232860969913)
          ·
            refine ⟨87209303087966424645727435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116279070783955232860969913 87209303087966424645727435)
            ·
              refine ⟨130813954631949636968591153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87209303087966424645727435 130813954631949636968591153)
              ·
                refine ⟨98110465973962227726443365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130813954631949636968591153 98110465973962227726443365)
                ·
                  refine ⟨18395712370117917698708131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98110465973962227726443365 18395712370117917698708131)
                  ·
                    refine ⟨27593568555176876548062197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18395712370117917698708131 27593568555176876548062197)
                    ·
                      refine ⟨2586897052047832176380831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27593568555176876548062197 2586897052047832176380831)
                      ·
                        rfl

theorem cell23_5037964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_5037964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037964 prefixEnd_5037964 := by exact prefixLift 5037964
  have htrace : WordTrace (prefixWord ++ tailWord_5037964) baseStart_5037964 baseEnd_5037964 := by
    simpa [prefixWord, tailWord_5037964, baseEnd_5037964] using wordTrace_append hprefix tailTrace_5037964
  have hstable : (prefixWord ++ tailWord_5037964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037964).length < 2 ^ (prefixWord ++ tailWord_5037964).sum := by decide
  have hdescent : baseEnd_5037964 < baseStart_5037964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5037972 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5037972 : Nat := 118140960795 + 5037972 * 2 ^ 59
def prefixEnd_5037972 : Nat := 4983230072969 + 3 ^ 40 * 5037972 * 2
def baseEnd_5037972 : Nat := 2586901159893068145080795

theorem tailTrace_5037972 : CollatzResearch.WordTrace tailWord_5037972 prefixEnd_5037972 2586901159893068145080795 := by
  unfold tailWord_5037972
  simp only [CollatzResearch.WordTrace]
  refine ⟨91874967252147667980702085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122499956336196890640936113 91874967252147667980702085)
  ·
    refine ⟨17226556359777687746381641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91874967252147667980702085 17226556359777687746381641)
    ·
      refine ⟨12919917269833265809786231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17226556359777687746381641 12919917269833265809786231)
      ·
        refine ⟨19379875904749898714679347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12919917269833265809786231 19379875904749898714679347)
        ·
          refine ⟨29069813857124848072019021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19379875904749898714679347 29069813857124848072019021)
          ·
            refine ⟨10901180196421818027007133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29069813857124848072019021 10901180196421818027007133)
            ·
              refine ⟨4087942573658181760127675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10901180196421818027007133 4087942573658181760127675)
              ·
                refine ⟨6131913860487272640191513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4087942573658181760127675 6131913860487272640191513)
                ·
                  refine ⟨4598935395365454480143635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6131913860487272640191513 4598935395365454480143635)
                  ·
                    refine ⟨6898403093048181720215453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4598935395365454480143635 6898403093048181720215453)
                    ·
                      refine ⟨2586901159893068145080795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898403093048181720215453 2586901159893068145080795)
                      ·
                        rfl

theorem cell23_5037972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5037972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5037972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5037972 prefixEnd_5037972 := by exact prefixLift 5037972
  have htrace : WordTrace (prefixWord ++ tailWord_5037972) baseStart_5037972 baseEnd_5037972 := by
    simpa [prefixWord, tailWord_5037972, baseEnd_5037972] using wordTrace_append hprefix tailTrace_5037972
  have hstable : (prefixWord ++ tailWord_5037972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5037972).length < 2 ^ (prefixWord ++ tailWord_5037972).sum := by decide
  have hdescent : baseEnd_5037972 < baseStart_5037972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5037972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038091 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 6]
def baseStart_5038091 : Nat := 118140960795 + 5038091 * 2 ^ 59
def prefixEnd_5038091 : Nat := 4983230072969 + 3 ^ 40 * 5038091 * 2
def baseEnd_5038091 : Nat := 287440251565661464388083

theorem tailTrace_5038091 : CollatzResearch.WordTrace tailWord_5038091 prefixEnd_5038091 287440251565661464388083 := by
  unfold tailWord_5038091
  simp only [CollatzResearch.WordTrace]
  refine ⟨183754274790864219284986127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122502849860576146189990751 183754274790864219284986127)
  ·
    refine ⟨275631412186296328927479191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183754274790864219284986127 275631412186296328927479191)
    ·
      refine ⟨413447118279444493391218787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275631412186296328927479191 413447118279444493391218787)
      ·
        refine ⟨620170677419166740086828181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413447118279444493391218787 620170677419166740086828181)
        ·
          refine ⟨29070500504023440941570071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 620170677419166740086828181 29070500504023440941570071)
          ·
            refine ⟨43605750756035161412355107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29070500504023440941570071 43605750756035161412355107)
            ·
              refine ⟨65408626134052742118532661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43605750756035161412355107 65408626134052742118532661)
              ·
                refine ⟨6132058700067444573612437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65408626134052742118532661 6132058700067444573612437)
                ·
                  refine ⟨287440251565661464388083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6132058700067444573612437 287440251565661464388083)
                  ·
                    rfl

theorem cell23_5038091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 6].length) (baseStart_5038091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038091 prefixEnd_5038091 := by exact prefixLift 5038091
  have htrace : WordTrace (prefixWord ++ tailWord_5038091) baseStart_5038091 baseEnd_5038091 := by
    simpa [prefixWord, tailWord_5038091, baseEnd_5038091] using wordTrace_append hprefix tailTrace_5038091
  have hstable : (prefixWord ++ tailWord_5038091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038091).length < 2 ^ (prefixWord ++ tailWord_5038091).sum := by decide
  have hdescent : baseEnd_5038091 < baseStart_5038091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038142 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_5038142 : Nat := 118140960795 + 5038142 * 2 ^ 59
def prefixEnd_5038142 : Nat := 4983230072969 + 3 ^ 40 * 5038142 * 2
def baseEnd_5038142 : Nat := 287443161289370275550557

theorem tailTrace_5038142 : CollatzResearch.WordTrace tailWord_5038142 prefixEnd_5038142 287443161289370275550557 := by
  unfold tailWord_5038142
  simp only [CollatzResearch.WordTrace]
  refine ⟨22969516864209931874386585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122504089942452969996728453 22969516864209931874386585)
  ·
    refine ⟨17227137648157448905789939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22969516864209931874386585 17227137648157448905789939)
    ·
      refine ⟨25840706472236173358684909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17227137648157448905789939 25840706472236173358684909)
      ·
        refine ⟨9690264927088565009506841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25840706472236173358684909 9690264927088565009506841)
        ·
          refine ⟨7267698695316423757130131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9690264927088565009506841 7267698695316423757130131)
          ·
            refine ⟨10901548042974635635695197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267698695316423757130131 10901548042974635635695197)
            ·
              refine ⟨4088080516115488363385699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10901548042974635635695197 4088080516115488363385699)
              ·
                refine ⟨6132120774173232545078549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088080516115488363385699 6132120774173232545078549)
                ·
                  refine ⟨287443161289370275550557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6132120774173232545078549 287443161289370275550557)
                  ·
                    rfl

theorem cell23_5038142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_5038142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038142 prefixEnd_5038142 := by exact prefixLift 5038142
  have htrace : WordTrace (prefixWord ++ tailWord_5038142) baseStart_5038142 baseEnd_5038142 := by
    simpa [prefixWord, tailWord_5038142, baseEnd_5038142] using wordTrace_append hprefix tailTrace_5038142
  have hstable : (prefixWord ++ tailWord_5038142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038142).length < 2 ^ (prefixWord ++ tailWord_5038142).sum := by decide
  have hdescent : baseEnd_5038142 < baseStart_5038142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038145 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5038145 : Nat := 118140960795 + 5038145 * 2 ^ 59
def prefixEnd_5038145 : Nat := 4983230072969 + 3 ^ 40 * 5038145 * 2
def baseEnd_5038145 : Nat := 2586989992046295968217499

theorem tailTrace_5038145 : CollatzResearch.WordTrace tailWord_5038145 prefixEnd_5038145 2586989992046295968217499 := by
  unfold tailWord_5038145
  simp only [CollatzResearch.WordTrace]
  refine ⟨183756244332668586507451889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122504162888445724338301259 183756244332668586507451889)
  ·
    refine ⟨137817183249501439880588917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183756244332668586507451889 137817183249501439880588917)
    ·
      refine ⟨12920360929640759988805211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137817183249501439880588917 12920360929640759988805211)
      ·
        refine ⟨19380541394461139983207817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12920360929640759988805211 19380541394461139983207817)
        ·
          refine ⟨14535406045845854987405863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19380541394461139983207817 14535406045845854987405863)
          ·
            refine ⟨21803109068768782481108795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14535406045845854987405863 21803109068768782481108795)
            ·
              refine ⟨32704663603153173721663193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21803109068768782481108795 32704663603153173721663193)
              ·
                refine ⟨24528497702364880291247395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32704663603153173721663193 24528497702364880291247395)
                ·
                  refine ⟨36792746553547320436871093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24528497702364880291247395 36792746553547320436871093)
                  ·
                    refine ⟨3449319989395061290956665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36792746553547320436871093 3449319989395061290956665)
                    ·
                      refine ⟨2586989992046295968217499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449319989395061290956665 2586989992046295968217499)
                      ·
                        rfl

theorem cell23_5038145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5038145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038145 prefixEnd_5038145 := by exact prefixLift 5038145
  have htrace : WordTrace (prefixWord ++ tailWord_5038145) baseStart_5038145 baseEnd_5038145 := by
    simpa [prefixWord, tailWord_5038145, baseEnd_5038145] using wordTrace_append hprefix tailTrace_5038145
  have hstable : (prefixWord ++ tailWord_5038145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038145).length < 2 ^ (prefixWord ++ tailWord_5038145).sum := by decide
  have hdescent : baseEnd_5038145 < baseStart_5038145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038161 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_5038161 : Nat := 118140960795 + 5038161 * 2 ^ 59
def prefixEnd_5038161 : Nat := 4983230072969 + 3 ^ 40 * 5038161 * 2
def baseEnd_5038161 : Nat := 2586998207736767905617425

theorem tailTrace_5038161 : CollatzResearch.WordTrace tailWord_5038161 prefixEnd_5038161 2586998207736767905617425 := by
  unfold tailWord_5038161
  simp only [CollatzResearch.WordTrace]
  refine ⟨183756827900610621240034337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122504551933740414160022891 183756827900610621240034337)
  ·
    refine ⟨137817620925457965930025753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183756827900610621240034337 137817620925457965930025753)
    ·
      refine ⟨103363215694093474447519315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137817620925457965930025753 103363215694093474447519315)
      ·
        refine ⟨155044823541140211671278973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103363215694093474447519315 155044823541140211671278973)
        ·
          refine ⟨58141808827927579376729615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155044823541140211671278973 58141808827927579376729615)
          ·
            refine ⟨87212713241891369065094423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58141808827927579376729615 87212713241891369065094423)
            ·
              refine ⟨130819069862837053597641635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87212713241891369065094423 130819069862837053597641635)
              ·
                refine ⟨196228604794255580396462453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130819069862837053597641635 196228604794255580396462453)
                ·
                  refine ⟨18396431699461460662168355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196228604794255580396462453 18396431699461460662168355)
                  ·
                    refine ⟨27594647549192190993252533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18396431699461460662168355 27594647549192190993252533)
                    ·
                      refine ⟨2586998207736767905617425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27594647549192190993252533 2586998207736767905617425)
                      ·
                        rfl

theorem cell23_5038161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_5038161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038161 prefixEnd_5038161 := by exact prefixLift 5038161
  have htrace : WordTrace (prefixWord ++ tailWord_5038161) baseStart_5038161 baseEnd_5038161 := by
    simpa [prefixWord, tailWord_5038161, baseEnd_5038161] using wordTrace_append hprefix tailTrace_5038161
  have hstable : (prefixWord ++ tailWord_5038161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038161).length < 2 ^ (prefixWord ++ tailWord_5038161).sum := by decide
  have hdescent : baseEnd_5038161 < baseStart_5038161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038168 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_5038168 : Nat := 118140960795 + 5038168 * 2 ^ 59
def prefixEnd_5038168 : Nat := 4983230072969 + 3 ^ 40 * 5038168 * 2
def baseEnd_5038168 : Nat := 862333934033783126076631

theorem tailTrace_5038168 : CollatzResearch.WordTrace tailWord_5038168 prefixEnd_5038168 862333934033783126076631 := by
  unfold tailWord_5038168
  simp only [CollatzResearch.WordTrace]
  refine ⟨91878541605792630717769579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122504722141056840957026105 91878541605792630717769579)
  ·
    refine ⟨137817812408688946076654369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91878541605792630717769579 137817812408688946076654369)
    ·
      refine ⟨103363359306516709557490777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137817812408688946076654369 103363359306516709557490777)
      ·
        refine ⟨77522519479887532168118083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103363359306516709557490777 77522519479887532168118083)
        ·
          refine ⟨116283779219831298252177125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77522519479887532168118083 116283779219831298252177125)
          ·
            refine ⟨21803208603718368422283211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116283779219831298252177125 21803208603718368422283211)
            ·
              refine ⟨32704812905577552633424817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21803208603718368422283211 32704812905577552633424817)
              ·
                refine ⟨24528609679183164475068613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32704812905577552633424817 24528609679183164475068613)
                ·
                  refine ⟨4599114314846843339075365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24528609679183164475068613 4599114314846843339075365)
                  ·
                    refine ⟨862333934033783126076631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599114314846843339075365 862333934033783126076631)
                    ·
                      rfl

theorem cell23_5038168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_5038168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038168 prefixEnd_5038168 := by exact prefixLift 5038168
  have htrace : WordTrace (prefixWord ++ tailWord_5038168) baseStart_5038168 baseEnd_5038168 := by
    simpa [prefixWord, tailWord_5038168, baseEnd_5038168] using wordTrace_append hprefix tailTrace_5038168
  have hstable : (prefixWord ++ tailWord_5038168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038168).length < 2 ^ (prefixWord ++ tailWord_5038168).sum := by decide
  have hdescent : baseEnd_5038168 < baseStart_5038168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038181 : List Nat := [1, 3, 1, 3, 2, 2, 11]
def baseStart_5038181 : Nat := 118140960795 + 5038181 * 2 ^ 59
def prefixEnd_5038181 : Nat := 4983230072969 + 3 ^ 40 * 5038181 * 2
def baseEnd_5038181 : Nat := 31938376263578491695893

theorem tailTrace_5038181 : CollatzResearch.WordTrace tailWord_5038181 prefixEnd_5038181 31938376263578491695893 := by
  unfold tailWord_5038181
  simp only [CollatzResearch.WordTrace]
  refine ⟨183757557360538164655762397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122505038240358776437174931 183757557360538164655762397)
  ·
    refine ⟨68909084010201811745910899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183757557360538164655762397 68909084010201811745910899)
    ·
      refine ⟨103363626015302717618866349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68909084010201811745910899 103363626015302717618866349)
      ·
        refine ⟨38761359755738519107074881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103363626015302717618866349 38761359755738519107074881)
        ·
          refine ⟨29071019816803889330306161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38761359755738519107074881 29071019816803889330306161)
          ·
            refine ⟨21803264862602916997729621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29071019816803889330306161 21803264862602916997729621)
            ·
              refine ⟨31938376263578491695893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21803264862602916997729621 31938376263578491695893)
              ·
                rfl

theorem cell23_5038181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 11].length) (baseStart_5038181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038181 prefixEnd_5038181 := by exact prefixLift 5038181
  have htrace : WordTrace (prefixWord ++ tailWord_5038181) baseStart_5038181 baseEnd_5038181 := by
    simpa [prefixWord, tailWord_5038181, baseEnd_5038181] using wordTrace_append hprefix tailTrace_5038181
  have hstable : (prefixWord ++ tailWord_5038181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038181).length < 2 ^ (prefixWord ++ tailWord_5038181).sum := by decide
  have hdescent : baseEnd_5038181 < baseStart_5038181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038186 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5038186 : Nat := 118140960795 + 5038186 * 2 ^ 59
def prefixEnd_5038186 : Nat := 4983230072969 + 3 ^ 40 * 5038186 * 2
def baseEnd_5038186 : Nat := 2587011044753130307804811

theorem tailTrace_5038186 : CollatzResearch.WordTrace tailWord_5038186 prefixEnd_5038186 2587011044753130307804811 := by
  unfold tailWord_5038186
  simp only [CollatzResearch.WordTrace]
  refine ⟨45939434931380012627423603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122505159817013367006462941 45939434931380012627423603)
  ·
    refine ⟨68909152397070018941135405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45939434931380012627423603 68909152397070018941135405)
    ·
      refine ⟨25840932148901257102925777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68909152397070018941135405 25840932148901257102925777)
      ·
        refine ⟨19380699111675942827194333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25840932148901257102925777 19380699111675942827194333)
        ·
          refine ⟨7267762166878478560197875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19380699111675942827194333 7267762166878478560197875)
          ·
            refine ⟨10901643250317717840296813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7267762166878478560197875 10901643250317717840296813)
            ·
              refine ⟨4088116218869144190111305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10901643250317717840296813 4088116218869144190111305)
              ·
                refine ⟨3066087164151858142583479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088116218869144190111305 3066087164151858142583479)
                ·
                  refine ⟨4599130746227787213875219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066087164151858142583479 4599130746227787213875219)
                  ·
                    refine ⟨6898696119341680820812829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599130746227787213875219 6898696119341680820812829)
                    ·
                      refine ⟨2587011044753130307804811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898696119341680820812829 2587011044753130307804811)
                      ·
                        rfl

theorem cell23_5038186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5038186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038186 prefixEnd_5038186 := by exact prefixLift 5038186
  have htrace : WordTrace (prefixWord ++ tailWord_5038186) baseStart_5038186 baseEnd_5038186 := by
    simpa [prefixWord, tailWord_5038186, baseEnd_5038186] using wordTrace_append hprefix tailTrace_5038186
  have hstable : (prefixWord ++ tailWord_5038186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038186).length < 2 ^ (prefixWord ++ tailWord_5038186).sum := by decide
  have hdescent : baseEnd_5038186 < baseStart_5038186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038192 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2]
def baseStart_5038192 : Nat := 118140960795 + 5038192 * 2 ^ 59
def prefixEnd_5038192 : Nat := 4983230072969 + 3 ^ 40 * 5038192 * 2
def baseEnd_5038192 : Nat := 2587014125637057284329783

theorem tailTrace_5038192 : CollatzResearch.WordTrace tailWord_5038192 prefixEnd_5038192 2587014125637057284329783 := by
  unfold tailWord_5038192
  simp only [CollatzResearch.WordTrace]
  refine ⟨91878979281749156767206415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122505305708998875689608553 91878979281749156767206415)
  ·
    refine ⟨137818468922623735150809623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91878979281749156767206415 137818468922623735150809623)
    ·
      refine ⟨206727703383935602726214435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137818468922623735150809623 206727703383935602726214435)
      ·
        refine ⟨310091555075903404089321653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206727703383935602726214435 310091555075903404089321653)
        ·
          refine ⟨29071083288365944133373905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310091555075903404089321653 29071083288365944133373905)
          ·
            refine ⟨21803312466274458100030429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29071083288365944133373905 21803312466274458100030429)
            ·
              refine ⟨8176242174852921787511411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21803312466274458100030429 8176242174852921787511411)
              ·
                refine ⟨12264363262279382681267117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8176242174852921787511411 12264363262279382681267117)
                ·
                  refine ⟨4599136223354768505475169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12264363262279382681267117 4599136223354768505475169)
                  ·
                    refine ⟨3449352167516076379106377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599136223354768505475169 3449352167516076379106377)
                    ·
                      refine ⟨2587014125637057284329783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449352167516076379106377 2587014125637057284329783)
                      ·
                        rfl

theorem cell23_5038192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2].length) (baseStart_5038192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038192 prefixEnd_5038192 := by exact prefixLift 5038192
  have htrace : WordTrace (prefixWord ++ tailWord_5038192) baseStart_5038192 baseEnd_5038192 := by
    simpa [prefixWord, tailWord_5038192, baseEnd_5038192] using wordTrace_append hprefix tailTrace_5038192
  have hstable : (prefixWord ++ tailWord_5038192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038192).length < 2 ^ (prefixWord ++ tailWord_5038192).sum := by decide
  have hdescent : baseEnd_5038192 < baseStart_5038192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038198 : List Nat := [5, 1, 1, 2, 1, 2, 1, 10]
def baseStart_5038198 : Nat := 118140960795 + 5038198 * 2 ^ 59
def prefixEnd_5038198 : Nat := 4983230072969 + 3 ^ 40 * 5038198 * 2
def baseEnd_5038198 : Nat := 95815452093369787439065

theorem tailTrace_5038198 : CollatzResearch.WordTrace tailWord_5038198 prefixEnd_5038198 95815452093369787439065 := by
  unfold tailWord_5038198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11484886087592286034945703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122505451600984384372754165 11484886087592286034945703)
  ·
    refine ⟨17227329131388429052418555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11484886087592286034945703 17227329131388429052418555)
    ·
      refine ⟨25840993697082643578627833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17227329131388429052418555 25840993697082643578627833)
      ·
        refine ⟨19380745272811982683970875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25840993697082643578627833 19380745272811982683970875)
        ·
          refine ⟨29071117909217974025956313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19380745272811982683970875 29071117909217974025956313)
          ·
            refine ⟨21803338431913480519467235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29071117909217974025956313 21803338431913480519467235)
            ·
              refine ⟨32705007647870220779200853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21803338431913480519467235 32705007647870220779200853)
              ·
                refine ⟨95815452093369787439065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32705007647870220779200853 95815452093369787439065)
                ·
                  rfl

theorem cell23_5038198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_5038198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038198 prefixEnd_5038198 := by exact prefixLift 5038198
  have htrace : WordTrace (prefixWord ++ tailWord_5038198) baseStart_5038198 baseEnd_5038198 := by
    simpa [prefixWord, tailWord_5038198, baseEnd_5038198] using wordTrace_append hprefix tailTrace_5038198
  have hstable : (prefixWord ++ tailWord_5038198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038198).length < 2 ^ (prefixWord ++ tailWord_5038198).sum := by decide
  have hdescent : baseEnd_5038198 < baseStart_5038198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038208 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_5038208 : Nat := 118140960795 + 5038208 * 2 ^ 59
def prefixEnd_5038208 : Nat := 4983230072969 + 3 ^ 40 * 5038208 * 2
def baseEnd_5038208 : Nat := 2587022341327529221729709

theorem tailTrace_5038208 : CollatzResearch.WordTrace tailWord_5038208 prefixEnd_5038208 2587022341327529221729709 := by
  unfold tailWord_5038208
  simp only [CollatzResearch.WordTrace]
  refine ⟨91879271065720174133497639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122505694754293565511330185 91879271065720174133497639)
  ·
    refine ⟨137818906598580261200246459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91879271065720174133497639 137818906598580261200246459)
    ·
      refine ⟨206728359897870391800369689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137818906598580261200246459 206728359897870391800369689)
      ·
        refine ⟨155046269923402793850277267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206728359897870391800369689 155046269923402793850277267)
        ·
          refine ⟨232569404885104190775415901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155046269923402793850277267 232569404885104190775415901)
          ·
            refine ⟨87213526831914071540780963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232569404885104190775415901 87213526831914071540780963)
            ·
              refine ⟨130820290247871107311171445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87213526831914071540780963 130820290247871107311171445)
              ·
                refine ⟨12264402210737916310422323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130820290247871107311171445 12264402210737916310422323)
                ·
                  refine ⟨18396603316106874465633485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12264402210737916310422323 18396603316106874465633485)
                  ·
                    refine ⟨6898726243540077924612557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18396603316106874465633485 6898726243540077924612557)
                    ·
                      refine ⟨2587022341327529221729709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6898726243540077924612557 2587022341327529221729709)
                      ·
                        rfl

theorem cell23_5038208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_5038208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038208 prefixEnd_5038208 := by exact prefixLift 5038208
  have htrace : WordTrace (prefixWord ++ tailWord_5038208) baseStart_5038208 baseEnd_5038208 := by
    simpa [prefixWord, tailWord_5038208, baseEnd_5038208] using wordTrace_append hprefix tailTrace_5038208
  have hstable : (prefixWord ++ tailWord_5038208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038208).length < 2 ^ (prefixWord ++ tailWord_5038208).sum := by decide
  have hdescent : baseEnd_5038208 < baseStart_5038208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038209 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_5038209 : Nat := 118140960795 + 5038209 * 2 ^ 59
def prefixEnd_5038209 : Nat := 4983230072969 + 3 ^ 40 * 5038209 * 2
def baseEnd_5038209 : Nat := 2587022854808183717817205

theorem tailTrace_5038209 : CollatzResearch.WordTrace tailWord_5038209 prefixEnd_5038209 2587022854808183717817205 := by
  unfold tailWord_5038209
  simp only [CollatzResearch.WordTrace]
  refine ⟨183758578604436725437781681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122505719069624483625187787 183758578604436725437781681)
  ·
    refine ⟨137818933953327544078336261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183758578604436725437781681 137818933953327544078336261)
    ·
      refine ⟨25841050116248914514688049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137818933953327544078336261 25841050116248914514688049)
      ·
        refine ⟨19380787587186685886016037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25841050116248914514688049 19380787587186685886016037)
        ·
          refine ⟨3633897672597503603628007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19380787587186685886016037 3633897672597503603628007)
          ·
            refine ⟨5450846508896255405442011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633897672597503603628007 5450846508896255405442011)
            ·
              refine ⟨8176269763344383108163017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5450846508896255405442011 8176269763344383108163017)
              ·
                refine ⟨6132202322508287331122263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8176269763344383108163017 6132202322508287331122263)
                ·
                  refine ⟨9198303483762430996683395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132202322508287331122263 9198303483762430996683395)
                  ·
                    refine ⟨13797455225643646495025093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9198303483762430996683395 13797455225643646495025093)
                    ·
                      refine ⟨2587022854808183717817205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13797455225643646495025093 2587022854808183717817205)
                      ·
                        rfl

theorem cell23_5038209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_5038209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038209 prefixEnd_5038209 := by exact prefixLift 5038209
  have htrace : WordTrace (prefixWord ++ tailWord_5038209) baseStart_5038209 baseEnd_5038209 := by
    simpa [prefixWord, tailWord_5038209, baseEnd_5038209] using wordTrace_append hprefix tailTrace_5038209
  have hstable : (prefixWord ++ tailWord_5038209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038209).length < 2 ^ (prefixWord ++ tailWord_5038209).sum := by decide
  have hdescent : baseEnd_5038209 < baseStart_5038209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038258 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_5038258 : Nat := 118140960795 + 5038258 * 2 ^ 59
def prefixEnd_5038258 : Nat := 4983230072969 + 3 ^ 40 * 5038258 * 2
def baseEnd_5038258 : Nat := 862349338453418008701493

theorem tailTrace_5038258 : CollatzResearch.WordTrace tailWord_5038258 prefixEnd_5038258 862349338453418008701493 := by
  unfold tailWord_5038258
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940091445314801701578857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122506910520839471204210285 45940091445314801701578857)
  ·
    refine ⟨34455068583986101276184143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45940091445314801701578857 34455068583986101276184143)
    ·
      refine ⟨51682602875979151914276215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34455068583986101276184143 51682602875979151914276215)
      ·
        refine ⟨77523904313968727871414323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51682602875979151914276215 77523904313968727871414323)
        ·
          refine ⟨116285856470953091807121485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77523904313968727871414323 116285856470953091807121485)
          ·
            refine ⟨43607196176607409427670557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116285856470953091807121485 43607196176607409427670557)
            ·
              refine ⟨16352698566227778535376459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43607196176607409427670557 16352698566227778535376459)
              ·
                refine ⟨24529047849341667803064689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16352698566227778535376459 24529047849341667803064689)
                ·
                  refine ⟨18396785887006250852298517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24529047849341667803064689 18396785887006250852298517)
                  ·
                    refine ⟨862349338453418008701493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18396785887006250852298517 862349338453418008701493)
                    ·
                      rfl

theorem cell23_5038258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_5038258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038258 prefixEnd_5038258 := by exact prefixLift 5038258
  have htrace : WordTrace (prefixWord ++ tailWord_5038258) baseStart_5038258 baseEnd_5038258 := by
    simpa [prefixWord, tailWord_5038258, baseEnd_5038258] using wordTrace_append hprefix tailTrace_5038258
  have hstable : (prefixWord ++ tailWord_5038258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038258).length < 2 ^ (prefixWord ++ tailWord_5038258).sum := by decide
  have hdescent : baseEnd_5038258 < baseStart_5038258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038282 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_5038282 : Nat := 118140960795 + 5038282 * 2 ^ 59
def prefixEnd_5038282 : Nat := 4983230072969 + 3 ^ 40 * 5038282 * 2
def baseEnd_5038282 : Nat := 2587060338895961932204369

theorem tailTrace_5038282 : CollatzResearch.WordTrace tailWord_5038282 prefixEnd_5038282 2587060338895961932204369 := by
  unfold tailWord_5038282
  simp only [CollatzResearch.WordTrace]
  refine ⟨45940310283293064726297275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122507494088781505936792733 45940310283293064726297275)
  ·
    refine ⟨68910465424939597089445913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45940310283293064726297275 68910465424939597089445913)
    ·
      refine ⟨51682849068704697817084435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68910465424939597089445913 51682849068704697817084435)
      ·
        refine ⟨77524273603057046725626653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51682849068704697817084435 77524273603057046725626653)
        ·
          refine ⟨29071602601146392522109995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77524273603057046725626653 29071602601146392522109995)
          ·
            refine ⟨43607403901719588783164993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29071602601146392522109995 43607403901719588783164993)
            ·
              refine ⟨32705552926289691587373745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43607403901719588783164993 32705552926289691587373745)
              ·
                refine ⟨24529164694717268690530309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32705552926289691587373745 24529164694717268690530309)
                ·
                  refine ⟨4599218380259487879474433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24529164694717268690530309 4599218380259487879474433)
                  ·
                    refine ⟨3449413785194615909605825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599218380259487879474433 3449413785194615909605825)
                    ·
                      refine ⟨2587060338895961932204369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449413785194615909605825 2587060338895961932204369)
                      ·
                        rfl

theorem cell23_5038282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_5038282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038282 prefixEnd_5038282 := by exact prefixLift 5038282
  have htrace : WordTrace (prefixWord ++ tailWord_5038282) baseStart_5038282 baseEnd_5038282 := by
    simpa [prefixWord, tailWord_5038282, baseEnd_5038282] using wordTrace_append hprefix tailTrace_5038282
  have hstable : (prefixWord ++ tailWord_5038282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038282).length < 2 ^ (prefixWord ++ tailWord_5038282).sum := by decide
  have hdescent : baseEnd_5038282 < baseStart_5038282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038286 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_5038286 : Nat := 118140960795 + 5038286 * 2 ^ 59
def prefixEnd_5038286 : Nat := 4983230072969 + 3 ^ 40 * 5038286 * 2
def baseEnd_5038286 : Nat := 2587062392818579916554351

theorem tailTrace_5038286 : CollatzResearch.WordTrace tailWord_5038286 prefixEnd_5038286 2587062392818579916554351 := by
  unfold tailWord_5038286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22970173378144720948541839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122507591350105178392223141 22970173378144720948541839)
  ·
    refine ⟨34455260067217081422812759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22970173378144720948541839 34455260067217081422812759)
    ·
      refine ⟨51682890100825622134219139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34455260067217081422812759 51682890100825622134219139)
      ·
        refine ⟨77524335151238433201328709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51682890100825622134219139 77524335151238433201328709)
        ·
          refine ⟨14535812840857206225249133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77524335151238433201328709 14535812840857206225249133)
          ·
            refine ⟨5450929815321452334468425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14535812840857206225249133 5450929815321452334468425)
            ·
              refine ⟨4088197361491089250851319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5450929815321452334468425 4088197361491089250851319)
              ·
                refine ⟨6132296042236633876276979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088197361491089250851319 6132296042236633876276979)
                ·
                  refine ⟨9198444063354950814415469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132296042236633876276979 9198444063354950814415469)
                  ·
                    refine ⟨3449416523758106555405801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9198444063354950814415469 3449416523758106555405801)
                    ·
                      refine ⟨2587062392818579916554351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449416523758106555405801 2587062392818579916554351)
                      ·
                        rfl

theorem cell23_5038286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_5038286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038286 prefixEnd_5038286 := by exact prefixLift 5038286
  have htrace : WordTrace (prefixWord ++ tailWord_5038286) baseStart_5038286 baseEnd_5038286 := by
    simpa [prefixWord, tailWord_5038286, baseEnd_5038286] using wordTrace_append hprefix tailTrace_5038286
  have hstable : (prefixWord ++ tailWord_5038286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038286).length < 2 ^ (prefixWord ++ tailWord_5038286).sum := by decide
  have hdescent : baseEnd_5038286 < baseStart_5038286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038305 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 5]
def baseStart_5038305 : Nat := 118140960795 + 5038305 * 2 ^ 59
def prefixEnd_5038305 : Nat := 4983230072969 + 3 ^ 40 * 5038305 * 2
def baseEnd_5038305 : Nat := 287452460994557260246307

theorem tailTrace_5038305 : CollatzResearch.WordTrace tailWord_5038305 prefixEnd_5038305 287452460994557260246307 := by
  unfold tailWord_5038305
  simp only [CollatzResearch.WordTrace]
  refine ⟨183762080012088933833276369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122508053341392622555517579 183762080012088933833276369)
  ·
    refine ⟨137821560009066700374957277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183762080012088933833276369 137821560009066700374957277)
    ·
      refine ⟨51683085003400012640608979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137821560009066700374957277 51683085003400012640608979)
      ·
        refine ⟨77524627505100018960913469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51683085003400012640608979 77524627505100018960913469)
        ·
          refine ⟨29071735314412507110342551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77524627505100018960913469 29071735314412507110342551)
          ·
            refine ⟨43607602971618760665513827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29071735314412507110342551 43607602971618760665513827)
            ·
              refine ⟨65411404457428140998270741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43607602971618760665513827 65411404457428140998270741)
              ·
                refine ⟨3066159583941944109293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65411404457428140998270741 3066159583941944109293941)
                ·
                  refine ⟨287452460994557260246307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3066159583941944109293941 287452460994557260246307)
                  ·
                    rfl

theorem cell23_5038305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 5].length) (baseStart_5038305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038305 prefixEnd_5038305 := by exact prefixLift 5038305
  have htrace : WordTrace (prefixWord ++ tailWord_5038305) baseStart_5038305 baseEnd_5038305 := by
    simpa [prefixWord, tailWord_5038305, baseEnd_5038305] using wordTrace_append hprefix tailTrace_5038305
  have hstable : (prefixWord ++ tailWord_5038305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038305).length < 2 ^ (prefixWord ++ tailWord_5038305).sum := by decide
  have hdescent : baseEnd_5038305 < baseStart_5038305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038355 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 4, 4, 2]
def baseStart_5038355 : Nat := 118140960795 + 5038355 * 2 ^ 59
def prefixEnd_5038355 : Nat := 4983230072969 + 3 ^ 40 * 5038355 * 2
def baseEnd_5038355 : Nat := 2587097822983740146591533

theorem tailTrace_5038355 : CollatzResearch.WordTrace tailWord_5038355 prefixEnd_5038355 2587097822983740146591533 := by
  unfold tailWord_5038355
  simp only [CollatzResearch.WordTrace]
  refine ⟨183763903661907792372596519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122509269107938528248397679 183763903661907792372596519)
  ·
    refine ⟨275645855492861688558894779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183763903661907792372596519 275645855492861688558894779)
    ·
      refine ⟨413468783239292532838342169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275645855492861688558894779 413468783239292532838342169)
      ·
        refine ⟨310101587429469399628756627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413468783239292532838342169 310101587429469399628756627)
        ·
          refine ⟨465152381144204099443134941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310101587429469399628756627 465152381144204099443134941)
          ·
            refine ⟨174432142929076537291175603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465152381144204099443134941 174432142929076537291175603)
            ·
              refine ⟨261648214393614805936763405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174432142929076537291175603 261648214393614805936763405)
              ·
                refine ⟨98118080397605552226286277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261648214393614805936763405 98118080397605552226286277)
                ·
                  refine ⟨18397140074551041042428677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98118080397605552226286277 18397140074551041042428677)
                  ·
                    refine ⟨3449463763978320195455377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18397140074551041042428677 3449463763978320195455377)
                    ·
                      refine ⟨2587097822983740146591533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449463763978320195455377 2587097822983740146591533)
                      ·
                        rfl

theorem cell23_5038355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4, 2].length) (baseStart_5038355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038355 prefixEnd_5038355 := by exact prefixLift 5038355
  have htrace : WordTrace (prefixWord ++ tailWord_5038355) baseStart_5038355 baseEnd_5038355 := by
    simpa [prefixWord, tailWord_5038355, baseEnd_5038355] using wordTrace_append hprefix tailTrace_5038355
  have hstable : (prefixWord ++ tailWord_5038355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038355).length < 2 ^ (prefixWord ++ tailWord_5038355).sum := by decide
  have hdescent : baseEnd_5038355 < baseStart_5038355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038416 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 1, 4]
def baseStart_5038416 : Nat := 118140960795 + 5038416 * 2 ^ 59
def prefixEnd_5038416 : Nat := 4983230072969 + 3 ^ 40 * 5038416 * 2
def baseEnd_5038416 : Nat := 862376381767888135976251

theorem tailTrace_5038416 : CollatzResearch.WordTrace tailWord_5038416 prefixEnd_5038416 862376381767888135976251 := by
  unfold tailWord_5038416
  simp only [CollatzResearch.WordTrace]
  refine ⟨91883064257343399895283551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122510752343124533193711401 91883064257343399895283551)
  ·
    refine ⟨137824596386015099842925327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91883064257343399895283551 137824596386015099842925327)
    ·
      refine ⟨206736894579022649764387991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137824596386015099842925327 206736894579022649764387991)
      ·
        refine ⟨310105341868533974646581987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206736894579022649764387991 310105341868533974646581987)
        ·
          refine ⟨465158012802800961969872981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310105341868533974646581987 465158012802800961969872981)
          ·
            refine ⟨5451070462532823773084449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 465158012802800961969872981 5451070462532823773084449)
            ·
              refine ⟨4088302846899617829813337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451070462532823773084449 4088302846899617829813337)
              ·
                refine ⟨3066227135174713372360003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088302846899617829813337 3066227135174713372360003)
                ·
                  refine ⟨4599340702762070058540005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066227135174713372360003 4599340702762070058540005)
                  ·
                    refine ⟨862376381767888135976251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599340702762070058540005 862376381767888135976251)
                    ·
                      rfl

theorem cell23_5038416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 4].length) (baseStart_5038416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038416 prefixEnd_5038416 := by exact prefixLift 5038416
  have htrace : WordTrace (prefixWord ++ tailWord_5038416) baseStart_5038416 baseEnd_5038416 := by
    simpa [prefixWord, tailWord_5038416, baseEnd_5038416] using wordTrace_append hprefix tailTrace_5038416
  have hstable : (prefixWord ++ tailWord_5038416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038416).length < 2 ^ (prefixWord ++ tailWord_5038416).sum := by decide
  have hdescent : baseEnd_5038416 < baseStart_5038416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038439 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_5038439 : Nat := 118140960795 + 5038439 * 2 ^ 59
def prefixEnd_5038439 : Nat := 4983230072969 + 3 ^ 40 * 5038439 * 2
def baseEnd_5038439 : Nat := 2587140955358717817941147

theorem tailTrace_5038439 : CollatzResearch.WordTrace tailWord_5038439 prefixEnd_5038439 2587140955358717817941147 := by
  unfold tailWord_5038439
  simp only [CollatzResearch.WordTrace]
  refine ⟨183766967393603474718654371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122511311595735649812436247 183766967393603474718654371)
  ·
    refine ⟨275650451090405212077981557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183766967393603474718654371 275650451090405212077981557)
    ·
      refine ⟨25842229789725488632310771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275650451090405212077981557 25842229789725488632310771)
      ·
        refine ⟨38763344684588232948466157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25842229789725488632310771 38763344684588232948466157)
        ·
          refine ⟨14536254256720587355674809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38763344684588232948466157 14536254256720587355674809)
          ·
            refine ⟨10902190692540440516756107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14536254256720587355674809 10902190692540440516756107)
            ·
              refine ⟨16353286038810660775134161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902190692540440516756107 16353286038810660775134161)
              ·
                refine ⟨12264964529107995581350621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16353286038810660775134161 12264964529107995581350621)
                ·
                  refine ⟨4599361698415498343006483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12264964529107995581350621 4599361698415498343006483)
                  ·
                    refine ⟨6899042547623247514509725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599361698415498343006483 6899042547623247514509725)
                    ·
                      refine ⟨2587140955358717817941147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899042547623247514509725 2587140955358717817941147)
                      ·
                        rfl

theorem cell23_5038439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_5038439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038439 prefixEnd_5038439 := by exact prefixLift 5038439
  have htrace : WordTrace (prefixWord ++ tailWord_5038439) baseStart_5038439 baseEnd_5038439 := by
    simpa [prefixWord, tailWord_5038439, baseEnd_5038439] using wordTrace_append hprefix tailTrace_5038439
  have hstable : (prefixWord ++ tailWord_5038439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038439).length < 2 ^ (prefixWord ++ tailWord_5038439).sum := by decide
  have hdescent : baseEnd_5038439 < baseStart_5038439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038442 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_5038442 : Nat := 118140960795 + 5038442 * 2 ^ 59
def prefixEnd_5038442 : Nat := 4983230072969 + 3 ^ 40 * 5038442 * 2
def baseEnd_5038442 : Nat := 862380831933560435401211

theorem tailTrace_5038442 : CollatzResearch.WordTrace tailWord_5038442 prefixEnd_5038442 862380831933560435401211 := by
  unfold tailWord_5038442
  simp only [CollatzResearch.WordTrace]
  refine ⟨45941769203148151557753395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122511384541728404154009053 45941769203148151557753395)
  ·
    refine ⟨68912653804722227336630093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45941769203148151557753395 68912653804722227336630093)
    ·
      refine ⟨25842245176770835251236285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68912653804722227336630093 25842245176770835251236285)
      ·
        refine ⟨9690841941289063219213607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25842245176770835251236285 9690841941289063219213607)
        ·
          refine ⟨14536262911933594828820411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9690841941289063219213607 14536262911933594828820411)
          ·
            refine ⟨21804394367900392243230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14536262911933594828820411 21804394367900392243230617)
            ·
              refine ⟨16353295775925294182422963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21804394367900392243230617 16353295775925294182422963)
              ·
                refine ⟨24529943663887941273634445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16353295775925294182422963 24529943663887941273634445)
                ·
                  refine ⟨9198728873957977977612917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24529943663887941273634445 9198728873957977977612917)
                  ·
                    refine ⟨862380831933560435401211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9198728873957977977612917 862380831933560435401211)
                    ·
                      rfl

theorem cell23_5038442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_5038442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038442 prefixEnd_5038442 := by exact prefixLift 5038442
  have htrace : WordTrace (prefixWord ++ tailWord_5038442) baseStart_5038442 baseEnd_5038442 := by
    simpa [prefixWord, tailWord_5038442, baseEnd_5038442] using wordTrace_append hprefix tailTrace_5038442
  have hstable : (prefixWord ++ tailWord_5038442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038442).length < 2 ^ (prefixWord ++ tailWord_5038442).sum := by decide
  have hdescent : baseEnd_5038442 < baseStart_5038442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038459 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 1, 5]
def baseStart_5038459 : Nat := 118140960795 + 5038459 * 2 ^ 59
def prefixEnd_5038459 : Nat := 4983230072969 + 3 ^ 40 * 5038459 * 2
def baseEnd_5038459 : Nat := 862383741657269246563685

theorem tailTrace_5038459 : CollatzResearch.WordTrace tailWord_5038459 prefixEnd_5038459 862383741657269246563685 := by
  unfold tailWord_5038459
  simp only [CollatzResearch.WordTrace]
  refine ⟨183767696853531018134382431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122511797902354012089588287 183767696853531018134382431)
  ·
    refine ⟨275651545280296527201573647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183767696853531018134382431 275651545280296527201573647)
    ·
      refine ⟨413477317920444790802360471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275651545280296527201573647 413477317920444790802360471)
      ·
        refine ⟨620215976880667186203540707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413477317920444790802360471 620215976880667186203540707)
        ·
          refine ⟨930323965321000779305311061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620215976880667186203540707 930323965321000779305311061)
          ·
            refine ⟨5451116984302738941242057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 930323965321000779305311061 5451116984302738941242057)
            ·
              refine ⟨4088337738227054205931543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451116984302738941242057 4088337738227054205931543)
              ·
                refine ⟨6132506607340581308897315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088337738227054205931543 6132506607340581308897315)
                ·
                  refine ⟨9198759911010871963345973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132506607340581308897315 9198759911010871963345973)
                  ·
                    refine ⟨862383741657269246563685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9198759911010871963345973 862383741657269246563685)
                    ·
                      rfl

theorem cell23_5038459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 5].length) (baseStart_5038459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038459 prefixEnd_5038459 := by exact prefixLift 5038459
  have htrace : WordTrace (prefixWord ++ tailWord_5038459) baseStart_5038459 baseEnd_5038459 := by
    simpa [prefixWord, tailWord_5038459, baseEnd_5038459] using wordTrace_append hprefix tailTrace_5038459
  have hstable : (prefixWord ++ tailWord_5038459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038459).length < 2 ^ (prefixWord ++ tailWord_5038459).sum := by decide
  have hdescent : baseEnd_5038459 < baseStart_5038459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038472 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_5038472 : Nat := 118140960795 + 5038472 * 2 ^ 59
def prefixEnd_5038472 : Nat := 4983230072969 + 3 ^ 40 * 5038472 * 2
def baseEnd_5038472 : Nat := 862385966740105396276165

theorem tailTrace_5038472 : CollatzResearch.WordTrace tailWord_5038472 prefixEnd_5038472 862385966740105396276165 := by
  unfold tailWord_5038472
  simp only [CollatzResearch.WordTrace]
  refine ⟨91884085501241960677302835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122512114001655947569737113 91884085501241960677302835)
  ·
    refine ⟨137826128251862941015954253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91884085501241960677302835 137826128251862941015954253)
    ·
      refine ⟨51684798094448602880982845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137826128251862941015954253 51684798094448602880982845)
      ·
        refine ⟨19381799285418226080368567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51684798094448602880982845 19381799285418226080368567)
        ·
          refine ⟨29072698928127339120552851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19381799285418226080368567 29072698928127339120552851)
          ·
            refine ⟨43609048392191008680829277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29072698928127339120552851 43609048392191008680829277)
            ·
              refine ⟨16353393147071628255310979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43609048392191008680829277 16353393147071628255310979)
              ·
                refine ⟨24530089720607442382966469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16353393147071628255310979 24530089720607442382966469)
                ·
                  refine ⟨4599391822613895446806213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24530089720607442382966469 4599391822613895446806213)
                  ·
                    refine ⟨862385966740105396276165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599391822613895446806213 862385966740105396276165)
                    ·
                      rfl

theorem cell23_5038472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_5038472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038472 prefixEnd_5038472 := by exact prefixLift 5038472
  have htrace : WordTrace (prefixWord ++ tailWord_5038472) baseStart_5038472 baseEnd_5038472 := by
    simpa [prefixWord, tailWord_5038472, baseEnd_5038472] using wordTrace_append hprefix tailTrace_5038472
  have hstable : (prefixWord ++ tailWord_5038472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038472).length < 2 ^ (prefixWord ++ tailWord_5038472).sum := by decide
  have hdescent : baseEnd_5038472 < baseStart_5038472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038489 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 2, 4]
def baseStart_5038489 : Nat := 118140960795 + 5038489 * 2 ^ 59
def prefixEnd_5038489 : Nat := 4983230072969 + 3 ^ 40 * 5038489 * 2
def baseEnd_5038489 : Nat := 862388876463814207438639

theorem tailTrace_5038489 : CollatzResearch.WordTrace tailWord_5038489 prefixEnd_5038489 862388876463814207438639 := by
  unfold tailWord_5038489
  simp only [CollatzResearch.WordTrace]
  refine ⟨183768791043422333257974521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122512527362281555505316347 183768791043422333257974521)
  ·
    refine ⟨137826593282566749943480891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183768791043422333257974521 137826593282566749943480891)
    ·
      refine ⟨206739889923850124915221337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137826593282566749943480891 206739889923850124915221337)
      ·
        refine ⟨155054917442887593686416003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206739889923850124915221337 155054917442887593686416003)
        ·
          refine ⟨232582376164331390529624005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155054917442887593686416003 232582376164331390529624005)
          ·
            refine ⟨43609195530812135724304501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232582376164331390529624005 43609195530812135724304501)
            ·
              refine ⟨4088362081013637724153547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43609195530812135724304501 4088362081013637724153547)
              ·
                refine ⟨6132543121520456586230321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088362081013637724153547 6132543121520456586230321)
                ·
                  refine ⟨4599407341140342439672741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6132543121520456586230321 4599407341140342439672741)
                  ·
                    refine ⟨862388876463814207438639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599407341140342439672741 862388876463814207438639)
                    ·
                      rfl

theorem cell23_5038489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_5038489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038489 prefixEnd_5038489 := by exact prefixLift 5038489
  have htrace : WordTrace (prefixWord ++ tailWord_5038489) baseStart_5038489 baseEnd_5038489 := by
    simpa [prefixWord, tailWord_5038489, baseEnd_5038489] using wordTrace_append hprefix tailTrace_5038489
  have hstable : (prefixWord ++ tailWord_5038489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038489).length < 2 ^ (prefixWord ++ tailWord_5038489).sum := by decide
  have hdescent : baseEnd_5038489 < baseStart_5038489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038499 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 3]
def baseStart_5038499 : Nat := 118140960795 + 5038499 * 2 ^ 59
def prefixEnd_5038499 : Nat := 4983230072969 + 3 ^ 40 * 5038499 * 2
def baseEnd_5038499 : Nat := 2587171764197987583190871

theorem tailTrace_5038499 : CollatzResearch.WordTrace tailWord_5038499 prefixEnd_5038499 2587171764197987583190871 := by
  unfold tailWord_5038499
  simp only [CollatzResearch.WordTrace]
  refine ⟨183769155773386104965838551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122512770515590736643892367 183769155773386104965838551)
  ·
    refine ⟨275653733660079157448757827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183769155773386104965838551 275653733660079157448757827)
    ·
      refine ⟨413480600490118736173136741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275653733660079157448757827 413480600490118736173136741)
      ·
        refine ⟨77527612591897263032463139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 413480600490118736173136741 77527612591897263032463139)
        ·
          refine ⟨116291418887845894548694709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77527612591897263032463139 116291418887845894548694709)
          ·
            refine ⟨10902320520735552613940129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116291418887845894548694709 10902320520735552613940129)
            ·
              refine ⟨8176740390551664460455097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10902320520735552613940129 8176740390551664460455097)
              ·
                refine ⟨6132555292913748345341323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8176740390551664460455097 6132555292913748345341323)
                ·
                  refine ⟨9198832939370622518011985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132555292913748345341323 9198832939370622518011985)
                  ·
                    refine ⟨6899124704527966888508989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9198832939370622518011985 6899124704527966888508989)
                    ·
                      refine ⟨2587171764197987583190871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899124704527966888508989 2587171764197987583190871)
                      ·
                        rfl

theorem cell23_5038499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_5038499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038499 prefixEnd_5038499 := by exact prefixLift 5038499
  have htrace : WordTrace (prefixWord ++ tailWord_5038499) baseStart_5038499 baseEnd_5038499 := by
    simpa [prefixWord, tailWord_5038499, baseEnd_5038499] using wordTrace_append hprefix tailTrace_5038499
  have hstable : (prefixWord ++ tailWord_5038499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038499).length < 2 ^ (prefixWord ++ tailWord_5038499).sum := by decide
  have hdescent : baseEnd_5038499 < baseStart_5038499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038513 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5038513 : Nat := 118140960795 + 5038513 * 2 ^ 59
def prefixEnd_5038513 : Nat := 4983230072969 + 3 ^ 40 * 5038513 * 2
def baseEnd_5038513 : Nat := 2587178952927150528415807

theorem tailTrace_5038513 : CollatzResearch.WordTrace tailWord_5038513 prefixEnd_5038513 2587178952927150528415807 := by
  unfold tailWord_5038513
  simp only [CollatzResearch.WordTrace]
  refine ⟨183769666395335385356848193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122513110930223590237898795 183769666395335385356848193)
  ·
    refine ⟨137827249796501539017636145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183769666395335385356848193 137827249796501539017636145)
    ·
      refine ⟨103370437347376154263227109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137827249796501539017636145 103370437347376154263227109)
      ·
        refine ⟨19381957002633028924355083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103370437347376154263227109 19381957002633028924355083)
        ·
          refine ⟨29072935503949543386532625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19381957002633028924355083 29072935503949543386532625)
          ·
            refine ⟨21804701627962157539899469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29072935503949543386532625 21804701627962157539899469)
            ·
              refine ⟨8176763110485809077462301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21804701627962157539899469 8176763110485809077462301)
              ·
                refine ⟨3066286166432178404048363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8176763110485809077462301 3066286166432178404048363)
                ·
                  refine ⟨4599429249648267606072545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066286166432178404048363 4599429249648267606072545)
                  ·
                    refine ⟨3449571937236200704554409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599429249648267606072545 3449571937236200704554409)
                    ·
                      refine ⟨2587178952927150528415807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449571937236200704554409 2587178952927150528415807)
                      ·
                        rfl

theorem cell23_5038513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5038513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038513 prefixEnd_5038513 := by exact prefixLift 5038513
  have htrace : WordTrace (prefixWord ++ tailWord_5038513) baseStart_5038513 baseEnd_5038513 := by
    simpa [prefixWord, tailWord_5038513, baseEnd_5038513] using wordTrace_append hprefix tailTrace_5038513
  have hstable : (prefixWord ++ tailWord_5038513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038513).length < 2 ^ (prefixWord ++ tailWord_5038513).sum := by decide
  have hdescent : baseEnd_5038513 < baseStart_5038513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038545 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_5038545 : Nat := 118140960795 + 5038545 * 2 ^ 59
def prefixEnd_5038545 : Nat := 4983230072969 + 3 ^ 40 * 5038545 * 2
def baseEnd_5038545 : Nat := 862398461436031467738553

theorem tailTrace_5038545 : CollatzResearch.WordTrace tailWord_5038545 prefixEnd_5038545 862398461436031467738553 := by
  unfold tailWord_5038545
  simp only [CollatzResearch.WordTrace]
  refine ⟨183770833531219454822013089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122513889020812969881342059 183770833531219454822013089)
  ·
    refine ⟨137828125148414591116509817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183770833531219454822013089 137828125148414591116509817)
    ·
      refine ⟨103371093861310943337382363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137828125148414591116509817 103371093861310943337382363)
      ·
        refine ⟨155056640791966415006073545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103371093861310943337382363 155056640791966415006073545)
        ·
          refine ⟨116292480593974811254555159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155056640791966415006073545 116292480593974811254555159)
          ·
            refine ⟨174438720890962216881832739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116292480593974811254555159 174438720890962216881832739)
            ·
              refine ⟨261658081336443325322749109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174438720890962216881832739 261658081336443325322749109)
              ·
                refine ⟨24530445125291561749007729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261658081336443325322749109 24530445125291561749007729)
                ·
                  refine ⟨18397833843968671311755797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24530445125291561749007729 18397833843968671311755797)
                  ·
                    refine ⟨862398461436031467738553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18397833843968671311755797 862398461436031467738553)
                    ·
                      rfl

theorem cell23_5038545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_5038545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038545 prefixEnd_5038545 := by exact prefixLift 5038545
  have htrace : WordTrace (prefixWord ++ tailWord_5038545) baseStart_5038545 baseEnd_5038545 := by
    simpa [prefixWord, tailWord_5038545, baseEnd_5038545] using wordTrace_append hprefix tailTrace_5038545
  have hstable : (prefixWord ++ tailWord_5038545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038545).length < 2 ^ (prefixWord ++ tailWord_5038545).sum := by decide
  have hdescent : baseEnd_5038545 < baseStart_5038545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038569 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 4, 2, 2]
def baseStart_5038569 : Nat := 118140960795 + 5038569 * 2 ^ 59
def prefixEnd_5038569 : Nat := 4983230072969 + 3 ^ 40 * 5038569 * 2
def baseEnd_5038569 : Nat := 2587207707843802309315549

theorem tailTrace_5038569 : CollatzResearch.WordTrace tailWord_5038569 prefixEnd_5038569 2587207707843802309315549 := by
  unfold tailWord_5038569
  simp only [CollatzResearch.WordTrace]
  refine ⟨183771708883132506920886761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122514472588755004613924507 183771708883132506920886761)
  ·
    refine ⟨137828781662349380190665071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183771708883132506920886761 137828781662349380190665071)
    ·
      refine ⟨206743172493524070285997607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137828781662349380190665071 206743172493524070285997607)
      ·
        refine ⟨310114758740286105428996411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206743172493524070285997607 310114758740286105428996411)
        ·
          refine ⟨465172138110429158143494617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310114758740286105428996411 465172138110429158143494617)
          ·
            refine ⟨348879103582821868607620963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465172138110429158143494617 348879103582821868607620963)
            ·
              refine ⟨523318655374232802911431445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348879103582821868607620963 523318655374232802911431445)
              ·
                refine ⟨24530561970667162636473349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 523318655374232802911431445 24530561970667162636473349)
                ·
                  refine ⟨4599480369500092994338753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24530561970667162636473349 4599480369500092994338753)
                  ·
                    refine ⟨3449610277125069745754065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599480369500092994338753 3449610277125069745754065)
                    ·
                      refine ⟨2587207707843802309315549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449610277125069745754065 2587207707843802309315549)
                      ·
                        rfl

theorem cell23_5038569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 2, 2].length) (baseStart_5038569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038569 prefixEnd_5038569 := by exact prefixLift 5038569
  have htrace : WordTrace (prefixWord ++ tailWord_5038569) baseStart_5038569 baseEnd_5038569 := by
    simpa [prefixWord, tailWord_5038569, baseEnd_5038569] using wordTrace_append hprefix tailTrace_5038569
  have hstable : (prefixWord ++ tailWord_5038569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038569).length < 2 ^ (prefixWord ++ tailWord_5038569).sum := by decide
  have hdescent : baseEnd_5038569 < baseStart_5038569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038585 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_5038585 : Nat := 118140960795 + 5038585 * 2 ^ 59
def prefixEnd_5038585 : Nat := 4983230072969 + 3 ^ 40 * 5038585 * 2
def baseEnd_5038585 : Nat := 2587215923534274246715475

theorem tailTrace_5038585 : CollatzResearch.WordTrace tailWord_5038585 prefixEnd_5038585 2587215923534274246715475 := by
  unfold tailWord_5038585
  simp only [CollatzResearch.WordTrace]
  refine ⟨183772292451074541653469209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122514861634049694435646139 183772292451074541653469209)
  ·
    refine ⟨137829219338305906240101907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183772292451074541653469209 137829219338305906240101907)
    ·
      refine ⟨206743829007458859360152861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137829219338305906240101907 206743829007458859360152861)
      ·
        refine ⟨77528935877797072260057323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206743829007458859360152861 77528935877797072260057323)
        ·
          refine ⟨116293403816695608390085985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77528935877797072260057323 116293403816695608390085985)
          ·
            refine ⟨87220052862521706292564489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116293403816695608390085985 87220052862521706292564489)
            ·
              refine ⟨65415039646891279719423367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87220052862521706292564489 65415039646891279719423367)
              ·
                refine ⟨98122559470336919579135051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65415039646891279719423367 98122559470336919579135051)
                ·
                  refine ⟨147183839205505379368702577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98122559470336919579135051 147183839205505379368702577)
                  ·
                    refine ⟨110387879404129034526526933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147183839205505379368702577 110387879404129034526526933)
                    ·
                      refine ⟨2587215923534274246715475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110387879404129034526526933 2587215923534274246715475)
                      ·
                        rfl

theorem cell23_5038585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_5038585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038585 prefixEnd_5038585 := by exact prefixLift 5038585
  have htrace : WordTrace (prefixWord ++ tailWord_5038585) baseStart_5038585 baseEnd_5038585 := by
    simpa [prefixWord, tailWord_5038585, baseEnd_5038585] using wordTrace_append hprefix tailTrace_5038585
  have hstable : (prefixWord ++ tailWord_5038585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038585).length < 2 ^ (prefixWord ++ tailWord_5038585).sum := by decide
  have hdescent : baseEnd_5038585 < baseStart_5038585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038599 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_5038599 : Nat := 118140960795 + 5038599 * 2 ^ 59
def prefixEnd_5038599 : Nat := 4983230072969 + 3 ^ 40 * 5038599 * 2
def baseEnd_5038599 : Nat := 2587223112263437191940411

theorem tailTrace_5038599 : CollatzResearch.WordTrace tailWord_5038599 prefixEnd_5038599 2587223112263437191940411 := by
  unfold tailWord_5038599
  simp only [CollatzResearch.WordTrace]
  refine ⟨183772803073023822044478851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122515202048682548029652567 183772803073023822044478851)
  ·
    refine ⟨275659204609535733066718277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183772803073023822044478851 275659204609535733066718277)
    ·
      refine ⟨51686100864287949950009677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275659204609535733066718277 51686100864287949950009677)
      ·
        refine ⟨19382287824107981231253629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51686100864287949950009677 19382287824107981231253629)
        ·
          refine ⟨7268357934040492961720111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19382287824107981231253629 7268357934040492961720111)
          ·
            refine ⟨10902536901060739442580167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268357934040492961720111 10902536901060739442580167)
            ·
              refine ⟨16353805351591109163870251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902536901060739442580167 16353805351591109163870251)
              ·
                refine ⟨24530708027386663745805377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16353805351591109163870251 24530708027386663745805377)
                ·
                  refine ⟨18398031020539997809354033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24530708027386663745805377 18398031020539997809354033)
                  ·
                    refine ⟨13798523265404998357015525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18398031020539997809354033 13798523265404998357015525)
                    ·
                      refine ⟨2587223112263437191940411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13798523265404998357015525 2587223112263437191940411)
                      ·
                        rfl

theorem cell23_5038599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_5038599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038599 prefixEnd_5038599 := by exact prefixLift 5038599
  have htrace : WordTrace (prefixWord ++ tailWord_5038599) baseStart_5038599 baseEnd_5038599 := by
    simpa [prefixWord, tailWord_5038599, baseEnd_5038599] using wordTrace_append hprefix tailTrace_5038599
  have hstable : (prefixWord ++ tailWord_5038599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038599).length < 2 ^ (prefixWord ++ tailWord_5038599).sum := by decide
  have hdescent : baseEnd_5038599 < baseStart_5038599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038635 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 10]
def baseStart_5038635 : Nat := 118140960795 + 5038635 * 2 ^ 59
def prefixEnd_5038635 : Nat := 4983230072969 + 3 ^ 40 * 5038635 * 2
def baseEnd_5038635 : Nat := 862413865855666350363415

theorem tailTrace_5038635 : CollatzResearch.WordTrace tailWord_5038635 prefixEnd_5038635 862413865855666350363415 := by
  unfold tailWord_5038635
  simp only [CollatzResearch.WordTrace]
  refine ⟨183774116100893400192789359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122516077400595600128526239 183774116100893400192789359)
  ·
    refine ⟨275661174151340100289184039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183774116100893400192789359 275661174151340100289184039)
    ·
      refine ⟨413491761227010150433776059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275661174151340100289184039 413491761227010150433776059)
      ·
        refine ⟨620237641840515225650664089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413491761227010150433776059 620237641840515225650664089)
        ·
          refine ⟨465178231380386419237998067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620237641840515225650664089 465178231380386419237998067)
          ·
            refine ⟨697767347070579628856997101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465178231380386419237998067 697767347070579628856997101)
            ·
              refine ⟨261662755151467360821373913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697767347070579628856997101 261662755151467360821373913)
              ·
                refine ⟨196247066363600520616030435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261662755151467360821373913 196247066363600520616030435)
                ·
                  refine ⟨294370599545400780924045653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196247066363600520616030435 294370599545400780924045653)
                  ·
                    refine ⟨862413865855666350363415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 294370599545400780924045653 862413865855666350363415)
                    ·
                      rfl

theorem cell23_5038635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_5038635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038635 prefixEnd_5038635 := by exact prefixLift 5038635
  have htrace : WordTrace (prefixWord ++ tailWord_5038635) baseStart_5038635 baseEnd_5038635 := by
    simpa [prefixWord, tailWord_5038635, baseEnd_5038635] using wordTrace_append hprefix tailTrace_5038635
  have hstable : (prefixWord ++ tailWord_5038635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038635).length < 2 ^ (prefixWord ++ tailWord_5038635).sum := by decide
  have hdescent : baseEnd_5038635 < baseStart_5038635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038637 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5038637 : Nat := 118140960795 + 5038637 * 2 ^ 59
def prefixEnd_5038637 : Nat := 4983230072969 + 3 ^ 40 * 5038637 * 2
def baseEnd_5038637 : Nat := 2587242624528308043265237

theorem tailTrace_5038637 : CollatzResearch.WordTrace tailWord_5038637 prefixEnd_5038637 2587242624528308043265237 := by
  unfold tailWord_5038637
  simp only [CollatzResearch.WordTrace]
  refine ⟨183774189046886154534362165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122516126031257436356241443 183774189046886154534362165)
  ·
    refine ⟨17228830223145576987596453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183774189046886154534362165 17228830223145576987596453)
    ·
      refine ⟨3230405666839795685174335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17228830223145576987596453 3230405666839795685174335)
      ·
        refine ⟨4845608500259693527761503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230405666839795685174335 4845608500259693527761503)
        ·
          refine ⟨7268412750389540291642255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845608500259693527761503 7268412750389540291642255)
          ·
            refine ⟨10902619125584310437463383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268412750389540291642255 10902619125584310437463383)
            ·
              refine ⟨16353928688376465656195075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902619125584310437463383 16353928688376465656195075)
              ·
                refine ⟨24530893032564698484292613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16353928688376465656195075 24530893032564698484292613)
                ·
                  refine ⟨4599542443605880965804865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24530893032564698484292613 4599542443605880965804865)
                  ·
                    refine ⟨3449656832704410724353649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599542443605880965804865 3449656832704410724353649)
                    ·
                      refine ⟨2587242624528308043265237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449656832704410724353649 2587242624528308043265237)
                      ·
                        rfl

theorem cell23_5038637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5038637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038637 prefixEnd_5038637 := by exact prefixLift 5038637
  have htrace : WordTrace (prefixWord ++ tailWord_5038637) baseStart_5038637 baseEnd_5038637 := by
    simpa [prefixWord, tailWord_5038637, baseEnd_5038637] using wordTrace_append hprefix tailTrace_5038637
  have hstable : (prefixWord ++ tailWord_5038637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038637).length < 2 ^ (prefixWord ++ tailWord_5038637).sum := by decide
  have hdescent : baseEnd_5038637 < baseStart_5038637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038679 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_5038679 : Nat := 118140960795 + 5038679 * 2 ^ 59
def prefixEnd_5038679 : Nat := 4983230072969 + 3 ^ 40 * 5038679 * 2
def baseEnd_5038679 : Nat := 2587264190715796878940043

theorem tailTrace_5038679 : CollatzResearch.WordTrace tailWord_5038679 prefixEnd_5038679 2587264190715796878940043 := by
  unfold tailWord_5038679
  simp only [CollatzResearch.WordTrace]
  refine ⟨183775720912733995707391091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122517147275155997138260727 183775720912733995707391091)
  ·
    refine ⟨275663581369100993561086637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183775720912733995707391091 275663581369100993561086637)
    ·
      refine ⟨103373843013412872585407489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275663581369100993561086637 103373843013412872585407489)
      ·
        refine ⟨77530382260059654439055617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103373843013412872585407489 77530382260059654439055617)
        ·
          refine ⟨58147786695044740829291713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77530382260059654439055617 58147786695044740829291713)
          ·
            refine ⟨43610840021283555621968785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58147786695044740829291713 43610840021283555621968785)
            ·
              refine ⟨32708130015962666716476589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43610840021283555621968785 32708130015962666716476589)
              ·
                refine ⟨12265548755986000018678721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32708130015962666716476589 12265548755986000018678721)
                ·
                  refine ⟨9199161566989500014009041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12265548755986000018678721 9199161566989500014009041)
                  ·
                    refine ⟨6899371175242125010506781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9199161566989500014009041 6899371175242125010506781)
                    ·
                      refine ⟨2587264190715796878940043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899371175242125010506781 2587264190715796878940043)
                      ·
                        rfl

theorem cell23_5038679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_5038679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038679 prefixEnd_5038679 := by exact prefixLift 5038679
  have htrace : WordTrace (prefixWord ++ tailWord_5038679) baseStart_5038679 baseEnd_5038679 := by
    simpa [prefixWord, tailWord_5038679, baseEnd_5038679] using wordTrace_append hprefix tailTrace_5038679
  have hstable : (prefixWord ++ tailWord_5038679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038679).length < 2 ^ (prefixWord ++ tailWord_5038679).sum := by decide
  have hdescent : baseEnd_5038679 < baseStart_5038679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038712 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_5038712 : Nat := 118140960795 + 5038712 * 2 ^ 59
def prefixEnd_5038712 : Nat := 4983230072969 + 3 ^ 40 * 5038712 * 2
def baseEnd_5038712 : Nat := 862427045192465083275797

theorem tailTrace_5038712 : CollatzResearch.WordTrace tailWord_5038712 prefixEnd_5038712 862427045192465083275797 := by
  unfold tailWord_5038712
  simp only [CollatzResearch.WordTrace]
  refine ⟨91888462260807221171671195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122517949681076294895561593 91888462260807221171671195)
  ·
    refine ⟨137832693391210831757506793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91888462260807221171671195 137832693391210831757506793)
    ·
      refine ⟨103374520043408123818130095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137832693391210831757506793 103374520043408123818130095)
      ·
        refine ⟨155061780065112185727195143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103374520043408123818130095 155061780065112185727195143)
        ·
          refine ⟨232592670097668278590792715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155061780065112185727195143 232592670097668278590792715)
          ·
            refine ⟨348889005146502417886189073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232592670097668278590792715 348889005146502417886189073)
            ·
              refine ⟨261666753859876813414641805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348889005146502417886189073 261666753859876813414641805)
              ·
                refine ⟨98125032697453805030490677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261666753859876813414641805 98125032697453805030490677)
                ·
                  refine ⟨9199221815386294221608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98125032697453805030490677 9199221815386294221608501)
                  ·
                    refine ⟨862427045192465083275797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9199221815386294221608501 862427045192465083275797)
                    ·
                      rfl

theorem cell23_5038712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_5038712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038712 prefixEnd_5038712 := by exact prefixLift 5038712
  have htrace : WordTrace (prefixWord ++ tailWord_5038712) baseStart_5038712 baseEnd_5038712 := by
    simpa [prefixWord, tailWord_5038712, baseEnd_5038712] using wordTrace_append hprefix tailTrace_5038712
  have hstable : (prefixWord ++ tailWord_5038712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038712).length < 2 ^ (prefixWord ++ tailWord_5038712).sum := by decide
  have hdescent : baseEnd_5038712 < baseStart_5038712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038719 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 5, 2]
def baseStart_5038719 : Nat := 118140960795 + 5038719 * 2 ^ 59
def prefixEnd_5038719 : Nat := 4983230072969 + 3 ^ 40 * 5038719 * 2
def baseEnd_5038719 : Nat := 2587284729941976722439859

theorem tailTrace_5038719 : CollatzResearch.WordTrace tailWord_5038719 prefixEnd_5038719 2587284729941976722439859 := by
  unfold tailWord_5038719
  simp only [CollatzResearch.WordTrace]
  refine ⟨183777179832589082538847211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122518119888392721692564807 183777179832589082538847211)
  ·
    refine ⟨275665769748883623808270817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183777179832589082538847211 275665769748883623808270817)
    ·
      refine ⟨206749327311662717856203113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275665769748883623808270817 206749327311662717856203113)
      ·
        refine ⟨155061995483747038392152335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206749327311662717856203113 155061995483747038392152335)
        ·
          refine ⟨232592993225620557588228503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155061995483747038392152335 232592993225620557588228503)
          ·
            refine ⟨348889489838430836382342755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232592993225620557588228503 348889489838430836382342755)
            ·
              refine ⟨523334234757646254573514133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348889489838430836382342755 523334234757646254573514133)
              ·
                refine ⟨24531292254264668183133475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 523334234757646254573514133 24531292254264668183133475)
                ·
                  refine ⟨36796938381397002274700213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24531292254264668183133475 36796938381397002274700213)
                  ·
                    refine ⟨3449712973255968963253145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36796938381397002274700213 3449712973255968963253145)
                    ·
                      refine ⟨2587284729941976722439859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449712973255968963253145 2587284729941976722439859)
                      ·
                        rfl

theorem cell23_5038719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_5038719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038719 prefixEnd_5038719 := by exact prefixLift 5038719
  have htrace : WordTrace (prefixWord ++ tailWord_5038719) baseStart_5038719 baseEnd_5038719 := by
    simpa [prefixWord, tailWord_5038719, baseEnd_5038719] using wordTrace_append hprefix tailTrace_5038719
  have hstable : (prefixWord ++ tailWord_5038719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038719).length < 2 ^ (prefixWord ++ tailWord_5038719).sum := by decide
  have hdescent : baseEnd_5038719 < baseStart_5038719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038743 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 1, 1, 3]
def baseStart_5038743 : Nat := 118140960795 + 5038743 * 2 ^ 59
def prefixEnd_5038743 : Nat := 4983230072969 + 3 ^ 40 * 5038743 * 2
def baseEnd_5038743 : Nat := 2587297053477684628539749

theorem tailTrace_5038743 : CollatzResearch.WordTrace tailWord_5038743 prefixEnd_5038743 2587297053477684628539749 := by
  unfold tailWord_5038743
  simp only [CollatzResearch.WordTrace]
  refine ⟨183778055184502134637720883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122518703456334756425147255 183778055184502134637720883)
  ·
    refine ⟨275667082776753201956581325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183778055184502134637720883 275667082776753201956581325)
    ·
      refine ⟨103375156041282450733717997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275667082776753201956581325 103375156041282450733717997)
      ·
        refine ⟨38765683515480919025144249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103375156041282450733717997 38765683515480919025144249)
        ·
          refine ⟨29074262636610689268858187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38765683515480919025144249 29074262636610689268858187)
          ·
            refine ⟨43611393954916033903287281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29074262636610689268858187 43611393954916033903287281)
            ·
              refine ⟨32708545466187025427465461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43611393954916033903287281 32708545466187025427465461)
              ·
                refine ⟨3066426137455033633824887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32708545466187025427465461 3066426137455033633824887)
                ·
                  refine ⟨4599639206182550450737331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066426137455033633824887 4599639206182550450737331)
                  ·
                    refine ⟨6899458809273825676105997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599639206182550450737331 6899458809273825676105997)
                    ·
                      refine ⟨2587297053477684628539749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899458809273825676105997 2587297053477684628539749)
                      ·
                        rfl

theorem cell23_5038743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_5038743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038743 prefixEnd_5038743 := by exact prefixLift 5038743
  have htrace : WordTrace (prefixWord ++ tailWord_5038743) baseStart_5038743 baseEnd_5038743 := by
    simpa [prefixWord, tailWord_5038743, baseEnd_5038743] using wordTrace_append hprefix tailTrace_5038743
  have hstable : (prefixWord ++ tailWord_5038743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038743).length < 2 ^ (prefixWord ++ tailWord_5038743).sum := by decide
  have hdescent : baseEnd_5038743 < baseStart_5038743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038783 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 3, 2, 2]
def baseStart_5038783 : Nat := 118140960795 + 5038783 * 2 ^ 59
def prefixEnd_5038783 : Nat := 4983230072969 + 3 ^ 40 * 5038783 * 2
def baseEnd_5038783 : Nat := 2587317592703864472039565

theorem tailTrace_5038783 : CollatzResearch.WordTrace tailWord_5038783 prefixEnd_5038783 2587317592703864472039565 := by
  unfold tailWord_5038783
  simp only [CollatzResearch.WordTrace]
  refine ⟨183779514104357221469177003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122519676069571480979451335 183779514104357221469177003)
  ·
    refine ⟨275669271156535832203765505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183779514104357221469177003 275669271156535832203765505)
    ·
      refine ⟨206751953367401874152824129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275669271156535832203765505 206751953367401874152824129)
      ·
        refine ⟨155063965025551405614618097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206751953367401874152824129 155063965025551405614618097)
        ·
          refine ⟨116297973769163554210963573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155063965025551405614618097 116297973769163554210963573)
          ·
            refine ⟨10902935040859083207277835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116297973769163554210963573 10902935040859083207277835)
            ·
              refine ⟨16354402561288624810916753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10902935040859083207277835 16354402561288624810916753)
              ·
                refine ⟨12265801920966468608187565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16354402561288624810916753 12265801920966468608187565)
                ·
                  refine ⟨4599675720362425728070337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12265801920966468608187565 4599675720362425728070337)
                  ·
                    refine ⟨3449756790271819296052753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4599675720362425728070337 3449756790271819296052753)
                    ·
                      refine ⟨2587317592703864472039565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449756790271819296052753 2587317592703864472039565)
                      ·
                        rfl

theorem cell23_5038783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_5038783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038783 prefixEnd_5038783 := by exact prefixLift 5038783
  have htrace : WordTrace (prefixWord ++ tailWord_5038783) baseStart_5038783 baseEnd_5038783 := by
    simpa [prefixWord, tailWord_5038783, baseEnd_5038783] using wordTrace_append hprefix tailTrace_5038783
  have hstable : (prefixWord ++ tailWord_5038783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038783).length < 2 ^ (prefixWord ++ tailWord_5038783).sum := by decide
  have hdescent : baseEnd_5038783 < baseStart_5038783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038796 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5038796 : Nat := 118140960795 + 5038796 * 2 ^ 59
def prefixEnd_5038796 : Nat := 4983230072969 + 3 ^ 40 * 5038796 * 2
def baseEnd_5038796 : Nat := 2587324267952372921177005

theorem tailTrace_5038796 : CollatzResearch.WordTrace tailWord_5038796 prefixEnd_5038796 2587324267952372921177005 := by
  unfold tailWord_5038796
  simp only [CollatzResearch.WordTrace]
  refine ⟨91889994126655062344700121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122519992168873416459600161 91889994126655062344700121)
  ·
    refine ⟨68917495594991296758525091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91889994126655062344700121 68917495594991296758525091)
    ·
      refine ⟨103376243392486945137787637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68917495594991296758525091 103376243392486945137787637)
      ·
        refine ⟨9691522818045651106667591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103376243392486945137787637 9691522818045651106667591)
        ·
          refine ⟨14537284227068476660001387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9691522818045651106667591 14537284227068476660001387)
          ·
            refine ⟨21805926340602714990002081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14537284227068476660001387 21805926340602714990002081)
            ·
              refine ⟨16354444755452036242501561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21805926340602714990002081 16354444755452036242501561)
              ·
                refine ⟨12265833566589027181876171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16354444755452036242501561 12265833566589027181876171)
                ·
                  refine ⟨18398750349883540772814257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12265833566589027181876171 18398750349883540772814257)
                  ·
                    refine ⟨13799062762412655579610693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18398750349883540772814257 13799062762412655579610693)
                    ·
                      refine ⟨2587324267952372921177005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13799062762412655579610693 2587324267952372921177005)
                      ·
                        rfl

theorem cell23_5038796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5038796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038796 prefixEnd_5038796 := by exact prefixLift 5038796
  have htrace : WordTrace (prefixWord ++ tailWord_5038796) baseStart_5038796 baseEnd_5038796 := by
    simpa [prefixWord, tailWord_5038796, baseEnd_5038796] using wordTrace_append hprefix tailTrace_5038796
  have hstable : (prefixWord ++ tailWord_5038796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038796).length < 2 ^ (prefixWord ++ tailWord_5038796).sum := by decide
  have hdescent : baseEnd_5038796 < baseStart_5038796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038797 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5038797 : Nat := 118140960795 + 5038797 * 2 ^ 59
def prefixEnd_5038797 : Nat := 4983230072969 + 3 ^ 40 * 5038797 * 2
def baseEnd_5038797 : Nat := 862441593811009139088167

theorem tailTrace_5038797 : CollatzResearch.WordTrace tailWord_5038797 prefixEnd_5038797 862441593811009139088167 := by
  unfold tailWord_5038797
  simp only [CollatzResearch.WordTrace]
  refine ⟨183780024726306501860186645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122520016484204334573457763 183780024726306501860186645)
  ·
    refine ⟨8614688659045617274696249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 183780024726306501860186645 8614688659045617274696249)
    ·
      refine ⟨6461016494284212956022187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8614688659045617274696249 6461016494284212956022187)
      ·
        refine ⟨9691524741426319434033281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461016494284212956022187 9691524741426319434033281)
        ·
          refine ⟨7268643556069739575524961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9691524741426319434033281 7268643556069739575524961)
          ·
            refine ⟨5451482667052304681643721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7268643556069739575524961 5451482667052304681643721)
            ·
              refine ⟨4088612000289228511232791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451482667052304681643721 4088612000289228511232791)
              ·
                refine ⟨6132918000433842766849187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088612000289228511232791 6132918000433842766849187)
                ·
                  refine ⟨9199377000650764150273781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6132918000433842766849187 9199377000650764150273781)
                  ·
                    refine ⟨862441593811009139088167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9199377000650764150273781 862441593811009139088167)
                    ·
                      rfl

theorem cell23_5038797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5038797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038797 prefixEnd_5038797 := by exact prefixLift 5038797
  have htrace : WordTrace (prefixWord ++ tailWord_5038797) baseStart_5038797 baseEnd_5038797 := by
    simpa [prefixWord, tailWord_5038797, baseEnd_5038797] using wordTrace_append hprefix tailTrace_5038797
  have hstable : (prefixWord ++ tailWord_5038797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038797).length < 2 ^ (prefixWord ++ tailWord_5038797).sum := by decide
  have hdescent : baseEnd_5038797 < baseStart_5038797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038846 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_5038846 : Nat := 118140960795 + 5038846 * 2 ^ 59
def prefixEnd_5038846 : Nat := 4983230072969 + 3 ^ 40 * 5038846 * 2
def baseEnd_5038846 : Nat := 2587349941985097725551775

theorem tailTrace_5038846 : CollatzResearch.WordTrace tailWord_5038846 prefixEnd_5038846 2587349941985097725551775 := by
  unfold tailWord_5038846
  simp only [CollatzResearch.WordTrace]
  refine ⟨22972726487891122903590049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122521207935419322152480261 22972726487891122903590049)
  ·
    refine ⟨17229544865918342177692537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22972726487891122903590049 17229544865918342177692537)
    ·
      refine ⟨12922158649438756633269403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17229544865918342177692537 12922158649438756633269403)
      ·
        refine ⟨19383237974158134949904105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12922158649438756633269403 19383237974158134949904105)
        ·
          refine ⟨14537428480618601212428079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19383237974158134949904105 14537428480618601212428079)
          ·
            refine ⟨21806142720927901818642119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14537428480618601212428079 21806142720927901818642119)
            ·
              refine ⟨32709214081391852727963179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21806142720927901818642119 32709214081391852727963179)
              ·
                refine ⟨49063821122087779091944769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32709214081391852727963179 49063821122087779091944769)
                ·
                  refine ⟨36797865841565834318958577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49063821122087779091944769 36797865841565834318958577)
                  ·
                    refine ⟨27598399381174375739218933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36797865841565834318958577 27598399381174375739218933)
                    ·
                      refine ⟨2587349941985097725551775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27598399381174375739218933 2587349941985097725551775)
                      ·
                        rfl

theorem cell23_5038846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_5038846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038846 prefixEnd_5038846 := by exact prefixLift 5038846
  have htrace : WordTrace (prefixWord ++ tailWord_5038846) baseStart_5038846 baseEnd_5038846 := by
    simpa [prefixWord, tailWord_5038846, baseEnd_5038846] using wordTrace_append hprefix tailTrace_5038846
  have hstable : (prefixWord ++ tailWord_5038846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038846).length < 2 ^ (prefixWord ++ tailWord_5038846).sum := by decide
  have hdescent : baseEnd_5038846 < baseStart_5038846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038859 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3]
def baseStart_5038859 : Nat := 118140960795 + 5038859 * 2 ^ 59
def prefixEnd_5038859 : Nat := 4983230072969 + 3 ^ 40 * 5038859 * 2
def baseEnd_5038859 : Nat := 2587356617233606174689215

theorem tailTrace_5038859 : CollatzResearch.WordTrace tailWord_5038859 prefixEnd_5038859 2587356617233606174689215 := by
  unfold tailWord_5038859
  simp only [CollatzResearch.WordTrace]
  refine ⟨183782286052081886448943631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122521524034721257632629087 183782286052081886448943631)
  ·
    refine ⟨275673429078122829673415447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183782286052081886448943631 275673429078122829673415447)
    ·
      refine ⟨413510143617184244510123171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275673429078122829673415447 413510143617184244510123171)
      ·
        refine ⟨620265215425776366765184757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413510143617184244510123171 620265215425776366765184757)
        ·
          refine ⟨58149863946166534384236071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 620265215425776366765184757 58149863946166534384236071)
          ·
            refine ⟨87224795919249801576354107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58149863946166534384236071 87224795919249801576354107)
            ·
              refine ⟨130837193878874702364531161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87224795919249801576354107 130837193878874702364531161)
              ·
                refine ⟨98127895409156026773398371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130837193878874702364531161 98127895409156026773398371)
                ·
                  refine ⟨147191843113734040160097557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98127895409156026773398371 147191843113734040160097557)
                  ·
                    refine ⟨6899617645956283132504573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147191843113734040160097557 6899617645956283132504573)
                    ·
                      refine ⟨2587356617233606174689215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899617645956283132504573 2587356617233606174689215)
                      ·
                        rfl

theorem cell23_5038859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 3].length) (baseStart_5038859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038859 prefixEnd_5038859 := by exact prefixLift 5038859
  have htrace : WordTrace (prefixWord ++ tailWord_5038859) baseStart_5038859 baseEnd_5038859 := by
    simpa [prefixWord, tailWord_5038859, baseEnd_5038859] using wordTrace_append hprefix tailTrace_5038859
  have hstable : (prefixWord ++ tailWord_5038859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038859).length < 2 ^ (prefixWord ++ tailWord_5038859).sum := by decide
  have hdescent : baseEnd_5038859 < baseStart_5038859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038884 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_5038884 : Nat := 118140960795 + 5038884 * 2 ^ 59
def prefixEnd_5038884 : Nat := 4983230072969 + 3 ^ 40 * 5038884 * 2
def baseEnd_5038884 : Nat := 2587369454249968576876601

theorem tailTrace_5038884 : CollatzResearch.WordTrace tailWord_5038884 prefixEnd_5038884 2587369454249968576876601 := by
  unfold tailWord_5038884
  simp only [CollatzResearch.WordTrace]
  refine ⟨91891598938495657859301853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122522131917994210479069137 91891598938495657859301853)
  ·
    refine ⟨34459349601935871697238195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91891598938495657859301853 34459349601935871697238195)
    ·
      refine ⟨51689024402903807545857293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34459349601935871697238195 51689024402903807545857293)
      ·
        refine ⟨19383384151088927829696485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51689024402903807545857293 19383384151088927829696485)
        ·
          refine ⟨3634384528329173968068091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19383384151088927829696485 3634384528329173968068091)
          ·
            refine ⟨5451576792493760952102137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634384528329173968068091 5451576792493760952102137)
            ·
              refine ⟨4088682594370320714076603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451576792493760952102137 4088682594370320714076603)
              ·
                refine ⟨6133023891555481071114905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088682594370320714076603 6133023891555481071114905)
                ·
                  refine ⟨4599767918666610803336179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6133023891555481071114905 4599767918666610803336179)
                  ·
                    refine ⟨6899651877999916205004269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4599767918666610803336179 6899651877999916205004269)
                    ·
                      refine ⟨2587369454249968576876601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899651877999916205004269 2587369454249968576876601)
                      ·
                        rfl

theorem cell23_5038884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_5038884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038884 prefixEnd_5038884 := by exact prefixLift 5038884
  have htrace : WordTrace (prefixWord ++ tailWord_5038884) baseStart_5038884 baseEnd_5038884 := by
    simpa [prefixWord, tailWord_5038884, baseEnd_5038884] using wordTrace_append hprefix tailTrace_5038884
  have hstable : (prefixWord ++ tailWord_5038884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038884).length < 2 ^ (prefixWord ++ tailWord_5038884).sum := by decide
  have hdescent : baseEnd_5038884 < baseStart_5038884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5038959 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_5038959 : Nat := 118140960795 + 5038959 * 2 ^ 59
def prefixEnd_5038959 : Nat := 4983230072969 + 3 ^ 40 * 5038959 * 2
def baseEnd_5038959 : Nat := 2587407965299055783438755

theorem tailTrace_5038959 : CollatzResearch.WordTrace tailWord_5038959 prefixEnd_5038959 2587407965299055783438755 := by
  unfold tailWord_5038959
  simp only [CollatzResearch.WordTrace]
  refine ⟨183785933351719603527583931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122523955567813069018389287 183785933351719603527583931)
  ·
    refine ⟨275678900027579405291375897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183785933351719603527583931 275678900027579405291375897)
    ·
      refine ⟨206759175020684553968531923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275678900027579405291375897 206759175020684553968531923)
      ·
        refine ⟨310138762531026830952797885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206759175020684553968531923 310138762531026830952797885)
        ·
          refine ⟨116302035949135061607299207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310138762531026830952797885 116302035949135061607299207)
          ·
            refine ⟨174453053923702592410948811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116302035949135061607299207 174453053923702592410948811)
            ·
              refine ⟨261679580885553888616423217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174453053923702592410948811 261679580885553888616423217)
              ·
                refine ⟨196259685664165416462317413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261679580885553888616423217 196259685664165416462317413)
                ·
                  refine ⟨36798691062031015586684515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196259685664165416462317413 36798691062031015586684515)
                  ·
                    refine ⟨55198036593046523380026773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36798691062031015586684515 55198036593046523380026773)
                    ·
                      refine ⟨2587407965299055783438755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55198036593046523380026773 2587407965299055783438755)
                      ·
                        rfl

theorem cell23_5038959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_5038959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5038959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5038959 prefixEnd_5038959 := by exact prefixLift 5038959
  have htrace : WordTrace (prefixWord ++ tailWord_5038959) baseStart_5038959 baseEnd_5038959 := by
    simpa [prefixWord, tailWord_5038959, baseEnd_5038959] using wordTrace_append hprefix tailTrace_5038959
  have hstable : (prefixWord ++ tailWord_5038959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5038959).length < 2 ^ (prefixWord ++ tailWord_5038959).sum := by decide
  have hdescent : baseEnd_5038959 < baseStart_5038959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5038959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039033 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_5039033 : Nat := 118140960795 + 5039033 * 2 ^ 59
def prefixEnd_5039033 : Nat := 4983230072969 + 3 ^ 40 * 5039033 * 2
def baseEnd_5039033 : Nat := 862481987622496164637805

theorem tailTrace_5039033 : CollatzResearch.WordTrace tailWord_5039033 prefixEnd_5039033 862481987622496164637805 := by
  unfold tailWord_5039033
  simp only [CollatzResearch.WordTrace]
  refine ⟨183788632353451514165777753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122525754902301009443851835 183788632353451514165777753)
  ·
    refine ⟨137841474265088635624333315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183788632353451514165777753 137841474265088635624333315)
    ·
      refine ⟨206762211397632953436499973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137841474265088635624333315 206762211397632953436499973)
      ·
        refine ⟨38767914637056178769343745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206762211397632953436499973 38767914637056178769343745)
        ·
          refine ⟨29075935977792134077007809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38767914637056178769343745 29075935977792134077007809)
          ·
            refine ⟨21806951983344100557755857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29075935977792134077007809 21806951983344100557755857)
            ·
              refine ⟨16355213987508075418316893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21806951983344100557755857 16355213987508075418316893)
              ·
                refine ⟨6133205245315528281868835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16355213987508075418316893 6133205245315528281868835)
                ·
                  refine ⟨9199807867973292422803253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6133205245315528281868835 9199807867973292422803253)
                  ·
                    refine ⟨862481987622496164637805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9199807867973292422803253 862481987622496164637805)
                    ·
                      rfl

theorem cell23_5039033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_5039033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039033 prefixEnd_5039033 := by exact prefixLift 5039033
  have htrace : WordTrace (prefixWord ++ tailWord_5039033) baseStart_5039033 baseEnd_5039033 := by
    simpa [prefixWord, tailWord_5039033, baseEnd_5039033] using wordTrace_append hprefix tailTrace_5039033
  have hstable : (prefixWord ++ tailWord_5039033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039033).length < 2 ^ (prefixWord ++ tailWord_5039033).sum := by decide
  have hdescent : baseEnd_5039033 < baseStart_5039033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039040 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2]
def baseStart_5039040 : Nat := 118140960795 + 5039040 * 2 ^ 59
def prefixEnd_5039040 : Nat := 4983230072969 + 3 ^ 40 * 5039040 * 2
def baseEnd_5039040 : Nat := 2587449557232069966525883

theorem tailTrace_5039040 : CollatzResearch.WordTrace tailWord_5039040 prefixEnd_5039040 2587449557232069966525883 := by
  unfold tailWord_5039040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91894443832213077180641287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122525925109617436240855049 91894443832213077180641287)
  ·
    refine ⟨137841665748319615770961931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91894443832213077180641287 137841665748319615770961931)
    ·
      refine ⟨206762498622479423656442897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137841665748319615770961931 206762498622479423656442897)
      ·
        refine ⟨155071873966859567742332173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206762498622479423656442897 155071873966859567742332173)
        ·
          refine ⟨58151952737572337903374565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155071873966859567742332173 58151952737572337903374565)
          ·
            refine ⟨10903491138294813356882731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58151952737572337903374565 10903491138294813356882731)
            ·
              refine ⟨16355236707442220035324097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10903491138294813356882731 16355236707442220035324097)
              ·
                refine ⟨12266427530581665026493073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16355236707442220035324097 12266427530581665026493073)
                ·
                  refine ⟨9199820647936248769869805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12266427530581665026493073 9199820647936248769869805)
                  ·
                    refine ⟨3449932742976093288701177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9199820647936248769869805 3449932742976093288701177)
                    ·
                      refine ⟨2587449557232069966525883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449932742976093288701177 2587449557232069966525883)
                      ·
                        rfl

theorem cell23_5039040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_5039040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039040 prefixEnd_5039040 := by exact prefixLift 5039040
  have htrace : WordTrace (prefixWord ++ tailWord_5039040) baseStart_5039040 baseEnd_5039040 := by
    simpa [prefixWord, tailWord_5039040, baseEnd_5039040] using wordTrace_append hprefix tailTrace_5039040
  have hstable : (prefixWord ++ tailWord_5039040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039040).length < 2 ^ (prefixWord ++ tailWord_5039040).sum := by decide
  have hdescent : baseEnd_5039040 < baseStart_5039040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039056 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_5039056 : Nat := 118140960795 + 5039056 * 2 ^ 59
def prefixEnd_5039056 : Nat := 4983230072969 + 3 ^ 40 * 5039056 * 2
def baseEnd_5039056 : Nat := 2587457772922541903925809

theorem tailTrace_5039056 : CollatzResearch.WordTrace tailWord_5039056 prefixEnd_5039056 2587457772922541903925809 := by
  unfold tailWord_5039056
  simp only [CollatzResearch.WordTrace]
  refine ⟨91894735616184094546932511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122526314154912126062576681 91894735616184094546932511)
  ·
    refine ⟨137842103424276141820398767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91894735616184094546932511 137842103424276141820398767)
    ·
      refine ⟨206763155136414212730598151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137842103424276141820398767 206763155136414212730598151)
      ·
        refine ⟨310144732704621319095897227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206763155136414212730598151 310144732704621319095897227)
        ·
          refine ⟨465217099056931978643845841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310144732704621319095897227 465217099056931978643845841)
          ·
            refine ⟨348912824292698983982884381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465217099056931978643845841 348912824292698983982884381)
            ·
              refine ⟨130842309109762118993581643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348912824292698983982884381 130842309109762118993581643)
              ·
                refine ⟨196263463664643178490372465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130842309109762118993581643 196263463664643178490372465)
                ·
                  refine ⟨147197597748482383867779349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196263463664643178490372465 147197597748482383867779349)
                  ·
                    refine ⟨6899887394460111743802157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147197597748482383867779349 6899887394460111743802157)
                    ·
                      refine ⟨2587457772922541903925809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6899887394460111743802157 2587457772922541903925809)
                      ·
                        rfl

theorem cell23_5039056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_5039056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039056 prefixEnd_5039056 := by exact prefixLift 5039056
  have htrace : WordTrace (prefixWord ++ tailWord_5039056) baseStart_5039056 baseEnd_5039056 := by
    simpa [prefixWord, tailWord_5039056, baseEnd_5039056] using wordTrace_append hprefix tailTrace_5039056
  have hstable : (prefixWord ++ tailWord_5039056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039056).length < 2 ^ (prefixWord ++ tailWord_5039056).sum := by decide
  have hdescent : baseEnd_5039056 < baseStart_5039056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039074 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5039074 : Nat := 118140960795 + 5039074 * 2 ^ 59
def prefixEnd_5039074 : Nat := 4983230072969 + 3 ^ 40 * 5039074 * 2
def baseEnd_5039074 : Nat := 2587467015574322833500727

theorem tailTrace_5039074 : CollatzResearch.WordTrace tailWord_5039074 prefixEnd_5039074 2587467015574322833500727 := by
  unfold tailWord_5039074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45947531936575744542005069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122526751830868652112013517 45947531936575744542005069)
  ·
    refine ⟨17230324476215904203251901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45947531936575744542005069 17230324476215904203251901)
    ·
      refine ⟨6461371678580964076219463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17230324476215904203251901 6461371678580964076219463)
      ·
        refine ⟨9692057517871446114329195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461371678580964076219463 9692057517871446114329195)
        ·
          refine ⟨14538086276807169171493793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9692057517871446114329195 14538086276807169171493793)
          ·
            refine ⟨10903564707605376878620345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14538086276807169171493793 10903564707605376878620345)
            ·
              refine ⟨8177673530704032658965259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10903564707605376878620345 8177673530704032658965259)
              ·
                refine ⟨12266510296056048988447889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8177673530704032658965259 12266510296056048988447889)
                ·
                  refine ⟨9199882722042036741335917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12266510296056048988447889 9199882722042036741335917)
                  ·
                    refine ⟨3449956020765763778000969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9199882722042036741335917 3449956020765763778000969)
                    ·
                      refine ⟨2587467015574322833500727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449956020765763778000969 2587467015574322833500727)
                      ·
                        rfl

theorem cell23_5039074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5039074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039074 prefixEnd_5039074 := by exact prefixLift 5039074
  have htrace : WordTrace (prefixWord ++ tailWord_5039074) baseStart_5039074 baseEnd_5039074 := by
    simpa [prefixWord, tailWord_5039074, baseEnd_5039074] using wordTrace_append hprefix tailTrace_5039074
  have hstable : (prefixWord ++ tailWord_5039074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039074).length < 2 ^ (prefixWord ++ tailWord_5039074).sum := by decide
  have hdescent : baseEnd_5039074 < baseStart_5039074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039092 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5039092 : Nat := 118140960795 + 5039092 * 2 ^ 59
def prefixEnd_5039092 : Nat := 4983230072969 + 3 ^ 40 * 5039092 * 2
def baseEnd_5039092 : Nat := 862492086075367921025215

theorem tailTrace_5039092 : CollatzResearch.WordTrace tailWord_5039092 prefixEnd_5039092 862492086075367921025215 := by
  unfold tailWord_5039092
  simp only [CollatzResearch.WordTrace]
  refine ⟨91895392130118883621087765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122527189506825178161450353 91895392130118883621087765)
  ·
    refine ⟨4307596506099322669738489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91895392130118883621087765 4307596506099322669738489)
    ·
      refine ⟨3230697379574492002303867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4307596506099322669738489 3230697379574492002303867)
      ·
        refine ⟨4846046069361738003455801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230697379574492002303867 4846046069361738003455801)
        ·
          refine ⟨3634534552021303502591851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4846046069361738003455801 3634534552021303502591851)
          ·
            refine ⟨5451801828031955253887777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634534552021303502591851 5451801828031955253887777)
            ·
              refine ⟨4088851371023966440415833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451801828031955253887777 4088851371023966440415833)
              ·
                refine ⟨3066638528267974830311875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088851371023966440415833 3066638528267974830311875)
                ·
                  refine ⟨4599957792401962245467813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066638528267974830311875 4599957792401962245467813)
                  ·
                    refine ⟨862492086075367921025215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4599957792401962245467813 862492086075367921025215)
                    ·
                      rfl

theorem cell23_5039092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5039092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039092 prefixEnd_5039092 := by exact prefixLift 5039092
  have htrace : WordTrace (prefixWord ++ tailWord_5039092) baseStart_5039092 baseEnd_5039092 := by
    simpa [prefixWord, tailWord_5039092, baseEnd_5039092] using wordTrace_append hprefix tailTrace_5039092
  have hstable : (prefixWord ++ tailWord_5039092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039092).length < 2 ^ (prefixWord ++ tailWord_5039092).sum := by decide
  have hdescent : baseEnd_5039092 < baseStart_5039092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039093 : List Nat := [1, 3, 5, 2, 12]
def baseStart_5039093 : Nat := 118140960795 + 5039093 * 2 ^ 59
def prefixEnd_5039093 : Nat := 4983230072969 + 3 ^ 40 * 5039093 * 2
def baseEnd_5039093 : Nat := 3549350852821341919291

theorem tailTrace_5039093 : CollatzResearch.WordTrace tailWord_5039093 prefixEnd_5039093 3549350852821341919291 := by
  unfold tailWord_5039093
  simp only [CollatzResearch.WordTrace]
  refine ⟨183790820733234144412961933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122527213822156096275307955 183790820733234144412961933)
  ·
    refine ⟨68921557774962804154860725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183790820733234144412961933 68921557774962804154860725)
    ·
      refine ⟨6461396041402762889518193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68921557774962804154860725 6461396041402762889518193)
      ·
        refine ⟨4846047031052072167138645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6461396041402762889518193 4846047031052072167138645)
        ·
          refine ⟨3549350852821341919291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4846047031052072167138645 3549350852821341919291)
          ·
            rfl

theorem cell23_5039093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 12].length) (baseStart_5039093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039093 prefixEnd_5039093 := by exact prefixLift 5039093
  have htrace : WordTrace (prefixWord ++ tailWord_5039093) baseStart_5039093 baseEnd_5039093 := by
    simpa [prefixWord, tailWord_5039093, baseEnd_5039093] using wordTrace_append hprefix tailTrace_5039093
  have hstable : (prefixWord ++ tailWord_5039093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039093).length < 2 ^ (prefixWord ++ tailWord_5039093).sum := by decide
  have hdescent : baseEnd_5039093 < baseStart_5039093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039130 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_5039130 : Nat := 118140960795 + 5039130 * 2 ^ 59
def prefixEnd_5039130 : Nat := 4983230072969 + 3 ^ 40 * 5039130 * 2
def baseEnd_5039130 : Nat := 2587495770490974614400469

theorem tailTrace_5039130 : CollatzResearch.WordTrace tailWord_5039130 prefixEnd_5039130 2587495770490974614400469 := by
  unfold tailWord_5039130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45948042558525024933014711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122528113489400066488039229 45948042558525024933014711)
  ·
    refine ⟨68922063837787537399522067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45948042558525024933014711 68922063837787537399522067)
    ·
      refine ⟨103383095756681306099283101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68922063837787537399522067 103383095756681306099283101)
      ·
        refine ⟨38768660908755489787231163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103383095756681306099283101 38768660908755489787231163)
        ·
          refine ⟨58152991363133234680846745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38768660908755489787231163 58152991363133234680846745)
          ·
            refine ⟨43614743522349926010635059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58152991363133234680846745 43614743522349926010635059)
            ·
              refine ⟨65422115283524889015952589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43614743522349926010635059 65422115283524889015952589)
              ·
                refine ⟨24533293231321833380982221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65422115283524889015952589 24533293231321833380982221)
                ·
                  refine ⟨9199984961745687517868333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24533293231321833380982221 9199984961745687517868333)
                  ·
                    refine ⟨3449994360654632819200625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9199984961745687517868333 3449994360654632819200625)
                    ·
                      refine ⟨2587495770490974614400469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3449994360654632819200625 2587495770490974614400469)
                      ·
                        rfl

theorem cell23_5039130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_5039130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039130 prefixEnd_5039130 := by exact prefixLift 5039130
  have htrace : WordTrace (prefixWord ++ tailWord_5039130) baseStart_5039130 baseEnd_5039130 := by
    simpa [prefixWord, tailWord_5039130, baseEnd_5039130] using wordTrace_append hprefix tailTrace_5039130
  have hstable : (prefixWord ++ tailWord_5039130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039130).length < 2 ^ (prefixWord ++ tailWord_5039130).sum := by decide
  have hdescent : baseEnd_5039130 < baseStart_5039130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039173 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_5039173 : Nat := 118140960795 + 5039173 * 2 ^ 59
def prefixEnd_5039173 : Nat := 4983230072969 + 3 ^ 40 * 5039173 * 2
def baseEnd_5039173 : Nat := 2587517850159117946162771

theorem tailTrace_5039173 : CollatzResearch.WordTrace tailWord_5039173 prefixEnd_5039173 2587517850159117946162771 := by
  unfold tailWord_5039173
  simp only [CollatzResearch.WordTrace]
  refine ⟨183793738572944318075874173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122529159048629545383916115 183793738572944318075874173)
  ·
    refine ⟨68922651964854119278452815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183793738572944318075874173 68922651964854119278452815)
    ·
      refine ⟨103383977947281178917679223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68922651964854119278452815 103383977947281178917679223)
      ·
        refine ⟨155075966920921768376518835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103383977947281178917679223 155075966920921768376518835)
        ·
          refine ⟨232613950381382652564778253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155075966920921768376518835 232613950381382652564778253)
          ·
            refine ⟨87230231393018494711791845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232613950381382652564778253 87230231393018494711791845)
            ·
              refine ⟨16355668386190967758460971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87230231393018494711791845 16355668386190967758460971)
              ·
                refine ⟨24533502579286451637691457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16355668386190967758460971 24533502579286451637691457)
                ·
                  refine ⟨18400126934464838728268593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24533502579286451637691457 18400126934464838728268593)
                  ·
                    refine ⟨13800095200848629046201445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18400126934464838728268593 13800095200848629046201445)
                    ·
                      refine ⟨2587517850159117946162771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13800095200848629046201445 2587517850159117946162771)
                      ·
                        rfl

theorem cell23_5039173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_5039173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039173 prefixEnd_5039173 := by exact prefixLift 5039173
  have htrace : WordTrace (prefixWord ++ tailWord_5039173) baseStart_5039173 baseEnd_5039173 := by
    simpa [prefixWord, tailWord_5039173, baseEnd_5039173] using wordTrace_append hprefix tailTrace_5039173
  have hstable : (prefixWord ++ tailWord_5039173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039173).length < 2 ^ (prefixWord ++ tailWord_5039173).sum := by decide
  have hdescent : baseEnd_5039173 < baseStart_5039173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039193 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_5039193 : Nat := 118140960795 + 5039193 * 2 ^ 59
def prefixEnd_5039193 : Nat := 4983230072969 + 3 ^ 40 * 5039193 * 2
def baseEnd_5039193 : Nat := 2587528119772207867912679

theorem tailTrace_5039193 : CollatzResearch.WordTrace tailWord_5039193 prefixEnd_5039193 2587528119772207867912679 := by
  unfold tailWord_5039193
  simp only [CollatzResearch.WordTrace]
  refine ⟨183794468032871861491602233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122529645355247907661068155 183794468032871861491602233)
  ·
    refine ⟨137845851024653896118701675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183794468032871861491602233 137845851024653896118701675)
    ·
      refine ⟨206768776536980844178052513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137845851024653896118701675 206768776536980844178052513)
      ·
        refine ⟨155076582402735633133539385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206768776536980844178052513 155076582402735633133539385)
        ·
          refine ⟨116307436802051724850154539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155076582402735633133539385 116307436802051724850154539)
          ·
            refine ⟨174461155203077587275231809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116307436802051724850154539 174461155203077587275231809)
            ·
              refine ⟨130845866402308190456423857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174461155203077587275231809 130845866402308190456423857)
              ·
                refine ⟨98134399801731142842317893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130845866402308190456423857 98134399801731142842317893)
                ·
                  refine ⟨18400199962824589282934605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98134399801731142842317893 18400199962824589282934605)
                  ·
                    refine ⟨6900074986059220981100477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18400199962824589282934605 6900074986059220981100477)
                    ·
                      refine ⟨2587528119772207867912679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900074986059220981100477 2587528119772207867912679)
                      ·
                        rfl

theorem cell23_5039193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_5039193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039193 prefixEnd_5039193 := by exact prefixLift 5039193
  have htrace : WordTrace (prefixWord ++ tailWord_5039193) baseStart_5039193 baseEnd_5039193 := by
    simpa [prefixWord, tailWord_5039193, baseEnd_5039193] using wordTrace_append hprefix tailTrace_5039193
  have hstable : (prefixWord ++ tailWord_5039193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039193).length < 2 ^ (prefixWord ++ tailWord_5039193).sum := by decide
  have hdescent : baseEnd_5039193 < baseStart_5039193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039197 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5039197 : Nat := 118140960795 + 5039197 * 2 ^ 59
def prefixEnd_5039197 : Nat := 4983230072969 + 3 ^ 40 * 5039197 * 2
def baseEnd_5039197 : Nat := 2587530173694825852262661

theorem tailTrace_5039197 : CollatzResearch.WordTrace tailWord_5039197 prefixEnd_5039197 2587530173694825852262661 := by
  unfold tailWord_5039197
  simp only [CollatzResearch.WordTrace]
  refine ⟨183794613924857370174747845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122529742616571580116498563 183794613924857370174747845)
  ·
    refine ⟨34461490110910756907765221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183794613924857370174747845 34461490110910756907765221)
    ·
      refine ⟨6461529395795766920205979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34461490110910756907765221 6461529395795766920205979)
      ·
        refine ⟨9692294093693650380308969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461529395795766920205979 9692294093693650380308969)
        ·
          refine ⟨7269220570270237785231727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9692294093693650380308969 7269220570270237785231727)
          ·
            refine ⟨10903830855405356677847591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269220570270237785231727 10903830855405356677847591)
            ·
              refine ⟨16355746283108035016771387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10903830855405356677847591 16355746283108035016771387)
              ·
                refine ⟨24533619424662052525157081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16355746283108035016771387 24533619424662052525157081)
                ·
                  refine ⟨18400214568496539393867811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24533619424662052525157081 18400214568496539393867811)
                  ·
                    refine ⟨27600321852744809090801717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18400214568496539393867811 27600321852744809090801717)
                    ·
                      refine ⟨2587530173694825852262661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27600321852744809090801717 2587530173694825852262661)
                      ·
                        rfl

theorem cell23_5039197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5039197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039197 prefixEnd_5039197 := by exact prefixLift 5039197
  have htrace : WordTrace (prefixWord ++ tailWord_5039197) baseStart_5039197 baseEnd_5039197 := by
    simpa [prefixWord, tailWord_5039197, baseEnd_5039197] using wordTrace_append hprefix tailTrace_5039197
  have hstable : (prefixWord ++ tailWord_5039197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039197).length < 2 ^ (prefixWord ++ tailWord_5039197).sum := by decide
  have hdescent : baseEnd_5039197 < baseStart_5039197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039223 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_5039223 : Nat := 118140960795 + 5039223 * 2 ^ 59
def prefixEnd_5039223 : Nat := 4983230072969 + 3 ^ 40 * 5039223 * 2
def baseEnd_5039223 : Nat := 2587543524191842750537541

theorem tailTrace_5039223 : CollatzResearch.WordTrace tailWord_5039223 prefixEnd_5039223 2587543524191842750537541 := by
  unfold tailWord_5039223
  simp only [CollatzResearch.WordTrace]
  refine ⟨183795562222763176615194323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122530374815175451076796215 183795562222763176615194323)
  ·
    refine ⟨275693343334144764922791485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183795562222763176615194323 275693343334144764922791485)
    ·
      refine ⟨103385003750304286846046807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275693343334144764922791485 103385003750304286846046807)
      ·
        refine ⟨155077505625456430269070211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103385003750304286846046807 155077505625456430269070211)
        ·
          refine ⟨232616258438184645403605317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155077505625456430269070211 232616258438184645403605317)
          ·
            refine ⟨43615548457159621013175997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232616258438184645403605317 43615548457159621013175997)
            ·
              refine ⟨16355830671434857879940999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43615548457159621013175997 16355830671434857879940999)
              ·
                refine ⟨24533746007152286819911499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16355830671434857879940999 24533746007152286819911499)
                ·
                  refine ⟨36800619010728430229867249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24533746007152286819911499 36800619010728430229867249)
                  ·
                    refine ⟨27600464258046322672400437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36800619010728430229867249 27600464258046322672400437)
                    ·
                      refine ⟨2587543524191842750537541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27600464258046322672400437 2587543524191842750537541)
                      ·
                        rfl

theorem cell23_5039223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_5039223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039223 prefixEnd_5039223 := by exact prefixLift 5039223
  have htrace : WordTrace (prefixWord ++ tailWord_5039223) baseStart_5039223 baseEnd_5039223 := by
    simpa [prefixWord, tailWord_5039223, baseEnd_5039223] using wordTrace_append hprefix tailTrace_5039223
  have hstable : (prefixWord ++ tailWord_5039223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039223).length < 2 ^ (prefixWord ++ tailWord_5039223).sum := by decide
  have hdescent : baseEnd_5039223 < baseStart_5039223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039298 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5039298 : Nat := 118140960795 + 5039298 * 2 ^ 59
def prefixEnd_5039298 : Nat := 4983230072969 + 3 ^ 40 * 5039298 * 2
def baseEnd_5039298 : Nat := 862527345080309985699899

theorem tailTrace_5039298 : CollatzResearch.WordTrace tailWord_5039298 prefixEnd_5039298 862527345080309985699899 := by
  unfold tailWord_5039298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45949574424372866106043637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122532198464994309616116365 45949574424372866106043637)
  ·
    refine ⟨4307772602284956197441591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45949574424372866106043637 4307772602284956197441591)
    ·
      refine ⟨6461658903427434296162387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4307772602284956197441591 6461658903427434296162387)
      ·
        refine ⟨9692488355141151444243581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461658903427434296162387 9692488355141151444243581)
        ·
          refine ⟨3634683133177931791591343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9692488355141151444243581 3634683133177931791591343)
          ·
            refine ⟨5452024699766897687387015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634683133177931791591343 5452024699766897687387015)
            ·
              refine ⟨8178037049650346531080523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452024699766897687387015 8178037049650346531080523)
              ·
                refine ⟨12267055574475519796620785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8178037049650346531080523 12267055574475519796620785)
                ·
                  refine ⟨9200291680856639847465589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12267055574475519796620785 9200291680856639847465589)
                  ·
                    refine ⟨862527345080309985699899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9200291680856639847465589 862527345080309985699899)
                    ·
                      rfl

theorem cell23_5039298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5039298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039298 prefixEnd_5039298 := by exact prefixLift 5039298
  have htrace : WordTrace (prefixWord ++ tailWord_5039298) baseStart_5039298 baseEnd_5039298 := by
    simpa [prefixWord, tailWord_5039298, baseEnd_5039298] using wordTrace_append hprefix tailTrace_5039298
  have hstable : (prefixWord ++ tailWord_5039298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039298).length < 2 ^ (prefixWord ++ tailWord_5039298).sum := by decide
  have hdescent : baseEnd_5039298 < baseStart_5039298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039313 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_5039313 : Nat := 118140960795 + 5039313 * 2 ^ 59
def prefixEnd_5039313 : Nat := 4983230072969 + 3 ^ 40 * 5039313 * 2
def baseEnd_5039313 : Nat := 2587589737450747398412127

theorem tailTrace_5039313 : CollatzResearch.WordTrace tailWord_5039313 prefixEnd_5039313 2587589737450747398412127 := by
  unfold tailWord_5039313
  simp only [CollatzResearch.WordTrace]
  refine ⟨183798844792437121985970593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122532563194958081323980395 183798844792437121985970593)
  ·
    refine ⟨137849133594327841489477945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183798844792437121985970593 137849133594327841489477945)
    ·
      refine ⟨103386850195745881117108459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137849133594327841489477945 103386850195745881117108459)
      ·
        refine ⟨155080275293618821675662689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103386850195745881117108459 155080275293618821675662689)
        ·
          refine ⟨116310206470214116256747017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155080275293618821675662689 116310206470214116256747017)
          ·
            refine ⟨87232654852660587192560263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116310206470214116256747017 87232654852660587192560263)
            ·
              refine ⟨130848982278990880788840395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87232654852660587192560263 130848982278990880788840395)
              ·
                refine ⟨196273473418486321183260593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130848982278990880788840395 196273473418486321183260593)
                ·
                  refine ⟨147205105063864740887445445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196273473418486321183260593 147205105063864740887445445)
                  ·
                    refine ⟨27600957199474638916396021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147205105063864740887445445 27600957199474638916396021)
                    ·
                      refine ⟨2587589737450747398412127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27600957199474638916396021 2587589737450747398412127)
                      ·
                        rfl

theorem cell23_5039313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_5039313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039313 prefixEnd_5039313 := by exact prefixLift 5039313
  have htrace : WordTrace (prefixWord ++ tailWord_5039313) baseStart_5039313 baseEnd_5039313 := by
    simpa [prefixWord, tailWord_5039313, baseEnd_5039313] using wordTrace_append hprefix tailTrace_5039313
  have hstable : (prefixWord ++ tailWord_5039313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039313).length < 2 ^ (prefixWord ++ tailWord_5039313).sum := by decide
  have hdescent : baseEnd_5039313 < baseStart_5039313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039323 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_5039323 : Nat := 118140960795 + 5039323 * 2 ^ 59
def prefixEnd_5039323 : Nat := 4983230072969 + 3 ^ 40 * 5039323 * 2
def baseEnd_5039323 : Nat := 2587594872257292359287081

theorem tailTrace_5039323 : CollatzResearch.WordTrace tailWord_5039323 prefixEnd_5039323 2587594872257292359287081 := by
  unfold tailWord_5039323
  simp only [CollatzResearch.WordTrace]
  refine ⟨183799209522400893693834623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122532806348267262462556415 183799209522400893693834623)
  ·
    refine ⟨275698814283601340540751935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183799209522400893693834623 275698814283601340540751935)
    ·
      refine ⟨413548221425402010811127903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275698814283601340540751935 413548221425402010811127903)
      ·
        refine ⟨620322332138103016216691855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413548221425402010811127903 620322332138103016216691855)
        ·
          refine ⟨930483498207154524325037783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620322332138103016216691855 930483498207154524325037783)
          ·
            refine ⟨1395725247310731786487556675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930483498207154524325037783 1395725247310731786487556675)
            ·
              refine ⟨2093587870966097679731335013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395725247310731786487556675 2093587870966097679731335013)
              ·
                refine ⟨392547725806143314949625315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2093587870966097679731335013 392547725806143314949625315)
                ·
                  refine ⟨588821588709214972424437973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392547725806143314949625315 588821588709214972424437973)
                  ·
                    refine ⟨13800505985372225916197765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 588821588709214972424437973 13800505985372225916197765)
                    ·
                      refine ⟨2587594872257292359287081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13800505985372225916197765 2587594872257292359287081)
                      ·
                        rfl

theorem cell23_5039323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_5039323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039323 prefixEnd_5039323 := by exact prefixLift 5039323
  have htrace : WordTrace (prefixWord ++ tailWord_5039323) baseStart_5039323 baseEnd_5039323 := by
    simpa [prefixWord, tailWord_5039323, baseEnd_5039323] using wordTrace_append hprefix tailTrace_5039323
  have hstable : (prefixWord ++ tailWord_5039323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039323).length < 2 ^ (prefixWord ++ tailWord_5039323).sum := by decide
  have hdescent : baseEnd_5039323 < baseStart_5039323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039327 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 2, 3, 2]
def baseStart_5039327 : Nat := 118140960795 + 5039327 * 2 ^ 59
def prefixEnd_5039327 : Nat := 4983230072969 + 3 ^ 40 * 5039327 * 2
def baseEnd_5039327 : Nat := 2587596926179910343637063

theorem tailTrace_5039327 : CollatzResearch.WordTrace tailWord_5039327 prefixEnd_5039327 2587596926179910343637063 := by
  unfold tailWord_5039327
  simp only [CollatzResearch.WordTrace]
  refine ⟨183799355414386402376980235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122532903609590934917986823 183799355414386402376980235)
  ·
    refine ⟨275699033121579603565470353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183799355414386402376980235 275699033121579603565470353)
    ·
      refine ⟨206774274841184702674102765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275699033121579603565470353 206774274841184702674102765)
      ·
        refine ⟨77540353065444263502788537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206774274841184702674102765 77540353065444263502788537)
        ·
          refine ⟨58155264799083197627091403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77540353065444263502788537 58155264799083197627091403)
          ·
            refine ⟨87232897198624796440637105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58155264799083197627091403 87232897198624796440637105)
            ·
              refine ⟨65424672898968597330477829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87232897198624796440637105 65424672898968597330477829)
              ·
                refine ⟨12267126168556611999464593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65424672898968597330477829 12267126168556611999464593)
                ·
                  refine ⟨9200344626417458999598445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12267126168556611999464593 9200344626417458999598445)
                  ·
                    refine ⟨3450129234906547124849417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9200344626417458999598445 3450129234906547124849417)
                    ·
                      refine ⟨2587596926179910343637063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450129234906547124849417 2587596926179910343637063)
                      ·
                        rfl

theorem cell23_5039327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_5039327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039327 prefixEnd_5039327 := by exact prefixLift 5039327
  have htrace : WordTrace (prefixWord ++ tailWord_5039327) baseStart_5039327 baseEnd_5039327 := by
    simpa [prefixWord, tailWord_5039327, baseEnd_5039327] using wordTrace_append hprefix tailTrace_5039327
  have hstable : (prefixWord ++ tailWord_5039327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039327).length < 2 ^ (prefixWord ++ tailWord_5039327).sum := by decide
  have hdescent : baseEnd_5039327 < baseStart_5039327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039368 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_5039368 : Nat := 118140960795 + 5039368 * 2 ^ 59
def prefixEnd_5039368 : Nat := 4983230072969 + 3 ^ 40 * 5039368 * 2
def baseEnd_5039368 : Nat := 2587617978886744683224375

theorem tailTrace_5039368 : CollatzResearch.WordTrace tailWord_5039368 prefixEnd_5039368 2587617978886744683224375 := by
  unfold tailWord_5039368
  simp only [CollatzResearch.WordTrace]
  refine ⟨91900425403618933189611379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122533900538158577586148505 91900425403618933189611379)
  ·
    refine ⟨137850638105428399784417069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91900425403618933189611379 137850638105428399784417069)
    ·
      refine ⟨51693989289535649919156401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137850638105428399784417069 51693989289535649919156401)
      ·
        refine ⟨38770491967151737439367301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51693989289535649919156401 38770491967151737439367301)
        ·
          refine ⟨7269467243840950769881369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38770491967151737439367301 7269467243840950769881369)
          ·
            refine ⟨5452100432880713077411027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7269467243840950769881369 5452100432880713077411027)
            ·
              refine ⟨8178150649321069616116541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452100432880713077411027 8178150649321069616116541)
              ·
                refine ⟨3066806493495401106043703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8178150649321069616116541 3066806493495401106043703)
                ·
                  refine ⟨4600209740243101659065555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3066806493495401106043703 4600209740243101659065555)
                  ·
                    refine ⟨6900314610364652488598333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4600209740243101659065555 6900314610364652488598333)
                    ·
                      refine ⟨2587617978886744683224375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900314610364652488598333 2587617978886744683224375)
                      ·
                        rfl

theorem cell23_5039368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_5039368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039368 prefixEnd_5039368 := by exact prefixLift 5039368
  have htrace : WordTrace (prefixWord ++ tailWord_5039368) baseStart_5039368 baseEnd_5039368 := by
    simpa [prefixWord, tailWord_5039368, baseEnd_5039368] using wordTrace_append hprefix tailTrace_5039368
  have hstable : (prefixWord ++ tailWord_5039368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039368).length < 2 ^ (prefixWord ++ tailWord_5039368).sum := by decide
  have hdescent : baseEnd_5039368 < baseStart_5039368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039370 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5039370 : Nat := 118140960795 + 5039370 * 2 ^ 59
def prefixEnd_5039370 : Nat := 4983230072969 + 3 ^ 40 * 5039370 * 2
def baseEnd_5039370 : Nat := 2587619005848053675399365

theorem tailTrace_5039370 : CollatzResearch.WordTrace tailWord_5039370 prefixEnd_5039370 2587619005848053675399365 := by
  unfold tailWord_5039370
  simp only [CollatzResearch.WordTrace]
  refine ⟨45950230938307655180198891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122533949168820413813863709 45950230938307655180198891)
  ·
    refine ⟨68925346407461482770298337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45950230938307655180198891 68925346407461482770298337)
    ·
      refine ⟨51694009805596112077723753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68925346407461482770298337 51694009805596112077723753)
      ·
        refine ⟨38770507354197084058292815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51694009805596112077723753 38770507354197084058292815)
        ·
          refine ⟨58155761031295626087439223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38770507354197084058292815 58155761031295626087439223)
          ·
            refine ⟨87233641546943439131158835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58155761031295626087439223 87233641546943439131158835)
            ·
              refine ⟨130850462320415158696738253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87233641546943439131158835 130850462320415158696738253)
              ·
                refine ⟨49068923370155684511276845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130850462320415158696738253 49068923370155684511276845)
                ·
                  refine ⟨18400846263808381691728817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49068923370155684511276845 18400846263808381691728817)
                  ·
                    refine ⟨13800634697856286268796613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18400846263808381691728817 13800634697856286268796613)
                    ·
                      refine ⟨2587619005848053675399365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13800634697856286268796613 2587619005848053675399365)
                      ·
                        rfl

theorem cell23_5039370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5039370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039370 prefixEnd_5039370 := by exact prefixLift 5039370
  have htrace : WordTrace (prefixWord ++ tailWord_5039370) baseStart_5039370 baseEnd_5039370 := by
    simpa [prefixWord, tailWord_5039370, baseEnd_5039370] using wordTrace_append hprefix tailTrace_5039370
  have hstable : (prefixWord ++ tailWord_5039370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039370).length < 2 ^ (prefixWord ++ tailWord_5039370).sum := by decide
  have hdescent : baseEnd_5039370 < baseStart_5039370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039377 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_5039377 : Nat := 118140960795 + 5039377 * 2 ^ 59
def prefixEnd_5039377 : Nat := 4983230072969 + 3 ^ 40 * 5039377 * 2
def baseEnd_5039377 : Nat := 2587622600212635148011833

theorem tailTrace_5039377 : CollatzResearch.WordTrace tailWord_5039377 prefixEnd_5039377 2587622600212635148011833 := by
  unfold tailWord_5039377
  simp only [CollatzResearch.WordTrace]
  refine ⟨183801179064205260916300385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122534119376136840610866923 183801179064205260916300385)
  ·
    refine ⟨137850884298153945687225289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183801179064205260916300385 137850884298153945687225289)
    ·
      refine ⟨103388163223615459265418967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137850884298153945687225289 103388163223615459265418967)
      ·
        refine ⟨155082244835423188898128451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103388163223615459265418967 155082244835423188898128451)
        ·
          refine ⟨232623367253134783347192677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155082244835423188898128451 232623367253134783347192677)
          ·
            refine ⟨43616881359962771877598627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232623367253134783347192677 43616881359962771877598627)
            ·
              refine ⟨65425322039944157816397941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43616881359962771877598627 65425322039944157816397941)
              ·
                refine ⟨6133623941244764795287307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65425322039944157816397941 6133623941244764795287307)
                ·
                  refine ⟨9200435911867147192930961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6133623941244764795287307 9200435911867147192930961)
                  ·
                    refine ⟨6900326933900360394698221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9200435911867147192930961 6900326933900360394698221)
                    ·
                      refine ⟨2587622600212635148011833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900326933900360394698221 2587622600212635148011833)
                      ·
                        rfl

theorem cell23_5039377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_5039377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039377 prefixEnd_5039377 := by exact prefixLift 5039377
  have htrace : WordTrace (prefixWord ++ tailWord_5039377) baseStart_5039377 baseEnd_5039377 := by
    simpa [prefixWord, tailWord_5039377, baseEnd_5039377] using wordTrace_append hprefix tailTrace_5039377
  have hstable : (prefixWord ++ tailWord_5039377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039377).length < 2 ^ (prefixWord ++ tailWord_5039377).sum := by decide
  have hdescent : baseEnd_5039377 < baseStart_5039377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039378 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5039378 : Nat := 118140960795 + 5039378 * 2 ^ 59
def prefixEnd_5039378 : Nat := 4983230072969 + 3 ^ 40 * 5039378 * 2
def baseEnd_5039378 : Nat := 2587623113693289644099329

theorem tailTrace_5039378 : CollatzResearch.WordTrace tailWord_5039378 prefixEnd_5039378 2587623113693289644099329 := by
  unfold tailWord_5039378
  simp only [CollatzResearch.WordTrace]
  refine ⟨45950303884300409521771697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122534143691467758724724525 45950303884300409521771697)
  ·
    refine ⟨34462727913225307141328773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45950303884300409521771697 34462727913225307141328773)
    ·
      refine ⟨6461761483729745088999145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34462727913225307141328773 6461761483729745088999145)
      ·
        refine ⟨4846321112797308816749359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6461761483729745088999145 4846321112797308816749359)
        ·
          refine ⟨7269481669195963225124039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846321112797308816749359 7269481669195963225124039)
          ·
            refine ⟨10904222503793944837686059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269481669195963225124039 10904222503793944837686059)
            ·
              refine ⟨16356333755690917256529089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10904222503793944837686059 16356333755690917256529089)
              ·
                refine ⟨12267250316768187942396817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16356333755690917256529089 12267250316768187942396817)
                ·
                  refine ⟨9200437737576140956797613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12267250316768187942396817 9200437737576140956797613)
                  ·
                    refine ⟨3450164151591052858799105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9200437737576140956797613 3450164151591052858799105)
                    ·
                      refine ⟨2587623113693289644099329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450164151591052858799105 2587623113693289644099329)
                      ·
                        rfl

theorem cell23_5039378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5039378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039378 prefixEnd_5039378 := by exact prefixLift 5039378
  have htrace : WordTrace (prefixWord ++ tailWord_5039378) baseStart_5039378 baseEnd_5039378 := by
    simpa [prefixWord, tailWord_5039378, baseEnd_5039378] using wordTrace_append hprefix tailTrace_5039378
  have hstable : (prefixWord ++ tailWord_5039378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039378).length < 2 ^ (prefixWord ++ tailWord_5039378).sum := by decide
  have hdescent : baseEnd_5039378 < baseStart_5039378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039428 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5039428 : Nat := 118140960795 + 5039428 * 2 ^ 59
def prefixEnd_5039428 : Nat := 4983230072969 + 3 ^ 40 * 5039428 * 2
def baseEnd_5039428 : Nat := 2587648787726014448474099

theorem tailTrace_5039428 : CollatzResearch.WordTrace tailWord_5039428 prefixEnd_5039428 2587648787726014448474099 := by
  unfold tailWord_5039428
  simp only [CollatzResearch.WordTrace]
  refine ⟨91901519593510248313203469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122535359458013664417604625 91901519593510248313203469)
  ·
    refine ⟨34463069847566343117451301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91901519593510248313203469 34463069847566343117451301)
    ·
      refine ⟨6461825596418689334522119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34463069847566343117451301 6461825596418689334522119)
      ·
        refine ⟨9692738394628034001783179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6461825596418689334522119 9692738394628034001783179)
        ·
          refine ⟨14539107591942051002674769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9692738394628034001783179 14539107591942051002674769)
          ·
            refine ⟨10904330693956538252006077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14539107591942051002674769 10904330693956538252006077)
            ·
              refine ⟨4089124010233701844502279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10904330693956538252006077 4089124010233701844502279)
              ·
                refine ⟨6133686015350552766753419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089124010233701844502279 6133686015350552766753419)
                ·
                  refine ⟨9200529023025829150130129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6133686015350552766753419 9200529023025829150130129)
                  ·
                    refine ⟨6900396767269371862597597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9200529023025829150130129 6900396767269371862597597)
                    ·
                      refine ⟨2587648787726014448474099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900396767269371862597597 2587648787726014448474099)
                      ·
                        rfl

theorem cell23_5039428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5039428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039428 prefixEnd_5039428 := by exact prefixLift 5039428
  have htrace : WordTrace (prefixWord ++ tailWord_5039428) baseStart_5039428 baseEnd_5039428 := by
    simpa [prefixWord, tailWord_5039428, baseEnd_5039428] using wordTrace_append hprefix tailTrace_5039428
  have hstable : (prefixWord ++ tailWord_5039428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039428).length < 2 ^ (prefixWord ++ tailWord_5039428).sum := by decide
  have hdescent : baseEnd_5039428 < baseStart_5039428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039434 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_5039434 : Nat := 118140960795 + 5039434 * 2 ^ 59
def prefixEnd_5039434 : Nat := 4983230072969 + 3 ^ 40 * 5039434 * 2
def baseEnd_5039434 : Nat := 2587651868609941424999071

theorem tailTrace_5039434 : CollatzResearch.WordTrace tailWord_5039434 prefixEnd_5039434 2587651868609941424999071 := by
  unfold tailWord_5039434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45950814506249689912781339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122535505349999173100750237 45950814506249689912781339)
  ·
    refine ⟨68926221759374534869172009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45950814506249689912781339 68926221759374534869172009)
    ·
      refine ⟨51694666319530901151879007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68926221759374534869172009 51694666319530901151879007)
      ·
        refine ⟨77541999479296351727818511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51694666319530901151879007 77541999479296351727818511)
        ·
          refine ⟨116312999218944527591727767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77541999479296351727818511 116312999218944527591727767)
          ·
            refine ⟨174469498828416791387591651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116312999218944527591727767 174469498828416791387591651)
            ·
              refine ⟨261704248242625187081387477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174469498828416791387591651 261704248242625187081387477)
              ·
                refine ⟨6133693318186527822220019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 261704248242625187081387477 6133693318186527822220019)
                ·
                  refine ⟨9200539977279791733330029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6133693318186527822220019 9200539977279791733330029)
                  ·
                    refine ⟨3450202491479921899998761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9200539977279791733330029 3450202491479921899998761)
                    ·
                      refine ⟨2587651868609941424999071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450202491479921899998761 2587651868609941424999071)
                      ·
                        rfl

theorem cell23_5039434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_5039434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039434 prefixEnd_5039434 := by exact prefixLift 5039434
  have htrace : WordTrace (prefixWord ++ tailWord_5039434) baseStart_5039434 baseEnd_5039434 := by
    simpa [prefixWord, tailWord_5039434, baseEnd_5039434] using wordTrace_append hprefix tailTrace_5039434
  have hstable : (prefixWord ++ tailWord_5039434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039434).length < 2 ^ (prefixWord ++ tailWord_5039434).sum := by decide
  have hdescent : baseEnd_5039434 < baseStart_5039434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039440 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_5039440 : Nat := 118140960795 + 5039440 * 2 ^ 59
def prefixEnd_5039440 : Nat := 4983230072969 + 3 ^ 40 * 5039440 * 2
def baseEnd_5039440 : Nat := 862551649831289467174681

theorem tailTrace_5039440 : CollatzResearch.WordTrace tailWord_5039440 prefixEnd_5039440 862551649831289467174681 := by
  unfold tailWord_5039440
  simp only [CollatzResearch.WordTrace]
  refine ⟨91901738431488511337921887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122535651241984681783895849 91901738431488511337921887)
  ·
    refine ⟨137852607647232767006882831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91901738431488511337921887 137852607647232767006882831)
    ·
      refine ⟨206778911470849150510324247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137852607647232767006882831 206778911470849150510324247)
      ·
        refine ⟨310168367206273725765486371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206778911470849150510324247 310168367206273725765486371)
        ·
          refine ⟨465252550809410588648229557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310168367206273725765486371 465252550809410588648229557)
          ·
            refine ⟨43617426638382242685771521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 465252550809410588648229557 43617426638382242685771521)
            ·
              refine ⟨32713069978786682014328641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43617426638382242685771521 32713069978786682014328641)
              ·
                refine ⟨24534802484090011510746481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32713069978786682014328641 24534802484090011510746481)
                ·
                  refine ⟨18401101863067508633059861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24534802484090011510746481 18401101863067508633059861)
                  ·
                    refine ⟨862551649831289467174681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18401101863067508633059861 862551649831289467174681)
                    ·
                      rfl

theorem cell23_5039440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_5039440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039440 prefixEnd_5039440 := by exact prefixLift 5039440
  have htrace : WordTrace (prefixWord ++ tailWord_5039440) baseStart_5039440 baseEnd_5039440 := by
    simpa [prefixWord, tailWord_5039440, baseEnd_5039440] using wordTrace_append hprefix tailTrace_5039440
  have hstable : (prefixWord ++ tailWord_5039440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039440).length < 2 ^ (prefixWord ++ tailWord_5039440).sum := by decide
  have hdescent : baseEnd_5039440 < baseStart_5039440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039450 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_5039450 : Nat := 118140960795 + 5039450 * 2 ^ 59
def prefixEnd_5039450 : Nat := 4983230072969 + 3 ^ 40 * 5039450 * 2
def baseEnd_5039450 : Nat := 2587660084300413362398997

theorem tailTrace_5039450 : CollatzResearch.WordTrace tailWord_5039450 prefixEnd_5039450 2587660084300413362398997 := by
  unfold tailWord_5039450
  simp only [CollatzResearch.WordTrace]
  refine ⟨45950960398235198595926951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122535894395293862922471869 45950960398235198595926951)
  ·
    refine ⟨68926440597352797893890427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45950960398235198595926951 68926440597352797893890427)
    ·
      refine ⟨103389660896029196840835641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68926440597352797893890427 103389660896029196840835641)
      ·
        refine ⟨77542245672021897630626731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103389660896029196840835641 77542245672021897630626731)
        ·
          refine ⟨116313368508032846445940097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77542245672021897630626731 116313368508032846445940097)
          ·
            refine ⟨87235026381024634834455073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116313368508032846445940097 87235026381024634834455073)
            ·
              refine ⟨65426269785768476125841305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87235026381024634834455073 65426269785768476125841305)
              ·
                refine ⟨49069702339326357094380979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65426269785768476125841305 49069702339326357094380979)
                ·
                  refine ⟨73604553508989535641571469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49069702339326357094380979 73604553508989535641571469)
                  ·
                    refine ⟨27601707565871075865589301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73604553508989535641571469 27601707565871075865589301)
                    ·
                      refine ⟨2587660084300413362398997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27601707565871075865589301 2587660084300413362398997)
                      ·
                        rfl

theorem cell23_5039450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_5039450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039450 prefixEnd_5039450 := by exact prefixLift 5039450
  have htrace : WordTrace (prefixWord ++ tailWord_5039450) baseStart_5039450 baseEnd_5039450 := by
    simpa [prefixWord, tailWord_5039450, baseEnd_5039450] using wordTrace_append hprefix tailTrace_5039450
  have hstable : (prefixWord ++ tailWord_5039450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039450).length < 2 ^ (prefixWord ++ tailWord_5039450).sum := by decide
  have hdescent : baseEnd_5039450 < baseStart_5039450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039517 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_5039517 : Nat := 118140960795 + 5039517 * 2 ^ 59
def prefixEnd_5039517 : Nat := 4983230072969 + 3 ^ 40 * 5039517 * 2
def baseEnd_5039517 : Nat := 862564829168088200087063

theorem tailTrace_5039517 : CollatzResearch.WordTrace tailWord_5039517 prefixEnd_5039517 862564829168088200087063 := by
  unfold tailWord_5039517
  simp only [CollatzResearch.WordTrace]
  refine ⟨183806285283698064826396805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122537523522465376550931203 183806285283698064826396805)
  ·
    refine ⟨34463678490693387154949401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183806285283698064826396805 34463678490693387154949401)
    ·
      refine ⟨25847758868020040366212051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34463678490693387154949401 25847758868020040366212051)
      ·
        refine ⟨38771638302030060549318077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25847758868020040366212051 38771638302030060549318077)
        ·
          refine ⟨14539364363261272705994279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38771638302030060549318077 14539364363261272705994279)
          ·
            refine ⟨21809046544891909058991419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14539364363261272705994279 21809046544891909058991419)
            ·
              refine ⟨32713569817337863588487129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21809046544891909058991419 32713569817337863588487129)
              ·
                refine ⟨24535177363003397691365347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32713569817337863588487129 24535177363003397691365347)
                ·
                  refine ⟨36802766044505096537048021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24535177363003397691365347 36802766044505096537048021)
                  ·
                    refine ⟨862564829168088200087063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36802766044505096537048021 862564829168088200087063)
                    ·
                      rfl

theorem cell23_5039517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_5039517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039517 prefixEnd_5039517 := by exact prefixLift 5039517
  have htrace : WordTrace (prefixWord ++ tailWord_5039517) baseStart_5039517 baseEnd_5039517 := by
    simpa [prefixWord, tailWord_5039517, baseEnd_5039517] using wordTrace_append hprefix tailTrace_5039517
  have hstable : (prefixWord ++ tailWord_5039517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039517).length < 2 ^ (prefixWord ++ tailWord_5039517).sum := by decide
  have hdescent : baseEnd_5039517 < baseStart_5039517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039537 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5039537 : Nat := 118140960795 + 5039537 * 2 ^ 59
def prefixEnd_5039537 : Nat := 4983230072969 + 3 ^ 40 * 5039537 * 2
def baseEnd_5039537 : Nat := 2587704757117354522011097

theorem tailTrace_5039537 : CollatzResearch.WordTrace tailWord_5039537 prefixEnd_5039537 2587704757117354522011097 := by
  unfold tailWord_5039537
  simp only [CollatzResearch.WordTrace]
  refine ⟨183807014743625608242124865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122538009829083738828083243 183807014743625608242124865)
  ·
    refine ⟨137855261057719206181593649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183807014743625608242124865 137855261057719206181593649)
    ·
      refine ⟨103391445793289404636195237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137855261057719206181593649 103391445793289404636195237)
      ·
        refine ⟨19385896086241763369286607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103391445793289404636195237 19385896086241763369286607)
        ·
          refine ⟨29078844129362645053929911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19385896086241763369286607 29078844129362645053929911)
          ·
            refine ⟨43618266194043967580894867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29078844129362645053929911 43618266194043967580894867)
            ·
              refine ⟨65427399291065951371342301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43618266194043967580894867 65427399291065951371342301)
              ·
                refine ⟨24535274734149731764253363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65427399291065951371342301 24535274734149731764253363)
                ·
                  refine ⟨36802912101224597646380045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24535274734149731764253363 36802912101224597646380045)
                  ·
                    refine ⟨13801092037959224117392517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36802912101224597646380045 13801092037959224117392517)
                    ·
                      refine ⟨2587704757117354522011097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13801092037959224117392517 2587704757117354522011097)
                      ·
                        rfl

theorem cell23_5039537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5039537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039537 prefixEnd_5039537 := by exact prefixLift 5039537
  have htrace : WordTrace (prefixWord ++ tailWord_5039537) baseStart_5039537 baseEnd_5039537 := by
    simpa [prefixWord, tailWord_5039537, baseEnd_5039537] using wordTrace_append hprefix tailTrace_5039537
  have hstable : (prefixWord ++ tailWord_5039537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039537).length < 2 ^ (prefixWord ++ tailWord_5039537).sum := by decide
  have hdescent : baseEnd_5039537 < baseStart_5039537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039591 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_5039591 : Nat := 118140960795 + 5039591 * 2 ^ 59
def prefixEnd_5039591 : Nat := 4983230072969 + 3 ^ 40 * 5039591 * 2
def baseEnd_5039591 : Nat := 2587732485072697310735849

theorem tailTrace_5039591 : CollatzResearch.WordTrace tailWord_5039591 prefixEnd_5039591 2587732485072697310735849 := by
  unfold tailWord_5039591
  simp only [CollatzResearch.WordTrace]
  refine ⟨183808984285429975464590627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122539322856953316976393751 183808984285429975464590627)
  ·
    refine ⟨275713476428144963196885941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183808984285429975464590627 275713476428144963196885941)
    ·
      refine ⟨25848138415138590299708057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275713476428144963196885941 25848138415138590299708057)
      ·
        refine ⟨19386103811353942724781043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25848138415138590299708057 19386103811353942724781043)
        ·
          refine ⟨29079155717030914087171565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19386103811353942724781043 29079155717030914087171565)
          ·
            refine ⟨10904683393886592782689337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29079155717030914087171565 10904683393886592782689337)
            ·
              refine ⟨8178512545414944587017003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10904683393886592782689337 8178512545414944587017003)
              ·
                refine ⟨12267768818122416880525505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8178512545414944587017003 12267768818122416880525505)
                ·
                  refine ⟨9200826613591812660394129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12267768818122416880525505 9200826613591812660394129)
                  ·
                    refine ⟨6900619960193859495295597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9200826613591812660394129 6900619960193859495295597)
                    ·
                      refine ⟨2587732485072697310735849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900619960193859495295597 2587732485072697310735849)
                      ·
                        rfl

theorem cell23_5039591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_5039591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039591 prefixEnd_5039591 := by exact prefixLift 5039591
  have htrace : WordTrace (prefixWord ++ tailWord_5039591) baseStart_5039591 baseEnd_5039591 := by
    simpa [prefixWord, tailWord_5039591, baseEnd_5039591] using wordTrace_append hprefix tailTrace_5039591
  have hstable : (prefixWord ++ tailWord_5039591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039591).length < 2 ^ (prefixWord ++ tailWord_5039591).sum := by decide
  have hdescent : baseEnd_5039591 < baseStart_5039591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039622 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5039622 : Nat := 118140960795 + 5039622 * 2 ^ 59
def prefixEnd_5039622 : Nat := 4983230072969 + 3 ^ 40 * 5039622 * 2
def baseEnd_5039622 : Nat := 2587748402972986689448207

theorem tailTrace_5039622 : CollatzResearch.WordTrace tailWord_5039622 prefixEnd_5039622 2587748402972986689448207 := by
  unfold tailWord_5039622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744066092134927117467785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122540076632211778505979413 5744066092134927117467785)
  ·
    refine ⟨4308049569101195338100839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5744066092134927117467785 4308049569101195338100839)
    ·
      refine ⟨6462074353651793007151259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4308049569101195338100839 6462074353651793007151259)
      ·
        refine ⟨9693111530477689510726889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462074353651793007151259 9693111530477689510726889)
        ·
          refine ⟨7269833647858267133045167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9693111530477689510726889 7269833647858267133045167)
          ·
            refine ⟨10904750471787400699567751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269833647858267133045167 10904750471787400699567751)
            ·
              refine ⟨16357125707681101049351627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10904750471787400699567751 16357125707681101049351627)
              ·
                refine ⟨24535688561521651574027441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16357125707681101049351627 24535688561521651574027441)
                ·
                  refine ⟨18401766421141238680520581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24535688561521651574027441 18401766421141238680520581)
                  ·
                    refine ⟨3450331203963982252597609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18401766421141238680520581 3450331203963982252597609)
                    ·
                      refine ⟨2587748402972986689448207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450331203963982252597609 2587748402972986689448207)
                      ·
                        rfl

theorem cell23_5039622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5039622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039622 prefixEnd_5039622 := by exact prefixLift 5039622
  have htrace : WordTrace (prefixWord ++ tailWord_5039622) baseStart_5039622 baseEnd_5039622 := by
    simpa [prefixWord, tailWord_5039622, baseEnd_5039622] using wordTrace_append hprefix tailTrace_5039622
  have hstable : (prefixWord ++ tailWord_5039622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039622).length < 2 ^ (prefixWord ++ tailWord_5039622).sum := by decide
  have hdescent : baseEnd_5039622 < baseStart_5039622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039644 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5039644 : Nat := 118140960795 + 5039644 * 2 ^ 59
def prefixEnd_5039644 : Nat := 4983230072969 + 3 ^ 40 * 5039644 * 2
def baseEnd_5039644 : Nat := 2587759699547385603373105

theorem tailTrace_5039644 : CollatzResearch.WordTrace tailWord_5039644 prefixEnd_5039644 2587759699547385603373105 := by
  unfold tailWord_5039644
  simp only [CollatzResearch.WordTrace]
  refine ⟨91905458677118982758134993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122540611569491977010846657 91905458677118982758134993)
  ·
    refine ⟨68929094007839237068601245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91905458677118982758134993 68929094007839237068601245)
    ·
      refine ⟨25848410252939713900725467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68929094007839237068601245 25848410252939713900725467)
      ·
        refine ⟨38772615379409570851088201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25848410252939713900725467 38772615379409570851088201)
        ·
          refine ⟨29079461534557178138316151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38772615379409570851088201 29079461534557178138316151)
          ·
            refine ⟨43619192301835767207474227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29079461534557178138316151 43619192301835767207474227)
            ·
              refine ⟨65428788452753650811211341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43619192301835767207474227 65428788452753650811211341)
              ·
                refine ⟨24535795669782619054204253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65428788452753650811211341 24535795669782619054204253)
                ·
                  refine ⟨9200923376168482145326595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24535795669782619054204253 9200923376168482145326595)
                  ·
                    refine ⟨13801385064252723217989893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9200923376168482145326595 13801385064252723217989893)
                    ·
                      refine ⟨2587759699547385603373105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13801385064252723217989893 2587759699547385603373105)
                      ·
                        rfl

theorem cell23_5039644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5039644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039644 prefixEnd_5039644 := by exact prefixLift 5039644
  have htrace : WordTrace (prefixWord ++ tailWord_5039644) baseStart_5039644 baseEnd_5039644 := by
    simpa [prefixWord, tailWord_5039644, baseEnd_5039644] using wordTrace_append hprefix tailTrace_5039644
  have hstable : (prefixWord ++ tailWord_5039644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039644).length < 2 ^ (prefixWord ++ tailWord_5039644).sum := by decide
  have hdescent : baseEnd_5039644 < baseStart_5039644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039648 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5039648 : Nat := 118140960795 + 5039648 * 2 ^ 59
def prefixEnd_5039648 : Nat := 4983230072969 + 3 ^ 40 * 5039648 * 2
def baseEnd_5039648 : Nat := 2587761753470003587723087

theorem tailTrace_5039648 : CollatzResearch.WordTrace tailWord_5039648 prefixEnd_5039648 2587761753470003587723087 := by
  unfold tailWord_5039648
  simp only [CollatzResearch.WordTrace]
  refine ⟨91905531623111737099707799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122540708830815649466277065 91905531623111737099707799)
  ·
    refine ⟨137858297434667605649561699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91905531623111737099707799 137858297434667605649561699)
    ·
      refine ⟨206787446152001408474342549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137858297434667605649561699 206787446152001408474342549)
      ·
        refine ⟨9693161538375066022234807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 206787446152001408474342549 9693161538375066022234807)
        ·
          refine ⟨14539742307562599033352211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9693161538375066022234807 14539742307562599033352211)
          ·
            refine ⟨21809613461343898550028317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14539742307562599033352211 21809613461343898550028317)
            ·
              refine ⟨8178605048003961956260619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21809613461343898550028317 8178605048003961956260619)
              ·
                refine ⟨12267907572005942934390929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8178605048003961956260619 12267907572005942934390929)
                ·
                  refine ⟨9200930679004457200793197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12267907572005942934390929 9200930679004457200793197)
                  ·
                    refine ⟨3450349004626671450297449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9200930679004457200793197 3450349004626671450297449)
                    ·
                      refine ⟨2587761753470003587723087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450349004626671450297449 2587761753470003587723087)
                      ·
                        rfl

theorem cell23_5039648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5039648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039648 prefixEnd_5039648 := by exact prefixLift 5039648
  have htrace : WordTrace (prefixWord ++ tailWord_5039648) baseStart_5039648 baseEnd_5039648 := by
    simpa [prefixWord, tailWord_5039648, baseEnd_5039648] using wordTrace_append hprefix tailTrace_5039648
  have hstable : (prefixWord ++ tailWord_5039648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039648).length < 2 ^ (prefixWord ++ tailWord_5039648).sum := by decide
  have hdescent : baseEnd_5039648 < baseStart_5039648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039667 : List Nat := [1, 1, 1, 2, 4, 4, 10]
def baseStart_5039667 : Nat := 118140960795 + 5039667 * 2 ^ 59
def prefixEnd_5039667 : Nat := 4983230072969 + 3 ^ 40 * 5039667 * 2
def baseEnd_5039667 : Nat := 31947796414844926091179

theorem tailTrace_5039667 : CollatzResearch.WordTrace tailWord_5039667 prefixEnd_5039667 31947796414844926091179 := by
  unfold tailWord_5039667
  simp only [CollatzResearch.WordTrace]
  refine ⟨183811756233154640444357255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122541170822103093629571503 183811756233154640444357255)
  ·
    refine ⟨275717634349731960666535883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183811756233154640444357255 275717634349731960666535883)
    ·
      refine ⟨413576451524597940999803825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275717634349731960666535883 413576451524597940999803825)
      ·
        refine ⟨310182338643448455749852869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413576451524597940999803825 310182338643448455749852869)
        ·
          refine ⟨58159188495646585453097413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310182338643448455749852869 58159188495646585453097413)
          ·
            refine ⟨10904847842933734772455765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58159188495646585453097413 10904847842933734772455765)
            ·
              refine ⟨31947796414844926091179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10904847842933734772455765 31947796414844926091179)
              ·
                rfl

theorem cell23_5039667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 10].length) (baseStart_5039667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039667 prefixEnd_5039667 := by exact prefixLift 5039667
  have htrace : WordTrace (prefixWord ++ tailWord_5039667) baseStart_5039667 baseEnd_5039667 := by
    simpa [prefixWord, tailWord_5039667, baseEnd_5039667] using wordTrace_append hprefix tailTrace_5039667
  have hstable : (prefixWord ++ tailWord_5039667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039667).length < 2 ^ (prefixWord ++ tailWord_5039667).sum := by decide
  have hdescent : baseEnd_5039667 < baseStart_5039667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039671 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 2, 4]
def baseStart_5039671 : Nat := 118140960795 + 5039671 * 2 ^ 59
def prefixEnd_5039671 : Nat := 4983230072969 + 3 ^ 40 * 5039671 * 2
def baseEnd_5039671 : Nat := 862591187841685665911827

theorem tailTrace_5039671 : CollatzResearch.WordTrace tailWord_5039671 prefixEnd_5039671 862591187841685665911827 := by
  unfold tailWord_5039671
  simp only [CollatzResearch.WordTrace]
  refine ⟨183811902125140149127502867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122541268083426766085001911 183811902125140149127502867)
  ·
    refine ⟨275717853187710223691254301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183811902125140149127502867 275717853187710223691254301)
    ·
      refine ⟨103394194945391333884220363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275717853187710223691254301 103394194945391333884220363)
      ·
        refine ⟨155091292418087000826330545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103394194945391333884220363 155091292418087000826330545)
        ·
          refine ⟨116318469313565250619747909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155091292418087000826330545 116318469313565250619747909)
          ·
            refine ⟨21809712996293484491202733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116318469313565250619747909 21809712996293484491202733)
            ·
              refine ⟨8178642373610056684201025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21809712996293484491202733 8178642373610056684201025)
              ·
                refine ⟨6133981780207542513150769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8178642373610056684201025 6133981780207542513150769)
                ·
                  refine ⟨4600486335155656884863077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6133981780207542513150769 4600486335155656884863077)
                  ·
                    refine ⟨862591187841685665911827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4600486335155656884863077 862591187841685665911827)
                    ·
                      rfl

theorem cell23_5039671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_5039671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039671 prefixEnd_5039671 := by exact prefixLift 5039671
  have htrace : WordTrace (prefixWord ++ tailWord_5039671) baseStart_5039671 baseEnd_5039671 := by
    simpa [prefixWord, tailWord_5039671, baseEnd_5039671] using wordTrace_append hprefix tailTrace_5039671
  have hstable : (prefixWord ++ tailWord_5039671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039671).length < 2 ^ (prefixWord ++ tailWord_5039671).sum := by decide
  have hdescent : baseEnd_5039671 < baseStart_5039671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039698 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_5039698 : Nat := 118140960795 + 5039698 * 2 ^ 59
def prefixEnd_5039698 : Nat := 4983230072969 + 3 ^ 40 * 5039698 * 2
def baseEnd_5039698 : Nat := 2587787427502728392097857

theorem tailTrace_5039698 : CollatzResearch.WordTrace tailWord_5039698 prefixEnd_5039698 2587787427502728392097857 := by
  unfold tailWord_5039698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45953221724010583184683937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122541924597361555159157165 45953221724010583184683937)
  ·
    refine ⟨34464916293007937388512953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45953221724010583184683937 34464916293007937388512953)
    ·
      refine ⟨25848687219755953041384715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34464916293007937388512953 25848687219755953041384715)
      ·
        refine ⟨38773030829633929562077073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25848687219755953041384715 38773030829633929562077073)
        ·
          refine ⟨29079773122225447171557805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38773030829633929562077073 29079773122225447171557805)
          ·
            refine ⟨10904914920834542689334177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29079773122225447171557805 10904914920834542689334177)
            ·
              refine ⟨8178686190625907017000633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10904914920834542689334177 8178686190625907017000633)
              ·
                refine ⟨6134014642969430262750475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8178686190625907017000633 6134014642969430262750475)
                ·
                  refine ⟨9201021964454145394125713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134014642969430262750475 9201021964454145394125713)
                  ·
                    refine ⟨6900766473340609045594285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9201021964454145394125713 6900766473340609045594285)
                    ·
                      refine ⟨2587787427502728392097857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900766473340609045594285 2587787427502728392097857)
                      ·
                        rfl

theorem cell23_5039698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_5039698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039698 prefixEnd_5039698 := by exact prefixLift 5039698
  have htrace : WordTrace (prefixWord ++ tailWord_5039698) baseStart_5039698 baseEnd_5039698 := by
    simpa [prefixWord, tailWord_5039698, baseEnd_5039698] using wordTrace_append hprefix tailTrace_5039698
  have hstable : (prefixWord ++ tailWord_5039698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039698).length < 2 ^ (prefixWord ++ tailWord_5039698).sum := by decide
  have hdescent : baseEnd_5039698 < baseStart_5039698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039745 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_5039745 : Nat := 118140960795 + 5039745 * 2 ^ 59
def prefixEnd_5039745 : Nat := 4983230072969 + 3 ^ 40 * 5039745 * 2
def baseEnd_5039745 : Nat := 2587811561093489708210141

theorem tailTrace_5039745 : CollatzResearch.WordTrace tailWord_5039745 prefixEnd_5039745 2587811561093489708210141 := by
  unfold tailWord_5039745
  simp only [CollatzResearch.WordTrace]
  refine ⟨183814601126872059765696689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122543067417914706510464459 183814601126872059765696689)
  ·
    refine ⟨137860950845154044824272517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183814601126872059765696689 137860950845154044824272517)
    ·
      refine ⟨25848928283466383404551097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137860950845154044824272517 25848928283466383404551097)
      ·
        refine ⟨19386696212599787553413323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25848928283466383404551097 19386696212599787553413323)
        ·
          refine ⟨29080044318899681330119985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19386696212599787553413323 29080044318899681330119985)
          ·
            refine ⟨21810033239174760997589989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29080044318899681330119985 21810033239174760997589989)
            ·
              refine ⟨4089381232345267687048123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21810033239174760997589989 4089381232345267687048123)
              ·
                refine ⟨6134071848517901530572185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089381232345267687048123 6134071848517901530572185)
                ·
                  refine ⟨4600553886388426147929139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6134071848517901530572185 4600553886388426147929139)
                  ·
                    refine ⟨6900830829582639221893709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4600553886388426147929139 6900830829582639221893709)
                    ·
                      refine ⟨2587811561093489708210141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6900830829582639221893709 2587811561093489708210141)
                      ·
                        rfl

theorem cell23_5039745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_5039745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039745 prefixEnd_5039745 := by exact prefixLift 5039745
  have htrace : WordTrace (prefixWord ++ tailWord_5039745) baseStart_5039745 baseEnd_5039745 := by
    simpa [prefixWord, tailWord_5039745, baseEnd_5039745] using wordTrace_append hprefix tailTrace_5039745
  have hstable : (prefixWord ++ tailWord_5039745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039745).length < 2 ^ (prefixWord ++ tailWord_5039745).sum := by decide
  have hdescent : baseEnd_5039745 < baseStart_5039745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039768 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5039768 : Nat := 118140960795 + 5039768 * 2 ^ 59
def prefixEnd_5039768 : Nat := 4983230072969 + 3 ^ 40 * 5039768 * 2
def baseEnd_5039768 : Nat := 2587823371148543118222535

theorem tailTrace_5039768 : CollatzResearch.WordTrace tailWord_5039768 prefixEnd_5039768 2587823371148543118222535 := by
  unfold tailWord_5039768
  simp only [CollatzResearch.WordTrace]
  refine ⟨91907720002894367346891979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122543626670525823129189305 91907720002894367346891979)
  ·
    refine ⟨137861580004341551020337969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91907720002894367346891979 137861580004341551020337969)
    ·
      refine ⟨103396185003256163265253477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137861580004341551020337969 103396185003256163265253477)
      ·
        refine ⟨19386784688110530612235027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103396185003256163265253477 19386784688110530612235027)
        ·
          refine ⟨29080177032165795918352541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19386784688110530612235027 29080177032165795918352541)
          ·
            refine ⟨10905066387062173469382203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29080177032165795918352541 10905066387062173469382203)
            ·
              refine ⟨16357599580593260204073305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905066387062173469382203 16357599580593260204073305)
              ·
                refine ⟨12268199685444945153054979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16357599580593260204073305 12268199685444945153054979)
                ·
                  refine ⟨18402299528167417729582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12268199685444945153054979 18402299528167417729582469)
                  ·
                    refine ⟨3450431161531390824296713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18402299528167417729582469 3450431161531390824296713)
                    ·
                      refine ⟨2587823371148543118222535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450431161531390824296713 2587823371148543118222535)
                      ·
                        rfl

theorem cell23_5039768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5039768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039768 prefixEnd_5039768 := by exact prefixLift 5039768
  have htrace : WordTrace (prefixWord ++ tailWord_5039768) baseStart_5039768 baseEnd_5039768 := by
    simpa [prefixWord, tailWord_5039768, baseEnd_5039768] using wordTrace_append hprefix tailTrace_5039768
  have hstable : (prefixWord ++ tailWord_5039768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039768).length < 2 ^ (prefixWord ++ tailWord_5039768).sum := by decide
  have hdescent : baseEnd_5039768 < baseStart_5039768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039772 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5039772 : Nat := 118140960795 + 5039772 * 2 ^ 59
def prefixEnd_5039772 : Nat := 4983230072969 + 3 ^ 40 * 5039772 * 2
def baseEnd_5039772 : Nat := 2587825425071161102572517

theorem tailTrace_5039772 : CollatzResearch.WordTrace tailWord_5039772 prefixEnd_5039772 2587825425071161102572517 := by
  unfold tailWord_5039772
  simp only [CollatzResearch.WordTrace]
  refine ⟨91907792948887121688464785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122543723931849495584619713 91907792948887121688464785)
  ·
    refine ⟨68930844711665341266348589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91907792948887121688464785 68930844711665341266348589)
    ·
      refine ⟨25849066766874502974880721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68930844711665341266348589 25849066766874502974880721)
      ·
        refine ⟨19386800075155877231160541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25849066766874502974880721 19386800075155877231160541)
        ·
          refine ⟨7270050028183453961685203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19386800075155877231160541 7270050028183453961685203)
          ·
            refine ⟨10905075042275180942527805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270050028183453961685203 10905075042275180942527805)
            ·
              refine ⟨4089403140853192853447927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10905075042275180942527805 4089403140853192853447927)
              ·
                refine ⟨6134104711279789280171891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089403140853192853447927 6134104711279789280171891)
                ·
                  refine ⟨9201157066919683920257837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134104711279789280171891 9201157066919683920257837)
                  ·
                    refine ⟨3450433900094881470096689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9201157066919683920257837 3450433900094881470096689)
                    ·
                      refine ⟨2587825425071161102572517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450433900094881470096689 2587825425071161102572517)
                      ·
                        rfl

theorem cell23_5039772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5039772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039772 prefixEnd_5039772 := by exact prefixLift 5039772
  have htrace : WordTrace (prefixWord ++ tailWord_5039772) baseStart_5039772 baseEnd_5039772 := by
    simpa [prefixWord, tailWord_5039772, baseEnd_5039772] using wordTrace_append hprefix tailTrace_5039772
  have hstable : (prefixWord ++ tailWord_5039772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039772).length < 2 ^ (prefixWord ++ tailWord_5039772).sum := by decide
  have hdescent : baseEnd_5039772 < baseStart_5039772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039791 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 5]
def baseStart_5039791 : Nat := 118140960795 + 5039791 * 2 ^ 59
def prefixEnd_5039791 : Nat := 4983230072969 + 3 ^ 40 * 5039791 * 2
def baseEnd_5039791 : Nat := 287537242355955169803881

theorem tailTrace_5039791 : CollatzResearch.WordTrace tailWord_5039791 prefixEnd_5039791 287537242355955169803881 := by
  unfold tailWord_5039791
  simp only [CollatzResearch.WordTrace]
  refine ⟨183816278884705409621871227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122544185923136939747914151 183816278884705409621871227)
  ·
    refine ⟨275724418327058114432806841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183816278884705409621871227 275724418327058114432806841)
    ·
      refine ⟨206793313745293585824605131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275724418327058114432806841 206793313745293585824605131)
      ·
        refine ⟨310189970617940378736907697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206793313745293585824605131 310189970617940378736907697)
        ·
          refine ⟨232642477963455284052680773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310189970617940378736907697 232642477963455284052680773)
          ·
            refine ⟨43620464618147865759877645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232642477963455284052680773 43620464618147865759877645)
            ·
              refine ⟨16357674231805449659954117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43620464618147865759877645 16357674231805449659954117)
              ·
                refine ⟨3067063918463521811241397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16357674231805449659954117 3067063918463521811241397)
                ·
                  refine ⟨287537242355955169803881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067063918463521811241397 287537242355955169803881)
                  ·
                    rfl

theorem cell23_5039791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 5].length) (baseStart_5039791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039791 prefixEnd_5039791 := by exact prefixLift 5039791
  have htrace : WordTrace (prefixWord ++ tailWord_5039791) baseStart_5039791 baseEnd_5039791 := by
    simpa [prefixWord, tailWord_5039791, baseEnd_5039791] using wordTrace_append hprefix tailTrace_5039791
  have hstable : (prefixWord ++ tailWord_5039791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039791).length < 2 ^ (prefixWord ++ tailWord_5039791).sum := by decide
  have hdescent : baseEnd_5039791 < baseStart_5039791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039798 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5039798 : Nat := 118140960795 + 5039798 * 2 ^ 59
def prefixEnd_5039798 : Nat := 4983230072969 + 3 ^ 40 * 5039798 * 2
def baseEnd_5039798 : Nat := 2587838775568178000847397

theorem tailTrace_5039798 : CollatzResearch.WordTrace tailWord_5039798 prefixEnd_5039798 2587838775568178000847397 := by
  unfold tailWord_5039798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11488533387230003113586003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122544356130453366544917365 11488533387230003113586003)
  ·
    refine ⟨17232800080845004670379005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11488533387230003113586003 17232800080845004670379005)
    ·
      refine ⟨6462300030316876751392127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17232800080845004670379005 6462300030316876751392127)
      ·
        refine ⟨9693450045475315127088191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462300030316876751392127 9693450045475315127088191)
        ·
          refine ⟨14540175068212972690632287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9693450045475315127088191 14540175068212972690632287)
          ·
            refine ⟨21810262602319459035948431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14540175068212972690632287 21810262602319459035948431)
            ·
              refine ⟨32715393903479188553922647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21810262602319459035948431 32715393903479188553922647)
              ·
                refine ⟨49073090855218782830883971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32715393903479188553922647 49073090855218782830883971)
                ·
                  refine ⟨73609636282828174246325957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49073090855218782830883971 73609636282828174246325957)
                  ·
                    refine ⟨13801806803030282671186117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73609636282828174246325957 13801806803030282671186117)
                    ·
                      refine ⟨2587838775568178000847397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13801806803030282671186117 2587838775568178000847397)
                      ·
                        rfl

theorem cell23_5039798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5039798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039798 prefixEnd_5039798 := by exact prefixLift 5039798
  have htrace : WordTrace (prefixWord ++ tailWord_5039798) baseStart_5039798 baseEnd_5039798 := by
    simpa [prefixWord, tailWord_5039798, baseEnd_5039798] using wordTrace_append hprefix tailTrace_5039798
  have hstable : (prefixWord ++ tailWord_5039798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039798).length < 2 ^ (prefixWord ++ tailWord_5039798).sum := by decide
  have hdescent : baseEnd_5039798 < baseStart_5039798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039836 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5039836 : Nat := 118140960795 + 5039836 * 2 ^ 59
def prefixEnd_5039836 : Nat := 4983230072969 + 3 ^ 40 * 5039836 * 2
def baseEnd_5039836 : Nat := 2587858287833048852172223

theorem tailTrace_5039836 : CollatzResearch.WordTrace tailWord_5039836 prefixEnd_5039836 2587858287833048852172223 := by
  unfold tailWord_5039836
  simp only [CollatzResearch.WordTrace]
  refine ⟨91908960084771191153629681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122545280113028254871506241 91908960084771191153629681)
  ·
    refine ⟨68931720063578393365222261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91908960084771191153629681 68931720063578393365222261)
    ·
      refine ⟨6462348755960474377989587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68931720063578393365222261 6462348755960474377989587)
      ·
        refine ⟨9693523133940711566984381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462348755960474377989587 9693523133940711566984381)
        ·
          refine ⟨3635071175227766837619143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9693523133940711566984381 3635071175227766837619143)
          ·
            refine ⟨5452606762841650256428715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635071175227766837619143 5452606762841650256428715)
            ·
              refine ⟨8178910144262475384643073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452606762841650256428715 8178910144262475384643073)
              ·
                refine ⟨6134182608196856538482305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8178910144262475384643073 6134182608196856538482305)
                ·
                  refine ⟨4600636956147642403861729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6134182608196856538482305 4600636956147642403861729)
                  ·
                    refine ⟨3450477717110731802896297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4600636956147642403861729 3450477717110731802896297)
                    ·
                      refine ⟨2587858287833048852172223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450477717110731802896297 2587858287833048852172223)
                      ·
                        rfl

theorem cell23_5039836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5039836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039836 prefixEnd_5039836 := by exact prefixLift 5039836
  have htrace : WordTrace (prefixWord ++ tailWord_5039836) baseStart_5039836 baseEnd_5039836 := by
    simpa [prefixWord, tailWord_5039836, baseEnd_5039836] using wordTrace_append hprefix tailTrace_5039836
  have hstable : (prefixWord ++ tailWord_5039836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039836).length < 2 ^ (prefixWord ++ tailWord_5039836).sum := by decide
  have hdescent : baseEnd_5039836 < baseStart_5039836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039851 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 3, 4]
def baseStart_5039851 : Nat := 118140960795 + 5039851 * 2 ^ 59
def prefixEnd_5039851 : Nat := 4983230072969 + 3 ^ 40 * 5039851 * 2
def baseEnd_5039851 : Nat := 862621996680955431161551

theorem tailTrace_5039851 : CollatzResearch.WordTrace tailWord_5039851 prefixEnd_5039851 862621996680955431161551 := by
  unfold tailWord_5039851
  simp only [CollatzResearch.WordTrace]
  refine ⟨183818467264488039869055407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122545644842992026579370271 183818467264488039869055407)
  ·
    refine ⟨275727700896732059803583111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183818467264488039869055407 275727700896732059803583111)
    ·
      refine ⟨413591551345098089705374667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275727700896732059803583111 413591551345098089705374667)
      ·
        refine ⟨620387327017647134558062001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413591551345098089705374667 620387327017647134558062001)
        ·
          refine ⟨465290495263235350918546501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620387327017647134558062001 465290495263235350918546501)
          ·
            refine ⟨87241967861856628297227469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 465290495263235350918546501 87241967861856628297227469)
            ·
              refine ⟨32715737948196235611460301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87241967861856628297227469 32715737948196235611460301)
              ·
                refine ⟨12268401730573588354297613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32715737948196235611460301 12268401730573588354297613)
                ·
                  refine ⟨4600650648965095632861605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12268401730573588354297613 4600650648965095632861605)
                  ·
                    refine ⟨862621996680955431161551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4600650648965095632861605 862621996680955431161551)
                    ·
                      rfl

theorem cell23_5039851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 4].length) (baseStart_5039851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039851 prefixEnd_5039851 := by exact prefixLift 5039851
  have htrace : WordTrace (prefixWord ++ tailWord_5039851) baseStart_5039851 baseEnd_5039851 := by
    simpa [prefixWord, tailWord_5039851, baseEnd_5039851] using wordTrace_append hprefix tailTrace_5039851
  have hstable : (prefixWord ++ tailWord_5039851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039851).length < 2 ^ (prefixWord ++ tailWord_5039851).sum := by decide
  have hdescent : baseEnd_5039851 < baseStart_5039851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039858 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5039858 : Nat := 118140960795 + 5039858 * 2 ^ 59
def prefixEnd_5039858 : Nat := 4983230072969 + 3 ^ 40 * 5039858 * 2
def baseEnd_5039858 : Nat := 2587869584407447766097121

theorem tailTrace_5039858 : CollatzResearch.WordTrace tailWord_5039858 prefixEnd_5039858 2587869584407447766097121 := by
  unfold tailWord_5039858
  simp only [CollatzResearch.WordTrace]
  refine ⟨45954680643865670016140057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122545815050308453376373485 45954680643865670016140057)
  ·
    refine ⟨34466010482899252512105043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45954680643865670016140057 34466010482899252512105043)
    ·
      refine ⟨51699015724348878768157565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34466010482899252512105043 51699015724348878768157565)
      ·
        refine ⟨19387130896630829538059087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51699015724348878768157565 19387130896630829538059087)
        ·
          refine ⟨29080696344946244307088631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19387130896630829538059087 29080696344946244307088631)
          ·
            refine ⟨43621044517419366460632947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29080696344946244307088631 43621044517419366460632947)
            ·
              refine ⟨65431566776129049690949421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43621044517419366460632947 65431566776129049690949421)
              ·
                refine ⟨24536837541048393634106033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65431566776129049690949421 24536837541048393634106033)
                ·
                  refine ⟨18402628155786295225579525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24536837541048393634106033 18402628155786295225579525)
                  ·
                    refine ⟨3450492779209930354796161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18402628155786295225579525 3450492779209930354796161)
                    ·
                      refine ⟨2587869584407447766097121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450492779209930354796161 2587869584407447766097121)
                      ·
                        rfl

theorem cell23_5039858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5039858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039858 prefixEnd_5039858 := by exact prefixLift 5039858
  have htrace : WordTrace (prefixWord ++ tailWord_5039858) baseStart_5039858 baseEnd_5039858 := by
    simpa [prefixWord, tailWord_5039858, baseEnd_5039858] using wordTrace_append hprefix tailTrace_5039858
  have hstable : (prefixWord ++ tailWord_5039858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039858).length < 2 ^ (prefixWord ++ tailWord_5039858).sum := by decide
  have hdescent : baseEnd_5039858 < baseStart_5039858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039928 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_5039928 : Nat := 118140960795 + 5039928 * 2 ^ 59
def prefixEnd_5039928 : Nat := 4983230072969 + 3 ^ 40 * 5039928 * 2
def baseEnd_5039928 : Nat := 862635176017754164073933

theorem tailTrace_5039928 : CollatzResearch.WordTrace tailWord_5039928 prefixEnd_5039928 862635176017754164073933 := by
  unfold tailWord_5039928
  simp only [CollatzResearch.WordTrace]
  refine ⟨91910637842604541009804219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122547517123472721346405625 91910637842604541009804219)
  ·
    refine ⟨137865956763906811514706329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91910637842604541009804219 137865956763906811514706329)
    ·
      refine ⟨103399467572930108636029747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137865956763906811514706329 103399467572930108636029747)
      ·
        refine ⟨155099201359395162954044621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103399467572930108636029747 155099201359395162954044621)
        ·
          refine ⟨58162200509773186107766733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155099201359395162954044621 58162200509773186107766733)
          ·
            refine ⟨21810825191164944790412525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58162200509773186107766733 21810825191164944790412525)
            ·
              refine ⟨8179059446686854296404697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21810825191164944790412525 8179059446686854296404697)
              ·
                refine ⟨6134294585015140722303523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8179059446686854296404697 6134294585015140722303523)
                ·
                  refine ⟨9201441877522711083455285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134294585015140722303523 9201441877522711083455285)
                  ·
                    refine ⟨862635176017754164073933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9201441877522711083455285 862635176017754164073933)
                    ·
                      rfl

theorem cell23_5039928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_5039928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039928 prefixEnd_5039928 := by exact prefixLift 5039928
  have htrace : WordTrace (prefixWord ++ tailWord_5039928) baseStart_5039928 baseEnd_5039928 := by
    simpa [prefixWord, tailWord_5039928, baseEnd_5039928] using wordTrace_append hprefix tailTrace_5039928
  have hstable : (prefixWord ++ tailWord_5039928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039928).length < 2 ^ (prefixWord ++ tailWord_5039928).sum := by decide
  have hdescent : baseEnd_5039928 < baseStart_5039928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039941 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_5039941 : Nat := 118140960795 + 5039941 * 2 ^ 59
def prefixEnd_5039941 : Nat := 4983230072969 + 3 ^ 40 * 5039941 * 2
def baseEnd_5039941 : Nat := 862637401100590313786413

theorem tailTrace_5039941 : CollatzResearch.WordTrace tailWord_5039941 prefixEnd_5039941 862637401100590313786413 := by
  unfold tailWord_5039941
  simp only [CollatzResearch.WordTrace]
  refine ⟨183821749834161985239831677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122547833222774656826554451 183821749834161985239831677)
  ·
    refine ⟨68933156187810744464936879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183821749834161985239831677 68933156187810744464936879)
    ·
      refine ⟨103399734281716116697405319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68933156187810744464936879 103399734281716116697405319)
      ·
        refine ⟨155099601422574175046107979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103399734281716116697405319 155099601422574175046107979)
        ·
          refine ⟨232649402133861262569161969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155099601422574175046107979 232649402133861262569161969)
          ·
            refine ⟨174487051600395946926871477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232649402133861262569161969 174487051600395946926871477)
            ·
              refine ⟨16358161087537120024394201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174487051600395946926871477 16358161087537120024394201)
              ·
                refine ⟨12268620815652840018295651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16358161087537120024394201 12268620815652840018295651)
                ·
                  refine ⟨18402931223479260027443477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12268620815652840018295651 18402931223479260027443477)
                  ·
                    refine ⟨862637401100590313786413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18402931223479260027443477 862637401100590313786413)
                    ·
                      rfl

theorem cell23_5039941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_5039941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039941 prefixEnd_5039941 := by exact prefixLift 5039941
  have htrace : WordTrace (prefixWord ++ tailWord_5039941) baseStart_5039941 baseEnd_5039941 := by
    simpa [prefixWord, tailWord_5039941, baseEnd_5039941] using wordTrace_append hprefix tailTrace_5039941
  have hstable : (prefixWord ++ tailWord_5039941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039941).length < 2 ^ (prefixWord ++ tailWord_5039941).sum := by decide
  have hdescent : baseEnd_5039941 < baseStart_5039941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039961 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_5039961 : Nat := 118140960795 + 5039961 * 2 ^ 59
def prefixEnd_5039961 : Nat := 4983230072969 + 3 ^ 40 * 5039961 * 2
def baseEnd_5039961 : Nat := 2587922472914860863109147

theorem tailTrace_5039961 : CollatzResearch.WordTrace tailWord_5039961 prefixEnd_5039961 2587922472914860863109147 := by
  unfold tailWord_5039961
  simp only [CollatzResearch.WordTrace]
  refine ⟨183822479294089528655559737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122548319529393019103706491 183822479294089528655559737)
  ·
    refine ⟨137866859470567146491669803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183822479294089528655559737 137866859470567146491669803)
    ·
      refine ⟨206800289205850719737504705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137866859470567146491669803 206800289205850719737504705)
      ·
        refine ⟨155100216904388039803128529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206800289205850719737504705 155100216904388039803128529)
        ·
          refine ⟨116325162678291029852346397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155100216904388039803128529 116325162678291029852346397)
          ·
            refine ⟨43621936004359136194629899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116325162678291029852346397 43621936004359136194629899)
            ·
              refine ⟨65432904006538704291944849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43621936004359136194629899 65432904006538704291944849)
              ·
                refine ⟨49074678004904028218958637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65432904006538704291944849 49074678004904028218958637)
                ·
                  refine ⟨18403004251839010582109489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49074678004904028218958637 18403004251839010582109489)
                  ·
                    refine ⟨13802253188879257936582117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18403004251839010582109489 13802253188879257936582117)
                    ·
                      refine ⟨2587922472914860863109147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13802253188879257936582117 2587922472914860863109147)
                      ·
                        rfl

theorem cell23_5039961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_5039961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039961 prefixEnd_5039961 := by exact prefixLift 5039961
  have htrace : WordTrace (prefixWord ++ tailWord_5039961) baseStart_5039961 baseEnd_5039961 := by
    simpa [prefixWord, tailWord_5039961, baseEnd_5039961] using wordTrace_append hprefix tailTrace_5039961
  have hstable : (prefixWord ++ tailWord_5039961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039961).length < 2 ^ (prefixWord ++ tailWord_5039961).sum := by decide
  have hdescent : baseEnd_5039961 < baseStart_5039961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039968 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_5039968 : Nat := 118140960795 + 5039968 * 2 ^ 59
def prefixEnd_5039968 : Nat := 4983230072969 + 3 ^ 40 * 5039968 * 2
def baseEnd_5039968 : Nat := 2587926067279442335721615

theorem tailTrace_5039968 : CollatzResearch.WordTrace tailWord_5039968 prefixEnd_5039968 2587926067279442335721615 := by
  unfold tailWord_5039968
  simp only [CollatzResearch.WordTrace]
  refine ⟨91911367302532084425532279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122548489736709445900709705 91911367302532084425532279)
  ·
    refine ⟨137867050953798126638298419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91911367302532084425532279 137867050953798126638298419)
    ·
      refine ⟨206800576430697189957447629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137867050953798126638298419 206800576430697189957447629)
      ·
        refine ⟨77550216161511446234042861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206800576430697189957447629 77550216161511446234042861)
        ·
          refine ⟨29081331060566792337766073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77550216161511446234042861 29081331060566792337766073)
          ·
            refine ⟨21810998295425094253324555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29081331060566792337766073 21810998295425094253324555)
            ·
              refine ⟨32716497443137641379986833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21810998295425094253324555 32716497443137641379986833)
              ·
                refine ⟨24537373082353231034990125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32716497443137641379986833 24537373082353231034990125)
                ·
                  refine ⟨9201514905882461638121297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24537373082353231034990125 9201514905882461638121297)
                  ·
                    refine ⟨6901136179411846228590973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9201514905882461638121297 6901136179411846228590973)
                    ·
                      refine ⟨2587926067279442335721615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6901136179411846228590973 2587926067279442335721615)
                      ·
                        rfl

theorem cell23_5039968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_5039968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039968 prefixEnd_5039968 := by exact prefixLift 5039968
  have htrace : WordTrace (prefixWord ++ tailWord_5039968) baseStart_5039968 baseEnd_5039968 := by
    simpa [prefixWord, tailWord_5039968, baseEnd_5039968] using wordTrace_append hprefix tailTrace_5039968
  have hstable : (prefixWord ++ tailWord_5039968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039968).length < 2 ^ (prefixWord ++ tailWord_5039968).sum := by decide
  have hdescent : baseEnd_5039968 < baseStart_5039968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5039982 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_5039982 : Nat := 118140960795 + 5039982 * 2 ^ 59
def prefixEnd_5039982 : Nat := 4983230072969 + 3 ^ 40 * 5039982 * 2
def baseEnd_5039982 : Nat := 2587933256008605280946551

theorem tailTrace_5039982 : CollatzResearch.WordTrace tailWord_5039982 prefixEnd_5039982 2587933256008605280946551 := by
  unfold tailWord_5039982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977905653376681155259275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122548830151342299494716133 22977905653376681155259275)
  ·
    refine ⟨34466858480065021732888913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22977905653376681155259275 34466858480065021732888913)
    ·
      refine ⟨25850143860048766299666685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34466858480065021732888913 25850143860048766299666685)
      ·
        refine ⟨9693803947518287362375007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25850143860048766299666685 9693803947518287362375007)
        ·
          refine ⟨14540705921277431043562511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9693803947518287362375007 14540705921277431043562511)
          ·
            refine ⟨21811058881916146565343767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14540705921277431043562511 21811058881916146565343767)
            ·
              refine ⟨32716588322874219848015651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21811058881916146565343767 32716588322874219848015651)
              ·
                refine ⟨49074882484311329772023477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32716588322874219848015651 49074882484311329772023477)
                ·
                  refine ⟨4600770232904187166127201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49074882484311329772023477 4600770232904187166127201)
                  ·
                    refine ⟨3450577674678140374595401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4600770232904187166127201 3450577674678140374595401)
                    ·
                      refine ⟨2587933256008605280946551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450577674678140374595401 2587933256008605280946551)
                      ·
                        rfl

theorem cell23_5039982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_5039982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5039982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5039982 prefixEnd_5039982 := by exact prefixLift 5039982
  have htrace : WordTrace (prefixWord ++ tailWord_5039982) baseStart_5039982 baseEnd_5039982 := by
    simpa [prefixWord, tailWord_5039982, baseEnd_5039982] using wordTrace_append hprefix tailTrace_5039982
  have hstable : (prefixWord ++ tailWord_5039982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5039982).length < 2 ^ (prefixWord ++ tailWord_5039982).sum := by decide
  have hdescent : baseEnd_5039982 < baseStart_5039982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5039982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040071 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_5040071 : Nat := 118140960795 + 5040071 * 2 ^ 59
def prefixEnd_5040071 : Nat := 4983230072969 + 3 ^ 40 * 5040071 * 2
def baseEnd_5040071 : Nat := 2587978955786855432733641

theorem tailTrace_5040071 : CollatzResearch.WordTrace tailWord_5040071 prefixEnd_5040071 2587978955786855432733641 := by
  unfold tailWord_5040071
  simp only [CollatzResearch.WordTrace]
  refine ⟨183826491323691017442064067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122550994215794011628042711 183826491323691017442064067)
  ·
    refine ⟨275739736985536526163096101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183826491323691017442064067 275739736985536526163096101)
    ·
      refine ⟨51701200684788098655580519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275739736985536526163096101 51701200684788098655580519)
      ·
        refine ⟨77551801027182147983370779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51701200684788098655580519 77551801027182147983370779)
        ·
          refine ⟨116327701540773221975056169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77551801027182147983370779 116327701540773221975056169)
          ·
            refine ⟨87245776155579916481292127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116327701540773221975056169 87245776155579916481292127)
            ·
              refine ⟨130868664233369874721938191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87245776155579916481292127 130868664233369874721938191)
              ·
                refine ⟨196302996350054812082907287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130868664233369874721938191 196302996350054812082907287)
                ·
                  refine ⟨294454494525082218124360931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196302996350054812082907287 294454494525082218124360931)
                  ·
                    refine ⟨441681741787623327186541397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294454494525082218124360931 441681741787623327186541397)
                    ·
                      refine ⟨2587978955786855432733641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 441681741787623327186541397 2587978955786855432733641)
                      ·
                        rfl

theorem cell23_5040071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_5040071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040071 prefixEnd_5040071 := by exact prefixLift 5040071
  have htrace : WordTrace (prefixWord ++ tailWord_5040071) baseStart_5040071 baseEnd_5040071 := by
    simpa [prefixWord, tailWord_5040071, baseEnd_5040071] using wordTrace_append hprefix tailTrace_5040071
  have hstable : (prefixWord ++ tailWord_5040071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040071).length < 2 ^ (prefixWord ++ tailWord_5040071).sum := by decide
  have hdescent : baseEnd_5040071 < baseStart_5040071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040072 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_5040072 : Nat := 118140960795 + 5040072 * 2 ^ 59
def prefixEnd_5040072 : Nat := 4983230072969 + 3 ^ 40 * 5040072 * 2
def baseEnd_5040072 : Nat := 2587979469267509928821137

theorem tailTrace_5040072 : CollatzResearch.WordTrace tailWord_5040072 prefixEnd_5040072 2587979469267509928821137 := by
  unfold tailWord_5040072
  simp only [CollatzResearch.WordTrace]
  refine ⟨91913263898343697306425235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122551018531124929741900313 91913263898343697306425235)
  ·
    refine ⟨137869895847515545959637853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91913263898343697306425235 137869895847515545959637853)
    ·
      refine ⟨51701210942818329734864195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137869895847515545959637853 51701210942818329734864195)
      ·
        refine ⟨77551816414227494602296293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51701210942818329734864195 77551816414227494602296293)
        ·
          refine ⟨14540965577667655237930555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77551816414227494602296293 14540965577667655237930555)
          ·
            refine ⟨21811448366501482856895833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14540965577667655237930555 21811448366501482856895833)
            ·
              refine ⟨16358586274876112142671875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21811448366501482856895833 16358586274876112142671875)
              ·
                refine ⟨24537879412314168214007813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16358586274876112142671875 24537879412314168214007813)
                ·
                  refine ⟨4600852389808906540126465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24537879412314168214007813 4600852389808906540126465)
                  ·
                    refine ⟨3450639292356679905094849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4600852389808906540126465 3450639292356679905094849)
                    ·
                      refine ⟨2587979469267509928821137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450639292356679905094849 2587979469267509928821137)
                      ·
                        rfl

theorem cell23_5040072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_5040072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040072 prefixEnd_5040072 := by exact prefixLift 5040072
  have htrace : WordTrace (prefixWord ++ tailWord_5040072) baseStart_5040072 baseEnd_5040072 := by
    simpa [prefixWord, tailWord_5040072, baseEnd_5040072] using wordTrace_append hprefix tailTrace_5040072
  have hstable : (prefixWord ++ tailWord_5040072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040072).length < 2 ^ (prefixWord ++ tailWord_5040072).sum := by decide
  have hdescent : baseEnd_5040072 < baseStart_5040072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040081 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_5040081 : Nat := 118140960795 + 5040081 * 2 ^ 59
def prefixEnd_5040081 : Nat := 4983230072969 + 3 ^ 40 * 5040081 * 2
def baseEnd_5040081 : Nat := 2587984090593400393608595

theorem tailTrace_5040081 : CollatzResearch.WordTrace tailWord_5040081 prefixEnd_5040081 2587984090593400393608595 := by
  unfold tailWord_5040081
  simp only [CollatzResearch.WordTrace]
  refine ⟨183826856053654789149928097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122551237369103192766618731 183826856053654789149928097)
  ·
    refine ⟨137870142040241091862446073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183826856053654789149928097 137870142040241091862446073)
    ·
      refine ⟨103402606530180818896834555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137870142040241091862446073 103402606530180818896834555)
      ·
        refine ⟨155103909795271228345251833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103402606530180818896834555 155103909795271228345251833)
        ·
          refine ⟨116327932346453421258938875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155103909795271228345251833 116327932346453421258938875)
          ·
            refine ⟨174491898519680131888408313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116327932346453421258938875 174491898519680131888408313)
            ·
              refine ⟨130868923889760098916306235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174491898519680131888408313 130868923889760098916306235)
              ·
                refine ⟨196303385834640148374459353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130868923889760098916306235 196303385834640148374459353)
                ·
                  refine ⟨147227539375980111280844515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196303385834640148374459353 147227539375980111280844515)
                  ·
                    refine ⟨220841309063970166921266773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147227539375980111280844515 220841309063970166921266773)
                    ·
                      refine ⟨2587984090593400393608595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220841309063970166921266773 2587984090593400393608595)
                      ·
                        rfl

theorem cell23_5040081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_5040081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040081 prefixEnd_5040081 := by exact prefixLift 5040081
  have htrace : WordTrace (prefixWord ++ tailWord_5040081) baseStart_5040081 baseEnd_5040081 := by
    simpa [prefixWord, tailWord_5040081, baseEnd_5040081] using wordTrace_append hprefix tailTrace_5040081
  have hstable : (prefixWord ++ tailWord_5040081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040081).length < 2 ^ (prefixWord ++ tailWord_5040081).sum := by decide
  have hdescent : baseEnd_5040081 < baseStart_5040081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040088 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_5040088 : Nat := 118140960795 + 5040088 * 2 ^ 59
def prefixEnd_5040088 : Nat := 4983230072969 + 3 ^ 40 * 5040088 * 2
def baseEnd_5040088 : Nat := 2587987684957981866221063

theorem tailTrace_5040088 : CollatzResearch.WordTrace tailWord_5040088 prefixEnd_5040088 2587987684957981866221063 := by
  unfold tailWord_5040088
  simp only [CollatzResearch.WordTrace]
  refine ⟨91913555682314714672716459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122551407576419619563621945 91913555682314714672716459)
  ·
    refine ⟨137870333523472072009074689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91913555682314714672716459 137870333523472072009074689)
    ·
      refine ⟨103402750142604054006806017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137870333523472072009074689 103402750142604054006806017)
      ·
        refine ⟨77552062606953040505104513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103402750142604054006806017 77552062606953040505104513)
        ·
          refine ⟨58164046955214780378828385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77552062606953040505104513 58164046955214780378828385)
          ·
            refine ⟨43623035216411085284121289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58164046955214780378828385 43623035216411085284121289)
            ·
              refine ⟨32717276412308313963090967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43623035216411085284121289 32717276412308313963090967)
              ·
                refine ⟨49075914618462470944636451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32717276412308313963090967 49075914618462470944636451)
                ·
                  refine ⟨73613871927693706416954677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49075914618462470944636451 73613871927693706416954677)
                  ·
                    refine ⟨6901300493221284976589501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73613871927693706416954677 6901300493221284976589501)
                    ·
                      refine ⟨2587987684957981866221063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6901300493221284976589501 2587987684957981866221063)
                      ·
                        rfl

theorem cell23_5040088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_5040088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040088 prefixEnd_5040088 := by exact prefixLift 5040088
  have htrace : WordTrace (prefixWord ++ tailWord_5040088) baseStart_5040088 baseEnd_5040088 := by
    simpa [prefixWord, tailWord_5040088, baseEnd_5040088] using wordTrace_append hprefix tailTrace_5040088
  have hstable : (prefixWord ++ tailWord_5040088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040088).length < 2 ^ (prefixWord ++ tailWord_5040088).sum := by decide
  have hdescent : baseEnd_5040088 < baseStart_5040088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040089 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 2, 2, 2]
def baseStart_5040089 : Nat := 118140960795 + 5040089 * 2 ^ 59
def prefixEnd_5040089 : Nat := 4983230072969 + 3 ^ 40 * 5040089 * 2
def baseEnd_5040089 : Nat := 2587988198438636362308559

theorem tailTrace_5040089 : CollatzResearch.WordTrace tailWord_5040089 prefixEnd_5040089 2587988198438636362308559 := by
  unfold tailWord_5040089
  simp only [CollatzResearch.WordTrace]
  refine ⟨183827147837625806516219321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122551431891750537677479547 183827147837625806516219321)
  ·
    refine ⟨137870360878219354887164491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183827147837625806516219321 137870360878219354887164491)
    ·
      refine ⟨206805541317329032330746737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137870360878219354887164491 206805541317329032330746737)
      ·
        refine ⟨155104155987996774248060053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206805541317329032330746737 155104155987996774248060053)
        ·
          refine ⟨7270507311937348792877815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155104155987996774248060053 7270507311937348792877815)
          ·
            refine ⟨10905760967906023189316723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270507311937348792877815 10905760967906023189316723)
            ·
              refine ⟨16358641451859034783975085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905760967906023189316723 16358641451859034783975085)
              ·
                refine ⟨6134490544447138043990657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16358641451859034783975085 6134490544447138043990657)
                ·
                  refine ⟨4600867908335353532992993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6134490544447138043990657 4600867908335353532992993)
                  ·
                    refine ⟨3450650931251515149744745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4600867908335353532992993 3450650931251515149744745)
                    ·
                      refine ⟨2587988198438636362308559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450650931251515149744745 2587988198438636362308559)
                      ·
                        rfl

theorem cell23_5040089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_5040089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040089 prefixEnd_5040089 := by exact prefixLift 5040089
  have htrace : WordTrace (prefixWord ++ tailWord_5040089) baseStart_5040089 baseEnd_5040089 := by
    simpa [prefixWord, tailWord_5040089, baseEnd_5040089] using wordTrace_append hprefix tailTrace_5040089
  have hstable : (prefixWord ++ tailWord_5040089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040089).length < 2 ^ (prefixWord ++ tailWord_5040089).sum := by decide
  have hdescent : baseEnd_5040089 < baseStart_5040089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040128 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_5040128 : Nat := 118140960795 + 5040128 * 2 ^ 59
def prefixEnd_5040128 : Nat := 4983230072969 + 3 ^ 40 * 5040128 * 2
def baseEnd_5040128 : Nat := 2588008224184161709720879

theorem tailTrace_5040128 : CollatzResearch.WordTrace tailWord_5040128 prefixEnd_5040128 2588008224184161709720879 := by
  unfold tailWord_5040128
  simp only [CollatzResearch.WordTrace]
  refine ⟨91914285142242258088444519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122552380189656344117926025 91914285142242258088444519)
  ·
    refine ⟨137871427713363387132666779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91914285142242258088444519 137871427713363387132666779)
    ·
      refine ⟨206807141570045080699000169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137871427713363387132666779 206807141570045080699000169)
      ·
        refine ⟨155105356177533810524250127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206807141570045080699000169 155105356177533810524250127)
        ·
          refine ⟨232658034266300715786375191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155105356177533810524250127 232658034266300715786375191)
          ·
            refine ⟨348987051399451073679562787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232658034266300715786375191 348987051399451073679562787)
            ·
              refine ⟨523480577099176610519344181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348987051399451073679562787 523480577099176610519344181)
              ·
                refine ⟨49076304103047807236188517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523480577099176610519344181 49076304103047807236188517)
                ·
                  refine ⟨9201807019321463856785347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49076304103047807236188517 9201807019321463856785347)
                  ·
                    refine ⟨13802710528982195785178021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9201807019321463856785347 13802710528982195785178021)
                    ·
                      refine ⟨2588008224184161709720879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13802710528982195785178021 2588008224184161709720879)
                      ·
                        rfl

theorem cell23_5040128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_5040128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040128 prefixEnd_5040128 := by exact prefixLift 5040128
  have htrace : WordTrace (prefixWord ++ tailWord_5040128) baseStart_5040128 baseEnd_5040128 := by
    simpa [prefixWord, tailWord_5040128, baseEnd_5040128] using wordTrace_append hprefix tailTrace_5040128
  have hstable : (prefixWord ++ tailWord_5040128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040128).length < 2 ^ (prefixWord ++ tailWord_5040128).sum := by decide
  have hdescent : baseEnd_5040128 < baseStart_5040128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040165 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_5040165 : Nat := 118140960795 + 5040165 * 2 ^ 59
def prefixEnd_5040165 : Nat := 4983230072969 + 3 ^ 40 * 5040165 * 2
def baseEnd_5040165 : Nat := 2588027222968378064958209

theorem tailTrace_5040165 : CollatzResearch.WordTrace tailWord_5040165 prefixEnd_5040165 2588027222968378064958209 := by
  unfold tailWord_5040165
  simp only [CollatzResearch.WordTrace]
  refine ⟨183829919785350471495985949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122553279856900314330657299 183829919785350471495985949)
  ·
    refine ⟨68936219919506426810994731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183829919785350471495985949 68936219919506426810994731)
    ·
      refine ⟨103404329879259640216492097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68936219919506426810994731 103404329879259640216492097)
      ·
        refine ⟨77553247409444730162369073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103404329879259640216492097 77553247409444730162369073)
        ·
          refine ⟨58164935557083547621776805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77553247409444730162369073 58164935557083547621776805)
          ·
            refine ⟨10905925416953165179083151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58164935557083547621776805 10905925416953165179083151)
            ·
              refine ⟨16358888125429747768624727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905925416953165179083151 16358888125429747768624727)
              ·
                refine ⟨24538332188144621652937091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16358888125429747768624727 24538332188144621652937091)
                ·
                  refine ⟨36807498282216932479405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24538332188144621652937091 36807498282216932479405637)
                  ·
                    refine ⟨6901405927915674839888557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36807498282216932479405637 6901405927915674839888557)
                    ·
                      refine ⟨2588027222968378064958209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6901405927915674839888557 2588027222968378064958209)
                      ·
                        rfl

theorem cell23_5040165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_5040165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040165 prefixEnd_5040165 := by exact prefixLift 5040165
  have htrace : WordTrace (prefixWord ++ tailWord_5040165) baseStart_5040165 baseEnd_5040165 := by
    simpa [prefixWord, tailWord_5040165, baseEnd_5040165] using wordTrace_append hprefix tailTrace_5040165
  have hstable : (prefixWord ++ tailWord_5040165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040165).length < 2 ^ (prefixWord ++ tailWord_5040165).sum := by decide
  have hdescent : baseEnd_5040165 < baseStart_5040165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040182 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5040182 : Nat := 118140960795 + 5040182 * 2 ^ 59
def prefixEnd_5040182 : Nat := 4983230072969 + 3 ^ 40 * 5040182 * 2
def baseEnd_5040182 : Nat := 2588035952139504498445631

theorem tailTrace_5040182 : CollatzResearch.WordTrace tailWord_5040182 prefixEnd_5040182 2588035952139504498445631 := by
  unfold tailWord_5040182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489408739143055212459675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122553693217525922266236533 11489408739143055212459675)
  ·
    refine ⟨17234113108714582818689513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11489408739143055212459675 17234113108714582818689513)
    ·
      refine ⟨12925584831535937114017135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17234113108714582818689513 12925584831535937114017135)
      ·
        refine ⟨19388377247303905671025703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12925584831535937114017135 19388377247303905671025703)
        ·
          refine ⟨29082565870955858506538555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19388377247303905671025703 29082565870955858506538555)
          ·
            refine ⟨43623848806433787759807833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29082565870955858506538555 43623848806433787759807833)
            ·
              refine ⟨32717886604825340819855875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43623848806433787759807833 32717886604825340819855875)
              ·
                refine ⟨49076829907238011229783813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32717886604825340819855875 49076829907238011229783813)
                ·
                  refine ⟨9201905607607127105584465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49076829907238011229783813 9201905607607127105584465)
                  ·
                    refine ⟨6901429205705345329188349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9201905607607127105584465 6901429205705345329188349)
                    ·
                      refine ⟨2588035952139504498445631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6901429205705345329188349 2588035952139504498445631)
                      ·
                        rfl

theorem cell23_5040182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5040182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040182 prefixEnd_5040182 := by exact prefixLift 5040182
  have htrace : WordTrace (prefixWord ++ tailWord_5040182) baseStart_5040182 baseEnd_5040182 := by
    simpa [prefixWord, tailWord_5040182, baseEnd_5040182] using wordTrace_append hprefix tailTrace_5040182
  have hstable : (prefixWord ++ tailWord_5040182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040182).length < 2 ^ (prefixWord ++ tailWord_5040182).sum := by decide
  have hdescent : baseEnd_5040182 < baseStart_5040182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040185 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 8]
def baseStart_5040185 : Nat := 118140960795 + 5040185 * 2 ^ 59
def prefixEnd_5040185 : Nat := 4983230072969 + 3 ^ 40 * 5040185 * 2
def baseEnd_5040185 : Nat := 287559721397940887412013

theorem tailTrace_5040185 : CollatzResearch.WordTrace tailWord_5040185 prefixEnd_5040185 287559721397940887412013 := by
  unfold tailWord_5040185
  simp only [CollatzResearch.WordTrace]
  refine ⟨183830649245278014911714009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122553766163518676607809339 183830649245278014911714009)
  ·
    refine ⟨137872986933958511183785507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183830649245278014911714009 137872986933958511183785507)
    ·
      refine ⟨206809480400937766775678261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137872986933958511183785507 206809480400937766775678261)
      ·
        refine ⟨19388388787587915635219837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206809480400937766775678261 19388388787587915635219837)
        ·
          refine ⟨7270645795345468363207439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19388388787587915635219837 7270645795345468363207439)
          ·
            refine ⟨10905968693018202544811159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270645795345468363207439 10905968693018202544811159)
            ·
              refine ⟨16358953039527303817216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905968693018202544811159 16358953039527303817216739)
              ·
                refine ⟨24538429559290955725825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16358953039527303817216739 24538429559290955725825109)
                ·
                  refine ⟨287559721397940887412013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24538429559290955725825109 287559721397940887412013)
                  ·
                    rfl

theorem cell23_5040185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_5040185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040185 prefixEnd_5040185 := by exact prefixLift 5040185
  have htrace : WordTrace (prefixWord ++ tailWord_5040185) baseStart_5040185 baseEnd_5040185 := by
    simpa [prefixWord, tailWord_5040185, baseEnd_5040185] using wordTrace_append hprefix tailTrace_5040185
  have hstable : (prefixWord ++ tailWord_5040185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040185).length < 2 ^ (prefixWord ++ tailWord_5040185).sum := by decide
  have hdescent : baseEnd_5040185 < baseStart_5040185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040188 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_5040188 : Nat := 118140960795 + 5040188 * 2 ^ 59
def prefixEnd_5040188 : Nat := 4983230072969 + 3 ^ 40 * 5040188 * 2
def baseEnd_5040188 : Nat := 2588039033023431474970603

theorem tailTrace_5040188 : CollatzResearch.WordTrace tailWord_5040188 prefixEnd_5040188 2588039033023431474970603 := by
  unfold tailWord_5040188
  simp only [CollatzResearch.WordTrace]
  refine ⟨91915379332133573212036609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122553839109511430949382145 91915379332133573212036609)
  ·
    refine ⟨68936534499100179909027457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91915379332133573212036609 68936534499100179909027457)
    ·
      refine ⟨51702400874325134931770593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68936534499100179909027457 51702400874325134931770593)
      ·
        refine ⟨38776800655743851198827945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51702400874325134931770593 38776800655743851198827945)
        ·
          refine ⟨29082600491807888399120959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38776800655743851198827945 29082600491807888399120959)
          ·
            refine ⟨43623900737711832598681439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29082600491807888399120959 43623900737711832598681439)
            ·
              refine ⟨65435851106567748898022159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43623900737711832598681439 65435851106567748898022159)
              ·
                refine ⟨98153776659851623347033239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65435851106567748898022159 98153776659851623347033239)
                ·
                  refine ⟨147230664989777435020549859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98153776659851623347033239 147230664989777435020549859)
                  ·
                    refine ⟨220845997484666152530824789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147230664989777435020549859 220845997484666152530824789)
                    ·
                      refine ⟨2588039033023431474970603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220845997484666152530824789 2588039033023431474970603)
                      ·
                        rfl

theorem cell23_5040188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_5040188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040188 prefixEnd_5040188 := by exact prefixLift 5040188
  have htrace : WordTrace (prefixWord ++ tailWord_5040188) baseStart_5040188 baseEnd_5040188 := by
    simpa [prefixWord, tailWord_5040188, baseEnd_5040188] using wordTrace_append hprefix tailTrace_5040188
  have hstable : (prefixWord ++ tailWord_5040188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040188).length < 2 ^ (prefixWord ++ tailWord_5040188).sum := by decide
  have hdescent : baseEnd_5040188 < baseStart_5040188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040205 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5040205 : Nat := 118140960795 + 5040205 * 2 ^ 59
def prefixEnd_5040205 : Nat := 4983230072969 + 3 ^ 40 * 5040205 * 2
def baseEnd_5040205 : Nat := 2588047762194557908458025

theorem tailTrace_5040205 : CollatzResearch.WordTrace tailWord_5040205 prefixEnd_5040205 2588047762194557908458025 := by
  unfold tailWord_5040205
  simp only [CollatzResearch.WordTrace]
  refine ⟨183831378705205558327442069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122554252470137038884961379 183831378705205558327442069)
  ·
    refine ⟨8617095876806510546598847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 183831378705205558327442069 8617095876806510546598847)
    ·
      refine ⟨12925643815209765819898271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8617095876806510546598847 12925643815209765819898271)
      ·
        refine ⟨19388465722814648729847407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12925643815209765819898271 19388465722814648729847407)
        ·
          refine ⟨29082698584221973094771111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19388465722814648729847407 29082698584221973094771111)
          ·
            refine ⟨43624047876332959642156667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29082698584221973094771111 43624047876332959642156667)
            ·
              refine ⟨65436071814499439463235001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43624047876332959642156667 65436071814499439463235001)
              ·
                refine ⟨49077053860874579597426251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65436071814499439463235001 49077053860874579597426251)
                ·
                  refine ⟨73615580791311869396139377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49077053860874579597426251 73615580791311869396139377)
                  ·
                    refine ⟨55211685593483902047104533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73615580791311869396139377 55211685593483902047104533)
                    ·
                      refine ⟨2588047762194557908458025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55211685593483902047104533 2588047762194557908458025)
                      ·
                        rfl

theorem cell23_5040205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5040205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040205 prefixEnd_5040205 := by exact prefixLift 5040205
  have htrace : WordTrace (prefixWord ++ tailWord_5040205) baseStart_5040205 baseEnd_5040205 := by
    simpa [prefixWord, tailWord_5040205, baseEnd_5040205] using wordTrace_append hprefix tailTrace_5040205
  have hstable : (prefixWord ++ tailWord_5040205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040205).length < 2 ^ (prefixWord ++ tailWord_5040205).sum := by decide
  have hdescent : baseEnd_5040205 < baseStart_5040205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040215 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 1, 5]
def baseStart_5040215 : Nat := 118140960795 + 5040215 * 2 ^ 59
def prefixEnd_5040215 : Nat := 4983230072969 + 3 ^ 40 * 5040215 * 2
def baseEnd_5040215 : Nat := 862684299000367623110993

theorem tailTrace_5040215 : CollatzResearch.WordTrace tailWord_5040215 prefixEnd_5040215 862684299000367623110993 := by
  unfold tailWord_5040215
  simp only [CollatzResearch.WordTrace]
  refine ⟨183831743435169330035306099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122554495623446220023537399 183831743435169330035306099)
  ·
    refine ⟨275747615152753995052959149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183831743435169330035306099 275747615152753995052959149)
    ·
      refine ⟨103405355682282748144859681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275747615152753995052959149 103405355682282748144859681)
      ·
        refine ⟨77554016761712061108644761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103405355682282748144859681 77554016761712061108644761)
        ·
          refine ⟨58165512571284045831483571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77554016761712061108644761 58165512571284045831483571)
          ·
            refine ⟨87248268856926068747225357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58165512571284045831483571 87248268856926068747225357)
            ·
              refine ⟨32718100821347275780209509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87248268856926068747225357 32718100821347275780209509)
              ·
                refine ⟨6134643904002614208789283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32718100821347275780209509 6134643904002614208789283)
                ·
                  refine ⟨9201965856003921313183925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134643904002614208789283 9201965856003921313183925)
                  ·
                    refine ⟨862684299000367623110993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9201965856003921313183925 862684299000367623110993)
                    ·
                      rfl

theorem cell23_5040215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_5040215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040215 prefixEnd_5040215 := by exact prefixLift 5040215
  have htrace : WordTrace (prefixWord ++ tailWord_5040215) baseStart_5040215 baseEnd_5040215 := by
    simpa [prefixWord, tailWord_5040215, baseEnd_5040215] using wordTrace_append hprefix tailTrace_5040215
  have hstable : (prefixWord ++ tailWord_5040215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040215).length < 2 ^ (prefixWord ++ tailWord_5040215).sum := by decide
  have hdescent : baseEnd_5040215 < baseStart_5040215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040246 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5040246 : Nat := 118140960795 + 5040246 * 2 ^ 59
def prefixEnd_5040246 : Nat := 4983230072969 + 3 ^ 40 * 5040246 * 2
def baseEnd_5040246 : Nat := 2588068814901392248045337

theorem tailTrace_5040246 : CollatzResearch.WordTrace tailWord_5040246 prefixEnd_5040246 2588068814901392248045337 := by
  unfold tailWord_5040246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489554631128563895605287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122555249398704681553123061 11489554631128563895605287)
  ·
    refine ⟨17234331946692845843407931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11489554631128563895605287 17234331946692845843407931)
    ·
      refine ⟨25851497920039268765111897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17234331946692845843407931 25851497920039268765111897)
      ·
        refine ⟨19388623440029451573833923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25851497920039268765111897 19388623440029451573833923)
        ·
          refine ⟨29082935160044177360750885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19388623440029451573833923 29082935160044177360750885)
          ·
            refine ⟨5453050342508283255140791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29082935160044177360750885 5453050342508283255140791)
            ·
              refine ⟨8179575513762424882711187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453050342508283255140791 8179575513762424882711187)
              ·
                refine ⟨12269363270643637324066781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8179575513762424882711187 12269363270643637324066781)
                ·
                  refine ⟨4601011226491363996525043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12269363270643637324066781 4601011226491363996525043)
                  ·
                    refine ⟨6901516839737045994787565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4601011226491363996525043 6901516839737045994787565)
                    ·
                      refine ⟨2588068814901392248045337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6901516839737045994787565 2588068814901392248045337)
                      ·
                        rfl

theorem cell23_5040246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5040246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040246 prefixEnd_5040246 := by exact prefixLift 5040246
  have htrace : WordTrace (prefixWord ++ tailWord_5040246) baseStart_5040246 baseEnd_5040246 := by
    simpa [prefixWord, tailWord_5040246, baseEnd_5040246] using wordTrace_append hprefix tailTrace_5040246
  have hstable : (prefixWord ++ tailWord_5040246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040246).length < 2 ^ (prefixWord ++ tailWord_5040246).sum := by decide
  have hdescent : baseEnd_5040246 < baseStart_5040246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040265 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_5040265 : Nat := 118140960795 + 5040265 * 2 ^ 59
def prefixEnd_5040265 : Nat := 4983230072969 + 3 ^ 40 * 5040265 * 2
def baseEnd_5040265 : Nat := 2588078571033827673707749

theorem tailTrace_5040265 : CollatzResearch.WordTrace tailWord_5040265 prefixEnd_5040265 2588078571033827673707749 := by
  unfold tailWord_5040265
  simp only [CollatzResearch.WordTrace]
  refine ⟨183833567084988188574626249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122555711389992125716417499 183833567084988188574626249)
  ·
    refine ⟨137875175313741141430969687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183833567084988188574626249 137875175313741141430969687)
    ·
      refine ⟨206812762970611712146454531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137875175313741141430969687 206812762970611712146454531)
      ·
        refine ⟨310219144455917568219681797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206812762970611712146454531 310219144455917568219681797)
        ·
          refine ⟨58166089585484544041190337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310219144455917568219681797 58166089585484544041190337)
          ·
            refine ⟨43624567189113408030892753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58166089585484544041190337 43624567189113408030892753)
            ·
              refine ⟨32718425391835056023169565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43624567189113408030892753 32718425391835056023169565)
              ·
                refine ⟨12269409521938146008688587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32718425391835056023169565 12269409521938146008688587)
                ·
                  refine ⟨18404114282907219013032881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12269409521938146008688587 18404114282907219013032881)
                  ·
                    refine ⟨13803085712180414259774661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18404114282907219013032881 13803085712180414259774661)
                    ·
                      refine ⟨2588078571033827673707749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13803085712180414259774661 2588078571033827673707749)
                      ·
                        rfl

theorem cell23_5040265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_5040265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040265 prefixEnd_5040265 := by exact prefixLift 5040265
  have htrace : WordTrace (prefixWord ++ tailWord_5040265) baseStart_5040265 baseEnd_5040265 := by
    simpa [prefixWord, tailWord_5040265, baseEnd_5040265] using wordTrace_append hprefix tailTrace_5040265
  have hstable : (prefixWord ++ tailWord_5040265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040265).length < 2 ^ (prefixWord ++ tailWord_5040265).sum := by decide
  have hdescent : baseEnd_5040265 < baseStart_5040265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040309 : List Nat := [1, 3, 3, 4, 1, 2, 1, 8]
def baseStart_5040309 : Nat := 118140960795 + 5040309 * 2 ^ 59
def prefixEnd_5040309 : Nat := 4983230072969 + 3 ^ 40 * 5040309 * 2
def baseEnd_5040309 : Nat := 95855598673430574131761

theorem tailTrace_5040309 : CollatzResearch.WordTrace tailWord_5040309 prefixEnd_5040309 95855598673430574131761 := by
  unfold tailWord_5040309
  simp only [CollatzResearch.WordTrace]
  refine ⟨183835171896828784089227981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122556781264552522726151987 183835171896828784089227981)
  ·
    refine ⟨68938189461310794033460493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183835171896828784089227981 68938189461310794033460493)
    ·
      refine ⟨25851821047991547762547685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68938189461310794033460493 25851821047991547762547685)
      ·
        refine ⟨4847216446498415205477691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25851821047991547762547685 4847216446498415205477691)
        ·
          refine ⟨7270824669747622808216537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847216446498415205477691 7270824669747622808216537)
          ·
            refine ⟨5453118502310717106162403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7270824669747622808216537 5453118502310717106162403)
            ·
              refine ⟨8179677753466075659243605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453118502310717106162403 8179677753466075659243605)
              ·
                refine ⟨95855598673430574131761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8179677753466075659243605 95855598673430574131761)
                ·
                  rfl

theorem cell23_5040309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 8].length) (baseStart_5040309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040309 prefixEnd_5040309 := by exact prefixLift 5040309
  have htrace : WordTrace (prefixWord ++ tailWord_5040309) baseStart_5040309 baseEnd_5040309 := by
    simpa [prefixWord, tailWord_5040309, baseEnd_5040309] using wordTrace_append hprefix tailTrace_5040309
  have hstable : (prefixWord ++ tailWord_5040309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040309).length < 2 ^ (prefixWord ++ tailWord_5040309).sum := by decide
  have hdescent : baseEnd_5040309 < baseStart_5040309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040312 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_5040312 : Nat := 118140960795 + 5040312 * 2 ^ 59
def prefixEnd_5040312 : Nat := 4983230072969 + 3 ^ 40 * 5040312 * 2
def baseEnd_5040312 : Nat := 2588102704624588989820033

theorem tailTrace_5040312 : CollatzResearch.WordTrace tailWord_5040312 prefixEnd_5040312 2588102704624588989820033 := by
  unfold tailWord_5040312
  simp only [CollatzResearch.WordTrace]
  refine ⟨91917640657908957800793595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122556854210545277067724793 91917640657908957800793595)
  ·
    refine ⟨137876460986863436701190393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91917640657908957800793595 137876460986863436701190393)
    ·
      refine ⟨103407345740147577525892795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137876460986863436701190393 103407345740147577525892795)
      ·
        refine ⟨155111018610221366288839193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103407345740147577525892795 155111018610221366288839193)
        ·
          refine ⟨116333263957666024716629395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155111018610221366288839193 116333263957666024716629395)
          ·
            refine ⟨174499895936499037074944093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116333263957666024716629395 174499895936499037074944093)
            ·
              refine ⟨65437460976187138903104035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174499895936499037074944093 65437460976187138903104035)
              ·
                refine ⟨98156191464280708354656053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65437460976187138903104035 98156191464280708354656053)
                ·
                  refine ⟨9202142949776316408249005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98156191464280708354656053 9202142949776316408249005)
                  ·
                    refine ⟨3450803606166118653093377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9202142949776316408249005 3450803606166118653093377)
                    ·
                      refine ⟨2588102704624588989820033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450803606166118653093377 2588102704624588989820033)
                      ·
                        rfl

theorem cell23_5040312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_5040312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040312 prefixEnd_5040312 := by exact prefixLift 5040312
  have htrace : WordTrace (prefixWord ++ tailWord_5040312) baseStart_5040312 baseEnd_5040312 := by
    simpa [prefixWord, tailWord_5040312, baseEnd_5040312] using wordTrace_append hprefix tailTrace_5040312
  have hstable : (prefixWord ++ tailWord_5040312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040312).length < 2 ^ (prefixWord ++ tailWord_5040312).sum := by decide
  have hdescent : baseEnd_5040312 < baseStart_5040312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040345 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_5040345 : Nat := 118140960795 + 5040345 * 2 ^ 59
def prefixEnd_5040345 : Nat := 4983230072969 + 3 ^ 40 * 5040345 * 2
def baseEnd_5040345 : Nat := 2588119649486187360707381

theorem tailTrace_5040345 : CollatzResearch.WordTrace tailWord_5040345 prefixEnd_5040345 2588119649486187360707381 := by
  unfold tailWord_5040345
  simp only [CollatzResearch.WordTrace]
  refine ⟨183836484924698362237538489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122557656616465574825025659 183836484924698362237538489)
  ·
    refine ⟨137877363693523771678153867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183836484924698362237538489 137877363693523771678153867)
    ·
      refine ⟨206816045540285657517230801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137877363693523771678153867 206816045540285657517230801)
      ·
        refine ⟨155112034155214243137923101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206816045540285657517230801 155112034155214243137923101)
        ·
          refine ⟨58167012808205341176721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155112034155214243137923101 58167012808205341176721163)
          ·
            refine ⟨87250519212308011765081745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58167012808205341176721163 87250519212308011765081745)
            ·
              refine ⟨65437889409231008823811309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87250519212308011765081745 65437889409231008823811309)
              ·
                refine ⟨24539208528461628308929241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65437889409231008823811309 24539208528461628308929241)
                ·
                  refine ⟨18404406396346221231696931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24539208528461628308929241 18404406396346221231696931)
                  ·
                    refine ⟨27606609594519331847545397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18404406396346221231696931 27606609594519331847545397)
                    ·
                      refine ⟨2588119649486187360707381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27606609594519331847545397 2588119649486187360707381)
                      ·
                        rfl

theorem cell23_5040345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_5040345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040345 prefixEnd_5040345 := by exact prefixLift 5040345
  have htrace : WordTrace (prefixWord ++ tailWord_5040345) baseStart_5040345 baseEnd_5040345 := by
    simpa [prefixWord, tailWord_5040345, baseEnd_5040345] using wordTrace_append hprefix tailTrace_5040345
  have hstable : (prefixWord ++ tailWord_5040345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040345).length < 2 ^ (prefixWord ++ tailWord_5040345).sum := by decide
  have hdescent : baseEnd_5040345 < baseStart_5040345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040346 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_5040346 : Nat := 118140960795 + 5040346 * 2 ^ 59
def prefixEnd_5040346 : Nat := 4983230072969 + 3 ^ 40 * 5040346 * 2
def baseEnd_5040346 : Nat := 2588120162966841856794877

theorem tailTrace_5040346 : CollatzResearch.WordTrace tailWord_5040346 prefixEnd_5040346 2588120162966841856794877 := by
  unfold tailWord_5040346
  simp only [CollatzResearch.WordTrace]
  refine ⟨45959130349423684852081223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122557680931796492938883261 45959130349423684852081223)
  ·
    refine ⟨68938695524135527278121835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45959130349423684852081223 68938695524135527278121835)
    ·
      refine ⟨103408043286203290917182753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68938695524135527278121835 103408043286203290917182753)
      ·
        refine ⟨77556032464652468187887065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103408043286203290917182753 77556032464652468187887065)
        ·
          refine ⟨58167024348489351140915299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77556032464652468187887065 58167024348489351140915299)
          ·
            refine ⟨87250536522734026711372949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58167024348489351140915299 87250536522734026711372949)
            ·
              refine ⟨4089868899503157502095607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87250536522734026711372949 4089868899503157502095607)
              ·
                refine ⟨6134803349254736253143411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089868899503157502095607 6134803349254736253143411)
                ·
                  refine ⟨9202205023882104379715117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6134803349254736253143411 9202205023882104379715117)
                  ·
                    refine ⟨3450826883955789142393169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9202205023882104379715117 3450826883955789142393169)
                    ·
                      refine ⟨2588120162966841856794877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450826883955789142393169 2588120162966841856794877)
                      ·
                        rfl

theorem cell23_5040346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_5040346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040346 prefixEnd_5040346 := by exact prefixLift 5040346
  have htrace : WordTrace (prefixWord ++ tailWord_5040346) baseStart_5040346 baseEnd_5040346 := by
    simpa [prefixWord, tailWord_5040346, baseEnd_5040346] using wordTrace_append hprefix tailTrace_5040346
  have hstable : (prefixWord ++ tailWord_5040346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040346).length < 2 ^ (prefixWord ++ tailWord_5040346).sum := by decide
  have hdescent : baseEnd_5040346 < baseStart_5040346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040382 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_5040382 : Nat := 118140960795 + 5040382 * 2 ^ 59
def prefixEnd_5040382 : Nat := 4983230072969 + 3 ^ 40 * 5040382 * 2
def baseEnd_5040382 : Nat := 287570960918933746216079

theorem tailTrace_5040382 : CollatzResearch.WordTrace tailWord_5040382 prefixEnd_5040382 287570960918933746216079 := by
  unfold tailWord_5040382
  simp only [CollatzResearch.WordTrace]
  refine ⟨22979729303195539694579425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122558556283709545037756933 22979729303195539694579425)
  ·
    refine ⟨17234796977396654770934569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22979729303195539694579425 17234796977396654770934569)
    ·
      refine ⟨12926097733047491078200927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17234796977396654770934569 12926097733047491078200927)
      ·
        refine ⟨19389146599571236617301391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12926097733047491078200927 19389146599571236617301391)
        ·
          refine ⟨29083719899356854925952087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19389146599571236617301391 29083719899356854925952087)
          ·
            refine ⟨43625579849035282388928131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29083719899356854925952087 43625579849035282388928131)
            ·
              refine ⟨65438369773552923583392197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43625579849035282388928131 65438369773552923583392197)
              ·
                refine ⟨12269694332541173171886037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65438369773552923583392197 12269694332541173171886037)
                ·
                  refine ⟨287570960918933746216079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12269694332541173171886037 287570960918933746216079)
                  ·
                    rfl

theorem cell23_5040382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_5040382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040382 prefixEnd_5040382 := by exact prefixLift 5040382
  have htrace : WordTrace (prefixWord ++ tailWord_5040382) baseStart_5040382 baseEnd_5040382 := by
    simpa [prefixWord, tailWord_5040382, baseEnd_5040382] using wordTrace_append hprefix tailTrace_5040382
  have hstable : (prefixWord ++ tailWord_5040382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040382).length < 2 ^ (prefixWord ++ tailWord_5040382).sum := by decide
  have hdescent : baseEnd_5040382 < baseStart_5040382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040395 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 7]
def baseStart_5040395 : Nat := 118140960795 + 5040395 * 2 ^ 59
def prefixEnd_5040395 : Nat := 4983230072969 + 3 ^ 40 * 5040395 * 2
def baseEnd_5040395 : Nat := 862715107839637388360717

theorem tailTrace_5040395 : CollatzResearch.WordTrace tailWord_5040395 prefixEnd_5040395 862715107839637388360717 := by
  unfold tailWord_5040395
  simp only [CollatzResearch.WordTrace]
  refine ⟨183838308574517220776858639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122558872383011480517905759 183838308574517220776858639)
  ·
    refine ⟨275757462861775831165287959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183838308574517220776858639 275757462861775831165287959)
    ·
      refine ⟨413636194292663746747931939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275757462861775831165287959 413636194292663746747931939)
      ·
        refine ⟨620454291438995620121897909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413636194292663746747931939 620454291438995620121897909)
        ·
          refine ⟨58167589822405839386427929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 620454291438995620121897909 58167589822405839386427929)
          ·
            refine ⟨43625692366804379539820947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58167589822405839386427929 43625692366804379539820947)
            ·
              refine ⟨65438538550206569309731421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43625692366804379539820947 65438538550206569309731421)
              ·
                refine ⟨24539451956327463491149283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65438538550206569309731421 24539451956327463491149283)
                ·
                  refine ⟨36809177934491195236723925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24539451956327463491149283 36809177934491195236723925)
                  ·
                    refine ⟨862715107839637388360717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36809177934491195236723925 862715107839637388360717)
                    ·
                      rfl

theorem cell23_5040395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 7].length) (baseStart_5040395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040395 prefixEnd_5040395 := by exact prefixLift 5040395
  have htrace : WordTrace (prefixWord ++ tailWord_5040395) baseStart_5040395 baseEnd_5040395 := by
    simpa [prefixWord, tailWord_5040395, baseEnd_5040395] using wordTrace_append hprefix tailTrace_5040395
  have hstable : (prefixWord ++ tailWord_5040395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040395).length < 2 ^ (prefixWord ++ tailWord_5040395).sum := by decide
  have hdescent : baseEnd_5040395 < baseStart_5040395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040416 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 5]
def baseStart_5040416 : Nat := 118140960795 + 5040416 * 2 ^ 59
def prefixEnd_5040416 : Nat := 4983230072969 + 3 ^ 40 * 5040416 * 2
def baseEnd_5040416 : Nat := 287572900734739620324395

theorem tailTrace_5040416 : CollatzResearch.WordTrace tailWord_5040416 prefixEnd_5040416 287572900734739620324395 := by
  unfold tailWord_5040416
  simp only [CollatzResearch.WordTrace]
  refine ⟨91919537253720570681686551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122559383004960760908915401 91919537253720570681686551)
  ·
    refine ⟨137879305880580856022529827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91919537253720570681686551 137879305880580856022529827)
    ·
      refine ⟨206818958820871284033794741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137879305880580856022529827 206818958820871284033794741)
      ·
        refine ⟨19389277389456682878168257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206818958820871284033794741 19389277389456682878168257)
        ·
          refine ⟨14541958042092512158626193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19389277389456682878168257 14541958042092512158626193)
          ·
            refine ⟨10906468531569384118969645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14541958042092512158626193 10906468531569384118969645)
            ·
              refine ⟨4089925699338519044613617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10906468531569384118969645 4089925699338519044613617)
              ·
                refine ⟨3067444274503889283460213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4089925699338519044613617 3067444274503889283460213)
                ·
                  refine ⟨287572900734739620324395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067444274503889283460213 287572900734739620324395)
                  ·
                    rfl

theorem cell23_5040416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 5].length) (baseStart_5040416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040416 prefixEnd_5040416 := by exact prefixLift 5040416
  have htrace : WordTrace (prefixWord ++ tailWord_5040416) baseStart_5040416 baseEnd_5040416 := by
    simpa [prefixWord, tailWord_5040416, baseEnd_5040416] using wordTrace_append hprefix tailTrace_5040416
  have hstable : (prefixWord ++ tailWord_5040416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040416).length < 2 ^ (prefixWord ++ tailWord_5040416).sum := by decide
  have hdescent : baseEnd_5040416 < baseStart_5040416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040499 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 3]
def baseStart_5040499 : Nat := 118140960795 + 5040499 * 2 ^ 59
def prefixEnd_5040499 : Nat := 4983230072969 + 3 ^ 40 * 5040499 * 2
def baseEnd_5040499 : Nat := 2588198725506979758181673

theorem tailTrace_5040499 : CollatzResearch.WordTrace tailWord_5040499 prefixEnd_5040499 2588198725506979758181673 := by
  unfold tailWord_5040499
  simp only [CollatzResearch.WordTrace]
  refine ⟨183842101766140446538644551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122561401177426964359096367 183842101766140446538644551)
  ·
    refine ⟨275763152649210669807966827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183842101766140446538644551 275763152649210669807966827)
    ·
      refine ⟨413644728973816004711950241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275763152649210669807966827 413644728973816004711950241)
      ·
        refine ⟨310233546730362003533962681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413644728973816004711950241 310233546730362003533962681)
        ·
          refine ⟨232675160047771502650472011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310233546730362003533962681 232675160047771502650472011)
          ·
            refine ⟨349012740071657253975708017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232675160047771502650472011 349012740071657253975708017)
            ·
              refine ⟨261759555053742940481781013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349012740071657253975708017 261759555053742940481781013)
              ·
                refine ⟨12269979143144200335083485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261759555053742940481781013 12269979143144200335083485)
                ·
                  refine ⟨4601242178679075125656307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12269979143144200335083485 4601242178679075125656307)
                  ·
                    refine ⟨6901863268018612688484461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4601242178679075125656307 6901863268018612688484461)
                    ·
                      refine ⟨2588198725506979758181673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6901863268018612688484461 2588198725506979758181673)
                      ·
                        rfl

theorem cell23_5040499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_5040499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040499 prefixEnd_5040499 := by exact prefixLift 5040499
  have htrace : WordTrace (prefixWord ++ tailWord_5040499) baseStart_5040499 baseEnd_5040499 := by
    simpa [prefixWord, tailWord_5040499, baseEnd_5040499] using wordTrace_append hprefix tailTrace_5040499
  have hstable : (prefixWord ++ tailWord_5040499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040499).length < 2 ^ (prefixWord ++ tailWord_5040499).sum := by decide
  have hdescent : baseEnd_5040499 < baseStart_5040499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040519 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 1, 5]
def baseStart_5040519 : Nat := 118140960795 + 5040519 * 2 ^ 59
def prefixEnd_5040519 : Nat := 4983230072969 + 3 ^ 40 * 5040519 * 2
def baseEnd_5040519 : Nat := 862736331706689893310527

theorem tailTrace_5040519 : CollatzResearch.WordTrace tailWord_5040519 prefixEnd_5040519 862736331706689893310527 := by
  unfold tailWord_5040519
  simp only [CollatzResearch.WordTrace]
  refine ⟨183842831226067989954372611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122561887484045326636248407 183842831226067989954372611)
  ·
    refine ⟨275764246839101984931558917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183842831226067989954372611 275764246839101984931558917)
    ·
      refine ⟨51705796282331622174667297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275764246839101984931558917 51705796282331622174667297)
      ·
        refine ⟨38779347211748716631000473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51705796282331622174667297 38779347211748716631000473)
        ·
          refine ⟨29084510408811537473250355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38779347211748716631000473 29084510408811537473250355)
          ·
            refine ⟨43626765613217306209875533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29084510408811537473250355 43626765613217306209875533)
            ·
              refine ⟨16360037104956489828703325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43626765613217306209875533 16360037104956489828703325)
              ·
                refine ⟨6135013914358683685763747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16360037104956489828703325 6135013914358683685763747)
                ·
                  refine ⟨9202520871538025528645621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6135013914358683685763747 9202520871538025528645621)
                  ·
                    refine ⟨862736331706689893310527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9202520871538025528645621 862736331706689893310527)
                    ·
                      rfl

theorem cell23_5040519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_5040519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040519 prefixEnd_5040519 := by exact prefixLift 5040519
  have htrace : WordTrace (prefixWord ++ tailWord_5040519) baseStart_5040519 baseEnd_5040519 := by
    simpa [prefixWord, tailWord_5040519, baseEnd_5040519] using wordTrace_append hprefix tailTrace_5040519
  have hstable : (prefixWord ++ tailWord_5040519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040519).length < 2 ^ (prefixWord ++ tailWord_5040519).sum := by decide
  have hdescent : baseEnd_5040519 < baseStart_5040519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040562 : List Nat := [3, 2, 1, 1, 1, 1, 5, 9]
def baseStart_5040562 : Nat := 118140960795 + 5040562 * 2 ^ 59
def prefixEnd_5040562 : Nat := 4983230072969 + 3 ^ 40 * 5040562 * 2
def baseEnd_5040562 : Nat := 95860410177341222655329

theorem tailTrace_5040562 : CollatzResearch.WordTrace tailWord_5040562 prefixEnd_5040562 95860410177341222655329 := by
  unfold tailWord_5040562
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961099891228052074546985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122562933043274805532125293 45961099891228052074546985)
  ·
    refine ⟨34470824918421039055910239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45961099891228052074546985 34470824918421039055910239)
    ·
      refine ⟨51706237377631558583865359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34470824918421039055910239 51706237377631558583865359)
      ·
        refine ⟨77559356066447337875798039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51706237377631558583865359 77559356066447337875798039)
        ·
          refine ⟨116339034099671006813697059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77559356066447337875798039 116339034099671006813697059)
          ·
            refine ⟨174508551149506510220545589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116339034099671006813697059 174508551149506510220545589)
            ·
              refine ⟨16360176670266235333176149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174508551149506510220545589 16360176670266235333176149)
              ·
                refine ⟨95860410177341222655329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16360176670266235333176149 95860410177341222655329)
                ·
                  rfl

theorem cell23_5040562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_5040562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040562 prefixEnd_5040562 := by exact prefixLift 5040562
  have htrace : WordTrace (prefixWord ++ tailWord_5040562) baseStart_5040562 baseEnd_5040562 := by
    simpa [prefixWord, tailWord_5040562, baseEnd_5040562] using wordTrace_append hprefix tailTrace_5040562
  have hstable : (prefixWord ++ tailWord_5040562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040562).length < 2 ^ (prefixWord ++ tailWord_5040562).sum := by decide
  have hdescent : baseEnd_5040562 < baseStart_5040562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040577 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5040577 : Nat := 118140960795 + 5040577 * 2 ^ 59
def prefixEnd_5040577 : Nat := 4983230072969 + 3 ^ 40 * 5040577 * 2
def baseEnd_5040577 : Nat := 2588238776998030453006315

theorem tailTrace_5040577 : CollatzResearch.WordTrace tailWord_5040577 prefixEnd_5040577 2588238776998030453006315 := by
  unfold tailWord_5040577
  simp only [CollatzResearch.WordTrace]
  refine ⟨183844946659857865859983985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122563297773238577239989323 183844946659857865859983985)
  ·
    refine ⟨137883709994893399394987989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183844946659857865859983985 137883709994893399394987989)
    ·
      refine ⟨3231649453005314048320031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 137883709994893399394987989 3231649453005314048320031)
      ·
        refine ⟨4847474179507971072480047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231649453005314048320031 4847474179507971072480047)
        ·
          refine ⟨7271211269261956608720071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847474179507971072480047 7271211269261956608720071)
          ·
            refine ⟨10906816903892934913080107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7271211269261956608720071 10906816903892934913080107)
            ·
              refine ⟨16360225355839402369620161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10906816903892934913080107 16360225355839402369620161)
              ·
                refine ⟨12270169016879551777215121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16360225355839402369620161 12270169016879551777215121)
                ·
                  refine ⟨9202626762659663832911341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12270169016879551777215121 9202626762659663832911341)
                  ·
                    refine ⟨3450985035997373937341753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9202626762659663832911341 3450985035997373937341753)
                    ·
                      refine ⟨2588238776998030453006315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3450985035997373937341753 2588238776998030453006315)
                      ·
                        rfl

theorem cell23_5040577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5040577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040577 prefixEnd_5040577 := by exact prefixLift 5040577
  have htrace : WordTrace (prefixWord ++ tailWord_5040577) baseStart_5040577 baseEnd_5040577 := by
    simpa [prefixWord, tailWord_5040577, baseEnd_5040577] using wordTrace_append hprefix tailTrace_5040577
  have hstable : (prefixWord ++ tailWord_5040577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040577).length < 2 ^ (prefixWord ++ tailWord_5040577).sum := by decide
  have hdescent : baseEnd_5040577 < baseStart_5040577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040599 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_5040599 : Nat := 118140960795 + 5040599 * 2 ^ 59
def prefixEnd_5040599 : Nat := 4983230072969 + 3 ^ 40 * 5040599 * 2
def baseEnd_5040599 : Nat := 2588250073572429366931213

theorem tailTrace_5040599 : CollatzResearch.WordTrace tailWord_5040599 prefixEnd_5040599 2588250073572429366931213 := by
  unfold tailWord_5040599
  simp only [CollatzResearch.WordTrace]
  refine ⟨183845749065778163617284851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122563832710518775744856567 183845749065778163617284851)
  ·
    refine ⟨275768623598667245425927277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183845749065778163617284851 275768623598667245425927277)
    ·
      refine ⟨103413233849500217034722729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275768623598667245425927277 103413233849500217034722729)
      ·
        refine ⟨77559925387125162776042047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103413233849500217034722729 77559925387125162776042047)
        ·
          refine ⟨116339888080687744164063071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77559925387125162776042047 116339888080687744164063071)
          ·
            refine ⟨174509832121031616246094607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116339888080687744164063071 174509832121031616246094607)
            ·
              refine ⟨261764748181547424369141911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174509832121031616246094607 261764748181547424369141911)
              ·
                refine ⟨392647122272321136553712867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261764748181547424369141911 392647122272321136553712867)
                ·
                  refine ⟨588970683408481704830569301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392647122272321136553712867 588970683408481704830569301)
                  ·
                    refine ⟨3451000098096572489241617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 588970683408481704830569301 3451000098096572489241617)
                    ·
                      refine ⟨2588250073572429366931213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451000098096572489241617 2588250073572429366931213)
                      ·
                        rfl

theorem cell23_5040599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_5040599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040599 prefixEnd_5040599 := by exact prefixLift 5040599
  have htrace : WordTrace (prefixWord ++ tailWord_5040599) baseStart_5040599 baseEnd_5040599 := by
    simpa [prefixWord, tailWord_5040599, baseEnd_5040599] using wordTrace_append hprefix tailTrace_5040599
  have hstable : (prefixWord ++ tailWord_5040599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040599).length < 2 ^ (prefixWord ++ tailWord_5040599).sum := by decide
  have hdescent : baseEnd_5040599 < baseStart_5040599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040610 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5040610 : Nat := 118140960795 + 5040610 * 2 ^ 59
def prefixEnd_5040610 : Nat := 4983230072969 + 3 ^ 40 * 5040610 * 2
def baseEnd_5040610 : Nat := 2588255721859628823893663

theorem tailTrace_5040610 : CollatzResearch.WordTrace tailWord_5040610 prefixEnd_5040610 2588255721859628823893663 := by
  unfold tailWord_5040610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45961537567184578123983821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122564100179158874997290189 45961537567184578123983821)
  ·
    refine ⟨17235576587694216796493933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45961537567184578123983821 17235576587694216796493933)
    ·
      refine ⟨6463341220385331298685225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17235576587694216796493933 6463341220385331298685225)
      ·
        refine ⟨4847505915288998474013919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6463341220385331298685225 4847505915288998474013919)
        ·
          refine ⟨7271258872933497711020879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847505915288998474013919 7271258872933497711020879)
          ·
            refine ⟨10906888309400246566531319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7271258872933497711020879 10906888309400246566531319)
            ·
              refine ⟨16360332464100369849796979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10906888309400246566531319 16360332464100369849796979)
              ·
                refine ⟨24540498696150554774695469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16360332464100369849796979 24540498696150554774695469)
                ·
                  refine ⟨9202687011056458040510801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24540498696150554774695469 9202687011056458040510801)
                  ·
                    refine ⟨6902015258292343530383101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9202687011056458040510801 6902015258292343530383101)
                    ·
                      refine ⟨2588255721859628823893663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6902015258292343530383101 2588255721859628823893663)
                      ·
                        rfl

theorem cell23_5040610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5040610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040610 prefixEnd_5040610 := by exact prefixLift 5040610
  have htrace : WordTrace (prefixWord ++ tailWord_5040610) baseStart_5040610 baseEnd_5040610 := by
    simpa [prefixWord, tailWord_5040610, baseEnd_5040610] using wordTrace_append hprefix tailTrace_5040610
  have hstable : (prefixWord ++ tailWord_5040610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040610).length < 2 ^ (prefixWord ++ tailWord_5040610).sum := by decide
  have hdescent : baseEnd_5040610 < baseStart_5040610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_5040612 : Nat := 118140960795 + 5040612 * 2 ^ 59
def prefixEnd_5040612 : Nat := 4983230072969 + 3 ^ 40 * 5040612 * 2
def baseEnd_5040612 : Nat := 2588256748820937816068653

theorem tailTrace_5040612 : CollatzResearch.WordTrace tailWord_5040612 prefixEnd_5040612 2588256748820937816068653 := by
  unfold tailWord_5040612
  simp only [CollatzResearch.WordTrace]
  refine ⟨91923111607365533418754045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122564148809820711225005393 91923111607365533418754045)
  ·
    refine ⟨34471166852762075032032767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91923111607365533418754045 34471166852762075032032767)
    ·
      refine ⟨51706750279143112548049151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34471166852762075032032767 51706750279143112548049151)
      ·
        refine ⟨77560125418714668822073727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51706750279143112548049151 77560125418714668822073727)
        ·
          refine ⟨116340188128072003233110591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77560125418714668822073727 116340188128072003233110591)
          ·
            refine ⟨174510282192108004849665887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116340188128072003233110591 174510282192108004849665887)
            ·
              refine ⟨261765423288162007274498831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174510282192108004849665887 261765423288162007274498831)
              ·
                refine ⟨392648134932243010911748247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261765423288162007274498831 392648134932243010911748247)
                ·
                  refine ⟨588972202398364516367622371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392648134932243010911748247 588972202398364516367622371)
                  ·
                    refine ⟨883458303597546774551433557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588972202398364516367622371 883458303597546774551433557)
                    ·
                      refine ⟨2588256748820937816068653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 883458303597546774551433557 2588256748820937816068653)
                      ·
                        rfl

theorem cell23_5040612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_5040612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040612 prefixEnd_5040612 := by exact prefixLift 5040612
  have htrace : WordTrace (prefixWord ++ tailWord_5040612) baseStart_5040612 baseEnd_5040612 := by
    simpa [prefixWord, tailWord_5040612, baseEnd_5040612] using wordTrace_append hprefix tailTrace_5040612
  have hstable : (prefixWord ++ tailWord_5040612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040612).length < 2 ^ (prefixWord ++ tailWord_5040612).sum := by decide
  have hdescent : baseEnd_5040612 < baseStart_5040612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040659 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4]
def baseStart_5040659 : Nat := 118140960795 + 5040659 * 2 ^ 59
def prefixEnd_5040659 : Nat := 4983230072969 + 3 ^ 40 * 5040659 * 2
def baseEnd_5040659 : Nat := 2588280882411699132180937

theorem tailTrace_5040659 : CollatzResearch.WordTrace tailWord_5040659 prefixEnd_5040659 2588280882411699132180937 := by
  unfold tailWord_5040659
  simp only [CollatzResearch.WordTrace]
  refine ⟨183847937445560793864469031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122565291630373862576312687 183847937445560793864469031)
  ·
    refine ⟨275771906168341190796703547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183847937445560793864469031 275771906168341190796703547)
    ·
      refine ⟨413657859252511786195055321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275771906168341190796703547 413657859252511786195055321)
      ·
        refine ⟨310243394439383839646291491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413657859252511786195055321 310243394439383839646291491)
        ·
          refine ⟨465365091659075759469437237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310243394439383839646291491 465365091659075759469437237)
          ·
            refine ⟨43627977343038352450259741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 465365091659075759469437237 43627977343038352450259741)
            ·
              refine ⟨16360491503639382168847403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43627977343038352450259741 16360491503639382168847403)
              ·
                refine ⟨24540737255459073253271105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16360491503639382168847403 24540737255459073253271105)
                ·
                  refine ⟨18405552941594304939953329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24540737255459073253271105 18405552941594304939953329)
                  ·
                    refine ⟨13804164706195728704964997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18405552941594304939953329 13804164706195728704964997)
                    ·
                      refine ⟨2588280882411699132180937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13804164706195728704964997 2588280882411699132180937)
                      ·
                        rfl

theorem cell23_5040659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_5040659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040659 prefixEnd_5040659 := by exact prefixLift 5040659
  have htrace : WordTrace (prefixWord ++ tailWord_5040659) baseStart_5040659 baseEnd_5040659 := by
    simpa [prefixWord, tailWord_5040659, baseEnd_5040659] using wordTrace_append hprefix tailTrace_5040659
  have hstable : (prefixWord ++ tailWord_5040659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040659).length < 2 ^ (prefixWord ++ tailWord_5040659).sum := by decide
  have hdescent : baseEnd_5040659 < baseStart_5040659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040669 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 9]
def baseStart_5040669 : Nat := 118140960795 + 5040669 * 2 ^ 59
def prefixEnd_5040669 : Nat := 4983230072969 + 3 ^ 40 * 5040669 * 2
def baseEnd_5040669 : Nat := 287587335246471565895099

theorem tailTrace_5040669 : CollatzResearch.WordTrace tailWord_5040669 prefixEnd_5040669 287587335246471565895099 := by
  unfold tailWord_5040669
  simp only [CollatzResearch.WordTrace]
  refine ⟨183848302175524565572333061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122565534783683043714888707 183848302175524565572333061)
  ·
    refine ⟨34471556657910856044812449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183848302175524565572333061 34471556657910856044812449)
    ·
      refine ⟨25853667493433142033609337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34471556657910856044812449 25853667493433142033609337)
      ·
        refine ⟨19390250620074856525207003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25853667493433142033609337 19390250620074856525207003)
        ·
          refine ⟨29085375930112284787810505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19390250620074856525207003 29085375930112284787810505)
          ·
            refine ⟨21814031947584213590857879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29085375930112284787810505 21814031947584213590857879)
            ·
              refine ⟨32721047921376320386286819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21814031947584213590857879 32721047921376320386286819)
              ·
                refine ⟨49081571882064480579430229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32721047921376320386286819 49081571882064480579430229)
                ·
                  refine ⟨287587335246471565895099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49081571882064480579430229 287587335246471565895099)
                  ·
                    rfl

theorem cell23_5040669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_5040669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040669 prefixEnd_5040669 := by exact prefixLift 5040669
  have htrace : WordTrace (prefixWord ++ tailWord_5040669) baseStart_5040669 baseEnd_5040669 := by
    simpa [prefixWord, tailWord_5040669, baseEnd_5040669] using wordTrace_append hprefix tailTrace_5040669
  have hstable : (prefixWord ++ tailWord_5040669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040669).length < 2 ^ (prefixWord ++ tailWord_5040669).sum := by decide
  have hdescent : baseEnd_5040669 < baseStart_5040669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040719 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_5040719 : Nat := 118140960795 + 5040719 * 2 ^ 59
def prefixEnd_5040719 : Nat := 4983230072969 + 3 ^ 40 * 5040719 * 2
def baseEnd_5040719 : Nat := 2588311691250968897430661

theorem tailTrace_5040719 : CollatzResearch.WordTrace tailWord_5040719 prefixEnd_5040719 2588311691250968897430661 := by
  unfold tailWord_5040719
  simp only [CollatzResearch.WordTrace]
  refine ⟨183850125825343424111653211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122566750550228949407768807 183850125825343424111653211)
  ·
    refine ⟨275775188738015136167479817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183850125825343424111653211 275775188738015136167479817)
    ·
      refine ⟨206831391553511352125609863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275775188738015136167479817 206831391553511352125609863)
      ·
        refine ⟨310247087330267028188414795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206831391553511352125609863 310247087330267028188414795)
        ·
          refine ⟨465370630995400542282622193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310247087330267028188414795 465370630995400542282622193)
          ·
            refine ⟨349027973246550406711966645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465370630995400542282622193 349027973246550406711966645)
            ·
              refine ⟨32721372491864100629246873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349027973246550406711966645 32721372491864100629246873)
              ·
                refine ⟨24541029368898075471935155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32721372491864100629246873 24541029368898075471935155)
                ·
                  refine ⟨36811544053347113207902733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24541029368898075471935155 36811544053347113207902733)
                  ·
                    refine ⟨13804329020005167452963525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36811544053347113207902733 13804329020005167452963525)
                    ·
                      refine ⟨2588311691250968897430661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13804329020005167452963525 2588311691250968897430661)
                      ·
                        rfl

theorem cell23_5040719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_5040719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040719 prefixEnd_5040719 := by exact prefixLift 5040719
  have htrace : WordTrace (prefixWord ++ tailWord_5040719) baseStart_5040719 baseEnd_5040719 := by
    simpa [prefixWord, tailWord_5040719, baseEnd_5040719] using wordTrace_append hprefix tailTrace_5040719
  have hstable : (prefixWord ++ tailWord_5040719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040719).length < 2 ^ (prefixWord ++ tailWord_5040719).sum := by decide
  have hdescent : baseEnd_5040719 < baseStart_5040719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040736 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2]
def baseStart_5040736 : Nat := 118140960795 + 5040736 * 2 ^ 59
def prefixEnd_5040736 : Nat := 4983230072969 + 3 ^ 40 * 5040736 * 2
def baseEnd_5040736 : Nat := 2588320420422095330918083

theorem tailTrace_5040736 : CollatzResearch.WordTrace tailWord_5040736 prefixEnd_5040736 2588320420422095330918083 := by
  unfold tailWord_5040736
  simp only [CollatzResearch.WordTrace]
  refine ⟨91925372933140918007511031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122567163910854557343348041 91925372933140918007511031)
  ·
    refine ⟨137888059399711377011266547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91925372933140918007511031 137888059399711377011266547)
    ·
      refine ⟨206832089099567065516899821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137888059399711377011266547 206832089099567065516899821)
      ·
        refine ⟨77562033412337649568837433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206832089099567065516899821 77562033412337649568837433)
        ·
          refine ⟨58171525059253237176628075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77562033412337649568837433 58171525059253237176628075)
          ·
            refine ⟨87257287588879855764942113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58171525059253237176628075 87257287588879855764942113)
            ·
              refine ⟨65442965691659891823706585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87257287588879855764942113 65442965691659891823706585)
              ·
                refine ⟨49082224268744918867779939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65442965691659891823706585 49082224268744918867779939)
                ·
                  refine ⟨73623336403117378301669909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49082224268744918867779939 73623336403117378301669909)
                  ·
                    refine ⟨3451093893896127107890777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73623336403117378301669909 3451093893896127107890777)
                    ·
                      refine ⟨2588320420422095330918083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451093893896127107890777 2588320420422095330918083)
                      ·
                        rfl

theorem cell23_5040736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_5040736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040736 prefixEnd_5040736 := by exact prefixLift 5040736
  have htrace : WordTrace (prefixWord ++ tailWord_5040736) baseStart_5040736 baseEnd_5040736 := by
    simpa [prefixWord, tailWord_5040736, baseEnd_5040736] using wordTrace_append hprefix tailTrace_5040736
  have hstable : (prefixWord ++ tailWord_5040736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040736).length < 2 ^ (prefixWord ++ tailWord_5040736).sum := by decide
  have hdescent : baseEnd_5040736 < baseStart_5040736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040759 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 8]
def baseStart_5040759 : Nat := 118140960795 + 5040759 * 2 ^ 59
def prefixEnd_5040759 : Nat := 4983230072969 + 3 ^ 40 * 5040759 * 2
def baseEnd_5040759 : Nat := 287592470053016526770053

theorem tailTrace_5040759 : CollatzResearch.WordTrace tailWord_5040759 prefixEnd_5040759 287592470053016526770053 := by
  unfold tailWord_5040759
  simp only [CollatzResearch.WordTrace]
  refine ⟨183851584745198510943109331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122567723163465673962072887 183851584745198510943109331)
  ·
    refine ⟨275777377117797766414663997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183851584745198510943109331 275777377117797766414663997)
    ·
      refine ⟨103416516419174162405498999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275777377117797766414663997 103416516419174162405498999)
      ·
        refine ⟨155124774628761243608248499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103416516419174162405498999 155124774628761243608248499)
        ·
          refine ⟨232687161943141865412372749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155124774628761243608248499 232687161943141865412372749)
          ·
            refine ⟨87257685728678199529639781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232687161943141865412372749 87257685728678199529639781)
            ·
              refine ⟨16360816074127162411807459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87257685728678199529639781 16360816074127162411807459)
              ·
                refine ⟨24541224111190743617711189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16360816074127162411807459 24541224111190743617711189)
                ·
                  refine ⟨287592470053016526770053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24541224111190743617711189 287592470053016526770053)
                  ·
                    rfl

theorem cell23_5040759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 8].length) (baseStart_5040759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040759 prefixEnd_5040759 := by exact prefixLift 5040759
  have htrace : WordTrace (prefixWord ++ tailWord_5040759) baseStart_5040759 baseEnd_5040759 := by
    simpa [prefixWord, tailWord_5040759, baseEnd_5040759] using wordTrace_append hprefix tailTrace_5040759
  have hstable : (prefixWord ++ tailWord_5040759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040759).length < 2 ^ (prefixWord ++ tailWord_5040759).sum := by decide
  have hdescent : baseEnd_5040759 < baseStart_5040759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040814 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5040814 : Nat := 118140960795 + 5040814 * 2 ^ 59
def prefixEnd_5040814 : Nat := 4983230072969 + 3 ^ 40 * 5040814 * 2
def baseEnd_5040814 : Nat := 862786823971048675247575

theorem tailTrace_5040814 : CollatzResearch.WordTrace tailWord_5040814 prefixEnd_5040814 862786823971048675247575 := by
  unfold tailWord_5040814
  simp only [CollatzResearch.WordTrace]
  refine ⟨22981698844999906917045187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122569060506666170224240997 22981698844999906917045187)
  ·
    refine ⟨34472548267499860375567781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22981698844999906917045187 34472548267499860375567781)
    ·
      refine ⟨6463602800156223820418959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34472548267499860375567781 6463602800156223820418959)
      ·
        refine ⟨9695404200234335730628439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463602800156223820418959 9695404200234335730628439)
        ·
          refine ⟨14543106300351503595942659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695404200234335730628439 14543106300351503595942659)
          ·
            refine ⟨21814659450527255393913989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14543106300351503595942659 21814659450527255393913989)
            ·
              refine ⟨4090248646973860386358873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21814659450527255393913989 4090248646973860386358873)
              ·
                refine ⟨3067686485230395289769155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4090248646973860386358873 3067686485230395289769155)
                ·
                  refine ⟨4601529727845592934653733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3067686485230395289769155 4601529727845592934653733)
                  ·
                    refine ⟨862786823971048675247575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4601529727845592934653733 862786823971048675247575)
                    ·
                      rfl

theorem cell23_5040814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5040814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040814 prefixEnd_5040814 := by exact prefixLift 5040814
  have htrace : WordTrace (prefixWord ++ tailWord_5040814) baseStart_5040814 baseEnd_5040814 := by
    simpa [prefixWord, tailWord_5040814, baseEnd_5040814] using wordTrace_append hprefix tailTrace_5040814
  have hstable : (prefixWord ++ tailWord_5040814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040814).length < 2 ^ (prefixWord ++ tailWord_5040814).sum := by decide
  have hdescent : baseEnd_5040814 < baseStart_5040814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040826 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_5040826 : Nat := 118140960795 + 5040826 * 2 ^ 59
def prefixEnd_5040826 : Nat := 4983230072969 + 3 ^ 40 * 5040826 * 2
def baseEnd_5040826 : Nat := 2588366633680999978792669

theorem tailTrace_5040826 : CollatzResearch.WordTrace tailWord_5040826 prefixEnd_5040826 2588366633680999978792669 := by
  unfold tailWord_5040826
  simp only [CollatzResearch.WordTrace]
  refine ⟨45963507108988945346449583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122569352290637187590532221 45963507108988945346449583)
  ·
    refine ⟨68945260663483418019674375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45963507108988945346449583 68945260663483418019674375)
    ·
      refine ⟨103417890995225127029511563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68945260663483418019674375 103417890995225127029511563)
      ·
        refine ⟨155126836492837690544267345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103417890995225127029511563 155126836492837690544267345)
        ·
          refine ⟨116345127369628267908200509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155126836492837690544267345 116345127369628267908200509)
          ·
            refine ⟨43629422763610600465575191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116345127369628267908200509 43629422763610600465575191)
            ·
              refine ⟨65444134145415900698362787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43629422763610600465575191 65444134145415900698362787)
              ·
                refine ⟨98166201218123851047544181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65444134145415900698362787 98166201218123851047544181)
                ·
                  refine ⟨9203081364199111035707267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98166201218123851047544181 9203081364199111035707267)
                  ·
                    refine ⟨13804622046298666553560901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9203081364199111035707267 13804622046298666553560901)
                    ·
                      refine ⟨2588366633680999978792669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13804622046298666553560901 2588366633680999978792669)
                      ·
                        rfl

theorem cell23_5040826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_5040826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040826 prefixEnd_5040826 := by exact prefixLift 5040826
  have htrace : WordTrace (prefixWord ++ tailWord_5040826) baseStart_5040826 baseEnd_5040826 := by
    simpa [prefixWord, tailWord_5040826, baseEnd_5040826] using wordTrace_append hprefix tailTrace_5040826
  have hstable : (prefixWord ++ tailWord_5040826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040826).length < 2 ^ (prefixWord ++ tailWord_5040826).sum := by decide
  have hdescent : baseEnd_5040826 < baseStart_5040826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040877 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5040877 : Nat := 118140960795 + 5040877 * 2 ^ 59
def prefixEnd_5040877 : Nat := 4983230072969 + 3 ^ 40 * 5040877 * 2
def baseEnd_5040877 : Nat := 2588392821194379279254935

theorem tailTrace_5040877 : CollatzResearch.WordTrace tailWord_5040877 prefixEnd_5040877 2588392821194379279254935 := by
  unfold tailWord_5040877
  simp only [CollatzResearch.WordTrace]
  refine ⟨183855888558771017095904885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122570592372514011397269923 183855888558771017095904885)
  ·
    refine ⟨17236489552384782852741083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183855888558771017095904885 17236489552384782852741083)
    ·
      refine ⟨25854734328577174279111625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17236489552384782852741083 25854734328577174279111625)
      ·
        refine ⟨19391050746432880709333719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25854734328577174279111625 19391050746432880709333719)
        ·
          refine ⟨29086576119649321064000579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19391050746432880709333719 29086576119649321064000579)
          ·
            refine ⟨43629864179473981596000869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29086576119649321064000579 43629864179473981596000869)
            ·
              refine ⟨8180599533651371549250163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43629864179473981596000869 8180599533651371549250163)
              ·
                refine ⟨12270899300477057323875245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8180599533651371549250163 12270899300477057323875245)
                ·
                  refine ⟨4601587237678896496453217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12270899300477057323875245 4601587237678896496453217)
                  ·
                    refine ⟨3451190428259172372339913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601587237678896496453217 3451190428259172372339913)
                    ·
                      refine ⟨2588392821194379279254935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451190428259172372339913 2588392821194379279254935)
                      ·
                        rfl

theorem cell23_5040877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5040877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040877 prefixEnd_5040877 := by exact prefixLift 5040877
  have htrace : WordTrace (prefixWord ++ tailWord_5040877) baseStart_5040877 baseEnd_5040877 := by
    simpa [prefixWord, tailWord_5040877, baseEnd_5040877] using wordTrace_append hprefix tailTrace_5040877
  have hstable : (prefixWord ++ tailWord_5040877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040877).length < 2 ^ (prefixWord ++ tailWord_5040877).sum := by decide
  have hdescent : baseEnd_5040877 < baseStart_5040877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040906 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5040906 : Nat := 118140960795 + 5040906 * 2 ^ 59
def prefixEnd_5040906 : Nat := 4983230072969 + 3 ^ 40 * 5040906 * 2
def baseEnd_5040906 : Nat := 2588407712133359665792301

theorem tailTrace_5040906 : CollatzResearch.WordTrace tailWord_5040906 prefixEnd_5040906 2588407712133359665792301 := by
  unfold tailWord_5040906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45964236568916488762177643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122571297517110636699140381 45964236568916488762177643)
  ·
    refine ⟨68946354853374733143266465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45964236568916488762177643 68946354853374733143266465)
    ·
      refine ⟨51709766140031049857449849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68946354853374733143266465 51709766140031049857449849)
      ·
        refine ⟨38782324605023287393087387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51709766140031049857449849 38782324605023287393087387)
        ·
          refine ⟨58173486907534931089631081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38782324605023287393087387 58173486907534931089631081)
          ·
            refine ⟨43630115180651198317223311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58173486907534931089631081 43630115180651198317223311)
            ·
              refine ⟨65445172770976797475834967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43630115180651198317223311 65445172770976797475834967)
              ·
                refine ⟨98167759156465196213752451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65445172770976797475834967 98167759156465196213752451)
                ·
                  refine ⟨147251638734697794320628677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98167759156465196213752451 147251638734697794320628677)
                  ·
                    refine ⟨27609682262755836435117877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147251638734697794320628677 27609682262755836435117877)
                    ·
                      refine ⟨2588407712133359665792301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27609682262755836435117877 2588407712133359665792301)
                      ·
                        rfl

theorem cell23_5040906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5040906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040906 prefixEnd_5040906 := by exact prefixLift 5040906
  have htrace : WordTrace (prefixWord ++ tailWord_5040906) baseStart_5040906 baseEnd_5040906 := by
    simpa [prefixWord, tailWord_5040906, baseEnd_5040906] using wordTrace_append hprefix tailTrace_5040906
  have hstable : (prefixWord ++ tailWord_5040906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040906).length < 2 ^ (prefixWord ++ tailWord_5040906).sum := by decide
  have hdescent : baseEnd_5040906 < baseStart_5040906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040954 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_5040954 : Nat := 118140960795 + 5040954 * 2 ^ 59
def prefixEnd_5040954 : Nat := 4983230072969 + 3 ^ 40 * 5040954 * 2
def baseEnd_5040954 : Nat := 2588432359204775477992081

theorem tailTrace_5040954 : CollatzResearch.WordTrace tailWord_5040954 prefixEnd_5040954 2588432359204775477992081 := by
  unfold tailWord_5040954
  simp only [CollatzResearch.WordTrace]
  refine ⟨45964674244873014811614479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122572464652994706164305277 45964674244873014811614479)
  ·
    refine ⟨68947011367309522217421719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45964674244873014811614479 68947011367309522217421719)
    ·
      refine ⟨103420517050964283326132579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68947011367309522217421719 103420517050964283326132579)
      ·
        refine ⟨155130775576446424989198869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103420517050964283326132579 155130775576446424989198869)
        ·
          refine ⟨7271755105145926171368697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155130775576446424989198869 7271755105145926171368697)
          ·
            refine ⟨5453816328859444628526523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7271755105145926171368697 5453816328859444628526523)
            ·
              refine ⟨8180724493289166942789785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5453816328859444628526523 8180724493289166942789785)
              ·
                refine ⟨6135543369966875207092339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8180724493289166942789785 6135543369966875207092339)
                ·
                  refine ⟨9203315054950312810638509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6135543369966875207092339 9203315054950312810638509)
                  ·
                    refine ⟨3451243145606367303989441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9203315054950312810638509 3451243145606367303989441)
                    ·
                      refine ⟨2588432359204775477992081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451243145606367303989441 2588432359204775477992081)
                      ·
                        rfl

theorem cell23_5040954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_5040954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040954 prefixEnd_5040954 := by exact prefixLift 5040954
  have htrace : WordTrace (prefixWord ++ tailWord_5040954) baseStart_5040954 baseEnd_5040954 := by
    simpa [prefixWord, tailWord_5040954, baseEnd_5040954] using wordTrace_append hprefix tailTrace_5040954
  have hstable : (prefixWord ++ tailWord_5040954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040954).length < 2 ^ (prefixWord ++ tailWord_5040954).sum := by decide
  have hdescent : baseEnd_5040954 < baseStart_5040954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5040956 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 9]
def baseStart_5040956 : Nat := 118140960795 + 5040956 * 2 ^ 59
def prefixEnd_5040956 : Nat := 4983230072969 + 3 ^ 40 * 5040956 * 2
def baseEnd_5040956 : Nat := 287603709574009385574119

theorem tailTrace_5040956 : CollatzResearch.WordTrace tailWord_5040956 prefixEnd_5040956 287603709574009385574119 := by
  unfold tailWord_5040956
  simp only [CollatzResearch.WordTrace]
  refine ⟨91929384962742406794015361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122572513283656542392020481 91929384962742406794015361)
  ·
    refine ⟨68947038722056805095511521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91929384962742406794015361 68947038722056805095511521)
    ·
      refine ⟨51710279041542603821633641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68947038722056805095511521 51710279041542603821633641)
      ·
        refine ⟨38782709281156952866225231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51710279041542603821633641 38782709281156952866225231)
        ·
          refine ⟨58174063921735429299337847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38782709281156952866225231 58174063921735429299337847)
          ·
            refine ⟨87261095882603143949006771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58174063921735429299337847 87261095882603143949006771)
            ·
              refine ⟨130891643823904715923510157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87261095882603143949006771 130891643823904715923510157)
              ·
                refine ⟨49084366433964268471316309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130891643823904715923510157 49084366433964268471316309)
                ·
                  refine ⟨287603709574009385574119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49084366433964268471316309 287603709574009385574119)
                  ·
                    rfl

theorem cell23_5040956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_5040956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5040956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5040956 prefixEnd_5040956 := by exact prefixLift 5040956
  have htrace : WordTrace (prefixWord ++ tailWord_5040956) baseStart_5040956 baseEnd_5040956 := by
    simpa [prefixWord, tailWord_5040956, baseEnd_5040956] using wordTrace_append hprefix tailTrace_5040956
  have hstable : (prefixWord ++ tailWord_5040956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5040956).length < 2 ^ (prefixWord ++ tailWord_5040956).sum := by decide
  have hdescent : baseEnd_5040956 < baseStart_5040956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5040956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041000 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5041000 : Nat := 118140960795 + 5041000 * 2 ^ 59
def prefixEnd_5041000 : Nat := 4983230072969 + 3 ^ 40 * 5041000 * 2
def baseEnd_5041000 : Nat := 2588455979314882298016869

theorem tailTrace_5041000 : CollatzResearch.WordTrace tailWord_5041000 prefixEnd_5041000 2588455979314882298016869 := by
  unfold tailWord_5041000
  simp only [CollatzResearch.WordTrace]
  refine ⟨91930187368662704551316227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122573583158216939401754969 91930187368662704551316227)
  ·
    refine ⟨137895281052994056826974341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91930187368662704551316227 137895281052994056826974341)
    ·
      refine ⟨25855365197436385655057689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137895281052994056826974341 25855365197436385655057689)
      ·
        refine ⟨19391523898077289241293267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25855365197436385655057689 19391523898077289241293267)
        ·
          refine ⟨29087285847115933861939901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19391523898077289241293267 29087285847115933861939901)
          ·
            refine ⟨10907732192668475198227463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29087285847115933861939901 10907732192668475198227463)
            ·
              refine ⟨16361598289002712797341195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10907732192668475198227463 16361598289002712797341195)
              ·
                refine ⟨24542397433504069196011793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16361598289002712797341195 24542397433504069196011793)
                ·
                  refine ⟨18406798075128051897008845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24542397433504069196011793 18406798075128051897008845)
                  ·
                    refine ⟨6902549278173019461378317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18406798075128051897008845 6902549278173019461378317)
                    ·
                      refine ⟨2588455979314882298016869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6902549278173019461378317 2588455979314882298016869)
                      ·
                        rfl

theorem cell23_5041000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5041000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041000 prefixEnd_5041000 := by exact prefixLift 5041000
  have htrace : WordTrace (prefixWord ++ tailWord_5041000) baseStart_5041000 baseEnd_5041000 := by
    simpa [prefixWord, tailWord_5041000, baseEnd_5041000] using wordTrace_append hprefix tailTrace_5041000
  have hstable : (prefixWord ++ tailWord_5041000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041000).length < 2 ^ (prefixWord ++ tailWord_5041000).sum := by decide
  have hdescent : baseEnd_5041000 < baseStart_5041000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041016 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_5041016 : Nat := 118140960795 + 5041016 * 2 ^ 59
def prefixEnd_5041016 : Nat := 4983230072969 + 3 ^ 40 * 5041016 * 2
def baseEnd_5041016 : Nat := 862821398335118078472265

theorem tailTrace_5041016 : CollatzResearch.WordTrace tailWord_5041016 prefixEnd_5041016 862821398335118078472265 := by
  unfold tailWord_5041016
  simp only [CollatzResearch.WordTrace]
  refine ⟨91930479152633721917607451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122573972203511629223476601 91930479152633721917607451)
  ·
    refine ⟨137895718728950582876411177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91930479152633721917607451 137895718728950582876411177)
    ·
      refine ⟨103421789046712937157308383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137895718728950582876411177 103421789046712937157308383)
      ·
        refine ⟨155132683570069405735962575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103421789046712937157308383 155132683570069405735962575)
        ·
          refine ⟨232699025355104108603943863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155132683570069405735962575 232699025355104108603943863)
          ·
            refine ⟨349048538032656162905915795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232699025355104108603943863 349048538032656162905915795)
            ·
              refine ⟨523572807048984244358873693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349048538032656162905915795 523572807048984244358873693)
              ·
                refine ⟨196339802643369091634577635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 523572807048984244358873693 196339802643369091634577635)
                ·
                  refine ⟨294509703965053637451866453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196339802643369091634577635 294509703965053637451866453)
                  ·
                    refine ⟨862821398335118078472265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 294509703965053637451866453 862821398335118078472265)
                    ·
                      rfl

theorem cell23_5041016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_5041016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041016 prefixEnd_5041016 := by exact prefixLift 5041016
  have htrace : WordTrace (prefixWord ++ tailWord_5041016) baseStart_5041016 baseEnd_5041016 := by
    simpa [prefixWord, tailWord_5041016, baseEnd_5041016] using wordTrace_append hprefix tailTrace_5041016
  have hstable : (prefixWord ++ tailWord_5041016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041016).length < 2 ^ (prefixWord ++ tailWord_5041016).sum := by decide
  have hdescent : baseEnd_5041016 < baseStart_5041016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041053 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5041053 : Nat := 118140960795 + 5041053 * 2 ^ 59
def prefixEnd_5041053 : Nat := 4983230072969 + 3 ^ 40 * 5041053 * 2
def baseEnd_5041053 : Nat := 2588483193789570590654125

theorem tailTrace_5041053 : CollatzResearch.WordTrace tailWord_5041053 prefixEnd_5041053 2588483193789570590654125 := by
  unfold tailWord_5041053
  simp only [CollatzResearch.WordTrace]
  refine ⟨183862307806133399154311813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122574871870755599436207875 183862307806133399154311813)
  ·
    refine ⟨34474182713650012341433465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183862307806133399154311813 34474182713650012341433465)
    ·
      refine ⟨25855637035237509256075099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34474182713650012341433465 25855637035237509256075099)
      ·
        refine ⟨38783455552856263884112649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25855637035237509256075099 38783455552856263884112649)
        ·
          refine ⟨29087591664642197913084487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38783455552856263884112649 29087591664642197913084487)
          ·
            refine ⟨43631387496963296869626731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29087591664642197913084487 43631387496963296869626731)
            ·
              refine ⟨65447081245444945304440097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43631387496963296869626731 65447081245444945304440097)
              ·
                refine ⟨49085310934083708978330073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65447081245444945304440097 49085310934083708978330073)
                ·
                  refine ⟨36813983200562781733747555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49085310934083708978330073 36813983200562781733747555)
                  ·
                    refine ⟨55220974800844172600621333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36813983200562781733747555 55220974800844172600621333)
                    ·
                      refine ⟨2588483193789570590654125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55220974800844172600621333 2588483193789570590654125)
                      ·
                        rfl

theorem cell23_5041053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5041053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041053 prefixEnd_5041053 := by exact prefixLift 5041053
  have htrace : WordTrace (prefixWord ++ tailWord_5041053) baseStart_5041053 baseEnd_5041053 := by
    simpa [prefixWord, tailWord_5041053, baseEnd_5041053] using wordTrace_append hprefix tailTrace_5041053
  have hstable : (prefixWord ++ tailWord_5041053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041053).length < 2 ^ (prefixWord ++ tailWord_5041053).sum := by decide
  have hdescent : baseEnd_5041053 < baseStart_5041053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041057 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5041057 : Nat := 118140960795 + 5041057 * 2 ^ 59
def prefixEnd_5041057 : Nat := 4983230072969 + 3 ^ 40 * 5041057 * 2
def baseEnd_5041057 : Nat := 2588485247712188575004107

theorem tailTrace_5041057 : CollatzResearch.WordTrace tailWord_5041057 prefixEnd_5041057 2588485247712188575004107 := by
  unfold tailWord_5041057
  simp only [CollatzResearch.WordTrace]
  refine ⟨183862453698118907837457425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122574969132079271891638283 183862453698118907837457425)
  ·
    refine ⟨137896840273589180878093069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183862453698118907837457425 137896840273589180878093069)
    ·
      refine ⟨51711315102595942829284901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137896840273589180878093069 51711315102595942829284901)
      ·
        refine ⟨9695871581736739280490919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51711315102595942829284901 9695871581736739280490919)
        ·
          refine ⟨14543807372605108920736379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695871581736739280490919 14543807372605108920736379)
          ·
            refine ⟨21815711058907663381104569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14543807372605108920736379 21815711058907663381104569)
            ·
              refine ⟨16361783294180747535828427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21815711058907663381104569 16361783294180747535828427)
              ·
                refine ⟨24542674941271121303742641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16361783294180747535828427 24542674941271121303742641)
                ·
                  refine ⟨18407006205953340977806981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24542674941271121303742641 18407006205953340977806981)
                  ·
                    refine ⟨3451313663616251433338809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18407006205953340977806981 3451313663616251433338809)
                    ·
                      refine ⟨2588485247712188575004107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451313663616251433338809 2588485247712188575004107)
                      ·
                        rfl

theorem cell23_5041057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5041057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041057 prefixEnd_5041057 := by exact prefixLift 5041057
  have htrace : WordTrace (prefixWord ++ tailWord_5041057) baseStart_5041057 baseEnd_5041057 := by
    simpa [prefixWord, tailWord_5041057, baseEnd_5041057] using wordTrace_append hprefix tailTrace_5041057
  have hstable : (prefixWord ++ tailWord_5041057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041057).length < 2 ^ (prefixWord ++ tailWord_5041057).sum := by decide
  have hdescent : baseEnd_5041057 < baseStart_5041057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041127 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 1, 5]
def baseStart_5041127 : Nat := 118140960795 + 5041127 * 2 ^ 59
def prefixEnd_5041127 : Nat := 4983230072969 + 3 ^ 40 * 5041127 * 2
def baseEnd_5041127 : Nat := 862840397119334433709595

theorem tailTrace_5041127 : CollatzResearch.WordTrace tailWord_5041127 prefixEnd_5041127 862840397119334433709595 := by
  unfold tailWord_5041127
  simp only [CollatzResearch.WordTrace]
  refine ⟨183865006807865309792505635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122576671205243539861670423 183865006807865309792505635)
  ·
    refine ⟨275797510211797964688758453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183865006807865309792505635 275797510211797964688758453)
    ·
      refine ⟨25856016582356059189571105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275797510211797964688758453 25856016582356059189571105)
      ·
        refine ⟨19392012436767044392178329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25856016582356059189571105 19392012436767044392178329)
        ·
          refine ⟨14544009327575283294133747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19392012436767044392178329 14544009327575283294133747)
          ·
            refine ⟨21816013991362924941200621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14544009327575283294133747 21816013991362924941200621)
            ·
              refine ⟨8181005246761096852950233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21816013991362924941200621 8181005246761096852950233)
              ·
                refine ⟨6135753935070822639712675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8181005246761096852950233 6135753935070822639712675)
                ·
                  refine ⟨9203630902606233959569013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6135753935070822639712675 9203630902606233959569013)
                  ·
                    refine ⟨862840397119334433709595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9203630902606233959569013 862840397119334433709595)
                    ·
                      rfl

theorem cell23_5041127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_5041127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041127 prefixEnd_5041127 := by exact prefixLift 5041127
  have htrace : WordTrace (prefixWord ++ tailWord_5041127) baseStart_5041127 baseEnd_5041127 := by
    simpa [prefixWord, tailWord_5041127, baseEnd_5041127] using wordTrace_append hprefix tailTrace_5041127
  have hstable : (prefixWord ++ tailWord_5041127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041127).length < 2 ^ (prefixWord ++ tailWord_5041127).sum := by decide
  have hdescent : baseEnd_5041127 < baseStart_5041127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041153 : List Nat := [1, 2, 4, 1, 2, 13]
def baseStart_5041153 : Nat := 118140960795 + 5041153 * 2 ^ 59
def prefixEnd_5041153 : Nat := 4983230072969 + 3 ^ 40 * 5041153 * 2
def baseEnd_5041153 : Nat := 10652405522037120162155

theorem tailTrace_5041153 : CollatzResearch.WordTrace tailWord_5041153 prefixEnd_5041153 10652405522037120162155 := by
  unfold tailWord_5041153
  simp only [CollatzResearch.WordTrace]
  refine ⟨183865955105771116232952113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122577303403847410821968075 183865955105771116232952113)
  ·
    refine ⟨137899466329328337174714085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183865955105771116232952113 137899466329328337174714085)
    ·
      refine ⟨25856149936749063220258891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137899466329328337174714085 25856149936749063220258891)
      ·
        refine ⟨38784224905123594830388337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25856149936749063220258891 38784224905123594830388337)
        ·
          refine ⟨29088168678842696122791253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38784224905123594830388337 29088168678842696122791253)
          ·
            refine ⟨10652405522037120162155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 29088168678842696122791253 10652405522037120162155)
            ·
              rfl

theorem cell23_5041153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 13].length) (baseStart_5041153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041153 prefixEnd_5041153 := by exact prefixLift 5041153
  have htrace : WordTrace (prefixWord ++ tailWord_5041153) baseStart_5041153 baseEnd_5041153 := by
    simpa [prefixWord, tailWord_5041153, baseEnd_5041153] using wordTrace_append hprefix tailTrace_5041153
  have hstable : (prefixWord ++ tailWord_5041153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041153).length < 2 ^ (prefixWord ++ tailWord_5041153).sum := by decide
  have hdescent : baseEnd_5041153 < baseStart_5041153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041157 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_5041157 : Nat := 118140960795 + 5041157 * 2 ^ 59
def prefixEnd_5041157 : Nat := 4983230072969 + 3 ^ 40 * 5041157 * 2
def baseEnd_5041157 : Nat := 862845531925879394584549

theorem tailTrace_5041157 : CollatzResearch.WordTrace tailWord_5041157 prefixEnd_5041157 862845531925879394584549 := by
  unfold tailWord_5041157
  simp only [CollatzResearch.WordTrace]
  refine ⟨183866100997756624916097725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122577400665171083277398483 183866100997756624916097725)
  ·
    refine ⟨68949787874158734343536647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183866100997756624916097725 68949787874158734343536647)
    ·
      refine ⟨103424681811238101515304971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68949787874158734343536647 103424681811238101515304971)
      ·
        refine ⟨155137022716857152272957457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103424681811238101515304971 155137022716857152272957457)
        ·
          refine ⟨116352767037642864204718093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155137022716857152272957457 116352767037642864204718093)
          ·
            refine ⟨43632287639116074076769285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116352767037642864204718093 43632287639116074076769285)
            ·
              refine ⟨8181053932334263889394241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43632287639116074076769285 8181053932334263889394241)
              ·
                refine ⟨6135790449250697917045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8181053932334263889394241 6135790449250697917045681)
                ·
                  refine ⟨4601842836938023437784261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135790449250697917045681 4601842836938023437784261)
                  ·
                    refine ⟨862845531925879394584549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4601842836938023437784261 862845531925879394584549)
                    ·
                      rfl

theorem cell23_5041157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_5041157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041157 prefixEnd_5041157 := by exact prefixLift 5041157
  have htrace : WordTrace (prefixWord ++ tailWord_5041157) baseStart_5041157 baseEnd_5041157 := by
    simpa [prefixWord, tailWord_5041157, baseEnd_5041157] using wordTrace_append hprefix tailTrace_5041157
  have hstable : (prefixWord ++ tailWord_5041157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041157).length < 2 ^ (prefixWord ++ tailWord_5041157).sum := by decide
  have hdescent : baseEnd_5041157 < baseStart_5041157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041181 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5041181 : Nat := 118140960795 + 5041181 * 2 ^ 59
def prefixEnd_5041181 : Nat := 4983230072969 + 3 ^ 40 * 5041181 * 2
def baseEnd_5041181 : Nat := 2588548919313346089853537

theorem tailTrace_5041181 : CollatzResearch.WordTrace tailWord_5041181 prefixEnd_5041181 2588548919313346089853537 := by
  unfold tailWord_5041181
  simp only [CollatzResearch.WordTrace]
  refine ⟨183866976349669677014971397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122577984233113118009980931 183866976349669677014971397)
  ·
    refine ⟨34475058065563064440307137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183866976349669677014971397 34475058065563064440307137)
    ·
      refine ⟨25856293549172298330230353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34475058065563064440307137 25856293549172298330230353)
      ·
        refine ⟨19392220161879223747672765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25856293549172298330230353 19392220161879223747672765)
        ·
          refine ⟨7272082560704708905377287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19392220161879223747672765 7272082560704708905377287)
          ·
            refine ⟨10908123841057063358065931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7272082560704708905377287 10908123841057063358065931)
            ·
              refine ⟨16362185761585595037098897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908123841057063358065931 16362185761585595037098897)
              ·
                refine ⟨12271639321189196277824173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16362185761585595037098897 12271639321189196277824173)
                ·
                  refine ⟨4601864745445948604184065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12271639321189196277824173 4601864745445948604184065)
                  ·
                    refine ⟨3451398559084461453138049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601864745445948604184065 3451398559084461453138049)
                    ·
                      refine ⟨2588548919313346089853537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451398559084461453138049 2588548919313346089853537)
                      ·
                        rfl

theorem cell23_5041181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5041181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041181 prefixEnd_5041181 := by exact prefixLift 5041181
  have htrace : WordTrace (prefixWord ++ tailWord_5041181) baseStart_5041181 baseEnd_5041181 := by
    simpa [prefixWord, tailWord_5041181, baseEnd_5041181] using wordTrace_append hprefix tailTrace_5041181
  have hstable : (prefixWord ++ tailWord_5041181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041181).length < 2 ^ (prefixWord ++ tailWord_5041181).sum := by decide
  have hdescent : baseEnd_5041181 < baseStart_5041181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041198 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5041198 : Nat := 118140960795 + 5041198 * 2 ^ 59
def prefixEnd_5041198 : Nat := 4983230072969 + 3 ^ 40 * 5041198 * 2
def baseEnd_5041198 : Nat := 2588557648484472523340959

theorem tailTrace_5041198 : CollatzResearch.WordTrace tailWord_5041198 prefixEnd_5041198 2588557648484472523340959 := by
  unfold tailWord_5041198
  simp only [CollatzResearch.WordTrace]
  refine ⟨22983449548826011114792531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122578397593738725945560165 22983449548826011114792531)
  ·
    refine ⟨34475174323239016672188797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22983449548826011114792531 34475174323239016672188797)
    ·
      refine ⟨12928190371214631252070799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34475174323239016672188797 12928190371214631252070799)
      ·
        refine ⟨19392285556821946878106199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12928190371214631252070799 19392285556821946878106199)
        ·
          refine ⟨29088428335232920317159299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19392285556821946878106199 29088428335232920317159299)
          ·
            refine ⟨43632642502849380475738949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29088428335232920317159299 43632642502849380475738949)
            ·
              refine ⟨8181120469284258839201053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43632642502849380475738949 8181120469284258839201053)
              ·
                refine ⟨3067920175981597064700395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8181120469284258839201053 3067920175981597064700395)
                ·
                  refine ⟨4601880263972395597050593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3067920175981597064700395 4601880263972395597050593)
                  ·
                    refine ⟨3451410197979296697787945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601880263972395597050593 3451410197979296697787945)
                    ·
                      refine ⟨2588557648484472523340959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451410197979296697787945 2588557648484472523340959)
                      ·
                        rfl

theorem cell23_5041198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5041198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041198 prefixEnd_5041198 := by exact prefixLift 5041198
  have htrace : WordTrace (prefixWord ++ tailWord_5041198) baseStart_5041198 baseEnd_5041198 := by
    simpa [prefixWord, tailWord_5041198, baseEnd_5041198] using wordTrace_append hprefix tailTrace_5041198
  have hstable : (prefixWord ++ tailWord_5041198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041198).length < 2 ^ (prefixWord ++ tailWord_5041198).sum := by decide
  have hdescent : baseEnd_5041198 < baseStart_5041198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041230 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_5041230 : Nat := 118140960795 + 5041230 * 2 ^ 59
def prefixEnd_5041230 : Nat := 4983230072969 + 3 ^ 40 * 5041230 * 2
def baseEnd_5041230 : Nat := 862858026621805466046937

theorem tailTrace_5041230 : CollatzResearch.WordTrace tailWord_5041230 prefixEnd_5041230 862858026621805466046937 := by
  unfold tailWord_5041230
  simp only [CollatzResearch.WordTrace]
  refine ⟨22983595440811519797938143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122579175684328105589003429 22983595440811519797938143)
  ·
    refine ⟨34475393161217279696907215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22983595440811519797938143 34475393161217279696907215)
    ·
      refine ⟨51713089741825919545360823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34475393161217279696907215 51713089741825919545360823)
      ·
        refine ⟨77569634612738879318041235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51713089741825919545360823 77569634612738879318041235)
        ·
          refine ⟨116354451919108318977061853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77569634612738879318041235 116354451919108318977061853)
          ·
            refine ⟨43632919469665619616398195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116354451919108318977061853 43632919469665619616398195)
            ·
              refine ⟨65449379204498429424597293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43632919469665619616398195 65449379204498429424597293)
              ·
                refine ⟨24543517201686911034223985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65449379204498429424597293 24543517201686911034223985)
                ·
                  refine ⟨18407637901265183275667989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24543517201686911034223985 18407637901265183275667989)
                  ·
                    refine ⟨862858026621805466046937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18407637901265183275667989 862858026621805466046937)
                    ·
                      rfl

theorem cell23_5041230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_5041230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041230 prefixEnd_5041230 := by exact prefixLift 5041230
  have htrace : WordTrace (prefixWord ++ tailWord_5041230) baseStart_5041230 baseEnd_5041230 := by
    simpa [prefixWord, tailWord_5041230, baseEnd_5041230] using wordTrace_append hprefix tailTrace_5041230
  have hstable : (prefixWord ++ tailWord_5041230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041230).length < 2 ^ (prefixWord ++ tailWord_5041230).sum := by decide
  have hdescent : baseEnd_5041230 < baseStart_5041230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041238 : List Nat := [5, 2, 2, 1, 3, 1, 2, 7]
def baseStart_5041238 : Nat := 118140960795 + 5041238 * 2 ^ 59
def prefixEnd_5041238 : Nat := 4983230072969 + 3 ^ 40 * 5041238 * 2
def baseEnd_5041238 : Nat := 95873266211505643216325

theorem tailTrace_5041238 : CollatzResearch.WordTrace tailWord_5041238 prefixEnd_5041238 95873266211505643216325 := by
  unfold tailWord_5041238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491815956903948484362273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122579370206975450499864245 11491815956903948484362273)
  ·
    refine ⟨8618861967677961363271705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11491815956903948484362273 8618861967677961363271705)
    ·
      refine ⟨6464146475758471022453779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8618861967677961363271705 6464146475758471022453779)
      ·
        refine ⟨9696219713637706533680669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6464146475758471022453779 9696219713637706533680669)
        ·
          refine ⟨3636082392614139950130251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9696219713637706533680669 3636082392614139950130251)
          ·
            refine ⟨5454123588921209925195377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636082392614139950130251 5454123588921209925195377)
            ·
              refine ⟨4090592691690907443896533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5454123588921209925195377 4090592691690907443896533)
              ·
                refine ⟨95873266211505643216325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4090592691690907443896533 95873266211505643216325)
                ·
                  rfl

theorem cell23_5041238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_5041238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041238 prefixEnd_5041238 := by exact prefixLift 5041238
  have htrace : WordTrace (prefixWord ++ tailWord_5041238) baseStart_5041238 baseEnd_5041238 := by
    simpa [prefixWord, tailWord_5041238, baseEnd_5041238] using wordTrace_append hprefix tailTrace_5041238
  have hstable : (prefixWord ++ tailWord_5041238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041238).length < 2 ^ (prefixWord ++ tailWord_5041238).sum := by decide
  have hdescent : baseEnd_5041238 < baseStart_5041238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041240 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5041240 : Nat := 118140960795 + 5041240 * 2 ^ 59
def prefixEnd_5041240 : Nat := 4983230072969 + 3 ^ 40 * 5041240 * 2
def baseEnd_5041240 : Nat := 2588579214671961359015765

theorem tailTrace_5041240 : CollatzResearch.WordTrace tailWord_5041240 prefixEnd_5041240 2588579214671961359015765 := by
  unfold tailWord_5041240
  simp only [CollatzResearch.WordTrace]
  refine ⟨91934564128227965045684587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122579418837637286727579449 91934564128227965045684587)
  ·
    refine ⟨137901846192341947568526881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91934564128227965045684587 137901846192341947568526881)
    ·
      refine ⟨103426384644256460676395161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137901846192341947568526881 103426384644256460676395161)
      ·
        refine ⟨77569788483192345507296371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103426384644256460676395161 77569788483192345507296371)
        ·
          refine ⟨116354682724788518260944557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77569788483192345507296371 116354682724788518260944557)
          ·
            refine ⟨43633006021795694347854209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116354682724788518260944557 43633006021795694347854209)
            ·
              refine ⟨32724754516346770760890657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43633006021795694347854209 32724754516346770760890657)
              ·
                refine ⟨24543565887260078070667993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32724754516346770760890657 24543565887260078070667993)
                ·
                  refine ⟨18407674415445058553000995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24543565887260078070667993 18407674415445058553000995)
                  ·
                    refine ⟨27611511623167587829501493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18407674415445058553000995 27611511623167587829501493)
                    ·
                      refine ⟨2588579214671961359015765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27611511623167587829501493 2588579214671961359015765)
                      ·
                        rfl

theorem cell23_5041240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5041240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041240 prefixEnd_5041240 := by exact prefixLift 5041240
  have htrace : WordTrace (prefixWord ++ tailWord_5041240) baseStart_5041240 baseEnd_5041240 := by
    simpa [prefixWord, tailWord_5041240, baseEnd_5041240] using wordTrace_append hprefix tailTrace_5041240
  have hstable : (prefixWord ++ tailWord_5041240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041240).length < 2 ^ (prefixWord ++ tailWord_5041240).sum := by decide
  have hdescent : baseEnd_5041240 < baseStart_5041240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041288 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5041288 : Nat := 118140960795 + 5041288 * 2 ^ 59
def prefixEnd_5041288 : Nat := 4983230072969 + 3 ^ 40 * 5041288 * 2
def baseEnd_5041288 : Nat := 2588603861743377171215545

theorem tailTrace_5041288 : CollatzResearch.WordTrace tailWord_5041288 prefixEnd_5041288 2588603861743377171215545 := by
  unfold tailWord_5041288
  simp only [CollatzResearch.WordTrace]
  refine ⟨91935439480141017144558259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122580585973521356192744345 91935439480141017144558259)
  ·
    refine ⟨137903159220211525716837389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91935439480141017144558259 137903159220211525716837389)
    ·
      refine ⟨51713684707579322143814021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137903159220211525716837389 51713684707579322143814021)
      ·
        refine ⟨9696315882671122901965129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51713684707579322143814021 9696315882671122901965129)
        ·
          refine ⟨7272236912003342176473847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9696315882671122901965129 7272236912003342176473847)
          ·
            refine ⟨10908355368005013264710771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7272236912003342176473847 10908355368005013264710771)
            ·
              refine ⟨16362533052007519897066157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908355368005013264710771 16362533052007519897066157)
              ·
                refine ⟨6135949894502819961399809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16362533052007519897066157 6135949894502819961399809)
                ·
                  refine ⟨4601962420877114971049857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135949894502819961399809 4601962420877114971049857)
                  ·
                    refine ⟨3451471815657836228287393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601962420877114971049857 3451471815657836228287393)
                    ·
                      refine ⟨2588603861743377171215545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451471815657836228287393 2588603861743377171215545)
                      ·
                        rfl

theorem cell23_5041288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5041288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041288 prefixEnd_5041288 := by exact prefixLift 5041288
  have htrace : WordTrace (prefixWord ++ tailWord_5041288) baseStart_5041288 baseEnd_5041288 := by
    simpa [prefixWord, tailWord_5041288, baseEnd_5041288] using wordTrace_append hprefix tailTrace_5041288
  have hstable : (prefixWord ++ tailWord_5041288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041288).length < 2 ^ (prefixWord ++ tailWord_5041288).sum := by decide
  have hdescent : baseEnd_5041288 < baseStart_5041288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041327 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_5041327 : Nat := 118140960795 + 5041327 * 2 ^ 59
def prefixEnd_5041327 : Nat := 4983230072969 + 3 ^ 40 * 5041327 * 2
def baseEnd_5041327 : Nat := 2588623887488902518627865

theorem tailTrace_5041327 : CollatzResearch.WordTrace tailWord_5041327 prefixEnd_5041327 2588623887488902518627865 := by
  unfold tailWord_5041327
  simp only [CollatzResearch.WordTrace]
  refine ⟨183872301407140743949786235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122581534271427162633190823 183872301407140743949786235)
  ·
    refine ⟨275808452110711115924679353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183872301407140743949786235 275808452110711115924679353)
    ·
      refine ⟨206856339083033336943509515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275808452110711115924679353 206856339083033336943509515)
      ·
        refine ⟨310284508624550005415264273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206856339083033336943509515 310284508624550005415264273)
        ·
          refine ⟨232713381468412504061448205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310284508624550005415264273 232713381468412504061448205)
          ·
            refine ⟨87267518050654689023043077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232713381468412504061448205 87267518050654689023043077)
            ·
              refine ⟨16362659634497754191820577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87267518050654689023043077 16362659634497754191820577)
              ·
                refine ⟨12271994725873315643865433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16362659634497754191820577 12271994725873315643865433)
                ·
                  refine ⟨9203996044404986732899075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12271994725873315643865433 9203996044404986732899075)
                  ·
                    refine ⟨13805994066607480099348613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9203996044404986732899075 13805994066607480099348613)
                    ·
                      refine ⟨2588623887488902518627865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13805994066607480099348613 2588623887488902518627865)
                      ·
                        rfl

theorem cell23_5041327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_5041327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041327 prefixEnd_5041327 := by exact prefixLift 5041327
  have htrace : WordTrace (prefixWord ++ tailWord_5041327) baseStart_5041327 baseEnd_5041327 := by
    simpa [prefixWord, tailWord_5041327, baseEnd_5041327] using wordTrace_append hprefix tailTrace_5041327
  have hstable : (prefixWord ++ tailWord_5041327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041327).length < 2 ^ (prefixWord ++ tailWord_5041327).sum := by decide
  have hdescent : baseEnd_5041327 < baseStart_5041327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041354 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_5041354 : Nat := 118140960795 + 5041354 * 2 ^ 59
def prefixEnd_5041354 : Nat := 4983230072969 + 3 ^ 40 * 5041354 * 2
def baseEnd_5041354 : Nat := 862879250488857970996747

theorem tailTrace_5041354 : CollatzResearch.WordTrace tailWord_5041354 prefixEnd_5041354 862879250488857970996747 := by
  unfold tailWord_5041354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45968321544510731890254779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122582190785361951707346077 45968321544510731890254779)
  ·
    refine ⟨68952482316766097835382169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45968321544510731890254779 68952482316766097835382169)
    ·
      refine ⟨51714361737574573376536627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68952482316766097835382169 51714361737574573376536627)
      ·
        refine ⟨77571542606361860064804941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51714361737574573376536627 77571542606361860064804941)
        ·
          refine ⟨29089328477385697524301853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77571542606361860064804941 29089328477385697524301853)
          ·
            refine ⟨10908498179019636571613195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29089328477385697524301853 10908498179019636571613195)
            ·
              refine ⟨16362747268529454857419793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908498179019636571613195 16362747268529454857419793)
              ·
                refine ⟨12272060451397091143064845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16362747268529454857419793 12272060451397091143064845)
                ·
                  refine ⟨4602022669273909178649317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12272060451397091143064845 4602022669273909178649317)
                  ·
                    refine ⟨862879250488857970996747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602022669273909178649317 862879250488857970996747)
                    ·
                      rfl

theorem cell23_5041354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_5041354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041354 prefixEnd_5041354 := by exact prefixLift 5041354
  have htrace : WordTrace (prefixWord ++ tailWord_5041354) baseStart_5041354 baseEnd_5041354 := by
    simpa [prefixWord, tailWord_5041354, baseEnd_5041354] using wordTrace_append hprefix tailTrace_5041354
  have hstable : (prefixWord ++ tailWord_5041354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041354).length < 2 ^ (prefixWord ++ tailWord_5041354).sum := by decide
  have hdescent : baseEnd_5041354 < baseStart_5041354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041444 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_5041444 : Nat := 118140960795 + 5041444 * 2 ^ 59
def prefixEnd_5041444 : Nat := 4983230072969 + 3 ^ 40 * 5041444 * 2
def baseEnd_5041444 : Nat := 862894654908492853621609

theorem tailTrace_5041444 : CollatzResearch.WordTrace tailWord_5041444 prefixEnd_5041444 862894654908492853621609 := by
  unfold tailWord_5041444
  simp only [CollatzResearch.WordTrace]
  refine ⟨91938284373858436465897693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122584379165144581954530257 91938284373858436465897693)
  ·
    refine ⟨34476856640196913674711635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91938284373858436465897693 34476856640196913674711635)
    ·
      refine ⟨51715284960295370512067453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34476856640196913674711635 51715284960295370512067453)
      ·
        refine ⟨19393231860110763942025295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51715284960295370512067453 19393231860110763942025295)
        ·
          refine ⟨29089847790166145913037943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19393231860110763942025295 29089847790166145913037943)
          ·
            refine ⟨43634771685249218869556915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29089847790166145913037943 43634771685249218869556915)
            ·
              refine ⟨65452157527873828304335373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43634771685249218869556915 65452157527873828304335373)
              ·
                refine ⟨24544559072952685614125765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65452157527873828304335373 24544559072952685614125765)
                ·
                  refine ⟨4602104826178628552648581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24544559072952685614125765 4602104826178628552648581)
                  ·
                    refine ⟨862894654908492853621609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602104826178628552648581 862894654908492853621609)
                    ·
                      rfl

theorem cell23_5041444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_5041444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041444 prefixEnd_5041444 := by exact prefixLift 5041444
  have htrace : WordTrace (prefixWord ++ tailWord_5041444) baseStart_5041444 baseEnd_5041444 := by
    simpa [prefixWord, tailWord_5041444, baseEnd_5041444] using wordTrace_append hprefix tailTrace_5041444
  have hstable : (prefixWord ++ tailWord_5041444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041444).length < 2 ^ (prefixWord ++ tailWord_5041444).sum := by decide
  have hdescent : baseEnd_5041444 < baseStart_5041444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041445 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 1, 1, 3]
def baseStart_5041445 : Nat := 118140960795 + 5041445 * 2 ^ 59
def prefixEnd_5041445 : Nat := 4983230072969 + 3 ^ 40 * 5041445 * 2
def baseEnd_5041445 : Nat := 2588684478206133056952323

theorem tailTrace_5041445 : CollatzResearch.WordTrace tailWord_5041445 prefixEnd_5041445 2588684478206133056952323 := by
  unfold tailWord_5041445
  simp only [CollatzResearch.WordTrace]
  refine ⟨183876605220713250102581789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122584403480475500068387859 183876605220713250102581789)
  ·
    refine ⟨68953726957767468788468171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183876605220713250102581789 68953726957767468788468171)
    ·
      refine ⟨103430590436651203182702257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68953726957767468788468171 103430590436651203182702257)
      ·
        refine ⟨77572942827488402387026693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103430590436651203182702257 77572942827488402387026693)
        ·
          refine ⟨14544926780154075447567505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77572942827488402387026693 14544926780154075447567505)
          ·
            refine ⟨10908695085115556585675629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14544926780154075447567505 10908695085115556585675629)
            ·
              refine ⟨4090760656918333719628361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10908695085115556585675629 4090760656918333719628361)
              ·
                refine ⟨3068070492688750289721271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4090760656918333719628361 3068070492688750289721271)
                ·
                  refine ⟨4602105739033125434581907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068070492688750289721271 4602105739033125434581907)
                  ·
                    refine ⟨6903158608549688151872861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602105739033125434581907 6903158608549688151872861)
                    ·
                      refine ⟨2588684478206133056952323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6903158608549688151872861 2588684478206133056952323)
                      ·
                        rfl

theorem cell23_5041445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_5041445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041445 prefixEnd_5041445 := by exact prefixLift 5041445
  have htrace : WordTrace (prefixWord ++ tailWord_5041445) baseStart_5041445 baseEnd_5041445 := by
    simpa [prefixWord, tailWord_5041445, baseEnd_5041445] using wordTrace_append hprefix tailTrace_5041445
  have hstable : (prefixWord ++ tailWord_5041445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041445).length < 2 ^ (prefixWord ++ tailWord_5041445).sum := by decide
  have hdescent : baseEnd_5041445 < baseStart_5041445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041457 : List Nat := [1, 2, 2, 3, 3, 1, 1, 10]
def baseStart_5041457 : Nat := 118140960795 + 5041457 * 2 ^ 59
def prefixEnd_5041457 : Nat := 4983230072969 + 3 ^ 40 * 5041457 * 2
def baseEnd_5041457 : Nat := 95877431110147667037121

theorem tailTrace_5041457 : CollatzResearch.WordTrace tailWord_5041457 prefixEnd_5041457 95877431110147667037121 := by
  unfold tailWord_5041457
  simp only [CollatzResearch.WordTrace]
  refine ⟨183877042896669776152018625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122584695264446517434679083 183877042896669776152018625)
  ·
    refine ⟨137907782172502332114013969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183877042896669776152018625 137907782172502332114013969)
    ·
      refine ⟨103430836629376749085510477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137907782172502332114013969 103430836629376749085510477)
      ·
        refine ⟨38786563736016280907066429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103430836629376749085510477 38786563736016280907066429)
        ·
          refine ⟨14544961401006105340149911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38786563736016280907066429 14544961401006105340149911)
          ·
            refine ⟨21817442101509158010224867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14544961401006105340149911 21817442101509158010224867)
            ·
              refine ⟨32726163152263737015337301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21817442101509158010224867 32726163152263737015337301)
              ·
                refine ⟨95877431110147667037121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32726163152263737015337301 95877431110147667037121)
                ·
                  rfl

theorem cell23_5041457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 10].length) (baseStart_5041457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041457 prefixEnd_5041457 := by exact prefixLift 5041457
  have htrace : WordTrace (prefixWord ++ tailWord_5041457) baseStart_5041457 baseEnd_5041457 := by
    simpa [prefixWord, tailWord_5041457, baseEnd_5041457] using wordTrace_append hprefix tailTrace_5041457
  have hstable : (prefixWord ++ tailWord_5041457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041457).length < 2 ^ (prefixWord ++ tailWord_5041457).sum := by decide
  have hdescent : baseEnd_5041457 < baseStart_5041457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041461 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_5041461 : Nat := 118140960795 + 5041461 * 2 ^ 59
def prefixEnd_5041461 : Nat := 4983230072969 + 3 ^ 40 * 5041461 * 2
def baseEnd_5041461 : Nat := 862897564632201664784083

theorem tailTrace_5041461 : CollatzResearch.WordTrace tailWord_5041461 prefixEnd_5041461 862897564632201664784083 := by
  unfold tailWord_5041461
  simp only [CollatzResearch.WordTrace]
  refine ⟨183877188788655284835164237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122584792525770189890109491 183877188788655284835164237)
  ·
    refine ⟨68953945795745731813186589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183877188788655284835164237 68953945795745731813186589)
    ·
      refine ⟨25857729673404649429944971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68953945795745731813186589 25857729673404649429944971)
      ·
        refine ⟨38786594510106974144917457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25857729673404649429944971 38786594510106974144917457)
        ·
          refine ⟨29089945882580230608688093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38786594510106974144917457 29089945882580230608688093)
          ·
            refine ⟨10908729705967586478258035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29089945882580230608688093 10908729705967586478258035)
            ·
              refine ⟨16363094558951379717387053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10908729705967586478258035 16363094558951379717387053)
              ·
                refine ⟨6136160459606767394020145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16363094558951379717387053 6136160459606767394020145)
                ·
                  refine ⟨4602120344705075545515109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6136160459606767394020145 4602120344705075545515109)
                  ·
                    refine ⟨862897564632201664784083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602120344705075545515109 862897564632201664784083)
                    ·
                      rfl

theorem cell23_5041461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_5041461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041461 prefixEnd_5041461 := by exact prefixLift 5041461
  have htrace : WordTrace (prefixWord ++ tailWord_5041461) baseStart_5041461 baseEnd_5041461 := by
    simpa [prefixWord, tailWord_5041461, baseEnd_5041461] using wordTrace_append hprefix tailTrace_5041461
  have hstable : (prefixWord ++ tailWord_5041461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041461).length < 2 ^ (prefixWord ++ tailWord_5041461).sum := by decide
  have hdescent : baseEnd_5041461 < baseStart_5041461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041471 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_5041471 : Nat := 118140960795 + 5041471 * 2 ^ 59
def prefixEnd_5041471 : Nat := 4983230072969 + 3 ^ 40 * 5041471 * 2
def baseEnd_5041471 : Nat := 2588697828703149955227203

theorem tailTrace_5041471 : CollatzResearch.WordTrace tailWord_5041471 prefixEnd_5041471 2588697828703149955227203 := by
  unfold tailWord_5041471
  simp only [CollatzResearch.WordTrace]
  refine ⟨183877553518619056543028267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122585035679079371028685511 183877553518619056543028267)
  ·
    refine ⟨275816330277928584814542401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183877553518619056543028267 275816330277928584814542401)
    ·
      refine ⟨206862247708446438610906801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275816330277928584814542401 206862247708446438610906801)
      ·
        refine ⟨155146685781334828958180101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206862247708446438610906801 155146685781334828958180101)
        ·
          refine ⟨29090003584000280429658769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155146685781334828958180101 29090003584000280429658769)
          ·
            refine ⟨21817502688000210322244077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29090003584000280429658769 21817502688000210322244077)
            ·
              refine ⟨8181563508000078870841529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21817502688000210322244077 8181563508000078870841529)
              ·
                refine ⟨6136172631000059153131147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8181563508000078870841529 6136172631000059153131147)
                ·
                  refine ⟨9204258946500088729696721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6136172631000059153131147 9204258946500088729696721)
                  ·
                    refine ⟨6903194209875066547272541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9204258946500088729696721 6903194209875066547272541)
                    ·
                      refine ⟨2588697828703149955227203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6903194209875066547272541 2588697828703149955227203)
                      ·
                        rfl

theorem cell23_5041471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_5041471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041471 prefixEnd_5041471 := by exact prefixLift 5041471
  have htrace : WordTrace (prefixWord ++ tailWord_5041471) baseStart_5041471 baseEnd_5041471 := by
    simpa [prefixWord, tailWord_5041471, baseEnd_5041471] using wordTrace_append hprefix tailTrace_5041471
  have hstable : (prefixWord ++ tailWord_5041471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041471).length < 2 ^ (prefixWord ++ tailWord_5041471).sum := by decide
  have hdescent : baseEnd_5041471 < baseStart_5041471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041484 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5041484 : Nat := 118140960795 + 5041484 * 2 ^ 59
def prefixEnd_5041484 : Nat := 4983230072969 + 3 ^ 40 * 5041484 * 2
def baseEnd_5041484 : Nat := 2588704503951658404364643

theorem tailTrace_5041484 : CollatzResearch.WordTrace tailWord_5041484 prefixEnd_5041484 2588704503951658404364643 := by
  unfold tailWord_5041484
  simp only [CollatzResearch.WordTrace]
  refine ⟨91939013833785979881625753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122585351778381306508834337 91939013833785979881625753)
  ·
    refine ⟨68954260375339484911219315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91939013833785979881625753 68954260375339484911219315)
    ·
      refine ⟨103431390563009227366828973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68954260375339484911219315 103431390563009227366828973)
      ·
        refine ⟨38786771461128460262560865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103431390563009227366828973 38786771461128460262560865)
        ·
          refine ⟨29090078595846345196920649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38786771461128460262560865 29090078595846345196920649)
          ·
            refine ⟨21817558946884758897690487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29090078595846345196920649 21817558946884758897690487)
            ·
              refine ⟨32726338420327138346535731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21817558946884758897690487 32726338420327138346535731)
              ·
                refine ⟨49089507630490707519803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32726338420327138346535731 49089507630490707519803597)
                ·
                  refine ⟨18408565361434015319926349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49089507630490707519803597 18408565361434015319926349)
                  ·
                    refine ⟨6903212010537755744972381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18408565361434015319926349 6903212010537755744972381)
                    ·
                      refine ⟨2588704503951658404364643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6903212010537755744972381 2588704503951658404364643)
                      ·
                        rfl

theorem cell23_5041484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5041484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041484 prefixEnd_5041484 := by exact prefixLift 5041484
  have htrace : WordTrace (prefixWord ++ tailWord_5041484) baseStart_5041484 baseEnd_5041484 := by
    simpa [prefixWord, tailWord_5041484, baseEnd_5041484] using wordTrace_append hprefix tailTrace_5041484
  have hstable : (prefixWord ++ tailWord_5041484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041484).length < 2 ^ (prefixWord ++ tailWord_5041484).sum := by decide
  have hdescent : baseEnd_5041484 < baseStart_5041484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041497 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_5041497 : Nat := 118140960795 + 5041497 * 2 ^ 59
def prefixEnd_5041497 : Nat := 4983230072969 + 3 ^ 40 * 5041497 * 2
def baseEnd_5041497 : Nat := 2588711179200166853502083

theorem tailTrace_5041497 : CollatzResearch.WordTrace tailWord_5041497 prefixEnd_5041497 2588711179200166853502083 := by
  unfold tailWord_5041497
  simp only [CollatzResearch.WordTrace]
  refine ⟨183878501816524862983474745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122585667877683241988983163 183878501816524862983474745)
  ·
    refine ⟨137908876362393647237606059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183878501816524862983474745 137908876362393647237606059)
    ·
      refine ⟨206863314543590470856409089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137908876362393647237606059 206863314543590470856409089)
      ·
        refine ⟨155147485907692853142306817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206863314543590470856409089 155147485907692853142306817)
        ·
          refine ⟨116360614430769639856730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155147485907692853142306817 116360614430769639856730113)
          ·
            refine ⟨87270460823077229892547585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116360614430769639856730113 87270460823077229892547585)
            ·
              refine ⟨65452845617307922419410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87270460823077229892547585 65452845617307922419410689)
              ·
                refine ⟨49089634212980941814558017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65452845617307922419410689 49089634212980941814558017)
                ·
                  refine ⟨36817225659735706360918513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49089634212980941814558017 36817225659735706360918513)
                  ·
                    refine ⟨27612919244801779770688885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36817225659735706360918513 27612919244801779770688885)
                    ·
                      refine ⟨2588711179200166853502083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27612919244801779770688885 2588711179200166853502083)
                      ·
                        rfl

theorem cell23_5041497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_5041497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041497 prefixEnd_5041497 := by exact prefixLift 5041497
  have htrace : WordTrace (prefixWord ++ tailWord_5041497) baseStart_5041497 baseEnd_5041497 := by
    simpa [prefixWord, tailWord_5041497, baseEnd_5041497] using wordTrace_append hprefix tailTrace_5041497
  have hstable : (prefixWord ++ tailWord_5041497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041497).length < 2 ^ (prefixWord ++ tailWord_5041497).sum := by decide
  have hdescent : baseEnd_5041497 < baseStart_5041497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041541 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_5041541 : Nat := 118140960795 + 5041541 * 2 ^ 59
def prefixEnd_5041541 : Nat := 4983230072969 + 3 ^ 40 * 5041541 * 2
def baseEnd_5041541 : Nat := 2588733772348964681351881

theorem tailTrace_5041541 : CollatzResearch.WordTrace tailWord_5041541 prefixEnd_5041541 2588733772348964681351881 := by
  unfold tailWord_5041541
  simp only [CollatzResearch.WordTrace]
  refine ⟨183880106628365458498076477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122586737752243638998717651 183880106628365458498076477)
  ·
    refine ⟨68955039985637046936778679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183880106628365458498076477 68955039985637046936778679)
    ·
      refine ⟨103432559978455570405168019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68955039985637046936778679 103432559978455570405168019)
      ·
        refine ⟨155148839967683355607752029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103432559978455570405168019 155148839967683355607752029)
        ·
          refine ⟨58180814987881258352907011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155148839967683355607752029 58180814987881258352907011)
          ·
            refine ⟨87271222481821887529360517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58180814987881258352907011 87271222481821887529360517)
            ·
              refine ⟨16363354215341603911755097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87271222481821887529360517 16363354215341603911755097)
              ·
                refine ⟨12272515661506202933816323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16363354215341603911755097 12272515661506202933816323)
                ·
                  refine ⟨18408773492259304400724485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12272515661506202933816323 18408773492259304400724485)
                  ·
                    refine ⟨3451645029798619575135841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18408773492259304400724485 3451645029798619575135841)
                    ·
                      refine ⟨2588733772348964681351881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451645029798619575135841 2588733772348964681351881)
                      ·
                        rfl

theorem cell23_5041541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_5041541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041541 prefixEnd_5041541 := by exact prefixLift 5041541
  have htrace : WordTrace (prefixWord ++ tailWord_5041541) baseStart_5041541 baseEnd_5041541 := by
    simpa [prefixWord, tailWord_5041541, baseEnd_5041541] using wordTrace_append hprefix tailTrace_5041541
  have hstable : (prefixWord ++ tailWord_5041541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041541).length < 2 ^ (prefixWord ++ tailWord_5041541).sum := by decide
  have hdescent : baseEnd_5041541 < baseStart_5041541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041547 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 9]
def baseStart_5041547 : Nat := 118140960795 + 5041547 * 2 ^ 59
def prefixEnd_5041547 : Nat := 4983230072969 + 3 ^ 40 * 5041547 * 2
def baseEnd_5041547 : Nat := 287637428136987961986317

theorem tailTrace_5041547 : CollatzResearch.WordTrace tailWord_5041547 prefixEnd_5041547 287637428136987961986317 := by
  unfold tailWord_5041547
  simp only [CollatzResearch.WordTrace]
  refine ⟨183880325466343721522794895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122586883644229147681863263 183880325466343721522794895)
  ·
    refine ⟨275820488199515582284192343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183880325466343721522794895 275820488199515582284192343)
    ·
      refine ⟨413730732299273373426288515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275820488199515582284192343 413730732299273373426288515)
      ·
        refine ⟨620596098448910060139432773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413730732299273373426288515 620596098448910060139432773)
        ·
          refine ⟨116361768459170636276143645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 620596098448910060139432773 116361768459170636276143645)
          ·
            refine ⟨43635663172188988603553867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116361768459170636276143645 43635663172188988603553867)
            ·
              refine ⟨65453494758283482905330801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43635663172188988603553867 65453494758283482905330801)
              ·
                refine ⟨49090121068712612178998101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65453494758283482905330801 49090121068712612178998101)
                ·
                  refine ⟨287637428136987961986317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49090121068712612178998101 287637428136987961986317)
                  ·
                    rfl

theorem cell23_5041547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 9].length) (baseStart_5041547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041547 prefixEnd_5041547 := by exact prefixLift 5041547
  have htrace : WordTrace (prefixWord ++ tailWord_5041547) baseStart_5041547 baseEnd_5041547 := by
    simpa [prefixWord, tailWord_5041547, baseEnd_5041547] using wordTrace_append hprefix tailTrace_5041547
  have hstable : (prefixWord ++ tailWord_5041547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041547).length < 2 ^ (prefixWord ++ tailWord_5041547).sum := by decide
  have hdescent : baseEnd_5041547 < baseStart_5041547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041581 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 7]
def baseStart_5041581 : Nat := 118140960795 + 5041581 * 2 ^ 59
def prefixEnd_5041581 : Nat := 4983230072969 + 3 ^ 40 * 5041581 * 2
def baseEnd_5041581 : Nat := 287639367952793836094633

theorem tailTrace_5041581 : CollatzResearch.WordTrace tailWord_5041581 prefixEnd_5041581 287639367952793836094633 := by
  unfold tailWord_5041581
  simp only [CollatzResearch.WordTrace]
  refine ⟨183881565548220545329532597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122587710365480363553021731 183881565548220545329532597)
  ·
    refine ⟨17238896770145676124643681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183881565548220545329532597 17238896770145676124643681)
    ·
      refine ⟨12929172577609257093482761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17238896770145676124643681 12929172577609257093482761)
      ·
        refine ⟨9696879433206942820112071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12929172577609257093482761 9696879433206942820112071)
        ·
          refine ⟨14545319149810414230168107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9696879433206942820112071 14545319149810414230168107)
          ·
            refine ⟨21817978724715621345252161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14545319149810414230168107 21817978724715621345252161)
            ·
              refine ⟨16363484043536716008939121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21817978724715621345252161 16363484043536716008939121)
              ·
                refine ⟨12272613032652537006704341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16363484043536716008939121 12272613032652537006704341)
                ·
                  refine ⟨287639367952793836094633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12272613032652537006704341 287639367952793836094633)
                  ·
                    rfl

theorem cell23_5041581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_5041581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041581 prefixEnd_5041581 := by exact prefixLift 5041581
  have htrace : WordTrace (prefixWord ++ tailWord_5041581) baseStart_5041581 baseEnd_5041581 := by
    simpa [prefixWord, tailWord_5041581, baseEnd_5041581] using wordTrace_append hprefix tailTrace_5041581
  have hstable : (prefixWord ++ tailWord_5041581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041581).length < 2 ^ (prefixWord ++ tailWord_5041581).sum := by decide
  have hdescent : baseEnd_5041581 < baseStart_5041581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041631 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 6, 2]
def baseStart_5041631 : Nat := 118140960795 + 5041631 * 2 ^ 59
def prefixEnd_5041631 : Nat := 4983230072969 + 3 ^ 40 * 5041631 * 2
def baseEnd_5041631 : Nat := 2588779985607869329226467

theorem tailTrace_5041631 : CollatzResearch.WordTrace tailWord_5041631 prefixEnd_5041631 2588779985607869329226467 := by
  unfold tailWord_5041631
  simp only [CollatzResearch.WordTrace]
  refine ⟨183883389198039403868852747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122588926132026269245901831 183883389198039403868852747)
  ·
    refine ⟨275825083797059105803279121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183883389198039403868852747 275825083797059105803279121)
    ·
      refine ⟨206868812847794329352459341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275825083797059105803279121 206868812847794329352459341)
      ·
        refine ⟨77575804817922873507172253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206868812847794329352459341 77575804817922873507172253)
        ·
          refine ⟨29090926806721077565189595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77575804817922873507172253 29090926806721077565189595)
          ·
            refine ⟨43636390210081616347784393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29090926806721077565189595 43636390210081616347784393)
            ·
              refine ⟨32727292657561212260838295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43636390210081616347784393 32727292657561212260838295)
              ·
                refine ⟨49090938986341818391257443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32727292657561212260838295 49090938986341818391257443)
                ·
                  refine ⟨73636408479512727586886165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49090938986341818391257443 73636408479512727586886165)
                  ·
                    refine ⟨3451706647477159105635289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73636408479512727586886165 3451706647477159105635289)
                    ·
                      refine ⟨2588779985607869329226467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451706647477159105635289 2588779985607869329226467)
                      ·
                        rfl

theorem cell23_5041631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_5041631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041631 prefixEnd_5041631 := by exact prefixLift 5041631
  have htrace : WordTrace (prefixWord ++ tailWord_5041631) baseStart_5041631 baseEnd_5041631 := by
    simpa [prefixWord, tailWord_5041631, baseEnd_5041631] using wordTrace_append hprefix tailTrace_5041631
  have hstable : (prefixWord ++ tailWord_5041631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041631).length < 2 ^ (prefixWord ++ tailWord_5041631).sum := by decide
  have hdescent : baseEnd_5041631 < baseStart_5041631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041658 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_5041658 : Nat := 118140960795 + 5041658 * 2 ^ 59
def prefixEnd_5041658 : Nat := 4983230072969 + 3 ^ 40 * 5041658 * 2
def baseEnd_5041658 : Nat := 862931283195180241196281

theorem tailTrace_5041658 : CollatzResearch.WordTrace tailWord_5041658 prefixEnd_5041658 862931283195180241196281 := by
  unfold tailWord_5041658
  simp only [CollatzResearch.WordTrace]
  refine ⟨45971093492235396870021407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122589582645961058320057085 45971093492235396870021407)
  ·
    refine ⟨68956640238353095305032111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45971093492235396870021407 68956640238353095305032111)
    ·
      refine ⟨103434960357529642957548167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68956640238353095305032111 103434960357529642957548167)
      ·
        refine ⟨155152440536294464436322251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103434960357529642957548167 155152440536294464436322251)
        ·
          refine ⟨232728660804441696654483377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155152440536294464436322251 232728660804441696654483377)
          ·
            refine ⟨174546495603331272490862533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232728660804441696654483377 174546495603331272490862533)
            ·
              refine ⟨32727467925624613592036725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174546495603331272490862533 32727467925624613592036725)
              ·
                refine ⟨3068200118027307524253443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32727467925624613592036725 3068200118027307524253443)
                ·
                  refine ⟨4602300177040961286380165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068200118027307524253443 4602300177040961286380165)
                  ·
                    refine ⟨862931283195180241196281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602300177040961286380165 862931283195180241196281)
                    ·
                      rfl

theorem cell23_5041658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_5041658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041658 prefixEnd_5041658 := by exact prefixLift 5041658
  have htrace : WordTrace (prefixWord ++ tailWord_5041658) baseStart_5041658 baseEnd_5041658 := by
    simpa [prefixWord, tailWord_5041658, baseEnd_5041658] using wordTrace_append hprefix tailTrace_5041658
  have hstable : (prefixWord ++ tailWord_5041658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041658).length < 2 ^ (prefixWord ++ tailWord_5041658).sum := by decide
  have hdescent : baseEnd_5041658 < baseStart_5041658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041671 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 6]
def baseStart_5041671 : Nat := 118140960795 + 5041671 * 2 ^ 59
def prefixEnd_5041671 : Nat := 4983230072969 + 3 ^ 40 * 5041671 * 2
def baseEnd_5041671 : Nat := 287644502759338796969587

theorem tailTrace_5041671 : CollatzResearch.WordTrace tailWord_5041671 prefixEnd_5041671 287644502759338796969587 := by
  unfold tailWord_5041671
  simp only [CollatzResearch.WordTrace]
  refine ⟨183884848117894490700308867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122589898745262993800205911 183884848117894490700308867)
  ·
    refine ⟨275827272176841736050463301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183884848117894490700308867 275827272176841736050463301)
    ·
      refine ⟨51717613533157825509461869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275827272176841736050463301 51717613533157825509461869)
      ·
        refine ⟨19394105074934184566048201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51717613533157825509461869 19394105074934184566048201)
        ·
          refine ⟨14545578806200638424536151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19394105074934184566048201 14545578806200638424536151)
          ·
            refine ⟨21818368209300957636804227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14545578806200638424536151 21818368209300957636804227)
            ·
              refine ⟨32727552313951436455206341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21818368209300957636804227 32727552313951436455206341)
              ·
                refine ⟨6136416058865894335351189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32727552313951436455206341 6136416058865894335351189)
                ·
                  refine ⟨287644502759338796969587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6136416058865894335351189 287644502759338796969587)
                  ·
                    rfl

theorem cell23_5041671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 6].length) (baseStart_5041671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041671 prefixEnd_5041671 := by exact prefixLift 5041671
  have htrace : WordTrace (prefixWord ++ tailWord_5041671) baseStart_5041671 baseEnd_5041671 := by
    simpa [prefixWord, tailWord_5041671, baseEnd_5041671] using wordTrace_append hprefix tailTrace_5041671
  have hstable : (prefixWord ++ tailWord_5041671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041671).length < 2 ^ (prefixWord ++ tailWord_5041671).sum := by decide
  have hdescent : baseEnd_5041671 < baseStart_5041671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041675 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 1, 4]
def baseStart_5041675 : Nat := 118140960795 + 5041675 * 2 ^ 59
def prefixEnd_5041675 : Nat := 4983230072969 + 3 ^ 40 * 5041675 * 2
def baseEnd_5041675 : Nat := 862934192918889052358755

theorem tailTrace_5041675 : CollatzResearch.WordTrace tailWord_5041675 prefixEnd_5041675 862934192918889052358755 := by
  unfold tailWord_5041675
  simp only [CollatzResearch.WordTrace]
  refine ⟨183884994009879999383454479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122589996006586666255636319 183884994009879999383454479)
  ·
    refine ⟨275827491014819999075181719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183884994009879999383454479 275827491014819999075181719)
    ·
      refine ⟨413741236522229998612772579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275827491014819999075181719 413741236522229998612772579)
      ·
        refine ⟨620611854783344997919158869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413741236522229998612772579 620611854783344997919158869)
        ·
          refine ⟨7272795173242324194365143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 620611854783344997919158869 7272795173242324194365143)
          ·
            refine ⟨10909192759863486291547715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7272795173242324194365143 10909192759863486291547715)
            ·
              refine ⟨16363789139795229437321573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10909192759863486291547715 16363789139795229437321573)
              ·
                refine ⟨3068210463711605519497795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16363789139795229437321573 3068210463711605519497795)
                ·
                  refine ⟨4602315695567408279246693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068210463711605519497795 4602315695567408279246693)
                  ·
                    refine ⟨862934192918889052358755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602315695567408279246693 862934192918889052358755)
                    ·
                      rfl

theorem cell23_5041675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 4].length) (baseStart_5041675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041675 prefixEnd_5041675 := by exact prefixLift 5041675
  have htrace : WordTrace (prefixWord ++ tailWord_5041675) baseStart_5041675 baseEnd_5041675 := by
    simpa [prefixWord, tailWord_5041675, baseEnd_5041675] using wordTrace_append hprefix tailTrace_5041675
  have hstable : (prefixWord ++ tailWord_5041675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041675).length < 2 ^ (prefixWord ++ tailWord_5041675).sum := by decide
  have hdescent : baseEnd_5041675 < baseStart_5041675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041698 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_5041698 : Nat := 118140960795 + 5041698 * 2 ^ 59
def prefixEnd_5041698 : Nat := 4983230072969 + 3 ^ 40 * 5041698 * 2
def baseEnd_5041698 : Nat := 2588814388811720567088659

theorem tailTrace_5041698 : CollatzResearch.WordTrace tailWord_5041698 prefixEnd_5041698 2588814388811720567088659 := by
  unfold tailWord_5041698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45971458222199168577885437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122590555259197782874361165 45971458222199168577885437)
  ·
    refine ⟨17239296833324688216707039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45971458222199168577885437 17239296833324688216707039)
    ·
      refine ⟨25858945249987032325060559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17239296833324688216707039 25858945249987032325060559)
      ·
        refine ⟨38788417874980548487590839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25858945249987032325060559 38788417874980548487590839)
        ·
          refine ⟨58182626812470822731386259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38788417874980548487590839 58182626812470822731386259)
          ·
            refine ⟨87273940218706234097079389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58182626812470822731386259 87273940218706234097079389)
            ·
              refine ⟨32727727582014837786404771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87273940218706234097079389 32727727582014837786404771)
              ·
                refine ⟨49091591373022256679607157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32727727582014837786404771 49091591373022256679607157)
                ·
                  refine ⟨4602336691220836563713171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49091591373022256679607157 4602336691220836563713171)
                  ·
                    refine ⟨6903505036831254845569757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602336691220836563713171 6903505036831254845569757)
                    ·
                      refine ⟨2588814388811720567088659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6903505036831254845569757 2588814388811720567088659)
                      ·
                        rfl

theorem cell23_5041698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_5041698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041698 prefixEnd_5041698 := by exact prefixLift 5041698
  have htrace : WordTrace (prefixWord ++ tailWord_5041698) baseStart_5041698 baseEnd_5041698 := by
    simpa [prefixWord, tailWord_5041698, baseEnd_5041698] using wordTrace_append hprefix tailTrace_5041698
  have hstable : (prefixWord ++ tailWord_5041698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041698).length < 2 ^ (prefixWord ++ tailWord_5041698).sum := by decide
  have hdescent : baseEnd_5041698 < baseStart_5041698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041701 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_5041701 : Nat := 118140960795 + 5041701 * 2 ^ 59
def prefixEnd_5041701 : Nat := 4983230072969 + 3 ^ 40 * 5041701 * 2
def baseEnd_5041701 : Nat := 862938643084561351783715

theorem tailTrace_5041701 : CollatzResearch.WordTrace tailWord_5041701 prefixEnd_5041701 862938643084561351783715 := by
  unfold tailWord_5041701
  simp only [CollatzResearch.WordTrace]
  refine ⟨183885942307785805823900957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122590628205190537215933971 183885942307785805823900957)
  ·
    refine ⟨68957228365419677183962859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183885942307785805823900957 68957228365419677183962859)
    ·
      refine ⟨103435842548129515775944289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68957228365419677183962859 103435842548129515775944289)
      ·
        refine ⟨77576881911097136831958217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103435842548129515775944289 77576881911097136831958217)
        ·
          refine ⟨58182661433322852623968663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77576881911097136831958217 58182661433322852623968663)
          ·
            refine ⟨87273992149984278935952995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58182661433322852623968663 87273992149984278935952995)
            ·
              refine ⟨130910988224976418403929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87273992149984278935952995 130910988224976418403929493)
              ·
                refine ⟨6136452573045769612684195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130910988224976418403929493 6136452573045769612684195)
                ·
                  refine ⟨9204678859568654419026293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6136452573045769612684195 9204678859568654419026293)
                  ·
                    refine ⟨862938643084561351783715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9204678859568654419026293 862938643084561351783715)
                    ·
                      rfl

theorem cell23_5041701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_5041701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041701 prefixEnd_5041701 := by exact prefixLift 5041701
  have htrace : WordTrace (prefixWord ++ tailWord_5041701) baseStart_5041701 baseEnd_5041701 := by
    simpa [prefixWord, tailWord_5041701, baseEnd_5041701] using wordTrace_append hprefix tailTrace_5041701
  have hstable : (prefixWord ++ tailWord_5041701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041701).length < 2 ^ (prefixWord ++ tailWord_5041701).sum := by decide
  have hdescent : baseEnd_5041701 < baseStart_5041701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041715 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 1, 1, 3]
def baseStart_5041715 : Nat := 118140960795 + 5041715 * 2 ^ 59
def prefixEnd_5041715 : Nat := 4983230072969 + 3 ^ 40 * 5041715 * 2
def baseEnd_5041715 : Nat := 2588823117982847000576081

theorem tailTrace_5041715 : CollatzResearch.WordTrace tailWord_5041715 prefixEnd_5041715 2588823117982847000576081 := by
  unfold tailWord_5041715
  simp only [CollatzResearch.WordTrace]
  refine ⟨183886452929735086214910599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122590968619823390809940399 183886452929735086214910599)
  ·
    refine ⟨275829679394602629322365899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183886452929735086214910599 275829679394602629322365899)
    ·
      refine ⟨413744519091903943983548849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275829679394602629322365899 413744519091903943983548849)
      ·
        refine ⟨310308389318927957987661637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413744519091903943983548849 310308389318927957987661637)
        ·
          refine ⟨58182822997298992122686557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310308389318927957987661637 58182822997298992122686557)
          ·
            refine ⟨21818558623987122046007459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58182822997298992122686557 21818558623987122046007459)
            ·
              refine ⟨32727837935980683069011189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21818558623987122046007459 32727837935980683069011189)
              ·
                refine ⟨3068234806498189037719799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32727837935980683069011189 3068234806498189037719799)
                ·
                  refine ⟨4602352209747283556579699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068234806498189037719799 4602352209747283556579699)
                  ·
                    refine ⟨6903528314620925334869549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602352209747283556579699 6903528314620925334869549)
                    ·
                      refine ⟨2588823117982847000576081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6903528314620925334869549 2588823117982847000576081)
                      ·
                        rfl

theorem cell23_5041715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 1, 3].length) (baseStart_5041715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041715 prefixEnd_5041715 := by exact prefixLift 5041715
  have htrace : WordTrace (prefixWord ++ tailWord_5041715) baseStart_5041715 baseEnd_5041715 := by
    simpa [prefixWord, tailWord_5041715, baseEnd_5041715] using wordTrace_append hprefix tailTrace_5041715
  have hstable : (prefixWord ++ tailWord_5041715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041715).length < 2 ^ (prefixWord ++ tailWord_5041715).sum := by decide
  have hdescent : baseEnd_5041715 < baseStart_5041715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041744 : List Nat := [2, 1, 1, 1, 1, 3, 4, 10]
def baseStart_5041744 : Nat := 118140960795 + 5041744 * 2 ^ 59
def prefixEnd_5041744 : Nat := 4983230072969 + 3 ^ 40 * 5041744 * 2
def baseEnd_5041744 : Nat := 95882889219326940263461

theorem tailTrace_5041744 : CollatzResearch.WordTrace tailWord_5041744 prefixEnd_5041744 95882889219326940263461 := by
  unfold tailWord_5041744
  simp only [CollatzResearch.WordTrace]
  refine ⟨91943755323315012083858143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122591673764420016111810857 91943755323315012083858143)
  ·
    refine ⟨137915632984972518125787215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91943755323315012083858143 137915632984972518125787215)
    ·
      refine ⟨206873449477458777188680823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137915632984972518125787215 206873449477458777188680823)
      ·
        refine ⟨310310174216188165783021235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206873449477458777188680823 310310174216188165783021235)
        ·
          refine ⟨465465261324282248674531853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310310174216188165783021235 465465261324282248674531853)
          ·
            refine ⟨174549472996605843252949445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465465261324282248674531853 174549472996605843252949445)
            ·
              refine ⟨32728026186863595609928021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174549472996605843252949445 32728026186863595609928021)
              ·
                refine ⟨95882889219326940263461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32728026186863595609928021 95882889219326940263461)
                ·
                  rfl

theorem cell23_5041744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 10].length) (baseStart_5041744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041744 prefixEnd_5041744 := by exact prefixLift 5041744
  have htrace : WordTrace (prefixWord ++ tailWord_5041744) baseStart_5041744 baseEnd_5041744 := by
    simpa [prefixWord, tailWord_5041744, baseEnd_5041744] using wordTrace_append hprefix tailTrace_5041744
  have hstable : (prefixWord ++ tailWord_5041744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041744).length < 2 ^ (prefixWord ++ tailWord_5041744).sum := by decide
  have hdescent : baseEnd_5041744 < baseStart_5041744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041751 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_5041751 : Nat := 118140960795 + 5041751 * 2 ^ 59
def prefixEnd_5041751 : Nat := 4983230072969 + 3 ^ 40 * 5041751 * 2
def baseEnd_5041751 : Nat := 2588841603286408859725915

theorem tailTrace_5041751 : CollatzResearch.WordTrace tailWord_5041751 prefixEnd_5041751 2588841603286408859725915 := by
  unfold tailWord_5041751
  simp only [CollatzResearch.WordTrace]
  refine ⟨183887765957604664363221107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122591843971736442908814071 183887765957604664363221107)
  ·
    refine ⟨275831648936406996544831661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183887765957604664363221107 275831648936406996544831661)
    ·
      refine ⟨103436868351152623704311873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275831648936406996544831661 103436868351152623704311873)
      ·
        refine ⟨77577651263364467778233905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103436868351152623704311873 77577651263364467778233905)
        ·
          refine ⟨58183238447523350833675429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77577651263364467778233905 58183238447523350833675429)
          ·
            refine ⟨10909357208910628281314143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58183238447523350833675429 10909357208910628281314143)
            ·
              refine ⟨16364035813365942421971215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10909357208910628281314143 16364035813365942421971215)
              ·
                refine ⟨24546053720048913632956823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16364035813365942421971215 24546053720048913632956823)
                ·
                  refine ⟨36819080580073370449435235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24546053720048913632956823 36819080580073370449435235)
                  ·
                    refine ⟨55228620870110055674152853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36819080580073370449435235 55228620870110055674152853)
                    ·
                      refine ⟨2588841603286408859725915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55228620870110055674152853 2588841603286408859725915)
                      ·
                        rfl

theorem cell23_5041751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_5041751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041751 prefixEnd_5041751 := by exact prefixLift 5041751
  have htrace : WordTrace (prefixWord ++ tailWord_5041751) baseStart_5041751 baseEnd_5041751 := by
    simpa [prefixWord, tailWord_5041751, baseEnd_5041751] using wordTrace_append hprefix tailTrace_5041751
  have hstable : (prefixWord ++ tailWord_5041751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041751).length < 2 ^ (prefixWord ++ tailWord_5041751).sum := by decide
  have hdescent : baseEnd_5041751 < baseStart_5041751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041815 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_5041815 : Nat := 118140960795 + 5041815 * 2 ^ 59
def prefixEnd_5041815 : Nat := 4983230072969 + 3 ^ 40 * 5041815 * 2
def baseEnd_5041815 : Nat := 2588874466048296609325621

theorem tailTrace_5041815 : CollatzResearch.WordTrace tailWord_5041815 prefixEnd_5041815 2588874466048296609325621 := by
  unfold tailWord_5041815
  simp only [CollatzResearch.WordTrace]
  refine ⟨183890100229372803293550899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122593400152915202195700599 183890100229372803293550899)
  ·
    refine ⟨275835150344059204940326349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183890100229372803293550899 275835150344059204940326349)
    ·
      refine ⟨103438181379022201852622381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275835150344059204940326349 103438181379022201852622381)
      ·
        refine ⟨38789318017133325694733393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103438181379022201852622381 38789318017133325694733393)
        ·
          refine ⟨29091988512849994271050045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38789318017133325694733393 29091988512849994271050045)
          ·
            refine ⟨10909495692318747851643767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29091988512849994271050045 10909495692318747851643767)
            ·
              refine ⟨16364243538478121777465651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10909495692318747851643767 16364243538478121777465651)
              ·
                refine ⟨24546365307717182666198477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16364243538478121777465651 24546365307717182666198477)
                ·
                  refine ⟨9204886990393943499824429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24546365307717182666198477 9204886990393943499824429)
                  ·
                    refine ⟨3451832621397728812434161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9204886990393943499824429 3451832621397728812434161)
                    ·
                      refine ⟨2588874466048296609325621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451832621397728812434161 2588874466048296609325621)
                      ·
                        rfl

theorem cell23_5041815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_5041815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041815 prefixEnd_5041815 := by exact prefixLift 5041815
  have htrace : WordTrace (prefixWord ++ tailWord_5041815) baseStart_5041815 baseEnd_5041815 := by
    simpa [prefixWord, tailWord_5041815, baseEnd_5041815] using wordTrace_append hprefix tailTrace_5041815
  have hstable : (prefixWord ++ tailWord_5041815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041815).length < 2 ^ (prefixWord ++ tailWord_5041815).sum := by decide
  have hdescent : baseEnd_5041815 < baseStart_5041815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041821 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_5041821 : Nat := 118140960795 + 5041821 * 2 ^ 59
def prefixEnd_5041821 : Nat := 4983230072969 + 3 ^ 40 * 5041821 * 2
def baseEnd_5041821 : Nat := 862959182310741195283531

theorem tailTrace_5041821 : CollatzResearch.WordTrace tailWord_5041821 prefixEnd_5041821 862959182310741195283531 := by
  unfold tailWord_5041821
  simp only [CollatzResearch.WordTrace]
  refine ⟨183890319067351066318269317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122593546044900710878846211 183890319067351066318269317)
  ·
    refine ⟨34479434825128324934675497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183890319067351066318269317 34479434825128324934675497)
    ·
      refine ⟨25859576118846243701006623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34479434825128324934675497 25859576118846243701006623)
      ·
        refine ⟨38789364178269365551509935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25859576118846243701006623 38789364178269365551509935)
        ·
          refine ⟨58184046267404048327264903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38789364178269365551509935 58184046267404048327264903)
          ·
            refine ⟨87276069401106072490897355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58184046267404048327264903 87276069401106072490897355)
            ·
              refine ⟨130914104101659108736346033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87276069401106072490897355 130914104101659108736346033)
              ·
                refine ⟨98185578076244331552259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130914104101659108736346033 98185578076244331552259525)
                ·
                  refine ⟨18409795889295812166048661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98185578076244331552259525 18409795889295812166048661)
                  ·
                    refine ⟨862959182310741195283531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18409795889295812166048661 862959182310741195283531)
                    ·
                      rfl

theorem cell23_5041821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_5041821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041821 prefixEnd_5041821 := by exact prefixLift 5041821
  have htrace : WordTrace (prefixWord ++ tailWord_5041821) baseStart_5041821 baseEnd_5041821 := by
    simpa [prefixWord, tailWord_5041821, baseEnd_5041821] using wordTrace_append hprefix tailTrace_5041821
  have hstable : (prefixWord ++ tailWord_5041821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041821).length < 2 ^ (prefixWord ++ tailWord_5041821).sum := by decide
  have hdescent : baseEnd_5041821 < baseStart_5041821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5041898 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_5041898 : Nat := 118140960795 + 5041898 * 2 ^ 59
def prefixEnd_5041898 : Nat := 4983230072969 + 3 ^ 40 * 5041898 * 2
def baseEnd_5041898 : Nat := 862972361647539928195913

theorem tailTrace_5041898 : CollatzResearch.WordTrace tailWord_5041898 prefixEnd_5041898 862972361647539928195913 := by
  unfold tailWord_5041898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45973281872018027117205587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122595418325381405645881565 45973281872018027117205587)
  ·
    refine ⟨68959922808027040675808381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45973281872018027117205587 68959922808027040675808381)
    ·
      refine ⟨25859971053010140253428143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68959922808027040675808381 25859971053010140253428143)
      ·
        refine ⟨38789956579515210380142215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25859971053010140253428143 38789956579515210380142215)
        ·
          refine ⟨58184934869272815570213323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38789956579515210380142215 58184934869272815570213323)
          ·
            refine ⟨87277402303909223355319985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58184934869272815570213323 87277402303909223355319985)
            ·
              refine ⟨65458051727931917516489989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87277402303909223355319985 65458051727931917516489989)
              ·
                refine ⟨12273384698987234534341873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65458051727931917516489989 12273384698987234534341873)
                ·
                  refine ⟨9205038524240425900756405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12273384698987234534341873 9205038524240425900756405)
                  ·
                    refine ⟨862972361647539928195913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9205038524240425900756405 862972361647539928195913)
                    ·
                      rfl

theorem cell23_5041898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_5041898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5041898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5041898 prefixEnd_5041898 := by exact prefixLift 5041898
  have htrace : WordTrace (prefixWord ++ tailWord_5041898) baseStart_5041898 baseEnd_5041898 := by
    simpa [prefixWord, tailWord_5041898, baseEnd_5041898] using wordTrace_append hprefix tailTrace_5041898
  have hstable : (prefixWord ++ tailWord_5041898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5041898).length < 2 ^ (prefixWord ++ tailWord_5041898).sum := by decide
  have hdescent : baseEnd_5041898 < baseStart_5041898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5041898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042042 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_5042042 : Nat := 118140960795 + 5042042 * 2 ^ 59
def prefixEnd_5042042 : Nat := 4983230072969 + 3 ^ 40 * 5042042 * 2
def baseEnd_5042042 : Nat := 2588991026156867221187077

theorem tailTrace_5042042 : CollatzResearch.WordTrace tailWord_5042042 prefixEnd_5042042 2588991026156867221187077 := by
  unfold tailWord_5042042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45974594899887605265516095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122598919733033614041376253 45974594899887605265516095)
  ·
    refine ⟨68961892349831407898274143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45974594899887605265516095 68961892349831407898274143)
    ·
      refine ⟨103442838524747111847411215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68961892349831407898274143 103442838524747111847411215)
      ·
        refine ⟨155164257787120667771116823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103442838524747111847411215 155164257787120667771116823)
        ·
          refine ⟨232746386680681001656675235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155164257787120667771116823 232746386680681001656675235)
          ·
            refine ⟨349119580021021502485012853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232746386680681001656675235 349119580021021502485012853)
            ·
              refine ⟨32729960626970765857969955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349119580021021502485012853 32729960626970765857969955)
              ·
                refine ⟨49094940940456148786954933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32729960626970765857969955 49094940940456148786954933)
                ·
                  refine ⟨4602650713167763948777025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49094940940456148786954933 4602650713167763948777025)
                  ·
                    refine ⟨3451988034875822961582769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602650713167763948777025 3451988034875822961582769)
                    ·
                      refine ⟨2588991026156867221187077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451988034875822961582769 2588991026156867221187077)
                      ·
                        rfl

theorem cell23_5042042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_5042042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042042 prefixEnd_5042042 := by exact prefixLift 5042042
  have htrace : WordTrace (prefixWord ++ tailWord_5042042) baseStart_5042042 baseEnd_5042042 := by
    simpa [prefixWord, tailWord_5042042, baseEnd_5042042] using wordTrace_append hprefix tailTrace_5042042
  have hstable : (prefixWord ++ tailWord_5042042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042042).length < 2 ^ (prefixWord ++ tailWord_5042042).sum := by decide
  have hdescent : baseEnd_5042042 < baseStart_5042042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042046 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5042046 : Nat := 118140960795 + 5042046 * 2 ^ 59
def prefixEnd_5042046 : Nat := 4983230072969 + 3 ^ 40 * 5042046 * 2
def baseEnd_5042046 : Nat := 2588993080079485205537059

theorem tailTrace_5042046 : CollatzResearch.WordTrace tailWord_5042046 prefixEnd_5042046 2588993080079485205537059 := by
  unfold tailWord_5042046
  simp only [CollatzResearch.WordTrace]
  refine ⟨22987315686441991218151249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122599016994357286496806661 22987315686441991218151249)
  ·
    refine ⟨17240486764831493413613437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22987315686441991218151249 17240486764831493413613437)
    ·
      refine ⟨6465182536811810030105039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17240486764831493413613437 6465182536811810030105039)
      ·
        refine ⟨9697773805217715045157559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465182536811810030105039 9697773805217715045157559)
        ·
          refine ⟨14546660707826572567736339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9697773805217715045157559 14546660707826572567736339)
          ·
            refine ⟨21819991061739858851604509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14546660707826572567736339 21819991061739858851604509)
            ·
              refine ⟨8182496648152447069351691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21819991061739858851604509 8182496648152447069351691)
              ·
                refine ⟨12273744972228670604027537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8182496648152447069351691 12273744972228670604027537)
                ·
                  refine ⟨9205308729171502953020653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12273744972228670604027537 9205308729171502953020653)
                  ·
                    refine ⟨3451990773439313607382745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9205308729171502953020653 3451990773439313607382745)
                    ·
                      refine ⟨2588993080079485205537059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3451990773439313607382745 2588993080079485205537059)
                      ·
                        rfl

theorem cell23_5042046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5042046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042046 prefixEnd_5042046 := by exact prefixLift 5042046
  have htrace : WordTrace (prefixWord ++ tailWord_5042046) baseStart_5042046 baseEnd_5042046 := by
    simpa [prefixWord, tailWord_5042046, baseEnd_5042046] using wordTrace_append hprefix tailTrace_5042046
  have hstable : (prefixWord ++ tailWord_5042046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042046).length < 2 ^ (prefixWord ++ tailWord_5042046).sum := by decide
  have hdescent : baseEnd_5042046 < baseStart_5042046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042056 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 1, 5]
def baseStart_5042056 : Nat := 118140960795 + 5042056 * 2 ^ 59
def prefixEnd_5042056 : Nat := 4983230072969 + 3 ^ 40 * 5042056 * 2
def baseEnd_5042056 : Nat := 862999404962010055470671

theorem tailTrace_5042056 : CollatzResearch.WordTrace tailWord_5042056 prefixEnd_5042056 862999404962010055470671 := by
  unfold tailWord_5042056
  simp only [CollatzResearch.WordTrace]
  refine ⟨91949445110749850726537011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122599260147666467635382681 91949445110749850726537011)
  ·
    refine ⟨137924167666124776089805517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91949445110749850726537011 137924167666124776089805517)
    ·
      refine ⟨51721562874796791033677069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137924167666124776089805517 51721562874796791033677069)
      ·
        refine ⟨19395586078048796637628901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51721562874796791033677069 19395586078048796637628901)
        ·
          refine ⟨3636672389634149369555419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19395586078048796637628901 3636672389634149369555419)
          ·
            refine ⟨5455008584451224054333129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636672389634149369555419 5455008584451224054333129)
            ·
              refine ⟨4091256438338418040749847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5455008584451224054333129 4091256438338418040749847)
              ·
                refine ⟨6136884657507627061124771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091256438338418040749847 6136884657507627061124771)
                ·
                  refine ⟨9205326986261440591687157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6136884657507627061124771 9205326986261440591687157)
                  ·
                    refine ⟨862999404962010055470671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9205326986261440591687157 862999404962010055470671)
                    ·
                      rfl

theorem cell23_5042056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_5042056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042056 prefixEnd_5042056 := by exact prefixLift 5042056
  have htrace : WordTrace (prefixWord ++ tailWord_5042056) baseStart_5042056 baseEnd_5042056 := by
    simpa [prefixWord, tailWord_5042056, baseEnd_5042056] using wordTrace_append hprefix tailTrace_5042056
  have hstable : (prefixWord ++ tailWord_5042056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042056).length < 2 ^ (prefixWord ++ tailWord_5042056).sum := by decide
  have hdescent : baseEnd_5042056 < baseStart_5042056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042076 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5042076 : Nat := 118140960795 + 5042076 * 2 ^ 59
def prefixEnd_5042076 : Nat := 4983230072969 + 3 ^ 40 * 5042076 * 2
def baseEnd_5042076 : Nat := 2589008484499120088161921

theorem tailTrace_5042076 : CollatzResearch.WordTrace tailWord_5042076 prefixEnd_5042076 2589008484499120088161921 := by
  unfold tailWord_5042076
  simp only [CollatzResearch.WordTrace]
  refine ⟨91949809840713622434401041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122599746454284829912534721 91949809840713622434401041)
  ·
    refine ⟨68962357380535216825800781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91949809840713622434401041 68962357380535216825800781)
    ·
      refine ⟨25860884017700706309675293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68962357380535216825800781 25860884017700706309675293)
      ·
        refine ⟨9697831506637764866128235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25860884017700706309675293 9697831506637764866128235)
        ·
          refine ⟨14546747259956647299192353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9697831506637764866128235 14546747259956647299192353)
          ·
            refine ⟨10910060444967485474394265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14546747259956647299192353 10910060444967485474394265)
            ·
              refine ⟨8182545333725614105795699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10910060444967485474394265 8182545333725614105795699)
              ·
                refine ⟨12273818000588421158693549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8182545333725614105795699 12273818000588421158693549)
                ·
                  refine ⟨4602681750220657934510081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12273818000588421158693549 4602681750220657934510081)
                  ·
                    refine ⟨3452011312665493450882561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602681750220657934510081 3452011312665493450882561)
                    ·
                      refine ⟨2589008484499120088161921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452011312665493450882561 2589008484499120088161921)
                      ·
                        rfl

theorem cell23_5042076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5042076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042076 prefixEnd_5042076 := by exact prefixLift 5042076
  have htrace : WordTrace (prefixWord ++ tailWord_5042076) baseStart_5042076 baseEnd_5042076 := by
    simpa [prefixWord, tailWord_5042076, baseEnd_5042076] using wordTrace_append hprefix tailTrace_5042076
  have hstable : (prefixWord ++ tailWord_5042076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042076).length < 2 ^ (prefixWord ++ tailWord_5042076).sum := by decide
  have hdescent : baseEnd_5042076 < baseStart_5042076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042135 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_5042135 : Nat := 118140960795 + 5042135 * 2 ^ 59
def prefixEnd_5042135 : Nat := 4983230072969 + 3 ^ 40 * 5042135 * 2
def baseEnd_5042135 : Nat := 2589038779857735357324149

theorem tailTrace_5042135 : CollatzResearch.WordTrace tailWord_5042135 prefixEnd_5042135 2589038779857735357324149 := by
  unfold tailWord_5042135
  simp only [CollatzResearch.WordTrace]
  refine ⟨183901771588213497945199859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122601181058808998630133239 183901771588213497945199859)
  ·
    refine ⟨275852657382320246917799789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183901771588213497945199859 275852657382320246917799789)
    ·
      refine ⟨103444746518370092594174921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275852657382320246917799789 103444746518370092594174921)
      ·
        refine ⟨77583559888777569445631191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103444746518370092594174921 77583559888777569445631191)
        ·
          refine ⟨116375339833166354168446787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77583559888777569445631191 116375339833166354168446787)
          ·
            refine ⟨174563009749749531252670181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116375339833166354168446787 174563009749749531252670181)
            ·
              refine ⟨32730564328078037109875659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174563009749749531252670181 32730564328078037109875659)
              ·
                refine ⟨49095846492117055664813489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32730564328078037109875659 49095846492117055664813489)
                ·
                  refine ⟨36821884869087791748610117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49095846492117055664813489 36821884869087791748610117)
                  ·
                    refine ⟨6904103412953960952864397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36821884869087791748610117 6904103412953960952864397)
                    ·
                      refine ⟨2589038779857735357324149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904103412953960952864397 2589038779857735357324149)
                      ·
                        rfl

theorem cell23_5042135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_5042135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042135 prefixEnd_5042135 := by exact prefixLift 5042135
  have htrace : WordTrace (prefixWord ++ tailWord_5042135) baseStart_5042135 baseEnd_5042135 := by
    simpa [prefixWord, tailWord_5042135, baseEnd_5042135] using wordTrace_append hprefix tailTrace_5042135
  have hstable : (prefixWord ++ tailWord_5042135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042135).length < 2 ^ (prefixWord ++ tailWord_5042135).sum := by decide
  have hdescent : baseEnd_5042135 < baseStart_5042135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042145 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_5042145 : Nat := 118140960795 + 5042145 * 2 ^ 59
def prefixEnd_5042145 : Nat := 4983230072969 + 3 ^ 40 * 5042145 * 2
def baseEnd_5042145 : Nat := 2589043914664280318199103

theorem tailTrace_5042145 : CollatzResearch.WordTrace tailWord_5042145 prefixEnd_5042145 2589043914664280318199103 := by
  unfold tailWord_5042145
  simp only [CollatzResearch.WordTrace]
  refine ⟨183902136318177269653063889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122601424212118179768709259 183902136318177269653063889)
  ·
    refine ⟨137926602238632952239797917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183902136318177269653063889 137926602238632952239797917)
    ·
      refine ⟨51722475839487357089924219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137926602238632952239797917 51722475839487357089924219)
      ·
        refine ⟨77583713759231035634886329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51722475839487357089924219 77583713759231035634886329)
        ·
          refine ⟨58187785319423276726164747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77583713759231035634886329 58187785319423276726164747)
          ·
            refine ⟨87281677979134915089247121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58187785319423276726164747 87281677979134915089247121)
            ·
              refine ⟨65461258484351186316935341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87281677979134915089247121 65461258484351186316935341)
              ·
                refine ⟨24547971931631694868850753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65461258484351186316935341 24547971931631694868850753)
                ·
                  refine ⟨18410978948723771151638065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24547971931631694868850753 18410978948723771151638065)
                  ·
                    refine ⟨13808234211542828363728549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18410978948723771151638065 13808234211542828363728549)
                    ·
                      refine ⟨2589043914664280318199103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13808234211542828363728549 2589043914664280318199103)
                      ·
                        rfl

theorem cell23_5042145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_5042145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042145 prefixEnd_5042145 := by exact prefixLift 5042145
  have htrace : WordTrace (prefixWord ++ tailWord_5042145) baseStart_5042145 baseEnd_5042145 := by
    simpa [prefixWord, tailWord_5042145, baseEnd_5042145] using wordTrace_append hprefix tailTrace_5042145
  have hstable : (prefixWord ++ tailWord_5042145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042145).length < 2 ^ (prefixWord ++ tailWord_5042145).sum := by decide
  have hdescent : baseEnd_5042145 < baseStart_5042145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042166 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_5042166 : Nat := 118140960795 + 5042166 * 2 ^ 59
def prefixEnd_5042166 : Nat := 4983230072969 + 3 ^ 40 * 5042166 * 2
def baseEnd_5042166 : Nat := 2589054697758024736036507

theorem tailTrace_5042166 : CollatzResearch.WordTrace tailWord_5042166 prefixEnd_5042166 2589054697758024736036507 := by
  unfold tailWord_5042166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493931390693824389973647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122601934834067460159718901 11493931390693824389973647)
  ·
    refine ⟨17240897086040736584960471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493931390693824389973647 17240897086040736584960471)
    ·
      refine ⟨25861345629061104877440707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17240897086040736584960471 25861345629061104877440707)
      ·
        refine ⟨38792018443591657316161061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25861345629061104877440707 38792018443591657316161061)
        ·
          refine ⟨7273503458173435746780199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38792018443591657316161061 7273503458173435746780199)
          ·
            refine ⟨10910255187260153620170299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273503458173435746780199 10910255187260153620170299)
            ·
              refine ⟨16365382780890230430255449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10910255187260153620170299 16365382780890230430255449)
              ·
                refine ⟨12274037085667672822691587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16365382780890230430255449 12274037085667672822691587)
                ·
                  refine ⟨18411055628501509234037381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12274037085667672822691587 18411055628501509234037381)
                  ·
                    refine ⟨3452072930344032981382009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18411055628501509234037381 3452072930344032981382009)
                    ·
                      refine ⟨2589054697758024736036507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452072930344032981382009 2589054697758024736036507)
                      ·
                        rfl

theorem cell23_5042166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_5042166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042166 prefixEnd_5042166 := by exact prefixLift 5042166
  have htrace : WordTrace (prefixWord ++ tailWord_5042166) baseStart_5042166 baseEnd_5042166 := by
    simpa [prefixWord, tailWord_5042166, baseEnd_5042166] using wordTrace_append hprefix tailTrace_5042166
  have hstable : (prefixWord ++ tailWord_5042166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042166).length < 2 ^ (prefixWord ++ tailWord_5042166).sum := by decide
  have hdescent : baseEnd_5042166 < baseStart_5042166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042172 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 5]
def baseStart_5042172 : Nat := 118140960795 + 5042172 * 2 ^ 59
def prefixEnd_5042172 : Nat := 4983230072969 + 3 ^ 40 * 5042172 * 2
def baseEnd_5042172 : Nat := 287673086515772412506831

theorem tailTrace_5042172 : CollatzResearch.WordTrace tailWord_5042172 prefixEnd_5042172 287673086515772412506831 := by
  unfold tailWord_5042172
  simp only [CollatzResearch.WordTrace]
  refine ⟨91951560544539726632148385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122602080726052968842864513 91951560544539726632148385)
  ·
    refine ⟨68963670408404794974111289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91951560544539726632148385 68963670408404794974111289)
    ·
      refine ⟨51722752806303596230583467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68963670408404794974111289 51722752806303596230583467)
      ·
        refine ⟨77584129209455394345875201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51722752806303596230583467 77584129209455394345875201)
        ·
          refine ⟨58188096907091545759406401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77584129209455394345875201 58188096907091545759406401)
          ·
            refine ⟨43641072680318659319554801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58188096907091545759406401 43641072680318659319554801)
            ·
              refine ⟨32730804510238994489666101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43641072680318659319554801 32730804510238994489666101)
              ·
                refine ⟨3068512922834905733406197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32730804510238994489666101 3068512922834905733406197)
                ·
                  refine ⟨287673086515772412506831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3068512922834905733406197 287673086515772412506831)
                  ·
                    rfl

theorem cell23_5042172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_5042172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042172 prefixEnd_5042172 := by exact prefixLift 5042172
  have htrace : WordTrace (prefixWord ++ tailWord_5042172) baseStart_5042172 baseEnd_5042172 := by
    simpa [prefixWord, tailWord_5042172, baseEnd_5042172] using wordTrace_append hprefix tailTrace_5042172
  have hstable : (prefixWord ++ tailWord_5042172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042172).length < 2 ^ (prefixWord ++ tailWord_5042172).sum := by decide
  have hdescent : baseEnd_5042172 < baseStart_5042172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042195 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_5042195 : Nat := 118140960795 + 5042195 * 2 ^ 59
def prefixEnd_5042195 : Nat := 4983230072969 + 3 ^ 40 * 5042195 * 2
def baseEnd_5042195 : Nat := 2589069588697005122573873

theorem tailTrace_5042195 : CollatzResearch.WordTrace tailWord_5042195 prefixEnd_5042195 2589069588697005122573873 := by
  unfold tailWord_5042195
  simp only [CollatzResearch.WordTrace]
  refine ⟨183903959967996128192384039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122602639978664085461589359 183903959967996128192384039)
  ·
    refine ⟨275855939951994192288576059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183903959967996128192384039 275855939951994192288576059)
    ·
      refine ⟨413783909927991288432864089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275855939951994192288576059 413783909927991288432864089)
      ·
        refine ⟨310337932445993466324648067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413783909927991288432864089 310337932445993466324648067)
        ·
          refine ⟨465506898668990199486972101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310337932445993466324648067 465506898668990199486972101)
          ·
            refine ⟨87282543500435662403807269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 465506898668990199486972101 87282543500435662403807269)
            ·
              refine ⟨16365476906331686700713863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87282543500435662403807269 16365476906331686700713863)
              ·
                refine ⟨24548215359497530051070795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16365476906331686700713863 24548215359497530051070795)
                ·
                  refine ⟨36822323039246295076606193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24548215359497530051070795 36822323039246295076606193)
                  ·
                    refine ⟨27616742279434721307454645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36822323039246295076606193 27616742279434721307454645)
                    ·
                      refine ⟨2589069588697005122573873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27616742279434721307454645 2589069588697005122573873)
                      ·
                        rfl

theorem cell23_5042195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_5042195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042195 prefixEnd_5042195 := by exact prefixLift 5042195
  have htrace : WordTrace (prefixWord ++ tailWord_5042195) baseStart_5042195 baseEnd_5042195 := by
    simpa [prefixWord, tailWord_5042195, baseEnd_5042195] using wordTrace_append hprefix tailTrace_5042195
  have hstable : (prefixWord ++ tailWord_5042195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042195).length < 2 ^ (prefixWord ++ tailWord_5042195).sum := by decide
  have hdescent : baseEnd_5042195 < baseStart_5042195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042196 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5042196 : Nat := 118140960795 + 5042196 * 2 ^ 59
def prefixEnd_5042196 : Nat := 4983230072969 + 3 ^ 40 * 5042196 * 2
def baseEnd_5042196 : Nat := 2589070102177659618661369

theorem tailTrace_5042196 : CollatzResearch.WordTrace tailWord_5042196 prefixEnd_5042196 2589070102177659618661369 := by
  unfold tailWord_5042196
  simp only [CollatzResearch.WordTrace]
  refine ⟨91951998220496252681585221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122602664293995003575446961 91951998220496252681585221)
  ·
    refine ⟨17240999666343047377797229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91951998220496252681585221 17240999666343047377797229)
    ·
      refine ⟨6465374874878642766673961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17240999666343047377797229 6465374874878642766673961)
      ·
        refine ⟨4849031156158982075005471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6465374874878642766673961 4849031156158982075005471)
        ·
          refine ⟨7273546734238473112508207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849031156158982075005471 7273546734238473112508207)
          ·
            refine ⟨10910320101357709668762311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273546734238473112508207 10910320101357709668762311)
            ·
              refine ⟨16365480152036564503143467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10910320101357709668762311 16365480152036564503143467)
              ·
                refine ⟨24548220228054846754715201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16365480152036564503143467 24548220228054846754715201)
                ·
                  refine ⟨18411165171041135066036401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24548220228054846754715201 18411165171041135066036401)
                  ·
                    refine ⟨13808373878280851299527301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18411165171041135066036401 13808373878280851299527301)
                    ·
                      refine ⟨2589070102177659618661369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13808373878280851299527301 2589070102177659618661369)
                      ·
                        rfl

theorem cell23_5042196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5042196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042196 prefixEnd_5042196 := by exact prefixLift 5042196
  have htrace : WordTrace (prefixWord ++ tailWord_5042196) baseStart_5042196 baseEnd_5042196 := by
    simpa [prefixWord, tailWord_5042196, baseEnd_5042196] using wordTrace_append hprefix tailTrace_5042196
  have hstable : (prefixWord ++ tailWord_5042196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042196).length < 2 ^ (prefixWord ++ tailWord_5042196).sum := by decide
  have hdescent : baseEnd_5042196 < baseStart_5042196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042199 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5042199 : Nat := 118140960795 + 5042199 * 2 ^ 59
def prefixEnd_5042199 : Nat := 4983230072969 + 3 ^ 40 * 5042199 * 2
def baseEnd_5042199 : Nat := 2589071642619623106923855

theorem tailTrace_5042199 : CollatzResearch.WordTrace tailWord_5042199 prefixEnd_5042199 2589071642619623106923855 := by
  unfold tailWord_5042199
  simp only [CollatzResearch.WordTrace]
  refine ⟨183904105859981636875529651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122602737239987757917019767 183904105859981636875529651)
  ·
    refine ⟨275856158789972455313294477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183904105859981636875529651 275856158789972455313294477)
    ·
      refine ⟨103446059546239670742485429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275856158789972455313294477 103446059546239670742485429)
      ·
        refine ⟨9698068082459969132108009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103446059546239670742485429 9698068082459969132108009)
        ·
          refine ⟨7273551061844976849081007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9698068082459969132108009 7273551061844976849081007)
          ·
            refine ⟨10910326592767465273621511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273551061844976849081007 10910326592767465273621511)
            ·
              refine ⟨16365489889151197910432267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10910326592767465273621511 16365489889151197910432267)
              ·
                refine ⟨24548234833726796865648401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16365489889151197910432267 24548234833726796865648401)
                ·
                  refine ⟨18411176125295097649236301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24548234833726796865648401 18411176125295097649236301)
                  ·
                    refine ⟨6904191046985661618463613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18411176125295097649236301 6904191046985661618463613)
                    ·
                      refine ⟨2589071642619623106923855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904191046985661618463613 2589071642619623106923855)
                      ·
                        rfl

theorem cell23_5042199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5042199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042199 prefixEnd_5042199 := by exact prefixLift 5042199
  have htrace : WordTrace (prefixWord ++ tailWord_5042199) baseStart_5042199 baseEnd_5042199 := by
    simpa [prefixWord, tailWord_5042199, baseEnd_5042199] using wordTrace_append hprefix tailTrace_5042199
  have hstable : (prefixWord ++ tailWord_5042199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042199).length < 2 ^ (prefixWord ++ tailWord_5042199).sum := by decide
  have hdescent : baseEnd_5042199 < baseStart_5042199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042249 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 1, 4]
def baseStart_5042249 : Nat := 118140960795 + 5042249 * 2 ^ 59
def prefixEnd_5042249 : Nat := 4983230072969 + 3 ^ 40 * 5042249 * 2
def baseEnd_5042249 : Nat := 863032438884115970432875

theorem tailTrace_5042249 : CollatzResearch.WordTrace tailWord_5042249 prefixEnd_5042249 863032438884115970432875 := by
  unfold tailWord_5042249
  simp only [CollatzResearch.WordTrace]
  refine ⟨183905929509800495414849801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122603953006533663609899867 183905929509800495414849801)
  ·
    refine ⟨137929447132350371561137351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183905929509800495414849801 137929447132350371561137351)
    ·
      refine ⟨206894170698525557341706027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137929447132350371561137351 206894170698525557341706027)
      ·
        refine ⟨310341256047788336012559041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206894170698525557341706027 310341256047788336012559041)
        ·
          refine ⟨232755942035841252009419281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310341256047788336012559041 232755942035841252009419281)
          ·
            refine ⟨174566956526880939007064461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232755942035841252009419281 174566956526880939007064461)
            ·
              refine ⟨65462608697580352127649173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174566956526880939007064461 65462608697580352127649173)
              ·
                refine ⟨3068559782699079005983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65462608697580352127649173 3068559782699079005983555)
                ·
                  refine ⟨4602839674048618508975333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068559782699079005983555 4602839674048618508975333)
                  ·
                    refine ⟨863032438884115970432875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4602839674048618508975333 863032438884115970432875)
                    ·
                      rfl

theorem cell23_5042249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 4].length) (baseStart_5042249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042249 prefixEnd_5042249 := by exact prefixLift 5042249
  have htrace : WordTrace (prefixWord ++ tailWord_5042249) baseStart_5042249 baseEnd_5042249 := by
    simpa [prefixWord, tailWord_5042249, baseEnd_5042249] using wordTrace_append hprefix tailTrace_5042249
  have hstable : (prefixWord ++ tailWord_5042249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042249).length < 2 ^ (prefixWord ++ tailWord_5042249).sum := by decide
  have hdescent : baseEnd_5042249 < baseStart_5042249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042265 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_5042265 : Nat := 118140960795 + 5042265 * 2 ^ 59
def prefixEnd_5042265 : Nat := 4983230072969 + 3 ^ 40 * 5042265 * 2
def baseEnd_5042265 : Nat := 2589105532342819848698551

theorem tailTrace_5042265 : CollatzResearch.WordTrace tailWord_5042265 prefixEnd_5042265 2589105532342819848698551 := by
  unfold tailWord_5042265
  simp only [CollatzResearch.WordTrace]
  refine ⟨183906513077742530147432249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122604342051828353431621499 183906513077742530147432249)
  ·
    refine ⟨137929884808306897610574187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183906513077742530147432249 137929884808306897610574187)
    ·
      refine ⟨206894827212460346415861281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137929884808306897610574187 206894827212460346415861281)
      ·
        refine ⟨155171120409345259811895961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206894827212460346415861281 155171120409345259811895961)
        ·
          refine ⟨116378340307008944858921971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155171120409345259811895961 116378340307008944858921971)
          ·
            refine ⟨174567510460513417288382957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116378340307008944858921971 174567510460513417288382957)
            ·
              refine ⟨65462816422692531483143609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174567510460513417288382957 65462816422692531483143609)
              ·
                refine ⟨49097112317019398612357707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65462816422692531483143609 49097112317019398612357707)
                ·
                  refine ⟨73645668475529097918536561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49097112317019398612357707 73645668475529097918536561)
                  ·
                    refine ⟨55234251356646823438902421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73645668475529097918536561 55234251356646823438902421)
                    ·
                      refine ⟨2589105532342819848698551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55234251356646823438902421 2589105532342819848698551)
                      ·
                        rfl

theorem cell23_5042265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_5042265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042265 prefixEnd_5042265 := by exact prefixLift 5042265
  have htrace : WordTrace (prefixWord ++ tailWord_5042265) baseStart_5042265 baseEnd_5042265 := by
    simpa [prefixWord, tailWord_5042265, baseEnd_5042265] using wordTrace_append hprefix tailTrace_5042265
  have hstable : (prefixWord ++ tailWord_5042265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042265).length < 2 ^ (prefixWord ++ tailWord_5042265).sum := by decide
  have hdescent : baseEnd_5042265 < baseStart_5042265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042343 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 1, 5]
def baseStart_5042343 : Nat := 118140960795 + 5042343 * 2 ^ 59
def prefixEnd_5042343 : Nat := 4983230072969 + 3 ^ 40 * 5042343 * 2
def baseEnd_5042343 : Nat := 863048527944623514507731

theorem tailTrace_5042343 : CollatzResearch.WordTrace tailWord_5042343 prefixEnd_5042343 863048527944623514507731 := by
  unfold tailWord_5042343
  simp only [CollatzResearch.WordTrace]
  refine ⟨183909357971459949468771683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122606238647639966312514455 183909357971459949468771683)
  ·
    refine ⟨275864036957189924203157525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183909357971459949468771683 275864036957189924203157525)
    ·
      refine ⟨12931126732368277697023009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 275864036957189924203157525 12931126732368277697023009)
      ·
        refine ⟨9698345049276208272767257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12931126732368277697023009 9698345049276208272767257)
        ·
          refine ⟨7273758786957156204575443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9698345049276208272767257 7273758786957156204575443)
          ·
            refine ⟨10910638180435734306863165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273758786957156204575443 10910638180435734306863165)
            ·
              refine ⟨4091489317663400365073687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10910638180435734306863165 4091489317663400365073687)
              ·
                refine ⟨6137233976495100547610531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091489317663400365073687 6137233976495100547610531)
                ·
                  refine ⟨9205850964742650821415797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137233976495100547610531 9205850964742650821415797)
                  ·
                    refine ⟨863048527944623514507731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9205850964742650821415797 863048527944623514507731)
                    ·
                      rfl

theorem cell23_5042343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_5042343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042343 prefixEnd_5042343 := by exact prefixLift 5042343
  have htrace : WordTrace (prefixWord ++ tailWord_5042343) baseStart_5042343 baseEnd_5042343 := by
    simpa [prefixWord, tailWord_5042343, baseEnd_5042343] using wordTrace_append hprefix tailTrace_5042343
  have hstable : (prefixWord ++ tailWord_5042343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042343).length < 2 ^ (prefixWord ++ tailWord_5042343).sum := by decide
  have hdescent : baseEnd_5042343 < baseStart_5042343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042363 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 1, 2, 2]
def baseStart_5042363 : Nat := 118140960795 + 5042363 * 2 ^ 59
def prefixEnd_5042363 : Nat := 4983230072969 + 3 ^ 40 * 5042363 * 2
def baseEnd_5042363 : Nat := 2589155853446960465273101

theorem tailTrace_5042363 : CollatzResearch.WordTrace tailWord_5042363 prefixEnd_5042363 2589155853446960465273101 := by
  unfold tailWord_5042363
  simp only [CollatzResearch.WordTrace]
  refine ⟨183910087431387492884499743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122606724954258328589666495 183910087431387492884499743)
  ·
    refine ⟨275865131147081239326749615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183910087431387492884499743 275865131147081239326749615)
    ·
      refine ⟨413797696720621858990124423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275865131147081239326749615 413797696720621858990124423)
      ·
        refine ⟨620696545080932788485186635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413797696720621858990124423 620696545080932788485186635)
        ·
          refine ⟨931044817621399182727779953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620696545080932788485186635 931044817621399182727779953)
          ·
            refine ⟨698283613216049387045834965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931044817621399182727779953 698283613216049387045834965)
            ·
              refine ⟨16366022184751157508886757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 698283613216049387045834965 16366022184751157508886757)
              ·
                refine ⟨3068629159640842032916267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16366022184751157508886757 3068629159640842032916267)
                ·
                  refine ⟨4602943739461263049374401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068629159640842032916267 4602943739461263049374401)
                  ·
                    refine ⟨3452207804595947287030801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602943739461263049374401 3452207804595947287030801)
                    ·
                      refine ⟨2589155853446960465273101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452207804595947287030801 2589155853446960465273101)
                      ·
                        rfl

theorem cell23_5042363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 2, 2].length) (baseStart_5042363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042363 prefixEnd_5042363 := by exact prefixLift 5042363
  have htrace : WordTrace (prefixWord ++ tailWord_5042363) baseStart_5042363 baseEnd_5042363 := by
    simpa [prefixWord, tailWord_5042363, baseEnd_5042363] using wordTrace_append hprefix tailTrace_5042363
  have hstable : (prefixWord ++ tailWord_5042363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042363).length < 2 ^ (prefixWord ++ tailWord_5042363).sum := by decide
  have hdescent : baseEnd_5042363 < baseStart_5042363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042379 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3]
def baseStart_5042379 : Nat := 118140960795 + 5042379 * 2 ^ 59
def prefixEnd_5042379 : Nat := 4983230072969 + 3 ^ 40 * 5042379 * 2
def baseEnd_5042379 : Nat := 2589164069137432402673027

theorem tailTrace_5042379 : CollatzResearch.WordTrace tailWord_5042379 prefixEnd_5042379 2589164069137432402673027 := by
  unfold tailWord_5042379
  simp only [CollatzResearch.WordTrace]
  refine ⟨183910670999329527617082191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122607113999553018411388127 183910670999329527617082191)
  ·
    refine ⟨275866006498994291425623287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183910670999329527617082191 275866006498994291425623287)
    ·
      refine ⟨413799009748491437138434931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275866006498994291425623287 413799009748491437138434931)
      ·
        refine ⟨620698514622737155707652397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413799009748491437138434931 620698514622737155707652397)
        ·
          refine ⟨232761942983526433390369649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 620698514622737155707652397 232761942983526433390369649)
          ·
            refine ⟨174571457237644825042777237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232761942983526433390369649 174571457237644825042777237)
            ·
              refine ⟨8183037058014601173880183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174571457237644825042777237 8183037058014601173880183)
              ·
                refine ⟨12274555587021901760820275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8183037058014601173880183 12274555587021901760820275)
                ·
                  refine ⟨18411833380532852641230413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12274555587021901760820275 18411833380532852641230413)
                  ·
                    refine ⟨6904437517699819740461405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18411833380532852641230413 6904437517699819740461405)
                    ·
                      refine ⟨2589164069137432402673027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904437517699819740461405 2589164069137432402673027)
                      ·
                        rfl

theorem cell23_5042379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3].length) (baseStart_5042379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042379 prefixEnd_5042379 := by exact prefixLift 5042379
  have htrace : WordTrace (prefixWord ++ tailWord_5042379) baseStart_5042379 baseEnd_5042379 := by
    simpa [prefixWord, tailWord_5042379, baseEnd_5042379] using wordTrace_append hprefix tailTrace_5042379
  have hstable : (prefixWord ++ tailWord_5042379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042379).length < 2 ^ (prefixWord ++ tailWord_5042379).sum := by decide
  have hdescent : baseEnd_5042379 < baseStart_5042379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042380 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5042380 : Nat := 118140960795 + 5042380 * 2 ^ 59
def prefixEnd_5042380 : Nat := 4983230072969 + 3 ^ 40 * 5042380 * 2
def baseEnd_5042380 : Nat := 2589164582618086898760523

theorem tailTrace_5042380 : CollatzResearch.WordTrace tailWord_5042380 prefixEnd_5042380 2589164582618086898760523 := by
  unfold tailWord_5042380
  simp only [CollatzResearch.WordTrace]
  refine ⟨91955353736162952393934297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122607138314883936525245729 91955353736162952393934297)
  ·
    refine ⟨68966515302122214295450723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91955353736162952393934297 68966515302122214295450723)
    ·
      refine ⟨103449772953183321443176085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68966515302122214295450723 103449772953183321443176085)
      ·
        refine ⟨4849208107180468192648879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103449772953183321443176085 4849208107180468192648879)
        ·
          refine ⟨7273812160770702288973319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849208107180468192648879 7273812160770702288973319)
          ·
            refine ⟨10910718241156053433459979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273812160770702288973319 10910718241156053433459979)
            ·
              refine ⟨16366077361734080150189969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10910718241156053433459979 16366077361734080150189969)
              ·
                refine ⟨12274558021300560112642477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16366077361734080150189969 12274558021300560112642477)
                ·
                  refine ⟨4602959257987710042240929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12274558021300560112642477 4602959257987710042240929)
                  ·
                    refine ⟨3452219443490782531680697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602959257987710042240929 3452219443490782531680697)
                    ·
                      refine ⟨2589164582618086898760523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452219443490782531680697 2589164582618086898760523)
                      ·
                        rfl

theorem cell23_5042380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5042380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042380 prefixEnd_5042380 := by exact prefixLift 5042380
  have htrace : WordTrace (prefixWord ++ tailWord_5042380) baseStart_5042380 baseEnd_5042380 := by
    simpa [prefixWord, tailWord_5042380, baseEnd_5042380] using wordTrace_append hprefix tailTrace_5042380
  have hstable : (prefixWord ++ tailWord_5042380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042380).length < 2 ^ (prefixWord ++ tailWord_5042380).sum := by decide
  have hdescent : baseEnd_5042380 < baseStart_5042380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042397 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5042397 : Nat := 118140960795 + 5042397 * 2 ^ 59
def prefixEnd_5042397 : Nat := 4983230072969 + 3 ^ 40 * 5042397 * 2
def baseEnd_5042397 : Nat := 2589173311789213332247945

theorem tailTrace_5042397 : CollatzResearch.WordTrace tailWord_5042397 prefixEnd_5042397 2589173311789213332247945 := by
  unfold tailWord_5042397
  simp only [CollatzResearch.WordTrace]
  refine ⟨183911327513264316691237445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122607551675509544460824963 183911327513264316691237445)
  ·
    refine ⟨34483373908737059379607021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183911327513264316691237445 34483373908737059379607021)
    ·
      refine ⟨12931265215776397267352633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34483373908737059379607021 12931265215776397267352633)
      ·
        refine ⟨9698448911832297950514475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12931265215776397267352633 9698448911832297950514475)
        ·
          refine ⟨14547673367748446925771713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9698448911832297950514475 14547673367748446925771713)
          ·
            refine ⟨10910755025811335194328785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14547673367748446925771713 10910755025811335194328785)
            ·
              refine ⟨8183066269358501395746589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10910755025811335194328785 8183066269358501395746589)
              ·
                refine ⟨3068649851009438023404971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8183066269358501395746589 3068649851009438023404971)
                ·
                  refine ⟨4602974776514157035107457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068649851009438023404971 4602974776514157035107457)
                  ·
                    refine ⟨3452231082385617776330593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602974776514157035107457 3452231082385617776330593)
                    ·
                      refine ⟨2589173311789213332247945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452231082385617776330593 2589173311789213332247945)
                      ·
                        rfl

theorem cell23_5042397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5042397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042397 prefixEnd_5042397 := by exact prefixLift 5042397
  have htrace : WordTrace (prefixWord ++ tailWord_5042397) baseStart_5042397 baseEnd_5042397 := by
    simpa [prefixWord, tailWord_5042397, baseEnd_5042397] using wordTrace_append hprefix tailTrace_5042397
  have hstable : (prefixWord ++ tailWord_5042397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042397).length < 2 ^ (prefixWord ++ tailWord_5042397).sum := by decide
  have hdescent : baseEnd_5042397 < baseStart_5042397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042412 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_5042412 : Nat := 118140960795 + 5042412 * 2 ^ 59
def prefixEnd_5042412 : Nat := 4983230072969 + 3 ^ 40 * 5042412 * 2
def baseEnd_5042412 : Nat := 863060337999676924520125

theorem tailTrace_5042412 : CollatzResearch.WordTrace tailWord_5042412 prefixEnd_5042412 863060337999676924520125 := by
  unfold tailWord_5042412
  simp only [CollatzResearch.WordTrace]
  refine ⟨91955937304104987126516745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122607916405473316168688993 91955937304104987126516745)
  ·
    refine ⟨68966952978078740344887559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91955937304104987126516745 68966952978078740344887559)
    ·
      refine ⟨103450429467118110517331339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68966952978078740344887559 103450429467118110517331339)
      ·
        refine ⟨155175644200677165775997009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103450429467118110517331339 155175644200677165775997009)
        ·
          refine ⟨116381733150507874331997757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155175644200677165775997009 116381733150507874331997757)
          ·
            refine ⟨43643149931440452874499159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116381733150507874331997757 43643149931440452874499159)
            ·
              refine ⟨65464724897160679311748739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43643149931440452874499159 65464724897160679311748739)
              ·
                refine ⟨98197087345741018967623109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65464724897160679311748739 98197087345741018967623109)
                ·
                  refine ⟨18411953877326441056429333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98197087345741018967623109 18411953877326441056429333)
                  ·
                    refine ⟨863060337999676924520125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18411953877326441056429333 863060337999676924520125)
                    ·
                      rfl

theorem cell23_5042412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_5042412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042412 prefixEnd_5042412 := by exact prefixLift 5042412
  have htrace : WordTrace (prefixWord ++ tailWord_5042412) baseStart_5042412 baseEnd_5042412 := by
    simpa [prefixWord, tailWord_5042412, baseEnd_5042412] using wordTrace_append hprefix tailTrace_5042412
  have hstable : (prefixWord ++ tailWord_5042412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042412).length < 2 ^ (prefixWord ++ tailWord_5042412).sum := by decide
  have hdescent : baseEnd_5042412 < baseStart_5042412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042413 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5042413 : Nat := 118140960795 + 5042413 * 2 ^ 59
def prefixEnd_5042413 : Nat := 4983230072969 + 3 ^ 40 * 5042413 * 2
def baseEnd_5042413 : Nat := 2589181527479685269647871

theorem tailTrace_5042413 : CollatzResearch.WordTrace tailWord_5042413 prefixEnd_5042413 2589181527479685269647871 := by
  unfold tailWord_5042413
  simp only [CollatzResearch.WordTrace]
  refine ⟨183911911081206351423819893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122607940720804234282546595 183911911081206351423819893)
  ·
    refine ⟨17241741663863095445983115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183911911081206351423819893 17241741663863095445983115)
    ·
      refine ⟨25862612495794643168974673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17241741663863095445983115 25862612495794643168974673)
      ·
        refine ⟨19396959371845982376731005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25862612495794643168974673 19396959371845982376731005)
        ·
          refine ⟨7273859764442243391274127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19396959371845982376731005 7273859764442243391274127)
          ·
            refine ⟨10910789646663365086911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273859764442243391274127 10910789646663365086911191)
            ·
              refine ⟨16366184469995047630366787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10910789646663365086911191 16366184469995047630366787)
              ·
                refine ⟨24549276704992571445550181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16366184469995047630366787 24549276704992571445550181)
                ·
                  refine ⟨4602989382186107146040659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24549276704992571445550181 4602989382186107146040659)
                  ·
                    refine ⟨6904484073279160719060989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602989382186107146040659 6904484073279160719060989)
                    ·
                      refine ⟨2589181527479685269647871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904484073279160719060989 2589181527479685269647871)
                      ·
                        rfl

theorem cell23_5042413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5042413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042413 prefixEnd_5042413 := by exact prefixLift 5042413
  have htrace : WordTrace (prefixWord ++ tailWord_5042413) baseStart_5042413 baseEnd_5042413 := by
    simpa [prefixWord, tailWord_5042413, baseEnd_5042413] using wordTrace_append hprefix tailTrace_5042413
  have hstable : (prefixWord ++ tailWord_5042413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042413).length < 2 ^ (prefixWord ++ tailWord_5042413).sum := by decide
  have hdescent : baseEnd_5042413 < baseStart_5042413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042430 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_5042430 : Nat := 118140960795 + 5042430 * 2 ^ 59
def prefixEnd_5042430 : Nat := 4983230072969 + 3 ^ 40 * 5042430 * 2
def baseEnd_5042430 : Nat := 2589190256650811703135293

theorem tailTrace_5042430 : CollatzResearch.WordTrace tailWord_5042430 prefixEnd_5042430 2589190256650811703135293 := by
  unfold tailWord_5042430
  simp only [CollatzResearch.WordTrace]
  refine ⟨22989066390268095415898593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122608354081429842218125829 22989066390268095415898593)
  ·
    refine ⟨17241799792701071561923945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22989066390268095415898593 17241799792701071561923945)
    ·
      refine ⟨12931349844525803671442959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17241799792701071561923945 12931349844525803671442959)
      ·
        refine ⟨19397024766788705507164439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931349844525803671442959 19397024766788705507164439)
        ·
          refine ⟨29095537150183058260746659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19397024766788705507164439 29095537150183058260746659)
          ·
            refine ⟨43643305725274587391119989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29095537150183058260746659 43643305725274587391119989)
            ·
              refine ⟨4091559911744492567917499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43643305725274587391119989 4091559911744492567917499)
              ·
                refine ⟨6137339867616738851876249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091559911744492567917499 6137339867616738851876249)
                ·
                  refine ⟨4603004900712554138907187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137339867616738851876249 4603004900712554138907187)
                  ·
                    refine ⟨6904507351068831208360781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4603004900712554138907187 6904507351068831208360781)
                    ·
                      refine ⟨2589190256650811703135293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904507351068831208360781 2589190256650811703135293)
                      ·
                        rfl

theorem cell23_5042430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_5042430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042430 prefixEnd_5042430 := by exact prefixLift 5042430
  have htrace : WordTrace (prefixWord ++ tailWord_5042430) baseStart_5042430 baseEnd_5042430 := by
    simpa [prefixWord, tailWord_5042430, baseEnd_5042430] using wordTrace_append hprefix tailTrace_5042430
  have hstable : (prefixWord ++ tailWord_5042430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042430).length < 2 ^ (prefixWord ++ tailWord_5042430).sum := by decide
  have hdescent : baseEnd_5042430 < baseStart_5042430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042529 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_5042529 : Nat := 118140960795 + 5042529 * 2 ^ 59
def prefixEnd_5042529 : Nat := 4983230072969 + 3 ^ 40 * 5042529 * 2
def baseEnd_5042529 : Nat := 2589241091235606815797337

theorem tailTrace_5042529 : CollatzResearch.WordTrace tailWord_5042529 prefixEnd_5042529 2589241091235606815797337 := by
  unfold tailWord_5042529
  simp only [CollatzResearch.WordTrace]
  refine ⟨183916141948786103235042641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122610761299190735490028427 183916141948786103235042641)
  ·
    refine ⟨137937106461589577426281981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183916141948786103235042641 137937106461589577426281981)
    ·
      refine ⟨51726414923096091534855743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137937106461589577426281981 51726414923096091534855743)
      ·
        refine ⟨77589622384644137302283615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51726414923096091534855743 77589622384644137302283615)
        ·
          refine ⟨116384433576966205953425423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77589622384644137302283615 116384433576966205953425423)
          ·
            refine ⟨174576650365449308930138135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116384433576966205953425423 174576650365449308930138135)
            ·
              refine ⟨261864975548173963395207203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174576650365449308930138135 261864975548173963395207203)
              ·
                refine ⟨392797463322260945092810805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261864975548173963395207203 392797463322260945092810805)
                ·
                  refine ⟨36824762186461963602451013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392797463322260945092810805 36824762186461963602451013)
                  ·
                    refine ⟨6904642909961618175459565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36824762186461963602451013 6904642909961618175459565)
                    ·
                      refine ⟨2589241091235606815797337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904642909961618175459565 2589241091235606815797337)
                      ·
                        rfl

theorem cell23_5042529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_5042529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042529 prefixEnd_5042529 := by exact prefixLift 5042529
  have htrace : WordTrace (prefixWord ++ tailWord_5042529) baseStart_5042529 baseEnd_5042529 := by
    simpa [prefixWord, tailWord_5042529, baseEnd_5042529] using wordTrace_append hprefix tailTrace_5042529
  have hstable : (prefixWord ++ tailWord_5042529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042529).length < 2 ^ (prefixWord ++ tailWord_5042529).sum := by decide
  have hdescent : baseEnd_5042529 < baseStart_5042529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042559 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_5042559 : Nat := 118140960795 + 5042559 * 2 ^ 59
def prefixEnd_5042559 : Nat := 4983230072969 + 3 ^ 40 * 5042559 * 2
def baseEnd_5042559 : Nat := 2589256495655241698422199

theorem tailTrace_5042559 : CollatzResearch.WordTrace tailWord_5042559 prefixEnd_5042559 2589256495655241698422199 := by
  unfold tailWord_5042559
  simp only [CollatzResearch.WordTrace]
  refine ⟨183917236138677418358634731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122611490759118278905756487 183917236138677418358634731)
  ·
    refine ⟨275875854208016127537952097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183917236138677418358634731 275875854208016127537952097)
    ·
      refine ⟨206906890656012095653464073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275875854208016127537952097 206906890656012095653464073)
      ·
        refine ⟨155180167992009071740098055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206906890656012095653464073 155180167992009071740098055)
        ·
          refine ⟨232770251988013607610147083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155180167992009071740098055 232770251988013607610147083)
          ·
            refine ⟨349155377982020411415220625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232770251988013607610147083 349155377982020411415220625)
            ·
              refine ⟨261866533486515308561415469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349155377982020411415220625 261866533486515308561415469)
              ·
                refine ⟨98199950057443240710530801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261866533486515308561415469 98199950057443240710530801)
                ·
                  refine ⟨73649962543082430532898101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98199950057443240710530801 73649962543082430532898101)
                  ·
                    refine ⟨6904683988413977862459197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73649962543082430532898101 6904683988413977862459197)
                    ·
                      refine ⟨2589256495655241698422199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904683988413977862459197 2589256495655241698422199)
                      ·
                        rfl

theorem cell23_5042559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_5042559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042559 prefixEnd_5042559 := by exact prefixLift 5042559
  have htrace : WordTrace (prefixWord ++ tailWord_5042559) baseStart_5042559 baseEnd_5042559 := by
    simpa [prefixWord, tailWord_5042559, baseEnd_5042559] using wordTrace_append hprefix tailTrace_5042559
  have hstable : (prefixWord ++ tailWord_5042559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042559).length < 2 ^ (prefixWord ++ tailWord_5042559).sum := by decide
  have hdescent : baseEnd_5042559 < baseStart_5042559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042600 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 6]
def baseStart_5042600 : Nat := 118140960795 + 5042600 * 2 ^ 59
def prefixEnd_5042600 : Nat := 4983230072969 + 3 ^ 40 * 5042600 * 2
def baseEnd_5042600 : Nat := 287697505373564004223279

theorem tailTrace_5042600 : CollatzResearch.WordTrace tailWord_5042600 prefixEnd_5042600 287697505373564004223279 := by
  unfold tailWord_5042600
  simp only [CollatzResearch.WordTrace]
  refine ⟨91959365765764441180438627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122612487687685921573918169 91959365765764441180438627)
  ·
    refine ⟨137939048648646661770657941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91959365765764441180438627 137939048648646661770657941)
    ·
      refine ⟨6465892905405312270499591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137939048648646661770657941 6465892905405312270499591)
      ·
        refine ⟨9698839358107968405749387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465892905405312270499591 9698839358107968405749387)
        ·
          refine ⟨14548259037161952608624081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9698839358107968405749387 14548259037161952608624081)
          ·
            refine ⟨10911194277871464456468061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14548259037161952608624081 10911194277871464456468061)
            ·
              refine ⟨4091697854201799171175523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10911194277871464456468061 4091697854201799171175523)
              ·
                refine ⟨6137546781302698756763285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091697854201799171175523 6137546781302698756763285)
                ·
                  refine ⟨287697505373564004223279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6137546781302698756763285 287697505373564004223279)
                  ·
                    rfl

theorem cell23_5042600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 6].length) (baseStart_5042600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042600 prefixEnd_5042600 := by exact prefixLift 5042600
  have htrace : WordTrace (prefixWord ++ tailWord_5042600) baseStart_5042600 baseEnd_5042600 := by
    simpa [prefixWord, tailWord_5042600, baseEnd_5042600] using wordTrace_append hprefix tailTrace_5042600
  have hstable : (prefixWord ++ tailWord_5042600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042600).length < 2 ^ (prefixWord ++ tailWord_5042600).sum := by decide
  have hdescent : baseEnd_5042600 < baseStart_5042600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042616 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_5042616 : Nat := 118140960795 + 5042616 * 2 ^ 59
def prefixEnd_5042616 : Nat := 4983230072969 + 3 ^ 40 * 5042616 * 2
def baseEnd_5042616 : Nat := 2589285764052547975409437

theorem tailTrace_5042616 : CollatzResearch.WordTrace tailWord_5042616 prefixEnd_5042616 2589285764052547975409437 := by
  unfold tailWord_5042616
  simp only [CollatzResearch.WordTrace]
  refine ⟨91959657549735458546729851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122612876732980611395639801 91959657549735458546729851)
  ·
    refine ⟨137939486324603187820094777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91959657549735458546729851 137939486324603187820094777)
    ·
      refine ⟨103454614743452390865071083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137939486324603187820094777 103454614743452390865071083)
      ·
        refine ⟨155181922115178586297606625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103454614743452390865071083 155181922115178586297606625)
        ·
          refine ⟨116386441586383939723204969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155181922115178586297606625 116386441586383939723204969)
          ·
            refine ⟨87289831189787954792403727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116386441586383939723204969 87289831189787954792403727)
            ·
              refine ⟨130934746784681932188605591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87289831189787954792403727 130934746784681932188605591)
              ·
                refine ⟨196402120177022898282908387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130934746784681932188605591 196402120177022898282908387)
                ·
                  refine ⟨294603180265534347424362581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196402120177022898282908387 294603180265534347424362581)
                  ·
                    refine ⟨3452381018736730633879249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 294603180265534347424362581 3452381018736730633879249)
                    ·
                      refine ⟨2589285764052547975409437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452381018736730633879249 2589285764052547975409437)
                      ·
                        rfl

theorem cell23_5042616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_5042616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042616 prefixEnd_5042616 := by exact prefixLift 5042616
  have htrace : WordTrace (prefixWord ++ tailWord_5042616) baseStart_5042616 baseEnd_5042616 := by
    simpa [prefixWord, tailWord_5042616, baseEnd_5042616] using wordTrace_append hprefix tailTrace_5042616
  have hstable : (prefixWord ++ tailWord_5042616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042616).length < 2 ^ (prefixWord ++ tailWord_5042616).sum := by decide
  have hdescent : baseEnd_5042616 < baseStart_5042616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042633 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 5, 2, 2]
def baseStart_5042633 : Nat := 118140960795 + 5042633 * 2 ^ 59
def prefixEnd_5042633 : Nat := 4983230072969 + 3 ^ 40 * 5042633 * 2
def baseEnd_5042633 : Nat := 2589294493223674408896859

theorem tailTrace_5042633 : CollatzResearch.WordTrace tailWord_5042633 prefixEnd_5042633 2589294493223674408896859 := by
  unfold tailWord_5042633
  simp only [CollatzResearch.WordTrace]
  refine ⟨183919935140409328996828553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122613290093606219331219035 183919935140409328996828553)
  ·
    refine ⟨137939951355306996747621415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183919935140409328996828553 137939951355306996747621415)
    ·
      refine ⟨206909927032960495121432123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137939951355306996747621415 206909927032960495121432123)
      ·
        refine ⟨310364890549440742682148185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206909927032960495121432123 310364890549440742682148185)
        ·
          refine ⟨232773667912080557011611139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310364890549440742682148185 232773667912080557011611139)
          ·
            refine ⟨349160501868120835517416709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232773667912080557011611139 349160501868120835517416709)
            ·
              refine ⟨65467594100272656659515633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 349160501868120835517416709 65467594100272656659515633)
              ·
                refine ⟨49100695575204492494636725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65467594100272656659515633 49100695575204492494636725)
                ·
                  refine ⟨4603190210175421171372193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49100695575204492494636725 4603190210175421171372193)
                  ·
                    refine ⟨3452392657631565878529145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603190210175421171372193 3452392657631565878529145)
                    ·
                      refine ⟨2589294493223674408896859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452392657631565878529145 2589294493223674408896859)
                      ·
                        rfl

theorem cell23_5042633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2, 2].length) (baseStart_5042633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042633 prefixEnd_5042633 := by exact prefixLift 5042633
  have htrace : WordTrace (prefixWord ++ tailWord_5042633) baseStart_5042633 baseEnd_5042633 := by
    simpa [prefixWord, tailWord_5042633, baseEnd_5042633] using wordTrace_append hprefix tailTrace_5042633
  have hstable : (prefixWord ++ tailWord_5042633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042633).length < 2 ^ (prefixWord ++ tailWord_5042633).sum := by decide
  have hdescent : baseEnd_5042633 < baseStart_5042633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042644 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5042644 : Nat := 118140960795 + 5042644 * 2 ^ 59
def prefixEnd_5042644 : Nat := 4983230072969 + 3 ^ 40 * 5042644 * 2
def baseEnd_5042644 : Nat := 2589300141510873865859309

theorem tailTrace_5042644 : CollatzResearch.WordTrace tailWord_5042644 prefixEnd_5042644 2589300141510873865859309 := by
  unfold tailWord_5042644
  simp only [CollatzResearch.WordTrace]
  refine ⟨91960168171684738937739493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122613557562246318583652657 91960168171684738937739493)
  ·
    refine ⟨17242531532190888550826155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91960168171684738937739493 17242531532190888550826155)
    ·
      refine ⟨25863797298286332826239233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17242531532190888550826155 25863797298286332826239233)
      ·
        refine ⟨19397847973714749619679425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25863797298286332826239233 19397847973714749619679425)
        ·
          refine ⟨14548385980286062214759569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19397847973714749619679425 14548385980286062214759569)
          ·
            refine ⟨10911289485214546661069677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14548385980286062214759569 10911289485214546661069677)
            ·
              refine ⟨4091733556955454997901129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10911289485214546661069677 4091733556955454997901129)
              ·
                refine ⟨3068800167716591248425847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4091733556955454997901129 3068800167716591248425847)
                ·
                  refine ⟨4603200251574886872638771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068800167716591248425847 4603200251574886872638771)
                  ·
                    refine ⟨6904800377362330308958157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4603200251574886872638771 6904800377362330308958157)
                    ·
                      refine ⟨2589300141510873865859309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904800377362330308958157 2589300141510873865859309)
                      ·
                        rfl

theorem cell23_5042644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5042644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042644 prefixEnd_5042644 := by exact prefixLift 5042644
  have htrace : WordTrace (prefixWord ++ tailWord_5042644) baseStart_5042644 baseEnd_5042644 := by
    simpa [prefixWord, tailWord_5042644, baseEnd_5042644] using wordTrace_append hprefix tailTrace_5042644
  have hstable : (prefixWord ++ tailWord_5042644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042644).length < 2 ^ (prefixWord ++ tailWord_5042644).sum := by decide
  have hdescent : baseEnd_5042644 < baseStart_5042644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042653 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_5042653 : Nat := 118140960795 + 5042653 * 2 ^ 59
def prefixEnd_5042653 : Nat := 4983230072969 + 3 ^ 40 * 5042653 * 2
def baseEnd_5042653 : Nat := 2589304762836764330646767

theorem tailTrace_5042653 : CollatzResearch.WordTrace tailWord_5042653 prefixEnd_5042653 2589304762836764330646767 := by
  unfold tailWord_5042653
  simp only [CollatzResearch.WordTrace]
  refine ⟨183920664600336872412556613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122613776400224581608371075 183920664600336872412556613)
  ·
    refine ⟨34485124612563163577354365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183920664600336872412556613 34485124612563163577354365)
    ·
      refine ⟨12931921729711186341507887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34485124612563163577354365 12931921729711186341507887)
      ·
        refine ⟨19397882594566779512261831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931921729711186341507887 19397882594566779512261831)
        ·
          refine ⟨29096823891850169268392747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19397882594566779512261831 29096823891850169268392747)
          ·
            refine ⟨43645235837775253902589121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29096823891850169268392747 43645235837775253902589121)
            ·
              refine ⟨32733926878331440426941841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43645235837775253902589121 32733926878331440426941841)
              ·
                refine ⟨24550445158748580320206381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32733926878331440426941841 24550445158748580320206381)
                ·
                  refine ⟨9206416934530717620077393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24550445158748580320206381 9206416934530717620077393)
                  ·
                    refine ⟨6904812700898038215058045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9206416934530717620077393 6904812700898038215058045)
                    ·
                      refine ⟨2589304762836764330646767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904812700898038215058045 2589304762836764330646767)
                      ·
                        rfl

theorem cell23_5042653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_5042653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042653 prefixEnd_5042653 := by exact prefixLift 5042653
  have htrace : WordTrace (prefixWord ++ tailWord_5042653) baseStart_5042653 baseEnd_5042653 := by
    simpa [prefixWord, tailWord_5042653, baseEnd_5042653] using wordTrace_append hprefix tailTrace_5042653
  have hstable : (prefixWord ++ tailWord_5042653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042653).length < 2 ^ (prefixWord ++ tailWord_5042653).sum := by decide
  have hdescent : baseEnd_5042653 < baseStart_5042653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042670 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_5042670 : Nat := 118140960795 + 5042670 * 2 ^ 59
def prefixEnd_5042670 : Nat := 4983230072969 + 3 ^ 40 * 5042670 * 2
def baseEnd_5042670 : Nat := 2589313492007890764134189

theorem tailTrace_5042670 : CollatzResearch.WordTrace tailWord_5042670 prefixEnd_5042670 2589313492007890764134189 := by
  unfold tailWord_5042670
  simp only [CollatzResearch.WordTrace]
  refine ⟨22990160580159410539490683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122614189760850189543950309 22990160580159410539490683)
  ·
    refine ⟨34485240870239115809236025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22990160580159410539490683 34485240870239115809236025)
    ·
      refine ⟨25863930652679336856927019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34485240870239115809236025 25863930652679336856927019)
      ·
        refine ⟨38795895979019005285390529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25863930652679336856927019 38795895979019005285390529)
        ·
          refine ⟨29096921984264253964042897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38795895979019005285390529 29096921984264253964042897)
          ·
            refine ⟨21822691488198190473032173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29096921984264253964042897 21822691488198190473032173)
            ·
              refine ⟨8183509308074321427387065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21822691488198190473032173 8183509308074321427387065)
              ·
                refine ⟨6137631981055741070540299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8183509308074321427387065 6137631981055741070540299)
                ·
                  refine ⟨9206447971583611605810449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137631981055741070540299 9206447971583611605810449)
                  ·
                    refine ⟨6904835978687708704357837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9206447971583611605810449 6904835978687708704357837)
                    ·
                      refine ⟨2589313492007890764134189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904835978687708704357837 2589313492007890764134189)
                      ·
                        rfl

theorem cell23_5042670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_5042670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042670 prefixEnd_5042670 := by exact prefixLift 5042670
  have htrace : WordTrace (prefixWord ++ tailWord_5042670) baseStart_5042670 baseEnd_5042670 := by
    simpa [prefixWord, tailWord_5042670, baseEnd_5042670] using wordTrace_append hprefix tailTrace_5042670
  have hstable : (prefixWord ++ tailWord_5042670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042670).length < 2 ^ (prefixWord ++ tailWord_5042670).sum := by decide
  have hdescent : baseEnd_5042670 < baseStart_5042670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042679 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_5042679 : Nat := 118140960795 + 5042679 * 2 ^ 59
def prefixEnd_5042679 : Nat := 4983230072969 + 3 ^ 40 * 5042679 * 2
def baseEnd_5042679 : Nat := 2589318113333781228921647

theorem tailTrace_5042679 : CollatzResearch.WordTrace tailWord_5042679 prefixEnd_5042679 2589318113333781228921647 := by
  unfold tailWord_5042679
  simp only [CollatzResearch.WordTrace]
  refine ⟨183921612898242678853003091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122614408598828452568668727 183921612898242678853003091)
  ·
    refine ⟨275882419347364018279504637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183921612898242678853003091 275882419347364018279504637)
    ·
      refine ⟨103455907255261506854814239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275882419347364018279504637 103455907255261506854814239)
      ·
        refine ⟨155183860882892260282221359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103455907255261506854814239 155183860882892260282221359)
        ·
          refine ⟨232775791324338390423332039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155183860882892260282221359 232775791324338390423332039)
          ·
            refine ⟨349163686986507585634998059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232775791324338390423332039 349163686986507585634998059)
            ·
              refine ⟨523745530479761378452497089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349163686986507585634998059 523745530479761378452497089)
              ·
                refine ⟨392809147859821033839372817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523745530479761378452497089 392809147859821033839372817)
                ·
                  refine ⟨294606860894865775379529613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392809147859821033839372817 294606860894865775379529613)
                  ·
                    refine ⟨110477572835574665767323605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294606860894865775379529613 110477572835574665767323605)
                    ·
                      refine ⟨2589318113333781228921647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110477572835574665767323605 2589318113333781228921647)
                      ·
                        rfl

theorem cell23_5042679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_5042679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042679 prefixEnd_5042679 := by exact prefixLift 5042679
  have htrace : WordTrace (prefixWord ++ tailWord_5042679) baseStart_5042679 baseEnd_5042679 := by
    simpa [prefixWord, tailWord_5042679, baseEnd_5042679] using wordTrace_append hprefix tailTrace_5042679
  have hstable : (prefixWord ++ tailWord_5042679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042679).length < 2 ^ (prefixWord ++ tailWord_5042679).sum := by decide
  have hdescent : baseEnd_5042679 < baseStart_5042679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042694 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5042694 : Nat := 118140960795 + 5042694 * 2 ^ 59
def prefixEnd_5042694 : Nat := 4983230072969 + 3 ^ 40 * 5042694 * 2
def baseEnd_5042694 : Nat := 863108605181199556744693

theorem tailTrace_5042694 : CollatzResearch.WordTrace tailWord_5042694 prefixEnd_5042694 863108605181199556744693 := by
  unfold tailWord_5042694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747567499787135512962473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122614773328792224276532757 5747567499787135512962473)
  ·
    refine ⟨4310675624840351634721855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5747567499787135512962473 4310675624840351634721855)
    ·
      refine ⟨6466013437260527452082783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4310675624840351634721855 6466013437260527452082783)
      ·
        refine ⟨9699020155890791178124175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466013437260527452082783 9699020155890791178124175)
        ·
          refine ⟨14548530233836186767186263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699020155890791178124175 14548530233836186767186263)
          ·
            refine ⟨21822795350754280150779395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14548530233836186767186263 21822795350754280150779395)
            ·
              refine ⟨32734193026131420226169093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21822795350754280150779395 32734193026131420226169093)
              ·
                refine ⟨6137661192399641292406705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32734193026131420226169093 6137661192399641292406705)
                ·
                  refine ⟨4603245894299730969305029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137661192399641292406705 4603245894299730969305029)
                  ·
                    refine ⟨863108605181199556744693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603245894299730969305029 863108605181199556744693)
                    ·
                      rfl

theorem cell23_5042694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5042694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042694 prefixEnd_5042694 := by exact prefixLift 5042694
  have htrace : WordTrace (prefixWord ++ tailWord_5042694) baseStart_5042694 baseEnd_5042694 := by
    simpa [prefixWord, tailWord_5042694, baseEnd_5042694] using wordTrace_append hprefix tailTrace_5042694
  have hstable : (prefixWord ++ tailWord_5042694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042694).length < 2 ^ (prefixWord ++ tailWord_5042694).sum := by decide
  have hdescent : baseEnd_5042694 < baseStart_5042694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042700 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_5042700 : Nat := 118140960795 + 5042700 * 2 ^ 59
def prefixEnd_5042700 : Nat := 4983230072969 + 3 ^ 40 * 5042700 * 2
def baseEnd_5042700 : Nat := 2589328896427525646759051

theorem tailTrace_5042700 : CollatzResearch.WordTrace tailWord_5042700 prefixEnd_5042700 2589328896427525646759051 := by
  unfold tailWord_5042700
  simp only [CollatzResearch.WordTrace]
  refine ⟨91961189415583299719758777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122614919220777732959678369 91961189415583299719758777)
  ·
    refine ⟨68970892061687474789819083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91961189415583299719758777 68970892061687474789819083)
    ·
      refine ⟨103456338092531212184728625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68970892061687474789819083 103456338092531212184728625)
      ·
        refine ⟨77592253569398409138546469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103456338092531212184728625 77592253569398409138546469)
        ·
          refine ⟨14548547544262201713477463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77592253569398409138546469 14548547544262201713477463)
          ·
            refine ⟨21822821316393302570216195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14548547544262201713477463 21822821316393302570216195)
            ·
              refine ⟨32734231974589953855324293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21822821316393302570216195 32734231974589953855324293)
              ·
                refine ⟨6137668495235616347873305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32734231974589953855324293 6137668495235616347873305)
                ·
                  refine ⟨4603251371426712260904979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137668495235616347873305 4603251371426712260904979)
                  ·
                    refine ⟨6904877057140068391357469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4603251371426712260904979 6904877057140068391357469)
                    ·
                      refine ⟨2589328896427525646759051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904877057140068391357469 2589328896427525646759051)
                      ·
                        rfl

theorem cell23_5042700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_5042700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042700 prefixEnd_5042700 := by exact prefixLift 5042700
  have htrace : WordTrace (prefixWord ++ tailWord_5042700) baseStart_5042700 baseEnd_5042700 := by
    simpa [prefixWord, tailWord_5042700, baseEnd_5042700] using wordTrace_append hprefix tailTrace_5042700
  have hstable : (prefixWord ++ tailWord_5042700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042700).length < 2 ^ (prefixWord ++ tailWord_5042700).sum := by decide
  have hdescent : baseEnd_5042700 < baseStart_5042700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042716 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_5042716 : Nat := 118140960795 + 5042716 * 2 ^ 59
def prefixEnd_5042716 : Nat := 4983230072969 + 3 ^ 40 * 5042716 * 2
def baseEnd_5042716 : Nat := 863112370705999194719659

theorem tailTrace_5042716 : CollatzResearch.WordTrace tailWord_5042716 prefixEnd_5042716 863112370705999194719659 := by
  unfold tailWord_5042716
  simp only [CollatzResearch.WordTrace]
  refine ⟨91961481199554317086050001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122615308266072422781400001 91961481199554317086050001)
  ·
    refine ⟨68971110899665737814537501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91961481199554317086050001 68971110899665737814537501)
    ·
      refine ⟨25864166587374651680451563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68971110899665737814537501 25864166587374651680451563)
      ·
        refine ⟨38796249881061977520677345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25864166587374651680451563 38796249881061977520677345)
        ·
          refine ⟨29097187410796483140508009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38796249881061977520677345 29097187410796483140508009)
          ·
            refine ⟨21822890558097362355381007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29097187410796483140508009 21822890558097362355381007)
            ·
              refine ⟨32734335837146043533071511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21822890558097362355381007 32734335837146043533071511)
              ·
                refine ⟨49101503755719065299607267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32734335837146043533071511 49101503755719065299607267)
                ·
                  refine ⟨73652255633578597949410901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49101503755719065299607267 73652255633578597949410901)
                  ·
                    refine ⟨863112370705999194719659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73652255633578597949410901 863112370705999194719659)
                    ·
                      rfl

theorem cell23_5042716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_5042716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042716 prefixEnd_5042716 := by exact prefixLift 5042716
  have htrace : WordTrace (prefixWord ++ tailWord_5042716) baseStart_5042716 baseEnd_5042716 := by
    simpa [prefixWord, tailWord_5042716, baseEnd_5042716] using wordTrace_append hprefix tailTrace_5042716
  have hstable : (prefixWord ++ tailWord_5042716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042716).length < 2 ^ (prefixWord ++ tailWord_5042716).sum := by decide
  have hdescent : baseEnd_5042716 < baseStart_5042716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042753 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5042753 : Nat := 118140960795 + 5042753 * 2 ^ 59
def prefixEnd_5042753 : Nat := 4983230072969 + 3 ^ 40 * 5042753 * 2
def baseEnd_5042753 : Nat := 2589356110902213939396307

theorem tailTrace_5042753 : CollatzResearch.WordTrace tailWord_5042753 prefixEnd_5042753 2589356110902213939396307 := by
  unfold tailWord_5042753
  simp only [CollatzResearch.WordTrace]
  refine ⟨183924311899974589491196913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122616207933316392994131275 183924311899974589491196913)
  ·
    refine ⟨137943233924980942118397685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183924311899974589491196913 137943233924980942118397685)
    ·
      refine ⟨12932178180466963323599783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137943233924980942118397685 12932178180466963323599783)
      ·
        refine ⟨19398267270700444985399675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12932178180466963323599783 19398267270700444985399675)
        ·
          refine ⟨29097400906050667478099513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19398267270700444985399675 29097400906050667478099513)
          ·
            refine ⟨21823050679538000608574635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29097400906050667478099513 21823050679538000608574635)
            ·
              refine ⟨32734576019307000912861953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21823050679538000608574635 32734576019307000912861953)
              ·
                refine ⟨24550932014480250684646465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32734576019307000912861953 24550932014480250684646465)
                ·
                  refine ⟨18413199010860188013484849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24550932014480250684646465 18413199010860188013484849)
                  ·
                    refine ⟨13809899258145141010113637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18413199010860188013484849 13809899258145141010113637)
                    ·
                      refine ⟨2589356110902213939396307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13809899258145141010113637 2589356110902213939396307)
                      ·
                        rfl

theorem cell23_5042753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5042753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042753 prefixEnd_5042753 := by exact prefixLift 5042753
  have htrace : WordTrace (prefixWord ++ tailWord_5042753) baseStart_5042753 baseEnd_5042753 := by
    simpa [prefixWord, tailWord_5042753, baseEnd_5042753] using wordTrace_append hprefix tailTrace_5042753
  have hstable : (prefixWord ++ tailWord_5042753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042753).length < 2 ^ (prefixWord ++ tailWord_5042753).sum := by decide
  have hdescent : baseEnd_5042753 < baseStart_5042753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042757 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_5042757 : Nat := 118140960795 + 5042757 * 2 ^ 59
def prefixEnd_5042757 : Nat := 4983230072969 + 3 ^ 40 * 5042757 * 2
def baseEnd_5042757 : Nat := 2589358164824831923746289

theorem tailTrace_5042757 : CollatzResearch.WordTrace tailWord_5042757 prefixEnd_5042757 2589358164824831923746289 := by
  unfold tailWord_5042757
  simp only [CollatzResearch.WordTrace]
  refine ⟨183924457791960098174342525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122616305194640065449561683 183924457791960098174342525)
  ·
    refine ⟨68971671671985036815378447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183924457791960098174342525 68971671671985036815378447)
    ·
      refine ⟨103457507507977555223067671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68971671671985036815378447 103457507507977555223067671)
      ·
        refine ⟨155186261261966332834601507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103457507507977555223067671 155186261261966332834601507)
        ·
          refine ⟨232779391892949499251902261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155186261261966332834601507 232779391892949499251902261)
          ·
            refine ⟨21823067989964015554865837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232779391892949499251902261 21823067989964015554865837)
            ·
              refine ⟨8183650496236505833074689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21823067989964015554865837 8183650496236505833074689)
              ·
                refine ⟨6137737872177379374806017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8183650496236505833074689 6137737872177379374806017)
                ·
                  refine ⟨4603303404133034531104513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6137737872177379374806017 4603303404133034531104513)
                  ·
                    refine ⟨3452477553099775898328385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603303404133034531104513 3452477553099775898328385)
                    ·
                      refine ⟨2589358164824831923746289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452477553099775898328385 2589358164824831923746289)
                      ·
                        rfl

theorem cell23_5042757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_5042757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042757 prefixEnd_5042757 := by exact prefixLift 5042757
  have htrace : WordTrace (prefixWord ++ tailWord_5042757) baseStart_5042757 baseEnd_5042757 := by
    simpa [prefixWord, tailWord_5042757, baseEnd_5042757] using wordTrace_append hprefix tailTrace_5042757
  have hstable : (prefixWord ++ tailWord_5042757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042757).length < 2 ^ (prefixWord ++ tailWord_5042757).sum := by decide
  have hdescent : baseEnd_5042757 < baseStart_5042757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042763 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 5]
def baseStart_5042763 : Nat := 118140960795 + 5042763 * 2 ^ 59
def prefixEnd_5042763 : Nat := 4983230072969 + 3 ^ 40 * 5042763 * 2
def baseEnd_5042763 : Nat := 287706805078750988919029

theorem tailTrace_5042763 : CollatzResearch.WordTrace tailWord_5042763 prefixEnd_5042763 287706805078750988919029 := by
  unfold tailWord_5042763
  simp only [CollatzResearch.WordTrace]
  refine ⟨183924676629938361199060943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122616451086625574132707295 183924676629938361199060943)
  ·
    refine ⟨275887014944907541798591415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183924676629938361199060943 275887014944907541798591415)
    ·
      refine ⟨413830522417361312697887123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275887014944907541798591415 413830522417361312697887123)
      ·
        refine ⟨620745783626041969046830685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413830522417361312697887123 620745783626041969046830685)
        ·
          refine ⟨232779668859765738392561507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 620745783626041969046830685 232779668859765738392561507)
          ·
            refine ⟨349169503289648607588842261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232779668859765738392561507 349169503289648607588842261)
            ·
              refine ⟨16367320466702278480726981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 349169503289648607588842261 16367320466702278480726981)
              ·
                refine ⟨3068872587506677215136309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16367320466702278480726981 3068872587506677215136309)
                ·
                  refine ⟨287706805078750988919029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3068872587506677215136309 287706805078750988919029)
                  ·
                    rfl

theorem cell23_5042763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 5].length) (baseStart_5042763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042763 prefixEnd_5042763 := by exact prefixLift 5042763
  have htrace : WordTrace (prefixWord ++ tailWord_5042763) baseStart_5042763 baseEnd_5042763 := by
    simpa [prefixWord, tailWord_5042763, baseEnd_5042763] using wordTrace_append hprefix tailTrace_5042763
  have hstable : (prefixWord ++ tailWord_5042763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042763).length < 2 ^ (prefixWord ++ tailWord_5042763).sum := by decide
  have hdescent : baseEnd_5042763 < baseStart_5042763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042773 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_5042773 : Nat := 118140960795 + 5042773 * 2 ^ 59
def prefixEnd_5042773 : Nat := 4983230072969 + 3 ^ 40 * 5042773 * 2
def baseEnd_5042773 : Nat := 2589366380515303861146215

theorem tailTrace_5042773 : CollatzResearch.WordTrace tailWord_5042773 prefixEnd_5042773 2589366380515303861146215 := by
  unfold tailWord_5042773
  simp only [CollatzResearch.WordTrace]
  refine ⟨183925041359902132906924973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122616694239934755271283315 183925041359902132906924973)
  ·
    refine ⟨68971890509963299840096865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183925041359902132906924973 68971890509963299840096865)
    ·
      refine ⟨51728917882472474880072649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68971890509963299840096865 51728917882472474880072649)
      ·
        refine ⟨38796688411854356160054487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51728917882472474880072649 38796688411854356160054487)
        ·
          refine ⟨58195032617781534240081731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38796688411854356160054487 58195032617781534240081731)
          ·
            refine ⟨87292548926672301360122597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58195032617781534240081731 87292548926672301360122597)
            ·
              refine ⟨16367352923751056505022987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87292548926672301360122597 16367352923751056505022987)
              ·
                refine ⟨24551029385626584757534481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16367352923751056505022987 24551029385626584757534481)
                ·
                  refine ⟨18413272039219938568150861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24551029385626584757534481 18413272039219938568150861)
                  ·
                    refine ⟨6904977014707476963056573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18413272039219938568150861 6904977014707476963056573)
                    ·
                      refine ⟨2589366380515303861146215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6904977014707476963056573 2589366380515303861146215)
                      ·
                        rfl

theorem cell23_5042773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_5042773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042773 prefixEnd_5042773 := by exact prefixLift 5042773
  have htrace : WordTrace (prefixWord ++ tailWord_5042773) baseStart_5042773 baseEnd_5042773 := by
    simpa [prefixWord, tailWord_5042773, baseEnd_5042773] using wordTrace_append hprefix tailTrace_5042773
  have hstable : (prefixWord ++ tailWord_5042773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042773).length < 2 ^ (prefixWord ++ tailWord_5042773).sum := by decide
  have hdescent : baseEnd_5042773 < baseStart_5042773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042776 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_5042776 : Nat := 118140960795 + 5042776 * 2 ^ 59
def prefixEnd_5042776 : Nat := 4983230072969 + 3 ^ 40 * 5042776 * 2
def baseEnd_5042776 : Nat := 863122640319089116469567

theorem tailTrace_5042776 : CollatzResearch.WordTrace tailWord_5042776 prefixEnd_5042776 863122640319089116469567 := by
  unfold tailWord_5042776
  simp only [CollatzResearch.WordTrace]
  refine ⟨91962575389445632209642091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122616767185927509612856121 91962575389445632209642091)
  ·
    refine ⟨137943863084168448314463137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91962575389445632209642091 137943863084168448314463137)
    ·
      refine ⟨103457897313126336235847353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137943863084168448314463137 103457897313126336235847353)
      ·
        refine ⟨77593422984844752176885515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103457897313126336235847353 77593422984844752176885515)
        ·
          refine ⟨116390134477267128265328273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77593422984844752176885515 116390134477267128265328273)
          ·
            refine ⟨87292600857950346198996205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116390134477267128265328273 87292600857950346198996205)
            ·
              refine ⟨32734725321731379824623577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87292600857950346198996205 32734725321731379824623577)
              ·
                refine ⟨24551043991298534868467683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32734725321731379824623577 24551043991298534868467683)
                ·
                  refine ⟨36826565986947802302701525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24551043991298534868467683 36826565986947802302701525)
                  ·
                    refine ⟨863122640319089116469567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36826565986947802302701525 863122640319089116469567)
                    ·
                      rfl

theorem cell23_5042776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_5042776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042776 prefixEnd_5042776 := by exact prefixLift 5042776
  have htrace : WordTrace (prefixWord ++ tailWord_5042776) baseStart_5042776 baseEnd_5042776 := by
    simpa [prefixWord, tailWord_5042776, baseEnd_5042776] using wordTrace_append hprefix tailTrace_5042776
  have hstable : (prefixWord ++ tailWord_5042776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042776).length < 2 ^ (prefixWord ++ tailWord_5042776).sum := by decide
  have hdescent : baseEnd_5042776 < baseStart_5042776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042783 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 5, 2]
def baseStart_5042783 : Nat := 118140960795 + 5042783 * 2 ^ 59
def prefixEnd_5042783 : Nat := 4983230072969 + 3 ^ 40 * 5042783 * 2
def baseEnd_5042783 : Nat := 2589371515321848822021169

theorem tailTrace_5042783 : CollatzResearch.WordTrace tailWord_5042783 prefixEnd_5042783 2589371515321848822021169 := by
  unfold tailWord_5042783
  simp only [CollatzResearch.WordTrace]
  refine ⟨183925406089865904614789003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122616937393243936409859335 183925406089865904614789003)
  ·
    refine ⟨275888109134798856922183505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183925406089865904614789003 275888109134798856922183505)
    ·
      refine ⟨206916081851099142691637629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275888109134798856922183505 206916081851099142691637629)
      ·
        refine ⟨77593530694162178509364111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206916081851099142691637629 77593530694162178509364111)
        ·
          refine ⟨116390296041243267764046167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77593530694162178509364111 116390296041243267764046167)
          ·
            refine ⟨174585444061864901646069251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116390296041243267764046167 174585444061864901646069251)
            ·
              refine ⟨261878166092797352469103877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174585444061864901646069251 261878166092797352469103877)
              ·
                refine ⟨49102156142399503587956977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261878166092797352469103877 49102156142399503587956977)
                ·
                  refine ⟨36826617106799627690967733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49102156142399503587956977 36826617106799627690967733)
                  ·
                    refine ⟨3452495353762465096028225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36826617106799627690967733 3452495353762465096028225)
                    ·
                      refine ⟨2589371515321848822021169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452495353762465096028225 2589371515321848822021169)
                      ·
                        rfl

theorem cell23_5042783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_5042783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042783 prefixEnd_5042783 := by exact prefixLift 5042783
  have htrace : WordTrace (prefixWord ++ tailWord_5042783) baseStart_5042783 baseEnd_5042783 := by
    simpa [prefixWord, tailWord_5042783, baseEnd_5042783] using wordTrace_append hprefix tailTrace_5042783
  have hstable : (prefixWord ++ tailWord_5042783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042783).length < 2 ^ (prefixWord ++ tailWord_5042783).sum := by decide
  have hdescent : baseEnd_5042783 < baseStart_5042783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
