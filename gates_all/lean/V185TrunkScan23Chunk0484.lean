import V185TrunkScan23Chunk0483

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2863283 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 1, 5]
def baseStart_2863283 : Nat := 118140960795 + 2863283 * 2 ^ 59
def prefixEnd_2863283 : Nat := 4983230072969 + 3 ^ 40 * 2863283 * 2
def baseEnd_2863283 : Nat := 490080142949208708598169

theorem tailTrace_2863283 : CollatzResearch.WordTrace tailWord_2863283 prefixEnd_2863283 490080142949208708598169 := by
  unfold tailWord_2863283
  simp only [CollatzResearch.WordTrace]
  refine ⟨104432510485822175649450503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69621673657214783766300335 104432510485822175649450503)
  ·
    refine ⟨156648765728733263474175755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104432510485822175649450503 156648765728733263474175755)
    ·
      refine ⟨234973148593099895211263633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156648765728733263474175755 234973148593099895211263633)
      ·
        refine ⟨176229861444824921408447725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234973148593099895211263633 176229861444824921408447725)
        ·
          refine ⟨66086198041809345528167897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176229861444824921408447725 66086198041809345528167897)
          ·
            refine ⟨49564648531357009146125923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66086198041809345528167897 49564648531357009146125923)
            ·
              refine ⟨74346972797035513719188885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49564648531357009146125923 74346972797035513719188885)
              ·
                refine ⟨3485014349861039705586979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74346972797035513719188885 3485014349861039705586979)
                ·
                  refine ⟨5227521524791559558380469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485014349861039705586979 5227521524791559558380469)
                  ·
                    refine ⟨490080142949208708598169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5227521524791559558380469 490080142949208708598169)
                    ·
                      rfl

theorem cell23_2863283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 5].length) (baseStart_2863283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863283 prefixEnd_2863283 := by exact prefixLift 2863283
  have htrace : WordTrace (prefixWord ++ tailWord_2863283) baseStart_2863283 baseEnd_2863283 := by
    simpa [prefixWord, tailWord_2863283, baseEnd_2863283] using wordTrace_append hprefix tailTrace_2863283
  have hstable : (prefixWord ++ tailWord_2863283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863283).length < 2 ^ (prefixWord ++ tailWord_2863283).sum := by decide
  have hdescent : baseEnd_2863283 < baseStart_2863283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863314 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_2863314 : Nat := 118140960795 + 2863314 * 2 ^ 59
def prefixEnd_2863314 : Nat := 4983230072969 + 3 ^ 40 * 2863314 * 2
def baseEnd_2863314 : Nat := 1470256346747915504506865

theorem tailTrace_2863314 : CollatzResearch.WordTrace tailWord_2863314 prefixEnd_2863314 1470256346747915504506865 := by
  unfold tailWord_2863314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26108410287177466985957249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69622427432473245295885997 26108410287177466985957249)
  ·
    refine ⟨19581307715383100239467937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26108410287177466985957249 19581307715383100239467937)
    ·
      refine ⟨14685980786537325179600953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19581307715383100239467937 14685980786537325179600953)
      ·
        refine ⟨11014485589902993884700715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14685980786537325179600953 11014485589902993884700715)
        ·
          refine ⟨16521728384854490827051073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11014485589902993884700715 16521728384854490827051073)
          ·
            refine ⟨12391296288640868120288305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16521728384854490827051073 12391296288640868120288305)
            ·
              refine ⟨9293472216480651090216229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12391296288640868120288305 9293472216480651090216229)
              ·
                refine ⟨1742526040590122079415543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9293472216480651090216229 1742526040590122079415543)
                ·
                  refine ⟨2613789060885183119123315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742526040590122079415543 2613789060885183119123315)
                  ·
                    refine ⟨3920683591327774678684973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613789060885183119123315 3920683591327774678684973)
                    ·
                      refine ⟨1470256346747915504506865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3920683591327774678684973 1470256346747915504506865)
                      ·
                        rfl

theorem cell23_2863314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_2863314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863314 prefixEnd_2863314 := by exact prefixLift 2863314
  have htrace : WordTrace (prefixWord ++ tailWord_2863314) baseStart_2863314 baseEnd_2863314 := by
    simpa [prefixWord, tailWord_2863314, baseEnd_2863314] using wordTrace_append hprefix tailTrace_2863314
  have hstable : (prefixWord ++ tailWord_2863314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863314).length < 2 ^ (prefixWord ++ tailWord_2863314).sum := by decide
  have hdescent : baseEnd_2863314 < baseStart_2863314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863343 : List Nat := [1, 1, 2, 1, 6, 2, 1, 9]
def baseStart_2863343 : Nat := 118140960795 + 2863343 * 2 ^ 59
def prefixEnd_2863343 : Nat := 4983230072969 + 3 ^ 40 * 2863343 * 2
def baseEnd_2863343 : Nat := 54454490284699847816453

theorem tailTrace_2863343 : CollatzResearch.WordTrace tailWord_2863343 prefixEnd_2863343 54454490284699847816453 := by
  unfold tailWord_2863343
  simp only [CollatzResearch.WordTrace]
  refine ⟨104434698865604805896634683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69623132577069870597756455 104434698865604805896634683)
  ·
    refine ⟨156652048298407208844952025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104434698865604805896634683 156652048298407208844952025)
    ·
      refine ⟨117489036223805406633714019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156652048298407208844952025 117489036223805406633714019)
      ·
        refine ⟨176233554335708109950571029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117489036223805406633714019 176233554335708109950571029)
        ·
          refine ⟨8260947859486317653933017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176233554335708109950571029 8260947859486317653933017)
          ·
            refine ⟨6195710894614738240449763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8260947859486317653933017 6195710894614738240449763)
            ·
              refine ⟨9293566341922107360674645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195710894614738240449763 9293566341922107360674645)
              ·
                refine ⟨54454490284699847816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9293566341922107360674645 54454490284699847816453)
                ·
                  rfl

theorem cell23_2863343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 9].length) (baseStart_2863343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863343 prefixEnd_2863343 := by exact prefixLift 2863343
  have htrace : WordTrace (prefixWord ++ tailWord_2863343) baseStart_2863343 baseEnd_2863343 := by
    simpa [prefixWord, tailWord_2863343, baseEnd_2863343] using wordTrace_append hprefix tailTrace_2863343
  have hstable : (prefixWord ++ tailWord_2863343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863343).length < 2 ^ (prefixWord ++ tailWord_2863343).sum := by decide
  have hdescent : baseEnd_2863343 < baseStart_2863343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863350 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2863350 : Nat := 118140960795 + 2863350 * 2 ^ 59
def prefixEnd_2863350 : Nat := 4983230072969 + 3 ^ 40 * 2863350 * 2
def baseEnd_2863350 : Nat := 1470274832051477363656699

theorem tailTrace_2863350 : CollatzResearch.WordTrace tailWord_2863350 prefixEnd_2863350 1470274832051477363656699 := by
  unfold tailWord_2863350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6527184636036215380758719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69623302784386297394759669 6527184636036215380758719)
  ·
    refine ⟨9790776954054323071138079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6527184636036215380758719 9790776954054323071138079)
    ·
      refine ⟨14686165431081484606707119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9790776954054323071138079 14686165431081484606707119)
      ·
        refine ⟨22029248146622226910060679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14686165431081484606707119 22029248146622226910060679)
        ·
          refine ⟨33043872219933340365091019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22029248146622226910060679 33043872219933340365091019)
          ·
            refine ⟨49565808329900010547636529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33043872219933340365091019 49565808329900010547636529)
            ·
              refine ⟨37174356247425007910727397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49565808329900010547636529 37174356247425007910727397)
              ·
                refine ⟨6970191796392188983261387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37174356247425007910727397 6970191796392188983261387)
                ·
                  refine ⟨10455287694588283474892081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970191796392188983261387 10455287694588283474892081)
                  ·
                    refine ⟨7841465770941212606169061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10455287694588283474892081 7841465770941212606169061)
                    ·
                      refine ⟨1470274832051477363656699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7841465770941212606169061 1470274832051477363656699)
                      ·
                        rfl

theorem cell23_2863350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2863350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863350 prefixEnd_2863350 := by exact prefixLift 2863350
  have htrace : WordTrace (prefixWord ++ tailWord_2863350) baseStart_2863350 baseEnd_2863350 := by
    simpa [prefixWord, tailWord_2863350, baseEnd_2863350] using wordTrace_append hprefix tailTrace_2863350
  have hstable : (prefixWord ++ tailWord_2863350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863350).length < 2 ^ (prefixWord ++ tailWord_2863350).sum := by decide
  have hdescent : baseEnd_2863350 < baseStart_2863350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863371 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 1, 2, 2]
def baseStart_2863371 : Nat := 118140960795 + 2863371 * 2 ^ 59
def prefixEnd_2863371 : Nat := 4983230072969 + 3 ^ 40 * 2863371 * 2
def baseEnd_2863371 : Nat := 1470285615145221781494103

theorem tailTrace_2863371 : CollatzResearch.WordTrace tailWord_2863371 prefixEnd_2863371 1470285615145221781494103 := by
  unfold tailWord_2863371
  simp only [CollatzResearch.WordTrace]
  refine ⟨104435720109503366678653967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69623813406335577785769311 104435720109503366678653967)
  ·
    refine ⟨156653580164255050017980951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104435720109503366678653967 156653580164255050017980951)
    ·
      refine ⟨234980370246382575026971427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156653580164255050017980951 234980370246382575026971427)
      ·
        refine ⟨352470555369573862540457141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234980370246382575026971427 352470555369573862540457141)
        ·
          refine ⟨33044114565897549613167857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352470555369573862540457141 33044114565897549613167857)
          ·
            refine ⟨24783085924423162209875893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33044114565897549613167857 24783085924423162209875893)
            ·
              refine ⟨2323414305414671457175865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24783085924423162209875893 2323414305414671457175865)
              ·
                refine ⟨1742560729061003592881899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323414305414671457175865 1742560729061003592881899)
                ·
                  refine ⟨2613841093591505389322849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742560729061003592881899 2613841093591505389322849)
                  ·
                    refine ⟨1960380820193629041992137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613841093591505389322849 1960380820193629041992137)
                    ·
                      refine ⟨1470285615145221781494103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960380820193629041992137 1470285615145221781494103)
                      ·
                        rfl

theorem cell23_2863371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 2, 2].length) (baseStart_2863371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863371 prefixEnd_2863371 := by exact prefixLift 2863371
  have htrace : WordTrace (prefixWord ++ tailWord_2863371) baseStart_2863371 baseEnd_2863371 := by
    simpa [prefixWord, tailWord_2863371, baseEnd_2863371] using wordTrace_append hprefix tailTrace_2863371
  have hstable : (prefixWord ++ tailWord_2863371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863371).length < 2 ^ (prefixWord ++ tailWord_2863371).sum := by decide
  have hdescent : baseEnd_2863371 < baseStart_2863371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863427 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 4, 2, 2]
def baseStart_2863427 : Nat := 118140960795 + 2863427 * 2 ^ 59
def prefixEnd_2863427 : Nat := 4983230072969 + 3 ^ 40 * 2863427 * 2
def baseEnd_2863427 : Nat := 1470314370061873562393845

theorem tailTrace_2863427 : CollatzResearch.WordTrace tailWord_2863427 prefixEnd_2863427 1470314370061873562393845 := by
  unfold tailWord_2863427
  simp only [CollatzResearch.WordTrace]
  refine ⟨104437762597300488242692535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69625175064866992161795023 104437762597300488242692535)
  ·
    refine ⟨156656643895950732364038803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104437762597300488242692535 156656643895950732364038803)
    ·
      refine ⟨234984965843926098546058205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156656643895950732364038803 234984965843926098546058205)
      ·
        refine ⟨88119362191472286954771827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234984965843926098546058205 88119362191472286954771827)
        ·
          refine ⟨132179043287208430432157741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88119362191472286954771827 132179043287208430432157741)
          ·
            refine ⟨49567141232703161412059153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132179043287208430432157741 49567141232703161412059153)
            ·
              refine ⟨37175355924527371059044365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49567141232703161412059153 37175355924527371059044365)
              ·
                refine ⟨13940758471697764147141637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37175355924527371059044365 13940758471697764147141637)
                ·
                  refine ⟨2613892213443330777589057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13940758471697764147141637 2613892213443330777589057)
                  ·
                    refine ⟨1960419160082498083191793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613892213443330777589057 1960419160082498083191793)
                    ·
                      refine ⟨1470314370061873562393845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960419160082498083191793 1470314370061873562393845)
                      ·
                        rfl

theorem cell23_2863427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_2863427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863427 prefixEnd_2863427 := by exact prefixLift 2863427
  have htrace : WordTrace (prefixWord ++ tailWord_2863427) baseStart_2863427 baseEnd_2863427 := by
    simpa [prefixWord, tailWord_2863427, baseEnd_2863427] using wordTrace_append hprefix tailTrace_2863427
  have hstable : (prefixWord ++ tailWord_2863427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863427).length < 2 ^ (prefixWord ++ tailWord_2863427).sum := by decide
  have hdescent : baseEnd_2863427 < baseStart_2863427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863433 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 7]
def baseStart_2863433 : Nat := 118140960795 + 2863433 * 2 ^ 59
def prefixEnd_2863433 : Nat := 4983230072969 + 3 ^ 40 * 2863433 * 2
def baseEnd_2863433 : Nat := 163368605660644504324313

theorem tailTrace_2863433 : CollatzResearch.WordTrace tailWord_2863433 prefixEnd_2863433 163368605660644504324313 := by
  unfold tailWord_2863433
  simp only [CollatzResearch.WordTrace]
  refine ⟨104437981435278751267410953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69625320956852500844940635 104437981435278751267410953)
  ·
    refine ⟨78328486076459063450558215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104437981435278751267410953 78328486076459063450558215)
    ·
      refine ⟨117492729114688595175837323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78328486076459063450558215 117492729114688595175837323)
      ·
        refine ⟨176239093672032892763755985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117492729114688595175837323 176239093672032892763755985)
        ·
          refine ⟨132179320254024669572816989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176239093672032892763755985 132179320254024669572816989)
          ·
            refine ⟨49567245095259251089806371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132179320254024669572816989 49567245095259251089806371)
            ·
              refine ⟨74350867642888876634709557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49567245095259251089806371 74350867642888876634709557)
              ·
                refine ⟨6970393841520832184504021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74350867642888876634709557 6970393841520832184504021)
                ·
                  refine ⟨163368605660644504324313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6970393841520832184504021 163368605660644504324313)
                  ·
                    rfl

theorem cell23_2863433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_2863433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863433 prefixEnd_2863433 := by exact prefixLift 2863433
  have htrace : WordTrace (prefixWord ++ tailWord_2863433) baseStart_2863433 baseEnd_2863433 := by
    simpa [prefixWord, tailWord_2863433, baseEnd_2863433] using wordTrace_append hprefix tailTrace_2863433
  have hstable : (prefixWord ++ tailWord_2863433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863433).length < 2 ^ (prefixWord ++ tailWord_2863433).sum := by decide
  have hdescent : baseEnd_2863433 < baseStart_2863433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863440 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_2863440 : Nat := 118140960795 + 2863440 * 2 ^ 59
def prefixEnd_2863440 : Nat := 4983230072969 + 3 ^ 40 * 2863440 * 2
def baseEnd_2863440 : Nat := 1470321045310382011531285

theorem tailTrace_2863440 : CollatzResearch.WordTrace tailWord_2863440 prefixEnd_2863440 1470321045310382011531285 := by
  unfold tailWord_2863440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52219118373126695731457887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69625491164168927641943849 52219118373126695731457887)
  ·
    refine ⟨78328677559690043597186831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52219118373126695731457887 78328677559690043597186831)
    ·
      refine ⟨117493016339535065395780247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78328677559690043597186831 117493016339535065395780247)
      ·
        refine ⟨176239524509302598093670371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117493016339535065395780247 176239524509302598093670371)
        ·
          refine ⟨264359286763953897140505557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176239524509302598093670371 264359286763953897140505557)
          ·
            refine ⟨6195920783530169464230599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 264359286763953897140505557 6195920783530169464230599)
            ·
              refine ⟨9293881175295254196345899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195920783530169464230599 9293881175295254196345899)
              ·
                refine ⟨13940821762942881294518849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9293881175295254196345899 13940821762942881294518849)
                ·
                  refine ⟨10455616322207160970889137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13940821762942881294518849 10455616322207160970889137)
                  ·
                    refine ⟨7841712241655370728166853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10455616322207160970889137 7841712241655370728166853)
                    ·
                      refine ⟨1470321045310382011531285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7841712241655370728166853 1470321045310382011531285)
                      ·
                        rfl

theorem cell23_2863440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_2863440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863440 prefixEnd_2863440 := by exact prefixLift 2863440
  have htrace : WordTrace (prefixWord ++ tailWord_2863440) baseStart_2863440 baseEnd_2863440 := by
    simpa [prefixWord, tailWord_2863440, baseEnd_2863440] using wordTrace_append hprefix tailTrace_2863440
  have hstable : (prefixWord ++ tailWord_2863440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863440).length < 2 ^ (prefixWord ++ tailWord_2863440).sum := by decide
  have hdescent : baseEnd_2863440 < baseStart_2863440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863444 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_2863444 : Nat := 118140960795 + 2863444 * 2 ^ 59
def prefixEnd_2863444 : Nat := 4983230072969 + 3 ^ 40 * 2863444 * 2
def baseEnd_2863444 : Nat := 1470323099232999995881267

theorem tailTrace_2863444 : CollatzResearch.WordTrace tailWord_2863444 prefixEnd_2863444 1470323099232999995881267 := by
  unfold tailWord_2863444
  simp only [CollatzResearch.WordTrace]
  refine ⟨52219191319119450073030693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69625588425492600097374257 52219191319119450073030693)
  ·
    refine ⟨9791098372334896888693255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52219191319119450073030693 9791098372334896888693255)
    ·
      refine ⟨14686647558502345333039883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9791098372334896888693255 14686647558502345333039883)
      ·
        refine ⟨22029971337753517999559825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14686647558502345333039883 22029971337753517999559825)
        ·
          refine ⟨16522478503315138499669869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22029971337753517999559825 16522478503315138499669869)
          ·
            refine ⟨6195929438743176937376201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16522478503315138499669869 6195929438743176937376201)
            ·
              refine ⟨4646947079057382703032151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6195929438743176937376201 4646947079057382703032151)
              ·
                refine ⟨6970420618586074054548227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646947079057382703032151 6970420618586074054548227)
                ·
                  refine ⟨10455630927879111081822341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970420618586074054548227 10455630927879111081822341)
                  ·
                    refine ⟨1960430798977333327841689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10455630927879111081822341 1960430798977333327841689)
                    ·
                      refine ⟨1470323099232999995881267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960430798977333327841689 1470323099232999995881267)
                      ·
                        rfl

theorem cell23_2863444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_2863444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863444 prefixEnd_2863444 := by exact prefixLift 2863444
  have htrace : WordTrace (prefixWord ++ tailWord_2863444) baseStart_2863444 baseEnd_2863444 := by
    simpa [prefixWord, tailWord_2863444, baseEnd_2863444] using wordTrace_append hprefix tailTrace_2863444
  have hstable : (prefixWord ++ tailWord_2863444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863444).length < 2 ^ (prefixWord ++ tailWord_2863444).sum := by decide
  have hdescent : baseEnd_2863444 < baseStart_2863444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863460 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_2863460 : Nat := 118140960795 + 2863460 * 2 ^ 59
def prefixEnd_2863460 : Nat := 4983230072969 + 3 ^ 40 * 2863460 * 2
def baseEnd_2863460 : Nat := 1470331314923471933281193

theorem tailTrace_2863460 : CollatzResearch.WordTrace tailWord_2863460 prefixEnd_2863460 1470331314923471933281193 := by
  unfold tailWord_2863460
  simp only [CollatzResearch.WordTrace]
  refine ⟨52219483103090467439321917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69625977470787289919095889 52219483103090467439321917)
  ·
    refine ⟨19582306163658925289745719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52219483103090467439321917 19582306163658925289745719)
    ·
      refine ⟨29373459245488387934618579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19582306163658925289745719 29373459245488387934618579)
      ·
        refine ⟨44060188868232581901927869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29373459245488387934618579 44060188868232581901927869)
        ·
          refine ⟨16522570825587218213222951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44060188868232581901927869 16522570825587218213222951)
          ·
            refine ⟨24783856238380827319834427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16522570825587218213222951 24783856238380827319834427)
            ·
              refine ⟨37175784357571240979751641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24783856238380827319834427 37175784357571240979751641)
              ·
                refine ⟨27881838268178430734813731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37175784357571240979751641 27881838268178430734813731)
                ·
                  refine ⟨41822757402267646102220597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27881838268178430734813731 41822757402267646102220597)
                  ·
                    refine ⟨3920883506462591822083181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41822757402267646102220597 3920883506462591822083181)
                    ·
                      refine ⟨1470331314923471933281193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3920883506462591822083181 1470331314923471933281193)
                      ·
                        rfl

theorem cell23_2863460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_2863460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863460 prefixEnd_2863460 := by exact prefixLift 2863460
  have htrace : WordTrace (prefixWord ++ tailWord_2863460) baseStart_2863460 baseEnd_2863460 := by
    simpa [prefixWord, tailWord_2863460, baseEnd_2863460] using wordTrace_append hprefix tailTrace_2863460
  have hstable : (prefixWord ++ tailWord_2863460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863460).length < 2 ^ (prefixWord ++ tailWord_2863460).sum := by decide
  have hdescent : baseEnd_2863460 < baseStart_2863460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863477 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2863477 : Nat := 118140960795 + 2863477 * 2 ^ 59
def prefixEnd_2863477 : Nat := 4983230072969 + 3 ^ 40 * 2863477 * 2
def baseEnd_2863477 : Nat := 1470340044094598366768615

theorem tailTrace_2863477 : CollatzResearch.WordTrace tailWord_2863477 prefixEnd_2863477 1470340044094598366768615 := by
  unfold tailWord_2863477
  simp only [CollatzResearch.WordTrace]
  refine ⟨104439586247119346782012685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69626390831412897854675123 104439586247119346782012685)
  ·
    refine ⟨39164844842669755043254757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104439586247119346782012685 39164844842669755043254757)
    ·
      refine ⟨7343408408000579070610267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39164844842669755043254757 7343408408000579070610267)
      ·
        refine ⟨11015112612000868605915401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7343408408000579070610267 11015112612000868605915401)
        ·
          refine ⟨8261334459000651454436551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11015112612000868605915401 8261334459000651454436551)
          ·
            refine ⟨12392001688500977181654827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261334459000651454436551 12392001688500977181654827)
            ·
              refine ⟨18588002532751465772482241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392001688500977181654827 18588002532751465772482241)
              ·
                refine ⟨13941001899563599329361681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18588002532751465772482241 13941001899563599329361681)
                ·
                  refine ⟨10455751424672699497021261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13941001899563599329361681 10455751424672699497021261)
                  ·
                    refine ⟨3920906784252262311382973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10455751424672699497021261 3920906784252262311382973)
                    ·
                      refine ⟨1470340044094598366768615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3920906784252262311382973 1470340044094598366768615)
                      ·
                        rfl

theorem cell23_2863477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2863477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863477 prefixEnd_2863477 := by exact prefixLift 2863477
  have htrace : WordTrace (prefixWord ++ tailWord_2863477) baseStart_2863477 baseEnd_2863477 := by
    simpa [prefixWord, tailWord_2863477, baseEnd_2863477] using wordTrace_append hprefix tailTrace_2863477
  have hstable : (prefixWord ++ tailWord_2863477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863477).length < 2 ^ (prefixWord ++ tailWord_2863477).sum := by decide
  have hdescent : baseEnd_2863477 < baseStart_2863477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863478 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2863478 : Nat := 118140960795 + 2863478 * 2 ^ 59
def prefixEnd_2863478 : Nat := 4983230072969 + 3 ^ 40 * 2863478 * 2
def baseEnd_2863478 : Nat := 1470340557575252862856111

theorem tailTrace_2863478 : CollatzResearch.WordTrace tailWord_2863478 prefixEnd_2863478 1470340557575252862856111 := by
  unfold tailWord_2863478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6527476420007232747049943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69626415146743815968532725 6527476420007232747049943)
  ·
    refine ⟨9791214630010849120574915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6527476420007232747049943 9791214630010849120574915)
    ·
      refine ⟨14686821945016273680862373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9791214630010849120574915 14686821945016273680862373)
      ·
        refine ⟨2753779114690551315161695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14686821945016273680862373 2753779114690551315161695)
        ·
          refine ⟨4130668672035826972742543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753779114690551315161695 4130668672035826972742543)
          ·
            refine ⟨6196003008053740459113815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130668672035826972742543 6196003008053740459113815)
            ·
              refine ⟨9294004512080610688670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196003008053740459113815 9294004512080610688670723)
              ·
                refine ⟨13941006768120916033006085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9294004512080610688670723 13941006768120916033006085)
                ·
                  refine ⟨2613938769022671756188641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13941006768120916033006085 2613938769022671756188641)
                  ·
                    refine ⟨1960454076767003817141481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2613938769022671756188641 1960454076767003817141481)
                    ·
                      refine ⟨1470340557575252862856111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960454076767003817141481 1470340557575252862856111)
                      ·
                        rfl

theorem cell23_2863478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2863478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863478 prefixEnd_2863478 := by exact prefixLift 2863478
  have htrace : WordTrace (prefixWord ++ tailWord_2863478) baseStart_2863478 baseEnd_2863478 := by
    simpa [prefixWord, tailWord_2863478, baseEnd_2863478] using wordTrace_append hprefix tailTrace_2863478
  have hstable : (prefixWord ++ tailWord_2863478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863478).length < 2 ^ (prefixWord ++ tailWord_2863478).sum := by decide
  have hdescent : baseEnd_2863478 < baseStart_2863478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863500 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2863500 : Nat := 118140960795 + 2863500 * 2 ^ 59
def prefixEnd_2863500 : Nat := 4983230072969 + 3 ^ 40 * 2863500 * 2
def baseEnd_2863500 : Nat := 1470351854149651776781009

theorem tailTrace_2863500 : CollatzResearch.WordTrace tailWord_2863500 prefixEnd_2863500 1470351854149651776781009 := by
  unfold tailWord_2863500
  simp only [CollatzResearch.WordTrace]
  refine ⟨52220212563018010855049977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69626950084024014473399969 52220212563018010855049977)
  ·
    refine ⟨39165159422263508141287483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52220212563018010855049977 39165159422263508141287483)
    ·
      refine ⟨58747739133395262211931225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39165159422263508141287483 58747739133395262211931225)
      ·
        refine ⟨44060804350046446658948419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58747739133395262211931225 44060804350046446658948419)
        ·
          refine ⟨66091206525069669988422629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44060804350046446658948419 66091206525069669988422629)
          ·
            refine ⟨12392101223450563122829243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66091206525069669988422629 12392101223450563122829243)
            ·
              refine ⟨18588151835175844684243865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392101223450563122829243 18588151835175844684243865)
              ·
                refine ⟨13941113876381883513182899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18588151835175844684243865 13941113876381883513182899)
                ·
                  refine ⟨20911670814572825269774349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13941113876381883513182899 20911670814572825269774349)
                  ·
                    refine ⟨7841876555464809476165381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20911670814572825269774349 7841876555464809476165381)
                    ·
                      refine ⟨1470351854149651776781009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7841876555464809476165381 1470351854149651776781009)
                      ·
                        rfl

theorem cell23_2863500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2863500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863500 prefixEnd_2863500 := by exact prefixLift 2863500
  have htrace : WordTrace (prefixWord ++ tailWord_2863500) baseStart_2863500 baseEnd_2863500 := by
    simpa [prefixWord, tailWord_2863500, baseEnd_2863500] using wordTrace_append hprefix tailTrace_2863500
  have hstable : (prefixWord ++ tailWord_2863500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863500).length < 2 ^ (prefixWord ++ tailWord_2863500).sum := by decide
  have hdescent : baseEnd_2863500 < baseStart_2863500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863537 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2863537 : Nat := 118140960795 + 2863537 * 2 ^ 59
def prefixEnd_2863537 : Nat := 4983230072969 + 3 ^ 40 * 2863537 * 2
def baseEnd_2863537 : Nat := 1470370852933868132018339

theorem tailTrace_2863537 : CollatzResearch.WordTrace tailWord_2863537 prefixEnd_2863537 1470370852933868132018339 := by
  unfold tailWord_2863537
  simp only [CollatzResearch.WordTrace]
  refine ⟨104441774626901977029196865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69627849751267984686131243 104441774626901977029196865)
  ·
    refine ⟨78331330970176482771897649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104441774626901977029196865 78331330970176482771897649)
    ·
      refine ⟨58748498227632362078923237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78331330970176482771897649 58748498227632362078923237)
      ·
        refine ⟨11015343417681067889798107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58748498227632362078923237 11015343417681067889798107)
        ·
          refine ⟨16523015126521601834697161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11015343417681067889798107 16523015126521601834697161)
          ·
            refine ⟨12392261344891201376022871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16523015126521601834697161 12392261344891201376022871)
            ·
              refine ⟨18588392017336802064034307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392261344891201376022871 18588392017336802064034307)
              ·
                refine ⟨27882588026005203096051461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18588392017336802064034307 27882588026005203096051461)
                ·
                  refine ⟨5227985254875975580509649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27882588026005203096051461 5227985254875975580509649)
                  ·
                    refine ⟨3920988941156981685382237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5227985254875975580509649 3920988941156981685382237)
                    ·
                      refine ⟨1470370852933868132018339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3920988941156981685382237 1470370852933868132018339)
                      ·
                        rfl

theorem cell23_2863537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2863537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863537 prefixEnd_2863537 := by exact prefixLift 2863537
  have htrace : WordTrace (prefixWord ++ tailWord_2863537) baseStart_2863537 baseEnd_2863537 := by
    simpa [prefixWord, tailWord_2863537, baseEnd_2863537] using wordTrace_append hprefix tailTrace_2863537
  have hstable : (prefixWord ++ tailWord_2863537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863537).length < 2 ^ (prefixWord ++ tailWord_2863537).sum := by decide
  have hdescent : baseEnd_2863537 < baseStart_2863537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863567 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 3]
def baseStart_2863567 : Nat := 118140960795 + 2863567 * 2 ^ 59
def prefixEnd_2863567 : Nat := 4983230072969 + 3 ^ 40 * 2863567 * 2
def baseEnd_2863567 : Nat := 1470386257353503014643201

theorem tailTrace_2863567 : CollatzResearch.WordTrace tailWord_2863567 prefixEnd_2863567 1470386257353503014643201 := by
  unfold tailWord_2863567
  simp only [CollatzResearch.WordTrace]
  refine ⟨104442868816793292152788955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69628579211195528101859303 104442868816793292152788955)
  ·
    refine ⟨156664303225189938229183433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104442868816793292152788955 156664303225189938229183433)
    ·
      refine ⟨117498227418892453671887575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156664303225189938229183433 117498227418892453671887575)
      ·
        refine ⟨176247341128338680507831363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117498227418892453671887575 176247341128338680507831363)
        ·
          refine ⟨264371011692508020761747045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176247341128338680507831363 264371011692508020761747045)
          ·
            refine ⟨49569564692345253892827571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264371011692508020761747045 49569564692345253892827571)
            ·
              refine ⟨74354347038517880839241357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49569564692345253892827571 74354347038517880839241357)
              ·
                refine ⟨27882880139444205314715509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74354347038517880839241357 27882880139444205314715509)
                ·
                  refine ⟨2614020013072894248254579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27882880139444205314715509 2614020013072894248254579)
                  ·
                    refine ⟨3921030019609341372381869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614020013072894248254579 3921030019609341372381869)
                    ·
                      refine ⟨1470386257353503014643201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921030019609341372381869 1470386257353503014643201)
                      ·
                        rfl

theorem cell23_2863567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_2863567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863567 prefixEnd_2863567 := by exact prefixLift 2863567
  have htrace : WordTrace (prefixWord ++ tailWord_2863567) baseStart_2863567 baseEnd_2863567 := by
    simpa [prefixWord, tailWord_2863567, baseEnd_2863567] using wordTrace_append hprefix tailTrace_2863567
  have hstable : (prefixWord ++ tailWord_2863567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863567).length < 2 ^ (prefixWord ++ tailWord_2863567).sum := by decide
  have hdescent : baseEnd_2863567 < baseStart_2863567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863600 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_2863600 : Nat := 118140960795 + 2863600 * 2 ^ 59
def prefixEnd_2863600 : Nat := 4983230072969 + 3 ^ 40 * 2863600 * 2
def baseEnd_2863600 : Nat := 490134400738367128510183

theorem tailTrace_2863600 : CollatzResearch.WordTrace tailWord_2863600 prefixEnd_2863600 490134400738367128510183 := by
  unfold tailWord_2863600
  simp only [CollatzResearch.WordTrace]
  refine ⟨52222036212836869394370127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69629381617115825859160169 52222036212836869394370127)
  ·
    refine ⟨78333054319255304091555191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52222036212836869394370127 78333054319255304091555191)
    ·
      refine ⟨117499581478882956137332787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78333054319255304091555191 117499581478882956137332787)
      ·
        refine ⟨176249372218324434205999181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117499581478882956137332787 176249372218324434205999181)
        ·
          refine ⟨66093514581871662827249693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176249372218324434205999181 66093514581871662827249693)
          ·
            refine ⟨24785067968201873560218635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66093514581871662827249693 24785067968201873560218635)
            ·
              refine ⟨37177601952302810340327953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24785067968201873560218635 37177601952302810340327953)
              ·
                refine ⟨27883201464227107755245965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37177601952302810340327953 27883201464227107755245965)
                ·
                  refine ⟨10456200549085165408217237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27883201464227107755245965 10456200549085165408217237)
                  ·
                    refine ⟨490134400738367128510183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10456200549085165408217237 490134400738367128510183)
                    ·
                      rfl

theorem cell23_2863600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_2863600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863600 prefixEnd_2863600 := by exact prefixLift 2863600
  have htrace : WordTrace (prefixWord ++ tailWord_2863600) baseStart_2863600 baseEnd_2863600 := by
    simpa [prefixWord, tailWord_2863600, baseEnd_2863600] using wordTrace_append hprefix tailTrace_2863600
  have hstable : (prefixWord ++ tailWord_2863600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863600).length < 2 ^ (prefixWord ++ tailWord_2863600).sum := by decide
  have hdescent : baseEnd_2863600 < baseStart_2863600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863601 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 1, 1, 3]
def baseStart_2863601 : Nat := 118140960795 + 2863601 * 2 ^ 59
def prefixEnd_2863601 : Nat := 4983230072969 + 3 ^ 40 * 2863601 * 2
def baseEnd_2863601 : Nat := 1470403715695755881618045

theorem tailTrace_2863601 : CollatzResearch.WordTrace tailWord_2863601 prefixEnd_2863601 1470403715695755881618045 := by
  unfold tailWord_2863601
  simp only [CollatzResearch.WordTrace]
  refine ⟨104444108898670115959526657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69629405932446743973017771 104444108898670115959526657)
  ·
    refine ⟨78333081674002586969644993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104444108898670115959526657 78333081674002586969644993)
    ·
      refine ⟨58749811255501940227233745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78333081674002586969644993 58749811255501940227233745)
      ·
        refine ⟨44062358441626455170425309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58749811255501940227233745 44062358441626455170425309)
        ·
          refine ⟨16523384415609920688909491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44062358441626455170425309 16523384415609920688909491)
          ·
            refine ⟨24785076623414881033364237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16523384415609920688909491 24785076623414881033364237)
            ·
              refine ⟨9294403733780580387511589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24785076623414881033364237 9294403733780580387511589)
              ·
                refine ⟨1742700700083858822658423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9294403733780580387511589 1742700700083858822658423)
                ·
                  refine ⟨2614051050125788233987635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742700700083858822658423 2614051050125788233987635)
                  ·
                    refine ⟨3921076575188682350981453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614051050125788233987635 3921076575188682350981453)
                    ·
                      refine ⟨1470403715695755881618045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921076575188682350981453 1470403715695755881618045)
                      ·
                        rfl

theorem cell23_2863601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_2863601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863601 prefixEnd_2863601 := by exact prefixLift 2863601
  have htrace : WordTrace (prefixWord ++ tailWord_2863601) baseStart_2863601 baseEnd_2863601 := by
    simpa [prefixWord, tailWord_2863601, baseEnd_2863601] using wordTrace_append hprefix tailTrace_2863601
  have hstable : (prefixWord ++ tailWord_2863601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863601).length < 2 ^ (prefixWord ++ tailWord_2863601).sum := by decide
  have hdescent : baseEnd_2863601 < baseStart_2863601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863617 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2863617 : Nat := 118140960795 + 2863617 * 2 ^ 59
def prefixEnd_2863617 : Nat := 4983230072969 + 3 ^ 40 * 2863617 * 2
def baseEnd_2863617 : Nat := 490137310462075939672657

theorem tailTrace_2863617 : CollatzResearch.WordTrace tailWord_2863617 prefixEnd_2863617 490137310462075939672657 := by
  unfold tailWord_2863617
  simp only [CollatzResearch.WordTrace]
  refine ⟨104444692466612150692109105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69629794977741433794739403 104444692466612150692109105)
  ·
    refine ⟨78333519349959113019081829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104444692466612150692109105 78333519349959113019081829)
    ·
      refine ⟨14687534878117333691077843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78333519349959113019081829 14687534878117333691077843)
      ·
        refine ⟨22031302317176000536616765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14687534878117333691077843 22031302317176000536616765)
        ·
          refine ⟨8261738368941000201231287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22031302317176000536616765 8261738368941000201231287)
          ·
            refine ⟨12392607553411500301846931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261738368941000201231287 12392607553411500301846931)
            ·
              refine ⟨18588911330117250452770397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392607553411500301846931 18588911330117250452770397)
              ·
                refine ⟨6970841748793968919788899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18588911330117250452770397 6970841748793968919788899)
                ·
                  refine ⟨10456262623190953379683349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970841748793968919788899 10456262623190953379683349)
                  ·
                    refine ⟨490137310462075939672657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10456262623190953379683349 490137310462075939672657)
                    ·
                      rfl

theorem cell23_2863617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2863617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863617 prefixEnd_2863617 := by exact prefixLift 2863617
  have htrace : WordTrace (prefixWord ++ tailWord_2863617) baseStart_2863617 baseEnd_2863617 := by
    simpa [prefixWord, tailWord_2863617, baseEnd_2863617] using wordTrace_append hprefix tailTrace_2863617
  have hstable : (prefixWord ++ tailWord_2863617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863617).length < 2 ^ (prefixWord ++ tailWord_2863617).sum := by decide
  have hdescent : baseEnd_2863617 < baseStart_2863617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863618 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2863618 : Nat := 118140960795 + 2863618 * 2 ^ 59
def prefixEnd_2863618 : Nat := 4983230072969 + 3 ^ 40 * 2863618 * 2
def baseEnd_2863618 : Nat := 1470412444866882315105467

theorem tailTrace_2863618 : CollatzResearch.WordTrace tailWord_2863618 prefixEnd_2863618 1470412444866882315105467 := by
  unfold tailWord_2863618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111182234902131965723877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69629819293072351908597005 26111182234902131965723877)
  ·
    refine ⟨4895846669044149743573227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26111182234902131965723877 4895846669044149743573227)
    ·
      refine ⟨7343770003566224615359841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895846669044149743573227 7343770003566224615359841)
      ·
        refine ⟨5507827502674668461519881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7343770003566224615359841 5507827502674668461519881)
        ·
          refine ⟨4130870627006001346139911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507827502674668461519881 4130870627006001346139911)
          ·
            refine ⟨6196305940509002019209867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130870627006001346139911 6196305940509002019209867)
            ·
              refine ⟨9294458910763503028814801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196305940509002019209867 9294458910763503028814801)
              ·
                refine ⟨6970844183072627271611101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9294458910763503028814801 6970844183072627271611101)
                ·
                  refine ⟨2614066568652235226854163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6970844183072627271611101 2614066568652235226854163)
                  ·
                    refine ⟨3921099852978352840281245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614066568652235226854163 3921099852978352840281245)
                    ·
                      refine ⟨1470412444866882315105467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921099852978352840281245 1470412444866882315105467)
                      ·
                        rfl

theorem cell23_2863618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2863618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863618 prefixEnd_2863618 := by exact prefixLift 2863618
  have htrace : WordTrace (prefixWord ++ tailWord_2863618) baseStart_2863618 baseEnd_2863618 := by
    simpa [prefixWord, tailWord_2863618, baseEnd_2863618] using wordTrace_append hprefix tailTrace_2863618
  have hstable : (prefixWord ++ tailWord_2863618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863618).length < 2 ^ (prefixWord ++ tailWord_2863618).sum := by decide
  have hdescent : baseEnd_2863618 < baseStart_2863618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863637 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2863637 : Nat := 118140960795 + 2863637 * 2 ^ 59
def prefixEnd_2863637 : Nat := 4983230072969 + 3 ^ 40 * 2863637 * 2
def baseEnd_2863637 : Nat := 1470422200999317740767879

theorem tailTrace_2863637 : CollatzResearch.WordTrace tailWord_2863637 prefixEnd_2863637 1470422200999317740767879 := by
  unfold tailWord_2863637
  simp only [CollatzResearch.WordTrace]
  refine ⟨104445421926539694107837165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69630281284359796071891443 104445421926539694107837165)
  ·
    refine ⟨39167033222452385290438937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104445421926539694107837165 39167033222452385290438937)
    ·
      refine ⟨29375274916839288967829203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39167033222452385290438937 29375274916839288967829203)
      ·
        refine ⟨44062912375258933451743805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29375274916839288967829203 44062912375258933451743805)
        ·
          refine ⟨16523592140722100044403927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44062912375258933451743805 16523592140722100044403927)
          ·
            refine ⟨24785388211083150066605891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16523592140722100044403927 24785388211083150066605891)
            ·
              refine ⟨37178082316624725099908837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24785388211083150066605891 37178082316624725099908837)
              ·
                refine ⟨6970890434367135956232907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37178082316624725099908837 6970890434367135956232907)
                ·
                  refine ⟨10456335651550703934349361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970890434367135956232907 10456335651550703934349361)
                  ·
                    refine ⟨7842251738663027950762021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10456335651550703934349361 7842251738663027950762021)
                    ·
                      refine ⟨1470422200999317740767879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7842251738663027950762021 1470422200999317740767879)
                      ·
                        rfl

theorem cell23_2863637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2863637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863637 prefixEnd_2863637 := by exact prefixLift 2863637
  have htrace : WordTrace (prefixWord ++ tailWord_2863637) baseStart_2863637 baseEnd_2863637 := by
    simpa [prefixWord, tailWord_2863637, baseEnd_2863637] using wordTrace_append hprefix tailTrace_2863637
  have hstable : (prefixWord ++ tailWord_2863637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863637).length < 2 ^ (prefixWord ++ tailWord_2863637).sum := by decide
  have hdescent : baseEnd_2863637 < baseStart_2863637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863651 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 2, 4]
def baseStart_2863651 : Nat := 118140960795 + 2863651 * 2 ^ 59
def prefixEnd_2863651 : Nat := 4983230072969 + 3 ^ 40 * 2863651 * 2
def baseEnd_2863651 : Nat := 490143129909493561997605

theorem tailTrace_2863651 : CollatzResearch.WordTrace tailWord_2863651 prefixEnd_2863651 490143129909493561997605 := by
  unfold tailWord_2863651
  simp only [CollatzResearch.WordTrace]
  refine ⟨104445932548488974498846807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69630621698992649665897871 104445932548488974498846807)
  ·
    refine ⟨156668898822733461748270211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104445932548488974498846807 156668898822733461748270211)
    ·
      refine ⟨235003348234100192622405317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156668898822733461748270211 235003348234100192622405317)
      ·
        refine ⟨44063127793893786116700997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235003348234100192622405317 44063127793893786116700997)
        ·
          refine ⟨8261836461355084896881437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44063127793893786116700997 8261836461355084896881437)
          ·
            refine ⟨3098188673008156836330539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8261836461355084896881437 3098188673008156836330539)
            ·
              refine ⟨4647283009512235254495809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098188673008156836330539 4647283009512235254495809)
              ·
                refine ⟨3485462257134176440871857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647283009512235254495809 3485462257134176440871857)
                ·
                  refine ⟨2614096692850632330653893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3485462257134176440871857 2614096692850632330653893)
                  ·
                    refine ⟨490143129909493561997605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2614096692850632330653893 490143129909493561997605)
                    ·
                      rfl

theorem cell23_2863651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 4].length) (baseStart_2863651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863651 prefixEnd_2863651 := by exact prefixLift 2863651
  have htrace : WordTrace (prefixWord ++ tailWord_2863651) baseStart_2863651 baseEnd_2863651 := by
    simpa [prefixWord, tailWord_2863651, baseEnd_2863651] using wordTrace_append hprefix tailTrace_2863651
  have hstable : (prefixWord ++ tailWord_2863651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863651).length < 2 ^ (prefixWord ++ tailWord_2863651).sum := by decide
  have hdescent : baseEnd_2863651 < baseStart_2863651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863658 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2863658 : Nat := 118140960795 + 2863658 * 2 ^ 59
def prefixEnd_2863658 : Nat := 4983230072969 + 3 ^ 40 * 2863658 * 2
def baseEnd_2863658 : Nat := 1470432984093062158605283

theorem tailTrace_2863658 : CollatzResearch.WordTrace tailWord_2863658 prefixEnd_2863658 1470432984093062158605283 := by
  unfold tailWord_2863658
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111546964865903673587907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69630791906309076462901085 26111546964865903673587907)
  ·
    refine ⟨39167320447298855510381861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26111546964865903673587907 39167320447298855510381861)
    ·
      refine ⟨7343872583868535408196599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39167320447298855510381861 7343872583868535408196599)
      ·
        refine ⟨11015808875802803112294899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7343872583868535408196599 11015808875802803112294899)
        ·
          refine ⟨16523713313704204668442349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11015808875802803112294899 16523713313704204668442349)
          ·
            refine ⟨6196392492639076750665881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16523713313704204668442349 6196392492639076750665881)
            ·
              refine ⟨4647294369479307562999411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196392492639076750665881 4647294369479307562999411)
              ·
                refine ⟨6970941554218961344499117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647294369479307562999411 6970941554218961344499117)
                ·
                  refine ⟨2614103082832110504187169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6970941554218961344499117 2614103082832110504187169)
                  ·
                    refine ⟨1960577312124082878140377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2614103082832110504187169 1960577312124082878140377)
                    ·
                      refine ⟨1470432984093062158605283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960577312124082878140377 1470432984093062158605283)
                      ·
                        rfl

theorem cell23_2863658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2863658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863658 prefixEnd_2863658 := by exact prefixLift 2863658
  have htrace : WordTrace (prefixWord ++ tailWord_2863658) baseStart_2863658 baseEnd_2863658 := by
    simpa [prefixWord, tailWord_2863658, baseEnd_2863658] using wordTrace_append hprefix tailTrace_2863658
  have hstable : (prefixWord ++ tailWord_2863658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863658).length < 2 ^ (prefixWord ++ tailWord_2863658).sum := by decide
  have hdescent : baseEnd_2863658 < baseStart_2863658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863660 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_2863660 : Nat := 118140960795 + 2863660 * 2 ^ 59
def prefixEnd_2863660 : Nat := 4983230072969 + 3 ^ 40 * 2863660 * 2
def baseEnd_2863660 : Nat := 490144670351457050260091

theorem tailTrace_2863660 : CollatzResearch.WordTrace tailWord_2863660 prefixEnd_2863660 490144670351457050260091 := by
  unfold tailWord_2863660
  simp only [CollatzResearch.WordTrace]
  refine ⟨52223130402728184517962217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69630840536970912690616289 52223130402728184517962217)
  ·
    refine ⟨39167347802046138388471663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52223130402728184517962217 39167347802046138388471663)
    ·
      refine ⟨58751021703069207582707495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39167347802046138388471663 58751021703069207582707495)
      ·
        refine ⟨88126532554603811374061243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58751021703069207582707495 88126532554603811374061243)
        ·
          refine ⟨132189798831905717061091865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88126532554603811374061243 132189798831905717061091865)
          ·
            refine ⟨99142349123929287795818899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132189798831905717061091865 99142349123929287795818899)
            ·
              refine ⟨148713523685893931693728349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99142349123929287795818899 148713523685893931693728349)
              ·
                refine ⟨55767571382210224385148131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148713523685893931693728349 55767571382210224385148131)
                ·
                  refine ⟨83651357073315336577722197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55767571382210224385148131 83651357073315336577722197)
                  ·
                    refine ⟨490144670351457050260091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 83651357073315336577722197 490144670351457050260091)
                    ·
                      rfl

theorem cell23_2863660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_2863660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863660 prefixEnd_2863660 := by exact prefixLift 2863660
  have htrace : WordTrace (prefixWord ++ tailWord_2863660) baseStart_2863660 baseEnd_2863660 := by
    simpa [prefixWord, tailWord_2863660, baseEnd_2863660] using wordTrace_append hprefix tailTrace_2863660
  have hstable : (prefixWord ++ tailWord_2863660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863660).length < 2 ^ (prefixWord ++ tailWord_2863660).sum := by decide
  have hdescent : baseEnd_2863660 < baseStart_2863660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863668 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2863668 : Nat := 118140960795 + 2863668 * 2 ^ 59
def prefixEnd_2863668 : Nat := 4983230072969 + 3 ^ 40 * 2863668 * 2
def baseEnd_2863668 : Nat := 490146039633202373160079

theorem tailTrace_2863668 : CollatzResearch.WordTrace tailWord_2863668 prefixEnd_2863668 490146039633202373160079 := by
  unfold tailWord_2863668
  simp only [CollatzResearch.WordTrace]
  refine ⟨52223276294713693201107829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69631035059618257601477105 52223276294713693201107829)
  ·
    refine ⟨4895932152629408737603859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52223276294713693201107829 4895932152629408737603859)
    ·
      refine ⟨7343898228944113106405789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895932152629408737603859 7343898228944113106405789)
      ·
        refine ⟨2753961835854042414902171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7343898228944113106405789 2753961835854042414902171)
        ·
          refine ⟨4130942753781063622353257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753961835854042414902171 4130942753781063622353257)
          ·
            refine ⟨3098207065335797716764943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130942753781063622353257 3098207065335797716764943)
            ·
              refine ⟨4647310598003696575147415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098207065335797716764943 4647310598003696575147415)
              ·
                refine ⟨6970965897005544862721123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647310598003696575147415 6970965897005544862721123)
                ·
                  refine ⟨10456448845508317294081685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970965897005544862721123 10456448845508317294081685)
                  ·
                    refine ⟨490146039633202373160079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10456448845508317294081685 490146039633202373160079)
                    ·
                      rfl

theorem cell23_2863668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2863668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863668 prefixEnd_2863668 := by exact prefixLift 2863668
  have htrace : WordTrace (prefixWord ++ tailWord_2863668) baseStart_2863668 baseEnd_2863668 := by
    simpa [prefixWord, tailWord_2863668, baseEnd_2863668] using wordTrace_append hprefix tailTrace_2863668
  have hstable : (prefixWord ++ tailWord_2863668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863668).length < 2 ^ (prefixWord ++ tailWord_2863668).sum := by decide
  have hdescent : baseEnd_2863668 < baseStart_2863668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863674 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_2863674 : Nat := 118140960795 + 2863674 * 2 ^ 59
def prefixEnd_2863674 : Nat := 4983230072969 + 3 ^ 40 * 2863674 * 2
def baseEnd_2863674 : Nat := 1470441199783534096005209

theorem tailTrace_2863674 : CollatzResearch.WordTrace tailWord_2863674 prefixEnd_2863674 1470441199783534096005209 := by
  unfold tailWord_2863674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111692856851412356733519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69631180951603766284622717 26111692856851412356733519)
  ·
    refine ⟨39167539285277118535100279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26111692856851412356733519 39167539285277118535100279)
    ·
      refine ⟨58751308927915677802650419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39167539285277118535100279 58751308927915677802650419)
      ·
        refine ⟨88126963391873516703975629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58751308927915677802650419 88126963391873516703975629)
        ·
          refine ⟨33047611271952568763990861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88126963391873516703975629 33047611271952568763990861)
          ·
            refine ⟨12392854226982213286496573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33047611271952568763990861 12392854226982213286496573)
            ·
              refine ⟨4647320335118329982436215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12392854226982213286496573 4647320335118329982436215)
              ·
                refine ⟨6970980502677494973654323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647320335118329982436215 6970980502677494973654323)
                ·
                  refine ⟨10456470754016242460481485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970980502677494973654323 10456470754016242460481485)
                  ·
                    refine ⟨3921176532756090922680557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10456470754016242460481485 3921176532756090922680557)
                    ·
                      refine ⟨1470441199783534096005209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921176532756090922680557 1470441199783534096005209)
                      ·
                        rfl

theorem cell23_2863674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_2863674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863674 prefixEnd_2863674 := by exact prefixLift 2863674
  have htrace : WordTrace (prefixWord ++ tailWord_2863674) baseStart_2863674 baseEnd_2863674 := by
    simpa [prefixWord, tailWord_2863674, baseEnd_2863674] using wordTrace_append hprefix tailTrace_2863674
  have hstable : (prefixWord ++ tailWord_2863674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863674).length < 2 ^ (prefixWord ++ tailWord_2863674).sum := by decide
  have hdescent : baseEnd_2863674 < baseStart_2863674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863687 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2863687 : Nat := 118140960795 + 2863687 * 2 ^ 59
def prefixEnd_2863687 : Nat := 4983230072969 + 3 ^ 40 * 2863687 * 2
def baseEnd_2863687 : Nat := 1470447875032042545142649

theorem tailTrace_2863687 : CollatzResearch.WordTrace tailWord_2863687 prefixEnd_2863687 1470447875032042545142649 := by
  unfold tailWord_2863687
  simp only [CollatzResearch.WordTrace]
  refine ⟨104447245576358552647157315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69631497050905701764771543 104447245576358552647157315)
  ·
    refine ⟨156670868364537828970735973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104447245576358552647157315 156670868364537828970735973)
    ·
      refine ⟨29375787818350842932012995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156670868364537828970735973 29375787818350842932012995)
      ·
        refine ⟨44063681727526264398019493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29375787818350842932012995 44063681727526264398019493)
        ·
          refine ⟨8261940323911174574628655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44063681727526264398019493 8261940323911174574628655)
          ·
            refine ⟨12392910485866761861942983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261940323911174574628655 12392910485866761861942983)
            ·
              refine ⟨18589365728800142792914475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392910485866761861942983 18589365728800142792914475)
              ·
                refine ⟨27884048593200214189371713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18589365728800142792914475 27884048593200214189371713)
                ·
                  refine ⟨20913036444900160642028785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27884048593200214189371713 20913036444900160642028785)
                  ·
                    refine ⟨15684777333675120481521589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20913036444900160642028785 15684777333675120481521589)
                    ·
                      refine ⟨1470447875032042545142649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15684777333675120481521589 1470447875032042545142649)
                      ·
                        rfl

theorem cell23_2863687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2863687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863687 prefixEnd_2863687 := by exact prefixLift 2863687
  have htrace : WordTrace (prefixWord ++ tailWord_2863687) baseStart_2863687 baseEnd_2863687 := by
    simpa [prefixWord, tailWord_2863687, baseEnd_2863687] using wordTrace_append hprefix tailTrace_2863687
  have hstable : (prefixWord ++ tailWord_2863687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863687).length < 2 ^ (prefixWord ++ tailWord_2863687).sum := by decide
  have hdescent : baseEnd_2863687 < baseStart_2863687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863701 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2863701 : Nat := 118140960795 + 2863701 * 2 ^ 59
def prefixEnd_2863701 : Nat := 4983230072969 + 3 ^ 40 * 2863701 * 2
def baseEnd_2863701 : Nat := 1470455063761205490367585

theorem tailTrace_2863701 : CollatzResearch.WordTrace tailWord_2863701 prefixEnd_2863701 1470455063761205490367585 := by
  unfold tailWord_2863701
  simp only [CollatzResearch.WordTrace]
  refine ⟨104447756198307833038166957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69631837465538555358777971 104447756198307833038166957)
  ·
    refine ⟨39167908574365437389312609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104447756198307833038166957 39167908574365437389312609)
    ·
      refine ⟨29375931430774078041984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39167908574365437389312609 29375931430774078041984457)
      ·
        refine ⟨22031948573080558531488343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29375931430774078041984457 22031948573080558531488343)
        ·
          refine ⟨33047922859620837797232515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22031948573080558531488343 33047922859620837797232515)
          ·
            refine ⟨49571884289431256695848773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33047922859620837797232515 49571884289431256695848773)
            ·
              refine ⟨9294728304268360630471645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49571884289431256695848773 9294728304268360630471645)
              ·
                refine ⟨3485523114100635236426867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9294728304268360630471645 3485523114100635236426867)
                ·
                  refine ⟨5228284671150952854640301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485523114100635236426867 5228284671150952854640301)
                  ·
                    refine ⟨1960606751681607320490113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5228284671150952854640301 1960606751681607320490113)
                    ·
                      refine ⟨1470455063761205490367585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960606751681607320490113 1470455063761205490367585)
                      ·
                        rfl

theorem cell23_2863701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2863701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863701 prefixEnd_2863701 := by exact prefixLift 2863701
  have htrace : WordTrace (prefixWord ++ tailWord_2863701) baseStart_2863701 baseEnd_2863701 := by
    simpa [prefixWord, tailWord_2863701, baseEnd_2863701] using wordTrace_append hprefix tailTrace_2863701
  have hstable : (prefixWord ++ tailWord_2863701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863701).length < 2 ^ (prefixWord ++ tailWord_2863701).sum := by decide
  have hdescent : baseEnd_2863701 < baseStart_2863701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863725 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_2863725 : Nat := 118140960795 + 2863725 * 2 ^ 59
def prefixEnd_2863725 : Nat := 4983230072969 + 3 ^ 40 * 2863725 * 2
def baseEnd_2863725 : Nat := 1470467387296913396467475

theorem tailTrace_2863725 : CollatzResearch.WordTrace tailWord_2863725 prefixEnd_2863725 1470467387296913396467475 := by
  unfold tailWord_2863725
  simp only [CollatzResearch.WordTrace]
  refine ⟨104448631550220885137040629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69632421033480590091360419 104448631550220885137040629)
  ·
    refine ⟨9792059207833207981597559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104448631550220885137040629 9792059207833207981597559)
    ·
      refine ⟨14688088811749811972396339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792059207833207981597559 14688088811749811972396339)
      ·
        refine ⟨22032133217624717958594509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14688088811749811972396339 22032133217624717958594509)
        ·
          refine ⟨8262049956609269234472941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22032133217624717958594509 8262049956609269234472941)
          ·
            refine ⟨3098268733728475962927353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8262049956609269234472941 3098268733728475962927353)
            ·
              refine ⟨2323701550296356972195515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098268733728475962927353 2323701550296356972195515)
              ·
                refine ⟨3485552325444535458293273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323701550296356972195515 3485552325444535458293273)
                ·
                  refine ⟨2614164244083401593719955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3485552325444535458293273 2614164244083401593719955)
                  ·
                    refine ⟨3921246366125102390579933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614164244083401593719955 3921246366125102390579933)
                    ·
                      refine ⟨1470467387296913396467475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921246366125102390579933 1470467387296913396467475)
                      ·
                        rfl

theorem cell23_2863725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_2863725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863725 prefixEnd_2863725 := by exact prefixLift 2863725
  have htrace : WordTrace (prefixWord ++ tailWord_2863725) baseStart_2863725 baseEnd_2863725 := by
    simpa [prefixWord, tailWord_2863725, baseEnd_2863725] using wordTrace_append hprefix tailTrace_2863725
  have hstable : (prefixWord ++ tailWord_2863725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863725).length < 2 ^ (prefixWord ++ tailWord_2863725).sum := by decide
  have hdescent : baseEnd_2863725 < baseStart_2863725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863727 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_2863727 : Nat := 118140960795 + 2863727 * 2 ^ 59
def prefixEnd_2863727 : Nat := 4983230072969 + 3 ^ 40 * 2863727 * 2
def baseEnd_2863727 : Nat := 1470468414258222388642465

theorem tailTrace_2863727 : CollatzResearch.WordTrace tailWord_2863727 prefixEnd_2863727 1470468414258222388642465 := by
  unfold tailWord_2863727
  simp only [CollatzResearch.WordTrace]
  refine ⟨104448704496213639478613435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69632469664142426319075623 104448704496213639478613435)
  ·
    refine ⟨156673056744320459217920153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104448704496213639478613435 156673056744320459217920153)
    ·
      refine ⟨117504792558240344413440115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156673056744320459217920153 117504792558240344413440115)
      ·
        refine ⟨176257188837360516620160173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117504792558240344413440115 176257188837360516620160173)
        ·
          refine ⟨66096445814010193732560065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176257188837360516620160173 66096445814010193732560065)
          ·
            refine ⟨49572334360507645299420049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66096445814010193732560065 49572334360507645299420049)
            ·
              refine ⟨37179250770380733974565037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49572334360507645299420049 37179250770380733974565037)
              ·
                refine ⟨13942219038892775240461889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37179250770380733974565037 13942219038892775240461889)
                ·
                  refine ⟨10456664279169581430346417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13942219038892775240461889 10456664279169581430346417)
                  ·
                    refine ⟨7842498209377186072759813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10456664279169581430346417 7842498209377186072759813)
                    ·
                      refine ⟨1470468414258222388642465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7842498209377186072759813 1470468414258222388642465)
                      ·
                        rfl

theorem cell23_2863727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_2863727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863727 prefixEnd_2863727 := by exact prefixLift 2863727
  have htrace : WordTrace (prefixWord ++ tailWord_2863727) baseStart_2863727 baseEnd_2863727 := by
    simpa [prefixWord, tailWord_2863727, baseEnd_2863727] using wordTrace_append hprefix tailTrace_2863727
  have hstable : (prefixWord ++ tailWord_2863727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863727).length < 2 ^ (prefixWord ++ tailWord_2863727).sum := by decide
  have hdescent : baseEnd_2863727 < baseStart_2863727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863804 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2863804 : Nat := 118140960795 + 2863804 * 2 ^ 59
def prefixEnd_2863804 : Nat := 4983230072969 + 3 ^ 40 * 2863804 * 2
def baseEnd_2863804 : Nat := 1470507952268618587379611

theorem tailTrace_2863804 : CollatzResearch.WordTrace tailWord_2863804 prefixEnd_2863804 1470507952268618587379611 := by
  unfold tailWord_2863804
  simp only [CollatzResearch.WordTrace]
  refine ⟨52225756458467340814583233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69634341944623121086110977 52225756458467340814583233)
  ·
    refine ⟨39169317343850505610937425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52225756458467340814583233 39169317343850505610937425)
    ·
      refine ⟨29376988007887879208203069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39169317343850505610937425 29376988007887879208203069)
      ·
        refine ⟨11016370502957954703076151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29376988007887879208203069 11016370502957954703076151)
        ·
          refine ⟨16524555754436932054614227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016370502957954703076151 16524555754436932054614227)
          ·
            refine ⟨24786833631655398081921341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16524555754436932054614227 24786833631655398081921341)
            ·
              refine ⟨9295062611870774280720503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24786833631655398081921341 9295062611870774280720503)
              ·
                refine ⟨13942593917806161421080755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9295062611870774280720503 13942593917806161421080755)
                ·
                  refine ⟨20913890876709242131621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13942593917806161421080755 20913890876709242131621133)
                  ·
                    refine ⟨7842709078765965799357925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20913890876709242131621133 7842709078765965799357925)
                    ·
                      refine ⟨1470507952268618587379611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7842709078765965799357925 1470507952268618587379611)
                      ·
                        rfl

theorem cell23_2863804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2863804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863804 prefixEnd_2863804 := by exact prefixLift 2863804
  have htrace : WordTrace (prefixWord ++ tailWord_2863804) baseStart_2863804 baseEnd_2863804 := by
    simpa [prefixWord, tailWord_2863804, baseEnd_2863804] using wordTrace_append hprefix tailTrace_2863804
  have hstable : (prefixWord ++ tailWord_2863804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863804).length < 2 ^ (prefixWord ++ tailWord_2863804).sum := by decide
  have hdescent : baseEnd_2863804 < baseStart_2863804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863817 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_2863817 : Nat := 118140960795 + 2863817 * 2 ^ 59
def prefixEnd_2863817 : Nat := 4983230072969 + 3 ^ 40 * 2863817 * 2
def baseEnd_2863817 : Nat := 1470514627517127036517051

theorem tailTrace_2863817 : CollatzResearch.WordTrace tailWord_2863817 prefixEnd_2863817 1470514627517127036517051 := by
  unfold tailWord_2863817
  simp only [CollatzResearch.WordTrace]
  refine ⟨104451987065887584849389705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69634658043925056566259803 104451987065887584849389705)
  ·
    refine ⟨78338990299415688637042279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104451987065887584849389705 78338990299415688637042279)
    ·
      refine ⟨117508485449123532955563419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78338990299415688637042279 117508485449123532955563419)
      ·
        refine ⟨176262728173685299433345129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117508485449123532955563419 176262728173685299433345129)
        ·
          refine ⟨132197046130263974575008847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176262728173685299433345129 132197046130263974575008847)
          ·
            refine ⟨198295569195395961862513271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132197046130263974575008847 198295569195395961862513271)
            ·
              refine ⟨297443353793093942793769907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198295569195395961862513271 297443353793093942793769907)
              ·
                refine ⟨446165030689640914190654861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297443353793093942793769907 446165030689640914190654861)
                ·
                  refine ⟨167311886508615342821495573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446165030689640914190654861 167311886508615342821495573)
                  ·
                    refine ⟨7842744680091344194757605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 167311886508615342821495573 7842744680091344194757605)
                    ·
                      refine ⟨1470514627517127036517051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7842744680091344194757605 1470514627517127036517051)
                      ·
                        rfl

theorem cell23_2863817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_2863817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863817 prefixEnd_2863817 := by exact prefixLift 2863817
  have htrace : WordTrace (prefixWord ++ tailWord_2863817) baseStart_2863817 baseEnd_2863817 := by
    simpa [prefixWord, tailWord_2863817, baseEnd_2863817] using wordTrace_append hprefix tailTrace_2863817
  have hstable : (prefixWord ++ tailWord_2863817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863817).length < 2 ^ (prefixWord ++ tailWord_2863817).sum := by decide
  have hdescent : baseEnd_2863817 < baseStart_2863817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863831 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 3, 4]
def baseStart_2863831 : Nat := 118140960795 + 2863831 * 2 ^ 59
def prefixEnd_2863831 : Nat := 4983230072969 + 3 ^ 40 * 2863831 * 2
def baseEnd_2863831 : Nat := 490173938748763327247329

theorem tailTrace_2863831 : CollatzResearch.WordTrace tailWord_2863831 prefixEnd_2863831 490173938748763327247329 := by
  unfold tailWord_2863831
  simp only [CollatzResearch.WordTrace]
  refine ⟨104452497687836865240399347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69634998458557910160266231 104452497687836865240399347)
  ·
    refine ⟨156678746531755297860599021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104452497687836865240399347 156678746531755297860599021)
    ·
      refine ⟨58754529949408236697724633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156678746531755297860599021 58754529949408236697724633)
      ·
        refine ⟨44065897462056177523293475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58754529949408236697724633 44065897462056177523293475)
        ·
          refine ⟨66098846193084266284940213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44065897462056177523293475 66098846193084266284940213)
          ·
            refine ⟨6196766830601649964213145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66098846193084266284940213 6196766830601649964213145)
            ·
              refine ⟨4647575122951237473159859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196766830601649964213145 4647575122951237473159859)
              ·
                refine ⟨6971362684426856209739789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647575122951237473159859 6971362684426856209739789)
                ·
                  refine ⟨2614261006660071078652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6971362684426856209739789 2614261006660071078652421)
                  ·
                    refine ⟨490173938748763327247329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2614261006660071078652421 490173938748763327247329)
                    ·
                      rfl

theorem cell23_2863831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_2863831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863831 prefixEnd_2863831 := by exact prefixLift 2863831
  have htrace : WordTrace (prefixWord ++ tailWord_2863831) baseStart_2863831 baseEnd_2863831 := by
    simpa [prefixWord, tailWord_2863831, baseEnd_2863831] using wordTrace_append hprefix tailTrace_2863831
  have hstable : (prefixWord ++ tailWord_2863831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863831).length < 2 ^ (prefixWord ++ tailWord_2863831).sum := by decide
  have hdescent : baseEnd_2863831 < baseStart_2863831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863867 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_2863867 : Nat := 118140960795 + 2863867 * 2 ^ 59
def prefixEnd_2863867 : Nat := 4983230072969 + 3 ^ 40 * 2863867 * 2
def baseEnd_2863867 : Nat := 1470540301549851840891821

theorem tailTrace_2863867 : CollatzResearch.WordTrace tailWord_2863867 prefixEnd_2863867 1470540301549851840891821 := by
  unfold tailWord_2863867
  simp only [CollatzResearch.WordTrace]
  refine ⟨104453810715706443388709855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69635873810470962259139903 104453810715706443388709855)
  ·
    refine ⟨156680716073559665083064783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104453810715706443388709855 156680716073559665083064783)
    ·
      refine ⟨235021074110339497624597175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156680716073559665083064783 235021074110339497624597175)
      ·
        refine ⟨352531611165509246436895763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235021074110339497624597175 352531611165509246436895763)
        ·
          refine ⟨528797416748263869655343645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352531611165509246436895763 528797416748263869655343645)
          ·
            refine ⟨198299031280598951120753867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528797416748263869655343645 198299031280598951120753867)
            ·
              refine ⟨297448546920898426681130801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198299031280598951120753867 297448546920898426681130801)
              ·
                refine ⟨223086410190673820010848101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297448546920898426681130801 223086410190673820010848101)
                ·
                  refine ⟨41828701910751341252034019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223086410190673820010848101 41828701910751341252034019)
                  ·
                    refine ⟨62743052866127011878051029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41828701910751341252034019 62743052866127011878051029)
                    ·
                      refine ⟨1470540301549851840891821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62743052866127011878051029 1470540301549851840891821)
                      ·
                        rfl

theorem cell23_2863867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_2863867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863867 prefixEnd_2863867 := by exact prefixLift 2863867
  have htrace : WordTrace (prefixWord ++ tailWord_2863867) baseStart_2863867 baseEnd_2863867 := by
    simpa [prefixWord, tailWord_2863867, baseEnd_2863867] using wordTrace_append hprefix tailTrace_2863867
  have hstable : (prefixWord ++ tailWord_2863867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863867).length < 2 ^ (prefixWord ++ tailWord_2863867).sum := by decide
  have hdescent : baseEnd_2863867 < baseStart_2863867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863881 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 4, 3, 2]
def baseStart_2863881 : Nat := 118140960795 + 2863881 * 2 ^ 59
def prefixEnd_2863881 : Nat := 4983230072969 + 3 ^ 40 * 2863881 * 2
def baseEnd_2863881 : Nat := 1470547490279014786116757

theorem tailTrace_2863881 : CollatzResearch.WordTrace tailWord_2863881 prefixEnd_2863881 1470547490279014786116757 := by
  unfold tailWord_2863881
  simp only [CollatzResearch.WordTrace]
  refine ⟨104454321337655723779719497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69636214225103815853146331 104454321337655723779719497)
  ·
    refine ⟨78340741003241792834789623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104454321337655723779719497 78340741003241792834789623)
    ·
      refine ⟨117511111504862689252184435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78340741003241792834789623 117511111504862689252184435)
      ·
        refine ⟨176266667257294033878276653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117511111504862689252184435 176266667257294033878276653)
        ·
          refine ⟨66100000221485262704353745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176266667257294033878276653 66100000221485262704353745)
          ·
            refine ⟨49575000166113947028265309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66100000221485262704353745 49575000166113947028265309)
            ·
              refine ⟨18590625062292730135599491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49575000166113947028265309 18590625062292730135599491)
              ·
                refine ⟨27885937593439095203399237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18590625062292730135599491 27885937593439095203399237)
                ·
                  refine ⟨5228613298769830350637357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27885937593439095203399237 5228613298769830350637357)
                  ·
                    refine ⟨1960729987038686381489009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5228613298769830350637357 1960729987038686381489009)
                    ·
                      refine ⟨1470547490279014786116757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960729987038686381489009 1470547490279014786116757)
                      ·
                        rfl

theorem cell23_2863881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 3, 2].length) (baseStart_2863881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863881 prefixEnd_2863881 := by exact prefixLift 2863881
  have htrace : WordTrace (prefixWord ++ tailWord_2863881) baseStart_2863881 baseEnd_2863881 := by
    simpa [prefixWord, tailWord_2863881, baseEnd_2863881] using wordTrace_append hprefix tailTrace_2863881
  have hstable : (prefixWord ++ tailWord_2863881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863881).length < 2 ^ (prefixWord ++ tailWord_2863881).sum := by decide
  have hdescent : baseEnd_2863881 < baseStart_2863881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863895 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 6]
def baseStart_2863895 : Nat := 118140960795 + 2863895 * 2 ^ 59
def prefixEnd_2863895 : Nat := 4983230072969 + 3 ^ 40 * 2863895 * 2
def baseEnd_2863895 : Nat := 163394964334241970149077

theorem tailTrace_2863895 : CollatzResearch.WordTrace tailWord_2863895 prefixEnd_2863895 163394964334241970149077 := by
  unfold tailWord_2863895
  simp only [CollatzResearch.WordTrace]
  refine ⟨104454831959605004170729139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69636554639736669447152759 104454831959605004170729139)
  ·
    refine ⟨156682247939407506256093709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104454831959605004170729139 156682247939407506256093709)
    ·
      refine ⟨58755842977277814846035141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156682247939407506256093709 58755842977277814846035141)
      ·
        refine ⟨11016720558239590283631589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58755842977277814846035141 11016720558239590283631589)
        ·
          refine ⟨2065635104669923178180923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11016720558239590283631589 2065635104669923178180923)
          ·
            refine ⟨3098452657004884767271385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065635104669923178180923 3098452657004884767271385)
            ·
              refine ⟨2323839492753663575453539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3098452657004884767271385 2323839492753663575453539)
              ·
                refine ⟨3485759239130495363180309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323839492753663575453539 3485759239130495363180309)
                ·
                  refine ⟨163394964334241970149077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3485759239130495363180309 163394964334241970149077)
                  ·
                    rfl

theorem cell23_2863895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 6].length) (baseStart_2863895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863895 prefixEnd_2863895 := by exact prefixLift 2863895
  have htrace : WordTrace (prefixWord ++ tailWord_2863895) baseStart_2863895 baseEnd_2863895 := by
    simpa [prefixWord, tailWord_2863895, baseEnd_2863895] using wordTrace_append hprefix tailTrace_2863895
  have hstable : (prefixWord ++ tailWord_2863895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863895).length < 2 ^ (prefixWord ++ tailWord_2863895).sum := by decide
  have hdescent : baseEnd_2863895 < baseStart_2863895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863928 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_2863928 : Nat := 118140960795 + 2863928 * 2 ^ 59
def prefixEnd_2863928 : Nat := 4983230072969 + 3 ^ 40 * 2863928 * 2
def baseEnd_2863928 : Nat := 1470571623869776102229041

theorem tailTrace_2863928 : CollatzResearch.WordTrace tailWord_2863928 prefixEnd_2863928 1470571623869776102229041 := by
  unfold tailWord_2863928
  simp only [CollatzResearch.WordTrace]
  refine ⟨52228017784242725403340219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69637357045656967204453625 52228017784242725403340219)
  ·
    refine ⟨78342026676364088105010329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52228017784242725403340219 78342026676364088105010329)
    ·
      refine ⟨58756520007273066078757747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78342026676364088105010329 58756520007273066078757747)
      ·
        refine ⟨88134780010909599118136621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58756520007273066078757747 88134780010909599118136621)
        ·
          refine ⟨33050542504091099669301233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88134780010909599118136621 33050542504091099669301233)
          ·
            refine ⟨24787906878068324751975925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33050542504091099669301233 24787906878068324751975925)
            ·
              refine ⟨2323866269818905445497743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24787906878068324751975925 2323866269818905445497743)
              ·
                refine ⟨3485799404728358168246615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323866269818905445497743 3485799404728358168246615)
                ·
                  refine ⟨5228699107092537252369923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485799404728358168246615 5228699107092537252369923)
                  ·
                    refine ⟨7843048660638805878554885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5228699107092537252369923 7843048660638805878554885)
                    ·
                      refine ⟨1470571623869776102229041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7843048660638805878554885 1470571623869776102229041)
                      ·
                        rfl

theorem cell23_2863928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_2863928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863928 prefixEnd_2863928 := by exact prefixLift 2863928
  have htrace : WordTrace (prefixWord ++ tailWord_2863928) baseStart_2863928 baseEnd_2863928 := by
    simpa [prefixWord, tailWord_2863928, baseEnd_2863928] using wordTrace_append hprefix tailTrace_2863928
  have hstable : (prefixWord ++ tailWord_2863928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863928).length < 2 ^ (prefixWord ++ tailWord_2863928).sum := by decide
  have hdescent : baseEnd_2863928 < baseStart_2863928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863934 : List Nat := [4, 2, 1, 2, 14]
def baseStart_2863934 : Nat := 118140960795 + 2863934 * 2 ^ 59
def prefixEnd_2863934 : Nat := 4983230072969 + 3 ^ 40 * 2863934 * 2
def baseEnd_2863934 : Nat := 2017249252062692837797

theorem tailTrace_2863934 : CollatzResearch.WordTrace tailWord_2863934 prefixEnd_2863934 2017249252062692837797 := by
  unfold tailWord_2863934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057031800807964228924857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69637502937642475887599237 13057031800807964228924857)
  ·
    refine ⟨9792773850605973171693643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13057031800807964228924857 9792773850605973171693643)
    ·
      refine ⟨14689160775908959757540465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792773850605973171693643 14689160775908959757540465)
      ·
        refine ⟨11016870581931719818155349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14689160775908959757540465 11016870581931719818155349)
        ·
          refine ⟨2017249252062692837797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 11016870581931719818155349 2017249252062692837797)
          ·
            rfl

theorem cell23_2863934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 14].length) (baseStart_2863934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863934 prefixEnd_2863934 := by exact prefixLift 2863934
  have htrace : WordTrace (prefixWord ++ tailWord_2863934) baseStart_2863934 baseEnd_2863934 := by
    simpa [prefixWord, tailWord_2863934, baseEnd_2863934] using wordTrace_append hprefix tailTrace_2863934
  have hstable : (prefixWord ++ tailWord_2863934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863934).length < 2 ^ (prefixWord ++ tailWord_2863934).sum := by decide
  have hdescent : baseEnd_2863934 < baseStart_2863934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2863961 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_2863961 : Nat := 118140960795 + 2863961 * 2 ^ 59
def prefixEnd_2863961 : Nat := 4983230072969 + 3 ^ 40 * 2863961 * 2
def baseEnd_2863961 : Nat := 1470588568731374473116389

theorem tailTrace_2863961 : CollatzResearch.WordTrace tailWord_2863961 prefixEnd_2863961 1470588568731374473116389 := by
  unfold tailWord_2863961
  simp only [CollatzResearch.WordTrace]
  refine ⟨104457239177365897442631737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69638159451577264961754491 104457239177365897442631737)
  ·
    refine ⟨78342929383024423081973803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104457239177365897442631737 78342929383024423081973803)
    ·
      refine ⟨117514394074536634622960705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78342929383024423081973803 117514394074536634622960705)
      ·
        refine ⟨88135795555902475967220529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117514394074536634622960705 88135795555902475967220529)
        ·
          refine ⟨66101846666926856975415397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88135795555902475967220529 66101846666926856975415397)
          ·
            refine ⟨12394096250048785682890387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66101846666926856975415397 12394096250048785682890387)
            ·
              refine ⟨18591144375073178524335581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394096250048785682890387 18591144375073178524335581)
              ·
                refine ⟨6971679140652441946625843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18591144375073178524335581 6971679140652441946625843)
                ·
                  refine ⟨10457518710978662919938765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971679140652441946625843 10457518710978662919938765)
                  ·
                    refine ⟨3921569516616998594977037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10457518710978662919938765 3921569516616998594977037)
                    ·
                      refine ⟨1470588568731374473116389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921569516616998594977037 1470588568731374473116389)
                      ·
                        rfl

theorem cell23_2863961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_2863961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2863961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2863961 prefixEnd_2863961 := by exact prefixLift 2863961
  have htrace : WordTrace (prefixWord ++ tailWord_2863961) baseStart_2863961 baseEnd_2863961 := by
    simpa [prefixWord, tailWord_2863961, baseEnd_2863961] using wordTrace_append hprefix tailTrace_2863961
  have hstable : (prefixWord ++ tailWord_2863961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2863961).length < 2 ^ (prefixWord ++ tailWord_2863961).sum := by decide
  have hdescent : baseEnd_2863961 < baseStart_2863961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2863961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864051 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3]
def baseStart_2864051 : Nat := 118140960795 + 2864051 * 2 ^ 59
def prefixEnd_2864051 : Nat := 4983230072969 + 3 ^ 40 * 2864051 * 2
def baseEnd_2864051 : Nat := 1470634781990279120990975

theorem tailTrace_2864051 : CollatzResearch.WordTrace tailWord_2864051 prefixEnd_2864051 1470634781990279120990975 := by
  unfold tailWord_2864051
  simp only [CollatzResearch.WordTrace]
  refine ⟨104460521747039842813408007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69640347831359895208938671 104460521747039842813408007)
  ·
    refine ⟨156690782620559764220112011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104460521747039842813408007 156690782620559764220112011)
    ·
      refine ⟨235036173930839646330168017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156690782620559764220112011 235036173930839646330168017)
      ·
        refine ⟨176277130448129734747626013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235036173930839646330168017 176277130448129734747626013)
        ·
          refine ⟨66103923918048650530359755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176277130448129734747626013 66103923918048650530359755)
          ·
            refine ⟨99155885877072975795539633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66103923918048650530359755 99155885877072975795539633)
            ·
              refine ⟨74366914407804731846654725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99155885877072975795539633 74366914407804731846654725)
              ·
                refine ⟨13943796451463387221247761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74366914407804731846654725 13943796451463387221247761)
                ·
                  refine ⟨10457847338597540415935821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13943796451463387221247761 10457847338597540415935821)
                  ·
                    refine ⟨3921692751974077655975933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10457847338597540415935821 3921692751974077655975933)
                    ·
                      refine ⟨1470634781990279120990975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921692751974077655975933 1470634781990279120990975)
                      ·
                        rfl

theorem cell23_2864051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_2864051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864051 prefixEnd_2864051 := by exact prefixLift 2864051
  have htrace : WordTrace (prefixWord ++ tailWord_2864051) baseStart_2864051 baseEnd_2864051 := by
    simpa [prefixWord, tailWord_2864051, baseEnd_2864051] using wordTrace_append hprefix tailTrace_2864051
  have hstable : (prefixWord ++ tailWord_2864051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864051).length < 2 ^ (prefixWord ++ tailWord_2864051).sum := by decide
  have hdescent : baseEnd_2864051 < baseStart_2864051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864088 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_2864088 : Nat := 118140960795 + 2864088 * 2 ^ 59
def prefixEnd_2864088 : Nat := 4983230072969 + 3 ^ 40 * 2864088 * 2
def baseEnd_2864088 : Nat := 490217926924831825409435

theorem tailTrace_2864088 : CollatzResearch.WordTrace tailWord_2864088 prefixEnd_2864088 490217926924831825409435 := by
  unfold tailWord_2864088
  simp only [CollatzResearch.WordTrace]
  refine ⟨52230935623952899066252459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69641247498603865421669945 52230935623952899066252459)
  ·
    refine ⟨78346403435929348599378689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52230935623952899066252459 78346403435929348599378689)
    ·
      refine ⟨58759802576947011449534017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78346403435929348599378689 58759802576947011449534017)
      ·
        refine ⟨44069851932710258587150513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58759802576947011449534017 44069851932710258587150513)
        ·
          refine ⟨33052388949532693940362885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44069851932710258587150513 33052388949532693940362885)
          ·
            refine ⟨6197322928037380113818041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33052388949532693940362885 6197322928037380113818041)
            ·
              refine ⟨4647992196028035085363531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197322928037380113818041 4647992196028035085363531)
              ·
                refine ⟨6971988294042052628045297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647992196028035085363531 6971988294042052628045297)
                ·
                  refine ⟨5228991220531539471033973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971988294042052628045297 5228991220531539471033973)
                  ·
                    refine ⟨490217926924831825409435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5228991220531539471033973 490217926924831825409435)
                    ·
                      rfl

theorem cell23_2864088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_2864088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864088 prefixEnd_2864088 := by exact prefixLift 2864088
  have htrace : WordTrace (prefixWord ++ tailWord_2864088) baseStart_2864088 baseEnd_2864088 := by
    simpa [prefixWord, tailWord_2864088, baseEnd_2864088] using wordTrace_append hprefix tailTrace_2864088
  have hstable : (prefixWord ++ tailWord_2864088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864088).length < 2 ^ (prefixWord ++ tailWord_2864088).sum := by decide
  have hdescent : baseEnd_2864088 < baseStart_2864088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864152 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 1, 4]
def baseStart_2864152 : Nat := 118140960795 + 2864152 * 2 ^ 59
def prefixEnd_2864152 : Nat := 4983230072969 + 3 ^ 40 * 2864152 * 2
def baseEnd_2864152 : Nat := 490228881178794408609337

theorem tailTrace_2864152 : CollatzResearch.WordTrace tailWord_2864152 prefixEnd_2864152 490228881178794408609337 := by
  unfold tailWord_2864152
  simp only [CollatzResearch.WordTrace]
  refine ⟨52232102759836968531417355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69642803679782624708556473 52232102759836968531417355)
  ·
    refine ⟨78348154139755452797126033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52232102759836968531417355 78348154139755452797126033)
    ·
      refine ⟨58761115604816589597844525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78348154139755452797126033 58761115604816589597844525)
      ·
        refine ⟨22035418351806221099191697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58761115604816589597844525 22035418351806221099191697)
        ·
          refine ⟨16526563763854665824393773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22035418351806221099191697 16526563763854665824393773)
          ·
            refine ⟨6197461411445499684147665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16526563763854665824393773 6197461411445499684147665)
            ·
              refine ⟨4648096058584124763110749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197461411445499684147665 4648096058584124763110749)
              ·
                refine ⟨1743036021969046786166531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4648096058584124763110749 1743036021969046786166531)
                ·
                  refine ⟨2614554032953570179249797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743036021969046786166531 2614554032953570179249797)
                  ·
                    refine ⟨490228881178794408609337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2614554032953570179249797 490228881178794408609337)
                    ·
                      rfl

theorem cell23_2864152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_2864152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864152 prefixEnd_2864152 := by exact prefixLift 2864152
  have htrace : WordTrace (prefixWord ++ tailWord_2864152) baseStart_2864152 baseEnd_2864152 := by
    simpa [prefixWord, tailWord_2864152, baseEnd_2864152] using wordTrace_append hprefix tailTrace_2864152
  have hstable : (prefixWord ++ tailWord_2864152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864152).length < 2 ^ (prefixWord ++ tailWord_2864152).sum := by decide
  have hdescent : baseEnd_2864152 < baseStart_2864152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864182 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2864182 : Nat := 118140960795 + 2864182 * 2 ^ 59
def prefixEnd_2864182 : Nat := 4983230072969 + 3 ^ 40 * 2864182 * 2
def baseEnd_2864182 : Nat := 163411338661779789828097

theorem tailTrace_2864182 : CollatzResearch.WordTrace tailWord_2864182 prefixEnd_2864182 163411338661779789828097 := by
  unfold tailWord_2864182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529081231847828261651675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69643533139710168124284533 6529081231847828261651675)
  ·
    refine ⟨9793621847771742392477513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6529081231847828261651675 9793621847771742392477513)
    ·
      refine ⟨7345216385828806794358135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9793621847771742392477513 7345216385828806794358135)
      ·
        refine ⟨11017824578743210191537203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345216385828806794358135 11017824578743210191537203)
        ·
          refine ⟨16526736868114815287305805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11017824578743210191537203 16526736868114815287305805)
          ·
            refine ⟨6197526325543055732739677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16526736868114815287305805 6197526325543055732739677)
            ·
              refine ⟨2324072372078645899777379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6197526325543055732739677 2324072372078645899777379)
              ·
                refine ⟨3486108558117968849666069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324072372078645899777379 3486108558117968849666069)
                ·
                  refine ⟨163411338661779789828097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3486108558117968849666069 163411338661779789828097)
                  ·
                    rfl

theorem cell23_2864182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2864182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864182 prefixEnd_2864182 := by exact prefixLift 2864182
  have htrace : WordTrace (prefixWord ++ tailWord_2864182) baseStart_2864182 baseEnd_2864182 := by
    simpa [prefixWord, tailWord_2864182, baseEnd_2864182] using wordTrace_append hprefix tailTrace_2864182
  have hstable : (prefixWord ++ tailWord_2864182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864182).length < 2 ^ (prefixWord ++ tailWord_2864182).sum := by decide
  have hdescent : baseEnd_2864182 < baseStart_2864182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864185 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2864185 : Nat := 118140960795 + 2864185 * 2 ^ 59
def prefixEnd_2864185 : Nat := 4983230072969 + 3 ^ 40 * 2864185 * 2
def baseEnd_2864185 : Nat := 1470703588397981596715359

theorem tailTrace_2864185 : CollatzResearch.WordTrace tailWord_2864185 prefixEnd_2864185 1470703588397981596715359 := by
  unfold tailWord_2864185
  simp only [CollatzResearch.WordTrace]
  refine ⟨104465409128554383698786009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69643606085702922465857339 104465409128554383698786009)
  ·
    refine ⟨78349056846415787774089507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104465409128554383698786009 78349056846415787774089507)
    ·
      refine ⟨117523585269623681661134261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78349056846415787774089507 117523585269623681661134261)
      ·
        refine ⟨11017836119027220155731337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117523585269623681661134261 11017836119027220155731337)
        ·
          refine ⟨8263377089270415116798503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11017836119027220155731337 8263377089270415116798503)
          ·
            refine ⟨12395065633905622675197755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263377089270415116798503 12395065633905622675197755)
            ·
              refine ⟨18592598450858434012796633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395065633905622675197755 18592598450858434012796633)
              ·
                refine ⟨13944448838143825509597475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18592598450858434012796633 13944448838143825509597475)
                ·
                  refine ⟨20916673257215738264396213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13944448838143825509597475 20916673257215738264396213)
                  ·
                    refine ⟨1960938117863975462287145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20916673257215738264396213 1960938117863975462287145)
                    ·
                      refine ⟨1470703588397981596715359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1960938117863975462287145 1470703588397981596715359)
                      ·
                        rfl

theorem cell23_2864185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2864185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864185 prefixEnd_2864185 := by exact prefixLift 2864185
  have htrace : WordTrace (prefixWord ++ tailWord_2864185) baseStart_2864185 baseEnd_2864185 := by
    simpa [prefixWord, tailWord_2864185, baseEnd_2864185] using wordTrace_append hprefix tailTrace_2864185
  have hstable : (prefixWord ++ tailWord_2864185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864185).length < 2 ^ (prefixWord ++ tailWord_2864185).sum := by decide
  have hdescent : baseEnd_2864185 < baseStart_2864185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864211 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_2864211 : Nat := 118140960795 + 2864211 * 2 ^ 59
def prefixEnd_2864211 : Nat := 4983230072969 + 3 ^ 40 * 2864211 * 2
def baseEnd_2864211 : Nat := 1470716938894998494990239

theorem tailTrace_2864211 : CollatzResearch.WordTrace tailWord_2864211 prefixEnd_2864211 1470716938894998494990239 := by
  unfold tailWord_2864211
  simp only [CollatzResearch.WordTrace]
  refine ⟨104466357426460190139232487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69644238284306793426154991 104466357426460190139232487)
  ·
    refine ⟨156699536139690285208848731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104466357426460190139232487 156699536139690285208848731)
    ·
      refine ⟨235049304209535427813273097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156699536139690285208848731 235049304209535427813273097)
      ·
        refine ⟨176286978157151570859954823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235049304209535427813273097 176286978157151570859954823)
        ·
          refine ⟨264430467235727356289932235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176286978157151570859954823 264430467235727356289932235)
          ·
            refine ⟨396645700853591034434898353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264430467235727356289932235 396645700853591034434898353)
            ·
              refine ⟨297484275640193275826173765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396645700853591034434898353 297484275640193275826173765)
              ·
                refine ⟨55778301682536239217407581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297484275640193275826173765 55778301682536239217407581)
                ·
                  refine ⟨20916863130951089706527843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55778301682536239217407581 20916863130951089706527843)
                  ·
                    refine ⟨31375294696426634559791765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20916863130951089706527843 31375294696426634559791765)
                    ·
                      refine ⟨1470716938894998494990239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31375294696426634559791765 1470716938894998494990239)
                      ·
                        rfl

theorem cell23_2864211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_2864211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864211 prefixEnd_2864211 := by exact prefixLift 2864211
  have htrace : WordTrace (prefixWord ++ tailWord_2864211) baseStart_2864211 baseEnd_2864211 := by
    simpa [prefixWord, tailWord_2864211, baseEnd_2864211] using wordTrace_append hprefix tailTrace_2864211
  have hstable : (prefixWord ++ tailWord_2864211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864211).length < 2 ^ (prefixWord ++ tailWord_2864211).sum := by decide
  have hdescent : baseEnd_2864211 < baseStart_2864211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864238 : List Nat := [4, 1, 2, 2, 1, 2, 1, 10]
def baseStart_2864238 : Nat := 118140960795 + 2864238 * 2 ^ 59
def prefixEnd_2864238 : Nat := 4983230072969 + 3 ^ 40 * 2864238 * 2
def baseEnd_2864238 : Nat := 54471511217506292198245

theorem tailTrace_2864238 : CollatzResearch.WordTrace tailWord_2864238 prefixEnd_2864238 54471511217506292198245 := by
  unfold tailWord_2864238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13058417774670296718808171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69644894798241582500310245 13058417774670296718808171)
  ·
    refine ⟨19587626662005445078212257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13058417774670296718808171 19587626662005445078212257)
    ·
      refine ⟨14690719996504083808659193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19587626662005445078212257 14690719996504083808659193)
      ·
        refine ⟨11018039997378062856494395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14690719996504083808659193 11018039997378062856494395)
        ·
          refine ⟨16527059996067094284741593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11018039997378062856494395 16527059996067094284741593)
          ·
            refine ⟨12395294997050320713556195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16527059996067094284741593 12395294997050320713556195)
            ·
              refine ⟨18592942495575481070334293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395294997050320713556195 18592942495575481070334293)
              ·
                refine ⟨54471511217506292198245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18592942495575481070334293 54471511217506292198245)
                ·
                  rfl

theorem cell23_2864238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_2864238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864238 prefixEnd_2864238 := by exact prefixLift 2864238
  have htrace : WordTrace (prefixWord ++ tailWord_2864238) baseStart_2864238 baseEnd_2864238 := by
    simpa [prefixWord, tailWord_2864238, baseEnd_2864238] using wordTrace_append hprefix tailTrace_2864238
  have hstable : (prefixWord ++ tailWord_2864238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864238).length < 2 ^ (prefixWord ++ tailWord_2864238).sum := by decide
  have hdescent : baseEnd_2864238 < baseStart_2864238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864249 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 1, 1, 4]
def baseStart_2864249 : Nat := 118140960795 + 2864249 * 2 ^ 59
def prefixEnd_2864249 : Nat := 4983230072969 + 3 ^ 40 * 2864249 * 2
def baseEnd_2864249 : Nat := 1470736451159869346315065

theorem tailTrace_2864249 : CollatzResearch.WordTrace tailWord_2864249 prefixEnd_2864249 1470736451159869346315065 := by
  unfold tailWord_2864249
  simp only [CollatzResearch.WordTrace]
  refine ⟨104467743400322522629115801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69645162266881681752743867 104467743400322522629115801)
  ·
    refine ⟨78350807550241891971836851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104467743400322522629115801 78350807550241891971836851)
    ·
      refine ⟨117526211325362837957755277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78350807550241891971836851 117526211325362837957755277)
      ·
        refine ⟨44072329247011064234158229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117526211325362837957755277 44072329247011064234158229)
        ·
          refine ⟨2065890433453643635976167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44072329247011064234158229 2065890433453643635976167)
          ·
            refine ⟨3098835650180465453964251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065890433453643635976167 3098835650180465453964251)
            ·
              refine ⟨4648253475270698180946377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098835650180465453964251 4648253475270698180946377)
              ·
                refine ⟨3486190106453023635709783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648253475270698180946377 3486190106453023635709783)
                ·
                  refine ⟨5229285159679535453564675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486190106453023635709783 5229285159679535453564675)
                  ·
                    refine ⟨7843927739519303180347013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229285159679535453564675 7843927739519303180347013)
                    ·
                      refine ⟨1470736451159869346315065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7843927739519303180347013 1470736451159869346315065)
                      ·
                        rfl

theorem cell23_2864249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_2864249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864249 prefixEnd_2864249 := by exact prefixLift 2864249
  have htrace : WordTrace (prefixWord ++ tailWord_2864249) baseStart_2864249 baseEnd_2864249 := by
    simpa [prefixWord, tailWord_2864249, baseEnd_2864249] using wordTrace_append hprefix tailTrace_2864249
  have hstable : (prefixWord ++ tailWord_2864249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864249).length < 2 ^ (prefixWord ++ tailWord_2864249).sum := by decide
  have hdescent : baseEnd_2864249 < baseStart_2864249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864265 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_2864265 : Nat := 118140960795 + 2864265 * 2 ^ 59
def prefixEnd_2864265 : Nat := 4983230072969 + 3 ^ 40 * 2864265 * 2
def baseEnd_2864265 : Nat := 1470744666850341283714991

theorem tailTrace_2864265 : CollatzResearch.WordTrace tailWord_2864265 prefixEnd_2864265 1470744666850341283714991 := by
  unfold tailWord_2864265
  simp only [CollatzResearch.WordTrace]
  refine ⟨104468326968264557361698249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69645551312176371574465499 104468326968264557361698249)
  ·
    refine ⟨78351245226198418021273687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104468326968264557361698249 78351245226198418021273687)
    ·
      refine ⟨117526867839297627031910531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78351245226198418021273687 117526867839297627031910531)
      ·
        refine ⟨176290301758946440547865797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117526867839297627031910531 176290301758946440547865797)
        ·
          refine ⟨33054431579802457602724837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176290301758946440547865797 33054431579802457602724837)
          ·
            refine ⟨6197705921212960800510907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33054431579802457602724837 6197705921212960800510907)
            ·
              refine ⟨9296558881819441200766361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6197705921212960800510907 9296558881819441200766361)
              ·
                refine ⟨6972419161364580900574771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9296558881819441200766361 6972419161364580900574771)
                ·
                  refine ⟨10458628742046871350862157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6972419161364580900574771 10458628742046871350862157)
                  ·
                    refine ⟨3921985778267576756573309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10458628742046871350862157 3921985778267576756573309)
                    ·
                      refine ⟨1470744666850341283714991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3921985778267576756573309 1470744666850341283714991)
                      ·
                        rfl

theorem cell23_2864265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_2864265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864265 prefixEnd_2864265 := by exact prefixLift 2864265
  have htrace : WordTrace (prefixWord ++ tailWord_2864265) baseStart_2864265 baseEnd_2864265 := by
    simpa [prefixWord, tailWord_2864265, baseEnd_2864265] using wordTrace_append hprefix tailTrace_2864265
  have hstable : (prefixWord ++ tailWord_2864265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864265).length < 2 ^ (prefixWord ++ tailWord_2864265).sum := by decide
  have hdescent : baseEnd_2864265 < baseStart_2864265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864288 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2864288 : Nat := 118140960795 + 2864288 * 2 ^ 59
def prefixEnd_2864288 : Nat := 4983230072969 + 3 ^ 40 * 2864288 * 2
def baseEnd_2864288 : Nat := 1470756476905394693727385

theorem tailTrace_2864288 : CollatzResearch.WordTrace tailWord_2864288 prefixEnd_2864288 1470756476905394693727385 := by
  unfold tailWord_2864288
  simp only [CollatzResearch.WordTrace]
  refine ⟨52234582923590616144892759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69646110564787488193190345 52234582923590616144892759)
  ·
    refine ⟨78351874385385924217339139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52234582923590616144892759 78351874385385924217339139)
    ·
      refine ⟨117527811578078886326008709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78351874385385924217339139 117527811578078886326008709)
      ·
        refine ⟨22036464670889791186126633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117527811578078886326008709 22036464670889791186126633)
        ·
          refine ⟨16527348503167343389594975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22036464670889791186126633 16527348503167343389594975)
          ·
            refine ⟨24791022754751015084392463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16527348503167343389594975 24791022754751015084392463)
            ·
              refine ⟨37186534132126522626588695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24791022754751015084392463 37186534132126522626588695)
              ·
                refine ⟨55779801198189783939883043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37186534132126522626588695 55779801198189783939883043)
                ·
                  refine ⟨83669701797284675909824565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55779801198189783939883043 83669701797284675909824565)
                  ·
                    refine ⟨7844034543495438366546053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83669701797284675909824565 7844034543495438366546053)
                    ·
                      refine ⟨1470756476905394693727385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7844034543495438366546053 1470756476905394693727385)
                      ·
                        rfl

theorem cell23_2864288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2864288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864288 prefixEnd_2864288 := by exact prefixLift 2864288
  have htrace : WordTrace (prefixWord ++ tailWord_2864288) baseStart_2864288 baseEnd_2864288 := by
    simpa [prefixWord, tailWord_2864288, baseEnd_2864288] using wordTrace_append hprefix tailTrace_2864288
  have hstable : (prefixWord ++ tailWord_2864288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864288).length < 2 ^ (prefixWord ++ tailWord_2864288).sum := by decide
  have hdescent : baseEnd_2864288 < baseStart_2864288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864292 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_2864292 : Nat := 118140960795 + 2864292 * 2 ^ 59
def prefixEnd_2864292 : Nat := 4983230072969 + 3 ^ 40 * 2864292 * 2
def baseEnd_2864292 : Nat := 1470758530828012678077367

theorem tailTrace_2864292 : CollatzResearch.WordTrace tailWord_2864292 prefixEnd_2864292 1470758530828012678077367 := by
  unfold tailWord_2864292
  simp only [CollatzResearch.WordTrace]
  refine ⟨52234655869583370486465565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69646207826111160648620753 52234655869583370486465565)
  ·
    refine ⟨19587995951093763932424587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52234655869583370486465565 19587995951093763932424587)
    ·
      refine ⟨29381993926640645898636881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19587995951093763932424587 29381993926640645898636881)
      ·
        refine ⟨22036495444980484423977661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29381993926640645898636881 22036495444980484423977661)
        ·
          refine ⟨8263685791867681658991623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22036495444980484423977661 8263685791867681658991623)
          ·
            refine ⟨12395528687801522488487435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263685791867681658991623 12395528687801522488487435)
            ·
              refine ⟨18593293031702283732731153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395528687801522488487435 18593293031702283732731153)
              ·
                refine ⟨13944969773776712799548365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18593293031702283732731153 13944969773776712799548365)
                ·
                  refine ⟨5229363665166267299830637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13944969773776712799548365 5229363665166267299830637)
                  ·
                    refine ⟨1961011374437350237436489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5229363665166267299830637 1961011374437350237436489)
                    ·
                      refine ⟨1470758530828012678077367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961011374437350237436489 1470758530828012678077367)
                      ·
                        rfl

theorem cell23_2864292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_2864292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864292 prefixEnd_2864292 := by exact prefixLift 2864292
  have htrace : WordTrace (prefixWord ++ tailWord_2864292) baseStart_2864292 baseEnd_2864292 := by
    simpa [prefixWord, tailWord_2864292, baseEnd_2864292] using wordTrace_append hprefix tailTrace_2864292
  have hstable : (prefixWord ++ tailWord_2864292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864292).length < 2 ^ (prefixWord ++ tailWord_2864292).sum := by decide
  have hdescent : baseEnd_2864292 < baseStart_2864292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864368 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_2864368 : Nat := 118140960795 + 2864368 * 2 ^ 59
def prefixEnd_2864368 : Nat := 4983230072969 + 3 ^ 40 * 2864368 * 2
def baseEnd_2864368 : Nat := 1470797555357754380727017

theorem tailTrace_2864368 : CollatzResearch.WordTrace tailWord_2864368 prefixEnd_2864368 1470797555357754380727017 := by
  unfold tailWord_2864368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52236041843445702976348879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69648055791260937301798505 52236041843445702976348879)
  ·
    refine ⟨78354062765168554464523319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52236041843445702976348879 78354062765168554464523319)
    ·
      refine ⟨117531094147752831696784979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78354062765168554464523319 117531094147752831696784979)
      ·
        refine ⟨176296641221629247545177469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117531094147752831696784979 176296641221629247545177469)
        ·
          refine ⟨66111240458110967829441551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176296641221629247545177469 66111240458110967829441551)
          ·
            refine ⟨99166860687166451744162327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66111240458110967829441551 99166860687166451744162327)
            ·
              refine ⟨148750291030749677616243491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99166860687166451744162327 148750291030749677616243491)
              ·
                refine ⟨223125436546124516424365237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148750291030749677616243491 223125436546124516424365237)
                ·
                  refine ⟨20918009676199173414784241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223125436546124516424365237 20918009676199173414784241)
                  ·
                    refine ⟨15688507257149380061088181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20918009676199173414784241 15688507257149380061088181)
                    ·
                      refine ⟨1470797555357754380727017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15688507257149380061088181 1470797555357754380727017)
                      ·
                        rfl

theorem cell23_2864368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_2864368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864368 prefixEnd_2864368 := by exact prefixLift 2864368
  have htrace : WordTrace (prefixWord ++ tailWord_2864368) baseStart_2864368 baseEnd_2864368 := by
    simpa [prefixWord, tailWord_2864368, baseEnd_2864368] using wordTrace_append hprefix tailTrace_2864368
  have hstable : (prefixWord ++ tailWord_2864368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864368).length < 2 ^ (prefixWord ++ tailWord_2864368).sum := by decide
  have hdescent : baseEnd_2864368 < baseStart_2864368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864392 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_2864392 : Nat := 118140960795 + 2864392 * 2 ^ 59
def prefixEnd_2864392 : Nat := 4983230072969 + 3 ^ 40 * 2864392 * 2
def baseEnd_2864392 : Nat := 490269959631154095608969

theorem tailTrace_2864392 : CollatzResearch.WordTrace tailWord_2864392 prefixEnd_2864392 490269959631154095608969 := by
  unfold tailWord_2864392
  simp only [CollatzResearch.WordTrace]
  refine ⟨52236479519402229025785715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69648639359202972034380953 52236479519402229025785715)
  ·
    refine ⟨78354719279103343538678573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52236479519402229025785715 78354719279103343538678573)
    ·
      refine ⟨29383019729663753827004465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78354719279103343538678573 29383019729663753827004465)
      ·
        refine ⟨22037264797247815370253349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29383019729663753827004465 22037264797247815370253349)
        ·
          refine ⟨4131987149483965381922503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22037264797247815370253349 4131987149483965381922503)
          ·
            refine ⟨6197980724225948072883755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131987149483965381922503 6197980724225948072883755)
            ·
              refine ⟨9296971086338922109325633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6197980724225948072883755 9296971086338922109325633)
              ·
                refine ⟨6972728314754191581994225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9296971086338922109325633 6972728314754191581994225)
                ·
                  refine ⟨5229546236065643686495669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972728314754191581994225 5229546236065643686495669)
                  ·
                    refine ⟨490269959631154095608969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5229546236065643686495669 490269959631154095608969)
                    ·
                      rfl

theorem cell23_2864392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_2864392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864392 prefixEnd_2864392 := by exact prefixLift 2864392
  have htrace : WordTrace (prefixWord ++ tailWord_2864392) baseStart_2864392 baseEnd_2864392 := by
    simpa [prefixWord, tailWord_2864392, baseEnd_2864392] using wordTrace_append hprefix tailTrace_2864392
  have hstable : (prefixWord ++ tailWord_2864392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864392).length < 2 ^ (prefixWord ++ tailWord_2864392).sum := by decide
  have hdescent : baseEnd_2864392 < baseStart_2864392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864395 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4]
def baseStart_2864395 : Nat := 118140960795 + 2864395 * 2 ^ 59
def prefixEnd_2864395 : Nat := 4983230072969 + 3 ^ 40 * 2864395 * 2
def baseEnd_2864395 : Nat := 1470811419335425775089393

theorem tailTrace_2864395 : CollatzResearch.WordTrace tailWord_2864395 prefixEnd_2864395 1470811419335425775089393 := by
  unfold tailWord_2864395
  simp only [CollatzResearch.WordTrace]
  refine ⟨104473068457793589563930639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69648712305195726375953759 104473068457793589563930639)
  ·
    refine ⟨156709602686690384345895959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104473068457793589563930639 156709602686690384345895959)
    ·
      refine ⟨235064404030035576518843939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156709602686690384345895959 235064404030035576518843939)
      ·
        refine ⟨352596606045053364778265909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235064404030035576518843939 352596606045053364778265909)
        ·
          refine ⟨33055931816723752947962429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352596606045053364778265909 33055931816723752947962429)
          ·
            refine ⟨12395974431271407355485911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33055931816723752947962429 12395974431271407355485911)
            ·
              refine ⟨18593961646907111033228867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395974431271407355485911 18593961646907111033228867)
              ·
                refine ⟨27890942470360666549843301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18593961646907111033228867 27890942470360666549843301)
                ·
                  refine ⟨5229551713192624978095619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27890942470360666549843301 5229551713192624978095619)
                  ·
                    refine ⟨7844327569788937467143429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229551713192624978095619 7844327569788937467143429)
                    ·
                      refine ⟨1470811419335425775089393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7844327569788937467143429 1470811419335425775089393)
                      ·
                        rfl

theorem cell23_2864395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4].length) (baseStart_2864395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864395 prefixEnd_2864395 := by exact prefixLift 2864395
  have htrace : WordTrace (prefixWord ++ tailWord_2864395) baseStart_2864395 baseEnd_2864395 := by
    simpa [prefixWord, tailWord_2864395, baseEnd_2864395] using wordTrace_append hprefix tailTrace_2864395
  have hstable : (prefixWord ++ tailWord_2864395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864395).length < 2 ^ (prefixWord ++ tailWord_2864395).sum := by decide
  have hdescent : baseEnd_2864395 < baseStart_2864395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864412 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2864412 : Nat := 118140960795 + 2864412 * 2 ^ 59
def prefixEnd_2864412 : Nat := 4983230072969 + 3 ^ 40 * 2864412 * 2
def baseEnd_2864412 : Nat := 1470820148506552208576815

theorem tailTrace_2864412 : CollatzResearch.WordTrace tailWord_2864412 prefixEnd_2864412 1470820148506552208576815 := by
  unfold tailWord_2864412
  simp only [CollatzResearch.WordTrace]
  refine ⟨52236844249366000733649745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69649125665821334311532993 52236844249366000733649745)
  ·
    refine ⟨39177633187024500550237309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52236844249366000733649745 39177633187024500550237309)
    ·
      refine ⟨14691612445134187706338991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39177633187024500550237309 14691612445134187706338991)
      ·
        refine ⟨22037418667701281559508487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14691612445134187706338991 22037418667701281559508487)
        ·
          refine ⟨33056128001551922339262731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22037418667701281559508487 33056128001551922339262731)
          ·
            refine ⟨49584192002327883508894097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33056128001551922339262731 49584192002327883508894097)
            ·
              refine ⟨37188144001745912631670573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49584192002327883508894097 37188144001745912631670573)
              ·
                refine ⟨13945554000654717236876465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37188144001745912631670573 13945554000654717236876465)
                ·
                  refine ⟨10459165500491037927657349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13945554000654717236876465 10459165500491037927657349)
                  ·
                    refine ⟨1961093531342069611435753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10459165500491037927657349 1961093531342069611435753)
                    ·
                      refine ⟨1470820148506552208576815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961093531342069611435753 1470820148506552208576815)
                      ·
                        rfl

theorem cell23_2864412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2864412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864412 prefixEnd_2864412 := by exact prefixLift 2864412
  have htrace : WordTrace (prefixWord ++ tailWord_2864412) baseStart_2864412 baseEnd_2864412 := by
    simpa [prefixWord, tailWord_2864412, baseEnd_2864412] using wordTrace_append hprefix tailTrace_2864412
  have hstable : (prefixWord ++ tailWord_2864412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864412).length < 2 ^ (prefixWord ++ tailWord_2864412).sum := by decide
  have hdescent : baseEnd_2864412 < baseStart_2864412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864429 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2864429 : Nat := 118140960795 + 2864429 * 2 ^ 59
def prefixEnd_2864429 : Nat := 4983230072969 + 3 ^ 40 * 2864429 * 2
def baseEnd_2864429 : Nat := 1470828877677678642064237

theorem tailTrace_2864429 : CollatzResearch.WordTrace tailWord_2864429 prefixEnd_2864429 1470828877677678642064237 := by
  unfold tailWord_2864429
  simp only [CollatzResearch.WordTrace]
  refine ⟨104474308539670413370668341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69649539026446942247112227 104474308539670413370668341)
  ·
    refine ⟨9794466425594101253500157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104474308539670413370668341 9794466425594101253500157)
    ·
      refine ⟨3672924909597787970062559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9794466425594101253500157 3672924909597787970062559)
      ·
        refine ⟨5509387364396681955093839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672924909597787970062559 5509387364396681955093839)
        ·
          refine ⟨8264081046595022932640759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509387364396681955093839 8264081046595022932640759)
          ·
            refine ⟨12396121569892534398961139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264081046595022932640759 12396121569892534398961139)
            ·
              refine ⟨18594182354838801598441709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12396121569892534398961139 18594182354838801598441709)
              ·
                refine ⟨6972818383064550599415641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18594182354838801598441709 6972818383064550599415641)
                ·
                  refine ⟨5229613787298412949561731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972818383064550599415641 5229613787298412949561731)
                  ·
                    refine ⟨7844420680947619424342597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229613787298412949561731 7844420680947619424342597)
                    ·
                      refine ⟨1470828877677678642064237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7844420680947619424342597 1470828877677678642064237)
                      ·
                        rfl

theorem cell23_2864429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2864429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864429 prefixEnd_2864429 := by exact prefixLift 2864429
  have htrace : WordTrace (prefixWord ++ tailWord_2864429) baseStart_2864429 baseEnd_2864429 := by
    simpa [prefixWord, tailWord_2864429, baseEnd_2864429] using wordTrace_append hprefix tailTrace_2864429
  have hstable : (prefixWord ++ tailWord_2864429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864429).length < 2 ^ (prefixWord ++ tailWord_2864429).sum := by decide
  have hdescent : baseEnd_2864429 < baseStart_2864429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864432 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_2864432 : Nat := 118140960795 + 2864432 * 2 ^ 59
def prefixEnd_2864432 : Nat := 4983230072969 + 3 ^ 40 * 2864432 * 2
def baseEnd_2864432 : Nat := 1470830418119642130326723

theorem tailTrace_2864432 : CollatzResearch.WordTrace tailWord_2864432 prefixEnd_2864432 1470830418119642130326723 := by
  unfold tailWord_2864432
  simp only [CollatzResearch.WordTrace]
  refine ⟨52237208979329772441513775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69649611972439696588685033 52237208979329772441513775)
  ·
    refine ⟨78355813468994658662270663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52237208979329772441513775 78355813468994658662270663)
    ·
      refine ⟨117533720203491987993405995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78355813468994658662270663 117533720203491987993405995)
      ·
        refine ⟨176300580305237981990108993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117533720203491987993405995 176300580305237981990108993)
        ·
          refine ⟨132225435228928486492581745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176300580305237981990108993 132225435228928486492581745)
          ·
            refine ⟨99169076421696364869436309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132225435228928486492581745 99169076421696364869436309)
            ·
              refine ⟨4648550457267017103254827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99169076421696364869436309 4648550457267017103254827)
              ·
                refine ⟨6972825685900525654882241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648550457267017103254827 6972825685900525654882241)
                ·
                  refine ⟨5229619264425394241161681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972825685900525654882241 5229619264425394241161681)
                  ·
                    refine ⟨3922214448319045680871261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229619264425394241161681 3922214448319045680871261)
                    ·
                      refine ⟨1470830418119642130326723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922214448319045680871261 1470830418119642130326723)
                      ·
                        rfl

theorem cell23_2864432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_2864432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864432 prefixEnd_2864432 := by exact prefixLift 2864432
  have htrace : WordTrace (prefixWord ++ tailWord_2864432) baseStart_2864432 baseEnd_2864432 := by
    simpa [prefixWord, tailWord_2864432, baseEnd_2864432] using wordTrace_append hprefix tailTrace_2864432
  have hstable : (prefixWord ++ tailWord_2864432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864432).length < 2 ^ (prefixWord ++ tailWord_2864432).sum := by decide
  have hdescent : baseEnd_2864432 < baseStart_2864432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864449 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2864449 : Nat := 118140960795 + 2864449 * 2 ^ 59
def prefixEnd_2864449 : Nat := 4983230072969 + 3 ^ 40 * 2864449 * 2
def baseEnd_2864449 : Nat := 1470839147290768563814145

theorem tailTrace_2864449 : CollatzResearch.WordTrace tailWord_2864449 prefixEnd_2864449 1470839147290768563814145 := by
  unfold tailWord_2864449
  simp only [CollatzResearch.WordTrace]
  refine ⟨104475037999597956786396401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69650025333065304524264267 104475037999597956786396401)
  ·
    refine ⟨78356278499698467589797301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104475037999597956786396401 78356278499698467589797301)
    ·
      refine ⟨7345901109346731336543497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78356278499698467589797301 7345901109346731336543497)
      ·
        refine ⟨5509425832010048502407623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7345901109346731336543497 5509425832010048502407623)
        ·
          refine ⟨8264138748015072753611435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509425832010048502407623 8264138748015072753611435)
          ·
            refine ⟨12396208122022609130417153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264138748015072753611435 12396208122022609130417153)
            ·
              refine ⟨9297156091516956847812865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12396208122022609130417153 9297156091516956847812865)
              ·
                refine ⟨6972867068637717635859649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297156091516956847812865 6972867068637717635859649)
                ·
                  refine ⟨5229650301478288226894737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972867068637717635859649 5229650301478288226894737)
                  ·
                    refine ⟨3922237726108716170171053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229650301478288226894737 3922237726108716170171053)
                    ·
                      refine ⟨1470839147290768563814145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922237726108716170171053 1470839147290768563814145)
                      ·
                        rfl

theorem cell23_2864449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2864449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864449 prefixEnd_2864449 := by exact prefixLift 2864449
  have htrace : WordTrace (prefixWord ++ tailWord_2864449) baseStart_2864449 baseEnd_2864449 := by
    simpa [prefixWord, tailWord_2864449, baseEnd_2864449] using wordTrace_append hprefix tailTrace_2864449
  have hstable : (prefixWord ++ tailWord_2864449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864449).length < 2 ^ (prefixWord ++ tailWord_2864449).sum := by decide
  have hdescent : baseEnd_2864449 < baseStart_2864449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864465 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_2864465 : Nat := 118140960795 + 2864465 * 2 ^ 59
def prefixEnd_2864465 : Nat := 4983230072969 + 3 ^ 40 * 2864465 * 2
def baseEnd_2864465 : Nat := 490282454327080167071357

theorem tailTrace_2864465 : CollatzResearch.WordTrace tailWord_2864465 prefixEnd_2864465 490282454327080167071357 := by
  unfold tailWord_2864465
  simp only [CollatzResearch.WordTrace]
  refine ⟨104475621567539991518978849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69650414378359994345985899 104475621567539991518978849)
  ·
    refine ⟨78356716175654993639234137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104475621567539991518978849 78356716175654993639234137)
    ·
      refine ⟨58767537131741245229425603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78356716175654993639234137 58767537131741245229425603)
      ·
        refine ⟨88151305697611867844138405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58767537131741245229425603 88151305697611867844138405)
        ·
          refine ⟨16528369818302225220775951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88151305697611867844138405 16528369818302225220775951)
          ·
            refine ⟨24792554727453337831163927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16528369818302225220775951 24792554727453337831163927)
            ·
              refine ⟨37188832091180006746745891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24792554727453337831163927 37188832091180006746745891)
              ·
                refine ⟨55783248136770010120118837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37188832091180006746745891 55783248136770010120118837)
                ·
                  refine ⟨5229679512822188448761141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55783248136770010120118837 5229679512822188448761141)
                  ·
                    refine ⟨490282454327080167071357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5229679512822188448761141 490282454327080167071357)
                    ·
                      rfl

theorem cell23_2864465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_2864465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864465 prefixEnd_2864465 := by exact prefixLift 2864465
  have htrace : WordTrace (prefixWord ++ tailWord_2864465) baseStart_2864465 baseEnd_2864465 := by
    simpa [prefixWord, tailWord_2864465, baseEnd_2864465] using wordTrace_append hprefix tailTrace_2864465
  have hstable : (prefixWord ++ tailWord_2864465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864465).length < 2 ^ (prefixWord ++ tailWord_2864465).sum := by decide
  have hdescent : baseEnd_2864465 < baseStart_2864465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864472 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_2864472 : Nat := 118140960795 + 2864472 * 2 ^ 59
def prefixEnd_2864472 : Nat := 4983230072969 + 3 ^ 40 * 2864472 * 2
def baseEnd_2864472 : Nat := 1470850957345821973826539

theorem tailTrace_2864472 : CollatzResearch.WordTrace tailWord_2864472 prefixEnd_2864472 1470850957345821973826539 := by
  unfold tailWord_2864472
  simp only [CollatzResearch.WordTrace]
  refine ⟨52237938439257315857241835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69650584585676421142989113 52237938439257315857241835)
  ·
    refine ⟨78356907658885973785862753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52237938439257315857241835 78356907658885973785862753)
    ·
      refine ⟨58767680744164480339397065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78356907658885973785862753 58767680744164480339397065)
      ·
        refine ⟨44075760558123360254547799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58767680744164480339397065 44075760558123360254547799)
        ·
          refine ⟨66113640837185040381821699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44075760558123360254547799 66113640837185040381821699)
          ·
            refine ⟨99170461255777560572732549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66113640837185040381821699 99170461255777560572732549)
            ·
              refine ⟨18594461485458292607387353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99170461255777560572732549 18594461485458292607387353)
              ·
                refine ⟨13945846114093719455540515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18594461485458292607387353 13945846114093719455540515)
                ·
                  refine ⟨20918769171140579183310773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13945846114093719455540515 20918769171140579183310773)
                  ·
                    refine ⟨1961134609794429298435385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20918769171140579183310773 1961134609794429298435385)
                    ·
                      refine ⟨1470850957345821973826539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961134609794429298435385 1470850957345821973826539)
                      ·
                        rfl

theorem cell23_2864472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_2864472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864472 prefixEnd_2864472 := by exact prefixLift 2864472
  have htrace : WordTrace (prefixWord ++ tailWord_2864472) baseStart_2864472 baseEnd_2864472 := by
    simpa [prefixWord, tailWord_2864472, baseEnd_2864472] using wordTrace_append hprefix tailTrace_2864472
  have hstable : (prefixWord ++ tailWord_2864472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864472).length < 2 ^ (prefixWord ++ tailWord_2864472).sum := by decide
  have hdescent : baseEnd_2864472 < baseStart_2864472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864482 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2864482 : Nat := 118140960795 + 2864482 * 2 ^ 59
def prefixEnd_2864482 : Nat := 4983230072969 + 3 ^ 40 * 2864482 * 2
def baseEnd_2864482 : Nat := 490285364050788978233831

theorem tailTrace_2864482 : CollatzResearch.WordTrace tailWord_2864482 prefixEnd_2864482 490285364050788978233831 := by
  unfold tailWord_2864482
  simp only [CollatzResearch.WordTrace]
  refine ⟨26119060402119600855586925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69650827738985602281565133 26119060402119600855586925)
  ·
    refine ⟨9794647650794850320845097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26119060402119600855586925 9794647650794850320845097)
    ·
      refine ⟨7345985738096137740633823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9794647650794850320845097 7345985738096137740633823)
      ·
        refine ⟨11018978607144206610950735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345985738096137740633823 11018978607144206610950735)
        ·
          refine ⟨16528467910716309916426103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11018978607144206610950735 16528467910716309916426103)
          ·
            refine ⟨24792701866074464874639155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16528467910716309916426103 24792701866074464874639155)
            ·
              refine ⟨37189052799111697311958733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24792701866074464874639155 37189052799111697311958733)
              ·
                refine ⟨13945894799666886491984525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37189052799111697311958733 13945894799666886491984525)
                ·
                  refine ⟨5229710549875082434494197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13945894799666886491984525 5229710549875082434494197)
                  ·
                    refine ⟨490285364050788978233831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5229710549875082434494197 490285364050788978233831)
                    ·
                      rfl

theorem cell23_2864482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2864482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864482 prefixEnd_2864482 := by exact prefixLift 2864482
  have htrace : WordTrace (prefixWord ++ tailWord_2864482) baseStart_2864482 baseEnd_2864482 := by
    simpa [prefixWord, tailWord_2864482, baseEnd_2864482] using wordTrace_append hprefix tailTrace_2864482
  have hstable : (prefixWord ++ tailWord_2864482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864482).length < 2 ^ (prefixWord ++ tailWord_2864482).sum := by decide
  have hdescent : baseEnd_2864482 < baseStart_2864482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864495 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 1, 6]
def baseStart_2864495 : Nat := 118140960795 + 2864495 * 2 ^ 59
def prefixEnd_2864495 : Nat := 4983230072969 + 3 ^ 40 * 2864495 * 2
def baseEnd_2864495 : Nat := 490287589133625127946311

theorem tailTrace_2864495 : CollatzResearch.WordTrace tailWord_2864495 prefixEnd_2864495 490287589133625127946311 := by
  unfold tailWord_2864495
  simp only [CollatzResearch.WordTrace]
  refine ⟨104476715757431306642570939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69651143838287537761713959 104476715757431306642570939)
  ·
    refine ⟨156715073636146959963856409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104476715757431306642570939 156715073636146959963856409)
    ·
      refine ⟨117536305227110219972892307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156715073636146959963856409 117536305227110219972892307)
      ·
        refine ⟨176304457840665329959338461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117536305227110219972892307 176304457840665329959338461)
        ·
          refine ⟨66114171690249498734751923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176304457840665329959338461 66114171690249498734751923)
          ·
            refine ⟨99171257535374248102127885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66114171690249498734751923 99171257535374248102127885)
            ·
              refine ⟨37189221575765343038297957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99171257535374248102127885 37189221575765343038297957)
              ·
                refine ⟨6972979045456001819680867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37189221575765343038297957 6972979045456001819680867)
                ·
                  refine ⟨10459468568184002729521301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6972979045456001819680867 10459468568184002729521301)
                  ·
                    refine ⟨490287589133625127946311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10459468568184002729521301 490287589133625127946311)
                    ·
                      rfl

theorem cell23_2864495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_2864495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864495 prefixEnd_2864495 := by exact prefixLift 2864495
  have htrace : WordTrace (prefixWord ++ tailWord_2864495) baseStart_2864495 baseEnd_2864495 := by
    simpa [prefixWord, tailWord_2864495, baseEnd_2864495] using wordTrace_append hprefix tailTrace_2864495
  have hstable : (prefixWord ++ tailWord_2864495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864495).length < 2 ^ (prefixWord ++ tailWord_2864495).sum := by decide
  have hdescent : baseEnd_2864495 < baseStart_2864495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864496 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 1, 1, 3]
def baseStart_2864496 : Nat := 118140960795 + 2864496 * 2 ^ 59
def prefixEnd_2864496 : Nat := 4983230072969 + 3 ^ 40 * 2864496 * 2
def baseEnd_2864496 : Nat := 1470863280881529879926429

theorem tailTrace_2864496 : CollatzResearch.WordTrace tailWord_2864496 prefixEnd_2864496 1470863280881529879926429 := by
  unfold tailWord_2864496
  simp only [CollatzResearch.WordTrace]
  refine ⟨52238376115213841906678671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69651168153618455875571561 52238376115213841906678671)
  ·
    refine ⟨78357564172820762860018007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52238376115213841906678671 78357564172820762860018007)
    ·
      refine ⟨117536346259231144290027011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78357564172820762860018007 117536346259231144290027011)
      ·
        refine ⟨176304519388846716435040517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117536346259231144290027011 176304519388846716435040517)
        ·
          refine ⟨33057097385408759331570097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176304519388846716435040517 33057097385408759331570097)
          ·
            refine ⟨24792823039056569498677573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33057097385408759331570097 24792823039056569498677573)
            ·
              refine ⟨4648654319823106781002045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24792823039056569498677573 4648654319823106781002045)
              ·
                refine ⟨1743245369933665042875767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4648654319823106781002045 1743245369933665042875767)
                ·
                  refine ⟨2614868054900497564313651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743245369933665042875767 2614868054900497564313651)
                  ·
                    refine ⟨3922302082350746346470477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614868054900497564313651 3922302082350746346470477)
                    ·
                      refine ⟨1470863280881529879926429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922302082350746346470477 1470863280881529879926429)
                      ·
                        rfl

theorem cell23_2864496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 1, 3].length) (baseStart_2864496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864496 prefixEnd_2864496 := by exact prefixLift 2864496
  have htrace : WordTrace (prefixWord ++ tailWord_2864496) baseStart_2864496 baseEnd_2864496 := by
    simpa [prefixWord, tailWord_2864496, baseEnd_2864496] using wordTrace_append hprefix tailTrace_2864496
  have hstable : (prefixWord ++ tailWord_2864496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864496).length < 2 ^ (prefixWord ++ tailWord_2864496).sum := by decide
  have hdescent : baseEnd_2864496 < baseStart_2864496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864536 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2864536 : Nat := 118140960795 + 2864536 * 2 ^ 59
def prefixEnd_2864536 : Nat := 4983230072969 + 3 ^ 40 * 2864536 * 2
def baseEnd_2864536 : Nat := 1470883820107709723426245

theorem tailTrace_2864536 : CollatzResearch.WordTrace tailWord_2864536 prefixEnd_2864536 1470883820107709723426245 := by
  unfold tailWord_2864536
  simp only [CollatzResearch.WordTrace]
  refine ⟨52239105575141385322406731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69652140766855180429875641 52239105575141385322406731)
  ·
    refine ⟨78358658362712077983610097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52239105575141385322406731 78358658362712077983610097)
    ·
      refine ⟨58768993772034058487707573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78358658362712077983610097 58768993772034058487707573)
      ·
        refine ⟨5509593166128192983222585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58768993772034058487707573 5509593166128192983222585)
        ·
          refine ⟨4132194874596144737416939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5509593166128192983222585 4132194874596144737416939)
          ·
            refine ⟨6198292311894217106125409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132194874596144737416939 6198292311894217106125409)
            ·
              refine ⟨4648719233920662829594057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6198292311894217106125409 4648719233920662829594057)
              ·
                refine ⟨3486539425440497122195543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648719233920662829594057 3486539425440497122195543)
                ·
                  refine ⟨5229809138160745683293315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486539425440497122195543 5229809138160745683293315)
                  ·
                    refine ⟨7844713707241118524939973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229809138160745683293315 7844713707241118524939973)
                    ·
                      refine ⟨1470883820107709723426245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7844713707241118524939973 1470883820107709723426245)
                      ·
                        rfl

theorem cell23_2864536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2864536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864536 prefixEnd_2864536 := by exact prefixLift 2864536
  have htrace : WordTrace (prefixWord ++ tailWord_2864536) baseStart_2864536 baseEnd_2864536 := by
    simpa [prefixWord, tailWord_2864536, baseEnd_2864536] using wordTrace_append hprefix tailTrace_2864536
  have hstable : (prefixWord ++ tailWord_2864536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864536).length < 2 ^ (prefixWord ++ tailWord_2864536).sum := by decide
  have hdescent : baseEnd_2864536 < baseStart_2864536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864585 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_2864585 : Nat := 118140960795 + 2864585 * 2 ^ 59
def prefixEnd_2864585 : Nat := 4983230072969 + 3 ^ 40 * 2864585 * 2
def baseEnd_2864585 : Nat := 490302993553260010571173

theorem tailTrace_2864585 : CollatzResearch.WordTrace tailWord_2864585 prefixEnd_2864585 490302993553260010571173 := by
  unfold tailWord_2864585
  simp only [CollatzResearch.WordTrace]
  refine ⟨104479998327105252013347209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69653332218070168008898139 104479998327105252013347209)
  ·
    refine ⟨78359998745328939010010407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104479998327105252013347209 78359998745328939010010407)
    ·
      refine ⟨117539998117993408515015611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78359998745328939010010407 117539998117993408515015611)
      ·
        refine ⟨176309997176990112772523417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117539998117993408515015611 176309997176990112772523417)
        ·
          refine ⟨132232497882742584579392563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176309997176990112772523417 132232497882742584579392563)
          ·
            refine ⟨198348746824113876869088845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132232497882742584579392563 198348746824113876869088845)
            ·
              refine ⟨74380780059042703825908317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198348746824113876869088845 74380780059042703825908317)
              ·
                refine ⟨27892792522141013934715619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74380780059042703825908317 27892792522141013934715619)
                ·
                  refine ⟨41839188783211520902073429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27892792522141013934715619 41839188783211520902073429)
                  ·
                    refine ⟨490302993553260010571173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41839188783211520902073429 490302993553260010571173)
                    ·
                      rfl

theorem cell23_2864585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_2864585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864585 prefixEnd_2864585 := by exact prefixLift 2864585
  have htrace : WordTrace (prefixWord ++ tailWord_2864585) baseStart_2864585 baseEnd_2864585 := by
    simpa [prefixWord, tailWord_2864585, baseEnd_2864585] using wordTrace_append hprefix tailTrace_2864585
  have hstable : (prefixWord ++ tailWord_2864585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864585).length < 2 ^ (prefixWord ++ tailWord_2864585).sum := by decide
  have hdescent : baseEnd_2864585 < baseStart_2864585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864586 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_2864586 : Nat := 118140960795 + 2864586 * 2 ^ 59
def prefixEnd_2864586 : Nat := 4983230072969 + 3 ^ 40 * 2864586 * 2
def baseEnd_2864586 : Nat := 1470909494140434527801015

theorem tailTrace_2864586 : CollatzResearch.WordTrace tailWord_2864586 prefixEnd_2864586 1470909494140434527801015 := by
  unfold tailWord_2864586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26120008700025407296033403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69653356533401086122755741 26120008700025407296033403)
  ·
    refine ⟨39180013050038110944050105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26120008700025407296033403 39180013050038110944050105)
    ·
      refine ⟨29385009787528583208037579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39180013050038110944050105 29385009787528583208037579)
      ·
        refine ⟨44077514681292874812056369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29385009787528583208037579 44077514681292874812056369)
        ·
          refine ⟨33058136010969656109042277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44077514681292874812056369 33058136010969656109042277)
          ·
            refine ⟨6198400502056810520445427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33058136010969656109042277 6198400502056810520445427)
            ·
              refine ⟨9297600753085215780668141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198400502056810520445427 9297600753085215780668141)
              ·
                refine ⟨3486600282406955917750553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9297600753085215780668141 3486600282406955917750553)
                ·
                  refine ⟨2614950211805216938312915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3486600282406955917750553 2614950211805216938312915)
                  ·
                    refine ⟨3922425317707825407469373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2614950211805216938312915 3922425317707825407469373)
                    ·
                      refine ⟨1470909494140434527801015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922425317707825407469373 1470909494140434527801015)
                      ·
                        rfl

theorem cell23_2864586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_2864586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864586 prefixEnd_2864586 := by exact prefixLift 2864586
  have htrace : WordTrace (prefixWord ++ tailWord_2864586) baseStart_2864586 baseEnd_2864586 := by
    simpa [prefixWord, tailWord_2864586, baseEnd_2864586] using wordTrace_append hprefix tailTrace_2864586
  have hstable : (prefixWord ++ tailWord_2864586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864586).length < 2 ^ (prefixWord ++ tailWord_2864586).sum := by decide
  have hdescent : baseEnd_2864586 < baseStart_2864586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864595 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_2864595 : Nat := 118140960795 + 2864595 * 2 ^ 59
def prefixEnd_2864595 : Nat := 4983230072969 + 3 ^ 40 * 2864595 * 2
def baseEnd_2864595 : Nat := 1470914115466324992588473

theorem tailTrace_2864595 : CollatzResearch.WordTrace tailWord_2864595 prefixEnd_2864595 1470914115466324992588473 := by
  unfold tailWord_2864595
  simp only [CollatzResearch.WordTrace]
  refine ⟨104480363057069023721211239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69653575371379349147474159 104480363057069023721211239)
  ·
    refine ⟨156720544585603535581816859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104480363057069023721211239 156720544585603535581816859)
    ·
      refine ⟨235080816878405303372725289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156720544585603535581816859 235080816878405303372725289)
      ·
        refine ⟨176310612658803977529543967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235080816878405303372725289 176310612658803977529543967)
        ·
          refine ⟨264465918988205966294315951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176310612658803977529543967 264465918988205966294315951)
          ·
            refine ⟨396698878482308949441473927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264465918988205966294315951 396698878482308949441473927)
            ·
              refine ⟨595048317723463424162210891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396698878482308949441473927 595048317723463424162210891)
              ·
                refine ⟨892572476585195136243316337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595048317723463424162210891 892572476585195136243316337)
                ·
                  refine ⟨669429357438896352182487253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892572476585195136243316337 669429357438896352182487253)
                  ·
                    refine ⟨15689750564974133254277045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 669429357438896352182487253 15689750564974133254277045)
                    ·
                      refine ⟨1470914115466324992588473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15689750564974133254277045 1470914115466324992588473)
                      ·
                        rfl

theorem cell23_2864595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_2864595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864595 prefixEnd_2864595 := by exact prefixLift 2864595
  have htrace : WordTrace (prefixWord ++ tailWord_2864595) baseStart_2864595 baseEnd_2864595 := by
    simpa [prefixWord, tailWord_2864595, baseEnd_2864595] using wordTrace_append hprefix tailTrace_2864595
  have hstable : (prefixWord ++ tailWord_2864595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864595).length < 2 ^ (prefixWord ++ tailWord_2864595).sum := by decide
  have hdescent : baseEnd_2864595 < baseStart_2864595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864609 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_2864609 : Nat := 118140960795 + 2864609 * 2 ^ 59
def prefixEnd_2864609 : Nat := 4983230072969 + 3 ^ 40 * 2864609 * 2
def baseEnd_2864609 : Nat := 1470921304195487937813409

theorem tailTrace_2864609 : CollatzResearch.WordTrace tailWord_2864609 prefixEnd_2864609 1470921304195487937813409 := by
  unfold tailWord_2864609
  simp only [CollatzResearch.WordTrace]
  refine ⟨104480873679018304112220881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69653915786012202741480587 104480873679018304112220881)
  ·
    refine ⟨78360655259263728084165661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104480873679018304112220881 78360655259263728084165661)
    ·
      refine ⟨29385245722223898031562123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78360655259263728084165661 29385245722223898031562123)
      ·
        refine ⟨44077868583335847047343185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29385245722223898031562123 44077868583335847047343185)
        ·
          refine ⟨33058401437501885285507389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44077868583335847047343185 33058401437501885285507389)
          ·
            refine ⟨12396900539063206982065271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33058401437501885285507389 12396900539063206982065271)
            ·
              refine ⟨18595350808594810473097907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12396900539063206982065271 18595350808594810473097907)
              ·
                refine ⟨27893026212892215709646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18595350808594810473097907 27893026212892215709646861)
                ·
                  refine ⟨10459884829834580891117573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27893026212892215709646861 10459884829834580891117573)
                  ·
                    refine ⟨1961228405593983917084545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10459884829834580891117573 1961228405593983917084545)
                    ·
                      refine ⟨1470921304195487937813409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961228405593983917084545 1470921304195487937813409)
                      ·
                        rfl

theorem cell23_2864609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_2864609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864609 prefixEnd_2864609 := by exact prefixLift 2864609
  have htrace : WordTrace (prefixWord ++ tailWord_2864609) baseStart_2864609 baseEnd_2864609 := by
    simpa [prefixWord, tailWord_2864609, baseEnd_2864609] using wordTrace_append hprefix tailTrace_2864609
  have hstable : (prefixWord ++ tailWord_2864609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864609).length < 2 ^ (prefixWord ++ tailWord_2864609).sum := by decide
  have hdescent : baseEnd_2864609 < baseStart_2864609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_2864612 : Nat := 118140960795 + 2864612 * 2 ^ 59
def prefixEnd_2864612 : Nat := 4983230072969 + 3 ^ 40 * 2864612 * 2
def baseEnd_2864612 : Nat := 1470922844637451426075895

theorem tailTrace_2864612 : CollatzResearch.WordTrace tailWord_2864612 prefixEnd_2864612 1470922844637451426075895 := by
  unfold tailWord_2864612
  simp only [CollatzResearch.WordTrace]
  refine ⟨52240491549003717812290045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69653988732004957083053393 52240491549003717812290045)
  ·
    refine ⟨19590184330876394179608767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52240491549003717812290045 19590184330876394179608767)
    ·
      refine ⟨29385276496314591269413151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19590184330876394179608767 29385276496314591269413151)
      ·
        refine ⟨44077914744471886904119727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29385276496314591269413151 44077914744471886904119727)
        ·
          refine ⟨66116872116707830356179591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44077914744471886904119727 66116872116707830356179591)
          ·
            refine ⟨99175308175061745534269387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66116872116707830356179591 99175308175061745534269387)
            ·
              refine ⟨148762962262592618301404081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99175308175061745534269387 148762962262592618301404081)
              ·
                refine ⟨111572221696944463726053061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148762962262592618301404081 111572221696944463726053061)
                ·
                  refine ⟨20919791568177086948634949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111572221696944463726053061 20919791568177086948634949)
                  ·
                    refine ⟨3922460919033203802869053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20919791568177086948634949 3922460919033203802869053)
                    ·
                      refine ⟨1470922844637451426075895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922460919033203802869053 1470922844637451426075895)
                      ·
                        rfl

theorem cell23_2864612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_2864612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864612 prefixEnd_2864612 := by exact prefixLift 2864612
  have htrace : WordTrace (prefixWord ++ tailWord_2864612) baseStart_2864612 baseEnd_2864612 := by
    simpa [prefixWord, tailWord_2864612, baseEnd_2864612] using wordTrace_append hprefix tailTrace_2864612
  have hstable : (prefixWord ++ tailWord_2864612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864612).length < 2 ^ (prefixWord ++ tailWord_2864612).sum := by decide
  have hdescent : baseEnd_2864612 < baseStart_2864612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864709 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_2864709 : Nat := 118140960795 + 2864709 * 2 ^ 59
def prefixEnd_2864709 : Nat := 4983230072969 + 3 ^ 40 * 2864709 * 2
def baseEnd_2864709 : Nat := 490324217420312515520983

theorem tailTrace_2864709 : CollatzResearch.WordTrace tailWord_2864709 prefixEnd_2864709 490324217420312515520983 := by
  unfold tailWord_2864709
  simp only [CollatzResearch.WordTrace]
  refine ⟨104484520978656021190861181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69656347319104014127240787 104484520978656021190861181)
  ·
    refine ⟨39181695366996007946572943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104484520978656021190861181 39181695366996007946572943)
    ·
      refine ⟨58772543050494011919859415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39181695366996007946572943 58772543050494011919859415)
      ·
        refine ⟨88158814575741017879789123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58772543050494011919859415 88158814575741017879789123)
        ·
          refine ⟨132238221863611526819683685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88158814575741017879789123 132238221863611526819683685)
          ·
            refine ⟨24794666599427161278690691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132238221863611526819683685 24794666599427161278690691)
            ·
              refine ⟨37191999899140741918036037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24794666599427161278690691 37191999899140741918036037)
              ·
                refine ⟨6973499981088889109631757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37191999899140741918036037 6973499981088889109631757)
                ·
                  refine ⟨2615062492908333416111909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6973499981088889109631757 2615062492908333416111909)
                  ·
                    refine ⟨490324217420312515520983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615062492908333416111909 490324217420312515520983)
                    ·
                      rfl

theorem cell23_2864709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_2864709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864709 prefixEnd_2864709 := by exact prefixLift 2864709
  have htrace : WordTrace (prefixWord ++ tailWord_2864709) baseStart_2864709 baseEnd_2864709 := by
    simpa [prefixWord, tailWord_2864709, baseEnd_2864709] using wordTrace_append hprefix tailTrace_2864709
  have hstable : (prefixWord ++ tailWord_2864709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864709).length < 2 ^ (prefixWord ++ tailWord_2864709).sum := by decide
  have hdescent : baseEnd_2864709 < baseStart_2864709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864719 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_2864719 : Nat := 118140960795 + 2864719 * 2 ^ 59
def prefixEnd_2864719 : Nat := 4983230072969 + 3 ^ 40 * 2864719 * 2
def baseEnd_2864719 : Nat := 1470977787067482507437903

theorem tailTrace_2864719 : CollatzResearch.WordTrace tailWord_2864719 prefixEnd_2864719 1470977787067482507437903 := by
  unfold tailWord_2864719
  simp only [CollatzResearch.WordTrace]
  refine ⟨104484885708619792898725211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69656590472413195265816807 104484885708619792898725211)
  ·
    refine ⟨156727328562929689348087817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104484885708619792898725211 156727328562929689348087817)
    ·
      refine ⟨117545496422197267011065863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156727328562929689348087817 117545496422197267011065863)
      ·
        refine ⟨176318244633295900516598795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117545496422197267011065863 176318244633295900516598795)
        ·
          refine ⟨264477366949943850774898193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176318244633295900516598795 264477366949943850774898193)
          ·
            refine ⟨198358025212457888081173645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264477366949943850774898193 198358025212457888081173645)
            ·
              refine ⟨74384259454671708030440117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198358025212457888081173645 74384259454671708030440117)
              ·
                refine ⟨6973524323875472627853761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74384259454671708030440117 6973524323875472627853761)
                ·
                  refine ⟨5230143242906604470890321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973524323875472627853761 5230143242906604470890321)
                  ·
                    refine ⟨3922607432179953353167741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230143242906604470890321 3922607432179953353167741)
                    ·
                      refine ⟨1470977787067482507437903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922607432179953353167741 1470977787067482507437903)
                      ·
                        rfl

theorem cell23_2864719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_2864719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864719 prefixEnd_2864719 := by exact prefixLift 2864719
  have htrace : WordTrace (prefixWord ++ tailWord_2864719) baseStart_2864719 baseEnd_2864719 := by
    simpa [prefixWord, tailWord_2864719, baseEnd_2864719] using wordTrace_append hprefix tailTrace_2864719
  have hstable : (prefixWord ++ tailWord_2864719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864719).length < 2 ^ (prefixWord ++ tailWord_2864719).sum := by decide
  have hdescent : baseEnd_2864719 < baseStart_2864719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864762 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2864762 : Nat := 118140960795 + 2864762 * 2 ^ 59
def prefixEnd_2864762 : Nat := 4983230072969 + 3 ^ 40 * 2864762 * 2
def baseEnd_2864762 : Nat := 1470999866735625839200205

theorem tailTrace_2864762 : CollatzResearch.WordTrace tailWord_2864762 prefixEnd_2864762 1470999866735625839200205 := by
  unfold tailWord_2864762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26121613511866002810635135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69657636031642674161693693 26121613511866002810635135)
  ·
    refine ⟨39182420267799004215952703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26121613511866002810635135 39182420267799004215952703)
    ·
      refine ⟨58773630401698506323929055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39182420267799004215952703 58773630401698506323929055)
      ·
        refine ⟨88160445602547759485893583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58773630401698506323929055 88160445602547759485893583)
        ·
          refine ⟨132240668403821639228840375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88160445602547759485893583 132240668403821639228840375)
          ·
            refine ⟨198361002605732458843260563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132240668403821639228840375 198361002605732458843260563)
            ·
              refine ⟨297541503908598688264890845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198361002605732458843260563 297541503908598688264890845)
              ·
                refine ⟨111578063965724508099334067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297541503908598688264890845 111578063965724508099334067)
                ·
                  refine ⟨167367095948586762149001101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111578063965724508099334067 167367095948586762149001101)
                  ·
                    refine ⟨62762660980720035805875413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167367095948586762149001101 62762660980720035805875413)
                    ·
                      refine ⟨1470999866735625839200205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62762660980720035805875413 1470999866735625839200205)
                      ·
                        rfl

theorem cell23_2864762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2864762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864762 prefixEnd_2864762 := by exact prefixLift 2864762
  have htrace : WordTrace (prefixWord ++ tailWord_2864762) baseStart_2864762 baseEnd_2864762 := by
    simpa [prefixWord, tailWord_2864762, baseEnd_2864762] using wordTrace_append hprefix tailTrace_2864762
  have hstable : (prefixWord ++ tailWord_2864762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864762).length < 2 ^ (prefixWord ++ tailWord_2864762).sum := by decide
  have hdescent : baseEnd_2864762 < baseStart_2864762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864800 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 1, 1, 3]
def baseStart_2864800 : Nat := 118140960795 + 2864800 * 2 ^ 59
def prefixEnd_2864800 : Nat := 4983230072969 + 3 ^ 40 * 2864800 * 2
def baseEnd_2864800 : Nat := 1471019379000496690525031

theorem tailTrace_2864800 : CollatzResearch.WordTrace tailWord_2864800 prefixEnd_2864800 1471019379000496690525031 := by
  unfold tailWord_2864800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52243920010663171866211927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69658560014217562488282569 52243920010663171866211927)
  ·
    refine ⟨78365880015994757799317891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52243920010663171866211927 78365880015994757799317891)
    ·
      refine ⟨117548820023992136698976837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78365880015994757799317891 117548820023992136698976837)
      ·
        refine ⟨22040403754498525631058157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117548820023992136698976837 22040403754498525631058157)
        ·
          refine ⟨8265151407936947111646809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22040403754498525631058157 8265151407936947111646809)
          ·
            refine ⟨6198863555952710333735107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8265151407936947111646809 6198863555952710333735107)
            ·
              refine ⟨9298295333929065500602661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198863555952710333735107 9298295333929065500602661)
              ·
                refine ⟨1743430375111699781362999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9298295333929065500602661 1743430375111699781362999)
                ·
                  refine ⟨2615145562667549672044499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743430375111699781362999 2615145562667549672044499)
                  ·
                    refine ⟨3922718344001324508066749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2615145562667549672044499 3922718344001324508066749)
                    ·
                      refine ⟨1471019379000496690525031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922718344001324508066749 1471019379000496690525031)
                      ·
                        rfl

theorem cell23_2864800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_2864800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864800 prefixEnd_2864800 := by exact prefixLift 2864800
  have htrace : WordTrace (prefixWord ++ tailWord_2864800) baseStart_2864800 baseEnd_2864800 := by
    simpa [prefixWord, tailWord_2864800, baseEnd_2864800] using wordTrace_append hprefix tailTrace_2864800
  have hstable : (prefixWord ++ tailWord_2864800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864800).length < 2 ^ (prefixWord ++ tailWord_2864800).sum := by decide
  have hdescent : baseEnd_2864800 < baseStart_2864800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864816 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_2864816 : Nat := 118140960795 + 2864816 * 2 ^ 59
def prefixEnd_2864816 : Nat := 4983230072969 + 3 ^ 40 * 2864816 * 2
def baseEnd_2864816 : Nat := 490342531563656209308319

theorem tailTrace_2864816 : CollatzResearch.WordTrace tailWord_2864816 prefixEnd_2864816 490342531563656209308319 := by
  unfold tailWord_2864816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244211794634189232503151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69658949059512252310004201 52244211794634189232503151)
  ·
    refine ⟨78366317691951283848754727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52244211794634189232503151 78366317691951283848754727)
    ·
      refine ⟨117549476537926925773132091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78366317691951283848754727 117549476537926925773132091)
      ·
        refine ⟨176324214806890388659698137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117549476537926925773132091 176324214806890388659698137)
        ·
          refine ⟨132243161105167791494773603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176324214806890388659698137 132243161105167791494773603)
          ·
            refine ⟨198364741657751687242160405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132243161105167791494773603 198364741657751687242160405)
            ·
              refine ⟨9298347265207110339476269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198364741657751687242160405 9298347265207110339476269)
              ·
                refine ⟨3486880224452666377303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9298347265207110339476269 3486880224452666377303601)
                ·
                  refine ⟨2615160168339499782977701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3486880224452666377303601 2615160168339499782977701)
                  ·
                    refine ⟨490342531563656209308319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615160168339499782977701 490342531563656209308319)
                    ·
                      rfl

theorem cell23_2864816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_2864816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864816 prefixEnd_2864816 := by exact prefixLift 2864816
  have htrace : WordTrace (prefixWord ++ tailWord_2864816) baseStart_2864816 baseEnd_2864816 := by
    simpa [prefixWord, tailWord_2864816, baseEnd_2864816] using wordTrace_append hprefix tailTrace_2864816
  have hstable : (prefixWord ++ tailWord_2864816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864816).length < 2 ^ (prefixWord ++ tailWord_2864816).sum := by decide
  have hdescent : baseEnd_2864816 < baseStart_2864816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864823 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_2864823 : Nat := 118140960795 + 2864823 * 2 ^ 59
def prefixEnd_2864823 : Nat := 4983230072969 + 3 ^ 40 * 2864823 * 2
def baseEnd_2864823 : Nat := 1471031189055550100537425

theorem tailTrace_2864823 : CollatzResearch.WordTrace tailWord_2864823 prefixEnd_2864823 1471031189055550100537425 := by
  unfold tailWord_2864823
  simp only [CollatzResearch.WordTrace]
  refine ⟨104488678900243018660511123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69659119266828679107007415 104488678900243018660511123)
  ·
    refine ⟨156733018350364527990766685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104488678900243018660511123 156733018350364527990766685)
    ·
      refine ⟨58774881881386697996537507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156733018350364527990766685 58774881881386697996537507)
      ·
        refine ⟨88162322822080046994806261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58774881881386697996537507 88162322822080046994806261)
        ·
          refine ⟨8265217764570004405763087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88162322822080046994806261 8265217764570004405763087)
          ·
            refine ⟨12397826646855006608644631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265217764570004405763087 12397826646855006608644631)
            ·
              refine ⟨18596739970282509912966947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12397826646855006608644631 18596739970282509912966947)
              ·
                refine ⟨27895109955423764869450421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18596739970282509912966947 27895109955423764869450421)
                ·
                  refine ⟨2615166558320977956510977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27895109955423764869450421 2615166558320977956510977)
                  ·
                    refine ⟨1961374918740733467383233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2615166558320977956510977 1961374918740733467383233)
                    ·
                      refine ⟨1471031189055550100537425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961374918740733467383233 1471031189055550100537425)
                      ·
                        rfl

theorem cell23_2864823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_2864823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864823 prefixEnd_2864823 := by exact prefixLift 2864823
  have htrace : WordTrace (prefixWord ++ tailWord_2864823) baseStart_2864823 baseEnd_2864823 := by
    simpa [prefixWord, tailWord_2864823, baseEnd_2864823] using wordTrace_append hprefix tailTrace_2864823
  have hstable : (prefixWord ++ tailWord_2864823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864823).length < 2 ^ (prefixWord ++ tailWord_2864823).sum := by decide
  have hdescent : baseEnd_2864823 < baseStart_2864823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864826 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_2864826 : Nat := 118140960795 + 2864826 * 2 ^ 59
def prefixEnd_2864826 : Nat := 4983230072969 + 3 ^ 40 * 2864826 * 2
def baseEnd_2864826 : Nat := 1471032729497513588799911

theorem tailTrace_2864826 : CollatzResearch.WordTrace tailWord_2864826 prefixEnd_2864826 1471032729497513588799911 := by
  unfold tailWord_2864826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122197079808037543217583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69659192212821433448580221 26122197079808037543217583)
  ·
    refine ⟨39183295619712056314826375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26122197079808037543217583 39183295619712056314826375)
    ·
      refine ⟨58774943429568084472239563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39183295619712056314826375 58774943429568084472239563)
      ·
        refine ⟨88162415144352126708359345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58774943429568084472239563 88162415144352126708359345)
        ·
          refine ⟨66121811358264095031269509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88162415144352126708359345 66121811358264095031269509)
          ·
            refine ⟨12397839629674517818363033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66121811358264095031269509 12397839629674517818363033)
            ·
              refine ⟨9298379722255888363772275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12397839629674517818363033 9298379722255888363772275)
              ·
                refine ⟨13947569583383832545658413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298379722255888363772275 13947569583383832545658413)
                ·
                  refine ⟨5230338593768937204621905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13947569583383832545658413 5230338593768937204621905)
                  ·
                    refine ⟨3922753945326702903466429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230338593768937204621905 3922753945326702903466429)
                    ·
                      refine ⟨1471032729497513588799911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3922753945326702903466429 1471032729497513588799911)
                      ·
                        rfl

theorem cell23_2864826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_2864826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864826 prefixEnd_2864826 := by exact prefixLift 2864826
  have htrace : WordTrace (prefixWord ++ tailWord_2864826) baseStart_2864826 baseEnd_2864826 := by
    simpa [prefixWord, tailWord_2864826, baseEnd_2864826] using wordTrace_append hprefix tailTrace_2864826
  have hstable : (prefixWord ++ tailWord_2864826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864826).length < 2 ^ (prefixWord ++ tailWord_2864826).sum := by decide
  have hdescent : baseEnd_2864826 < baseStart_2864826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864836 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2864836 : Nat := 118140960795 + 2864836 * 2 ^ 59
def prefixEnd_2864836 : Nat := 4983230072969 + 3 ^ 40 * 2864836 * 2
def baseEnd_2864836 : Nat := 1471037864304058549674865

theorem tailTrace_2864836 : CollatzResearch.WordTrace tailWord_2864836 prefixEnd_2864836 1471037864304058549674865 := by
  unfold tailWord_2864836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244576524597960940367181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69659435366130614587156241 52244576524597960940367181)
  ·
    refine ⟨19591716196724235352637693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52244576524597960940367181 19591716196724235352637693)
    ·
      refine ⟨7346893573771588257239135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19591716196724235352637693 7346893573771588257239135)
      ·
        refine ⟨11020340360657382385858703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346893573771588257239135 11020340360657382385858703)
        ·
          refine ⟨16530510540986073578788055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11020340360657382385858703 16530510540986073578788055)
          ·
            refine ⟨24795765811479110368182083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16530510540986073578788055 24795765811479110368182083)
            ·
              refine ⟨37193648717218665552273125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24795765811479110368182083 37193648717218665552273125)
              ·
                refine ⟨6973809134478499791051211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37193648717218665552273125 6973809134478499791051211)
                ·
                  refine ⟨10460713701717749686576817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973809134478499791051211 10460713701717749686576817)
                  ·
                    refine ⟨7845535276288312264932613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10460713701717749686576817 7845535276288312264932613)
                    ·
                      refine ⟨1471037864304058549674865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7845535276288312264932613 1471037864304058549674865)
                      ·
                        rfl

theorem cell23_2864836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2864836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864836 prefixEnd_2864836 := by exact prefixLift 2864836
  have htrace : WordTrace (prefixWord ++ tailWord_2864836) baseStart_2864836 baseEnd_2864836 := by
    simpa [prefixWord, tailWord_2864836, baseEnd_2864836] using wordTrace_append hprefix tailTrace_2864836
  have hstable : (prefixWord ++ tailWord_2864836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864836).length < 2 ^ (prefixWord ++ tailWord_2864836).sum := by decide
  have hdescent : baseEnd_2864836 < baseStart_2864836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864850 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2864850 : Nat := 118140960795 + 2864850 * 2 ^ 59
def prefixEnd_2864850 : Nat := 4983230072969 + 3 ^ 40 * 2864850 * 2
def baseEnd_2864850 : Nat := 490348351011073831633267

theorem tailTrace_2864850 : CollatzResearch.WordTrace tailWord_2864850 prefixEnd_2864850 490348351011073831633267 := by
  unfold tailWord_2864850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122415917786300567936001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69659775780763468181162669 26122415917786300567936001)
  ·
    refine ⟨19591811938339725425952001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26122415917786300567936001 19591811938339725425952001)
    ·
      refine ⟨14693858953754794069464001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19591811938339725425952001 14693858953754794069464001)
      ·
        refine ⟨11020394215316095552098001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14693858953754794069464001 11020394215316095552098001)
        ·
          refine ⟨8265295661487071664073501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11020394215316095552098001 8265295661487071664073501)
          ·
            refine ⟨3099485873057651874027563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8265295661487071664073501 3099485873057651874027563)
            ·
              refine ⟨4649228809586477811041345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099485873057651874027563 4649228809586477811041345)
              ·
                refine ⟨3486921607189858358281009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649228809586477811041345 3486921607189858358281009)
                ·
                  refine ⟨2615191205392393768710757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3486921607189858358281009 2615191205392393768710757)
                  ·
                    refine ⟨490348351011073831633267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615191205392393768710757 490348351011073831633267)
                    ·
                      rfl

theorem cell23_2864850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2864850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864850 prefixEnd_2864850 := by exact prefixLift 2864850
  have htrace : WordTrace (prefixWord ++ tailWord_2864850) baseStart_2864850 baseEnd_2864850 := by
    simpa [prefixWord, tailWord_2864850, baseEnd_2864850] using wordTrace_append hprefix tailTrace_2864850
  have hstable : (prefixWord ++ tailWord_2864850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864850).length < 2 ^ (prefixWord ++ tailWord_2864850).sum := by decide
  have hdescent : baseEnd_2864850 < baseStart_2864850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864883 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 1, 3, 2]
def baseStart_2864883 : Nat := 118140960795 + 2864883 * 2 ^ 59
def prefixEnd_2864883 : Nat := 4983230072969 + 3 ^ 40 * 2864883 * 2
def baseEnd_2864883 : Nat := 1471061997894819865787149

theorem tailTrace_2864883 : CollatzResearch.WordTrace tailWord_2864883 prefixEnd_2864883 1471061997894819865787149 := by
  unfold tailWord_2864883
  simp only [CollatzResearch.WordTrace]
  refine ⟨104490867280025648907695303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69660578186683765938463535 104490867280025648907695303)
  ·
    refine ⟨156736300920038473361542955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104490867280025648907695303 156736300920038473361542955)
    ·
      refine ⟨235104451380057710042314433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156736300920038473361542955 235104451380057710042314433)
      ·
        refine ⟨176328338535043282531735825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235104451380057710042314433 176328338535043282531735825)
        ·
          refine ⟨132246253901282461898801869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176328338535043282531735825 132246253901282461898801869)
          ·
            refine ⟨49592345212980923212050701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132246253901282461898801869 49592345212980923212050701)
            ·
              refine ⟨18597129454867846204519013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49592345212980923212050701 18597129454867846204519013)
              ·
                refine ⟨3486961772787721163347315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18597129454867846204519013 3486961772787721163347315)
                ·
                  refine ⟨5230442659181581745020973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486961772787721163347315 5230442659181581745020973)
                  ·
                    refine ⟨1961415997193093154382865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5230442659181581745020973 1961415997193093154382865)
                    ·
                      refine ⟨1471061997894819865787149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961415997193093154382865 1471061997894819865787149)
                      ·
                        rfl

theorem cell23_2864883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3, 2].length) (baseStart_2864883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864883 prefixEnd_2864883 := by exact prefixLift 2864883
  have htrace : WordTrace (prefixWord ++ tailWord_2864883) baseStart_2864883 baseEnd_2864883 := by
    simpa [prefixWord, tailWord_2864883, baseEnd_2864883] using wordTrace_append hprefix tailTrace_2864883
  have hstable : (prefixWord ++ tailWord_2864883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864883).length < 2 ^ (prefixWord ++ tailWord_2864883).sum := by decide
  have hdescent : baseEnd_2864883 < baseStart_2864883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864886 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2864886 : Nat := 118140960795 + 2864886 * 2 ^ 59
def prefixEnd_2864886 : Nat := 4983230072969 + 3 ^ 40 * 2864886 * 2
def baseEnd_2864886 : Nat := 1471063538336783354049635

theorem tailTrace_2864886 : CollatzResearch.WordTrace tailWord_2864886 prefixEnd_2864886 1471063538336783354049635 := by
  unfold tailWord_2864886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6530686043688423776253407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69660651132676520280036341 6530686043688423776253407)
  ·
    refine ⟨9796029065532635664380111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6530686043688423776253407 9796029065532635664380111)
    ·
      refine ⟨14694043598298953496570167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9796029065532635664380111 14694043598298953496570167)
      ·
        refine ⟨22041065397448430244855251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14694043598298953496570167 22041065397448430244855251)
        ·
          refine ⟨33061598096172645367282877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041065397448430244855251 33061598096172645367282877)
          ·
            refine ⟨12398099286064742012731079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33061598096172645367282877 12398099286064742012731079)
            ·
              refine ⟨18597148929097113019096619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12398099286064742012731079 18597148929097113019096619)
              ·
                refine ⟨27895723393645669528644929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18597148929097113019096619 27895723393645669528644929)
                ·
                  refine ⟨20921792545234252146483697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27895723393645669528644929 20921792545234252146483697)
                  ·
                    refine ⟨15691344408925689109862773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20921792545234252146483697 15691344408925689109862773)
                    ·
                      refine ⟨1471063538336783354049635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15691344408925689109862773 1471063538336783354049635)
                      ·
                        rfl

theorem cell23_2864886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2864886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864886 prefixEnd_2864886 := by exact prefixLift 2864886
  have htrace : WordTrace (prefixWord ++ tailWord_2864886) baseStart_2864886 baseEnd_2864886 := by
    simpa [prefixWord, tailWord_2864886, baseEnd_2864886] using wordTrace_append hprefix tailTrace_2864886
  have hstable : (prefixWord ++ tailWord_2864886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864886).length < 2 ^ (prefixWord ++ tailWord_2864886).sum := by decide
  have hdescent : baseEnd_2864886 < baseStart_2864886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864899 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_2864899 : Nat := 118140960795 + 2864899 * 2 ^ 59
def prefixEnd_2864899 : Nat := 4983230072969 + 3 ^ 40 * 2864899 * 2
def baseEnd_2864899 : Nat := 1471070213585291803187075

theorem tailTrace_2864899 : CollatzResearch.WordTrace tailWord_2864899 prefixEnd_2864899 1471070213585291803187075 := by
  unfold tailWord_2864899
  simp only [CollatzResearch.WordTrace]
  refine ⟨104491450847967683640277751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69660967231978455760185167 104491450847967683640277751)
  ·
    refine ⟨156737176271951525460416627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104491450847967683640277751 156737176271951525460416627)
    ·
      refine ⟨235105764407927288190624941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156737176271951525460416627 235105764407927288190624941)
      ·
        refine ⟨88164661652972733071484353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235105764407927288190624941 88164661652972733071484353)
        ·
          refine ⟨66123496239729549803613265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88164661652972733071484353 66123496239729549803613265)
          ·
            refine ⟨49592622179797162352709949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66123496239729549803613265 49592622179797162352709949)
            ·
              refine ⟨18597233317423935882266231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49592622179797162352709949 18597233317423935882266231)
              ·
                refine ⟨27895849976135903823399347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18597233317423935882266231 27895849976135903823399347)
                ·
                  refine ⟨41843774964203855735099021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27895849976135903823399347 41843774964203855735099021)
                  ·
                    refine ⟨15691415611576445900662133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41843774964203855735099021 15691415611576445900662133)
                    ·
                      refine ⟨1471070213585291803187075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15691415611576445900662133 1471070213585291803187075)
                      ·
                        rfl

theorem cell23_2864899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_2864899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864899 prefixEnd_2864899 := by exact prefixLift 2864899
  have htrace : WordTrace (prefixWord ++ tailWord_2864899) baseStart_2864899 baseEnd_2864899 := by
    simpa [prefixWord, tailWord_2864899, baseEnd_2864899] using wordTrace_append hprefix tailTrace_2864899
  have hstable : (prefixWord ++ tailWord_2864899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864899).length < 2 ^ (prefixWord ++ tailWord_2864899).sum := by decide
  have hdescent : baseEnd_2864899 < baseStart_2864899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864900 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2864900 : Nat := 118140960795 + 2864900 * 2 ^ 59
def prefixEnd_2864900 : Nat := 4983230072969 + 3 ^ 40 * 2864900 * 2
def baseEnd_2864900 : Nat := 1471070727065946299274571

theorem tailTrace_2864900 : CollatzResearch.WordTrace tailWord_2864900 prefixEnd_2864900 1471070727065946299274571 := by
  unfold tailWord_2864900
  simp only [CollatzResearch.WordTrace]
  refine ⟨52245743660482030405532077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69660991547309373874042769 52245743660482030405532077)
  ·
    refine ⟨19592153872680761402074529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52245743660482030405532077 19592153872680761402074529)
    ·
      refine ⟨14694115404510571051555897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19592153872680761402074529 14694115404510571051555897)
      ·
        refine ⟨11020586553382928288666923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14694115404510571051555897 11020586553382928288666923)
        ·
          refine ⟨16530879830074392433000385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11020586553382928288666923 16530879830074392433000385)
          ·
            refine ⟨12398159872555794324750289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16530879830074392433000385 12398159872555794324750289)
            ·
              refine ⟨9298619904416845743562717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12398159872555794324750289 9298619904416845743562717)
              ·
                refine ⟨3486982464156317153836019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9298619904416845743562717 3486982464156317153836019)
                ·
                  refine ⟨5230473696234475730754029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486982464156317153836019 5230473696234475730754029)
                  ·
                    refine ⟨1961427636087928399032761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5230473696234475730754029 1961427636087928399032761)
                    ·
                      refine ⟨1471070727065946299274571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961427636087928399032761 1471070727065946299274571)
                      ·
                        rfl

theorem cell23_2864900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2864900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864900 prefixEnd_2864900 := by exact prefixLift 2864900
  have htrace : WordTrace (prefixWord ++ tailWord_2864900) baseStart_2864900 baseEnd_2864900 := by
    simpa [prefixWord, tailWord_2864900, baseEnd_2864900] using wordTrace_append hprefix tailTrace_2864900
  have hstable : (prefixWord ++ tailWord_2864900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864900).length < 2 ^ (prefixWord ++ tailWord_2864900).sum := by decide
  have hdescent : baseEnd_2864900 < baseStart_2864900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864979 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 8]
def baseStart_2864979 : Nat := 118140960795 + 2864979 * 2 ^ 59
def prefixEnd_2864979 : Nat := 4983230072969 + 3 ^ 40 * 2864979 * 2
def baseEnd_2864979 : Nat := 490370430679217163395569

theorem tailTrace_2864979 : CollatzResearch.WordTrace tailWord_2864979 prefixEnd_2864979 490370430679217163395569 := by
  unfold tailWord_2864979
  simp only [CollatzResearch.WordTrace]
  refine ⟨104494368687677857303189991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69662912458451904868793327 104494368687677857303189991)
  ·
    refine ⟨156741553031516785954784987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104494368687677857303189991 156741553031516785954784987)
    ·
      refine ⟨235112329547275178932177481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156741553031516785954784987 235112329547275178932177481)
      ·
        refine ⟨176334247160456384199133111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235112329547275178932177481 176334247160456384199133111)
        ·
          refine ⟨264501370740684576298699667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176334247160456384199133111 264501370740684576298699667)
          ·
            refine ⟨396752056111026864448049501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264501370740684576298699667 396752056111026864448049501)
            ·
              refine ⟨148782021041635074168018563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396752056111026864448049501 148782021041635074168018563)
              ·
                refine ⟨223173031562452611252027845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148782021041635074168018563 223173031562452611252027845)
                ·
                  refine ⟨41844943417959864609755221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223173031562452611252027845 41844943417959864609755221)
                  ·
                    refine ⟨490370430679217163395569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41844943417959864609755221 490370430679217163395569)
                    ·
                      rfl

theorem cell23_2864979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_2864979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864979 prefixEnd_2864979 := by exact prefixLift 2864979
  have htrace : WordTrace (prefixWord ++ tailWord_2864979) baseStart_2864979 baseEnd_2864979 := by
    simpa [prefixWord, tailWord_2864979, baseEnd_2864979] using wordTrace_append hprefix tailTrace_2864979
  have hstable : (prefixWord ++ tailWord_2864979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864979).length < 2 ^ (prefixWord ++ tailWord_2864979).sum := by decide
  have hdescent : baseEnd_2864979 < baseStart_2864979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2864986 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_2864986 : Nat := 118140960795 + 2864986 * 2 ^ 59
def prefixEnd_2864986 : Nat := 4983230072969 + 3 ^ 40 * 2864986 * 2
def baseEnd_2864986 : Nat := 1471114886402232962799175

theorem tailTrace_2864986 : CollatzResearch.WordTrace tailWord_2864986 prefixEnd_2864986 1471114886402232962799175 := by
  unfold tailWord_2864986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26123655999663124374673703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69663082665768331665796541 26123655999663124374673703)
  ·
    refine ⟨39185483999494686562010555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26123655999663124374673703 39185483999494686562010555)
    ·
      refine ⟨58778225999242029843015833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39185483999494686562010555 58778225999242029843015833)
      ·
        refine ⟨44083669499431522382261875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58778225999242029843015833 44083669499431522382261875)
        ·
          refine ⟨66125504249147283573392813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44083669499431522382261875 66125504249147283573392813)
          ·
            refine ⟨24797064093430231340022305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66125504249147283573392813 24797064093430231340022305)
            ·
              refine ⟨18597798070072673505016729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24797064093430231340022305 18597798070072673505016729)
              ·
                refine ⟨13948348552554505128762547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18597798070072673505016729 13948348552554505128762547)
                ·
                  refine ⟨20922522828831757693143821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13948348552554505128762547 20922522828831757693143821)
                  ·
                    refine ⟨7845946060811909134928933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20922522828831757693143821 7845946060811909134928933)
                    ·
                      refine ⟨1471114886402232962799175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7845946060811909134928933 1471114886402232962799175)
                      ·
                        rfl

theorem cell23_2864986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_2864986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2864986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2864986 prefixEnd_2864986 := by exact prefixLift 2864986
  have htrace : WordTrace (prefixWord ++ tailWord_2864986) baseStart_2864986 baseEnd_2864986 := by
    simpa [prefixWord, tailWord_2864986, baseEnd_2864986] using wordTrace_append hprefix tailTrace_2864986
  have hstable : (prefixWord ++ tailWord_2864986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2864986).length < 2 ^ (prefixWord ++ tailWord_2864986).sum := by decide
  have hdescent : baseEnd_2864986 < baseStart_2864986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2864986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865013 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2865013 : Nat := 118140960795 + 2865013 * 2 ^ 59
def prefixEnd_2865013 : Nat := 4983230072969 + 3 ^ 40 * 2865013 * 2
def baseEnd_2865013 : Nat := 490376250126634785720517

theorem tailTrace_2865013 : CollatzResearch.WordTrace tailWord_2865013 prefixEnd_2865013 490376250126634785720517 := by
  unfold tailWord_2865013
  simp only [CollatzResearch.WordTrace]
  refine ⟨104495608769554681109927693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69663739179703120739951795 104495608769554681109927693)
  ·
    refine ⟨39185853288583005416222885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104495608769554681109927693 39185853288583005416222885)
    ·
      refine ⟨7347347491609313515541791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39185853288583005416222885 7347347491609313515541791)
      ·
        refine ⟨11021021237413970273312687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347347491609313515541791 11021021237413970273312687)
        ·
          refine ⟨16531531856120955409969031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11021021237413970273312687 16531531856120955409969031)
          ·
            refine ⟨24797297784181433114953547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16531531856120955409969031 24797297784181433114953547)
            ·
              refine ⟨37195946676272149672430321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24797297784181433114953547 37195946676272149672430321)
              ·
                refine ⟨27896960007204112254322741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37195946676272149672430321 27896960007204112254322741)
                ·
                  refine ⟨2615340000675385523842757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27896960007204112254322741 2615340000675385523842757)
                  ·
                    refine ⟨490376250126634785720517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615340000675385523842757 490376250126634785720517)
                    ·
                      rfl

theorem cell23_2865013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2865013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865013 prefixEnd_2865013 := by exact prefixLift 2865013
  have htrace : WordTrace (prefixWord ++ tailWord_2865013) baseStart_2865013 baseEnd_2865013 := by
    simpa [prefixWord, tailWord_2865013, baseEnd_2865013] using wordTrace_append hprefix tailTrace_2865013
  have hstable : (prefixWord ++ tailWord_2865013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865013).length < 2 ^ (prefixWord ++ tailWord_2865013).sum := by decide
  have hdescent : baseEnd_2865013 < baseStart_2865013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865080 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_2865080 : Nat := 118140960795 + 2865080 * 2 ^ 59
def prefixEnd_2865080 : Nat := 4983230072969 + 3 ^ 40 * 2865080 * 2
def baseEnd_2865080 : Nat := 1471163153583755595023743

theorem tailTrace_2865080 : CollatzResearch.WordTrace tailWord_2865080 prefixEnd_2865080 1471163153583755595023743 := by
  unfold tailWord_2865080
  simp only [CollatzResearch.WordTrace]
  refine ⟨52249026230155975776308347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69665368306874634368411129 52249026230155975776308347)
  ·
    refine ⟨78373539345233963664462521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52249026230155975776308347 78373539345233963664462521)
    ·
      refine ⟨58780154508925472748346891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78373539345233963664462521 58780154508925472748346891)
      ·
        refine ⟨88170231763388209122520337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58780154508925472748346891 88170231763388209122520337)
        ·
          refine ⟨66127673822541156841890253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88170231763388209122520337 66127673822541156841890253)
          ·
            refine ⟨24797877683452933815708845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66127673822541156841890253 24797877683452933815708845)
            ·
              refine ⟨9299204131294850180890817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24797877683452933815708845 9299204131294850180890817)
              ·
                refine ⟨6974403098471137635668113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9299204131294850180890817 6974403098471137635668113)
                ·
                  refine ⟨5230802323853353226751085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6974403098471137635668113 5230802323853353226751085)
                  ·
                    refine ⟨1961550871445007460031657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5230802323853353226751085 1961550871445007460031657)
                    ·
                      refine ⟨1471163153583755595023743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961550871445007460031657 1471163153583755595023743)
                      ·
                        rfl

theorem cell23_2865080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_2865080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865080 prefixEnd_2865080 := by exact prefixLift 2865080
  have htrace : WordTrace (prefixWord ++ tailWord_2865080) baseStart_2865080 baseEnd_2865080 := by
    simpa [prefixWord, tailWord_2865080, baseEnd_2865080] using wordTrace_append hprefix tailTrace_2865080
  have hstable : (prefixWord ++ tailWord_2865080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865080).length < 2 ^ (prefixWord ++ tailWord_2865080).sum := by decide
  have hdescent : baseEnd_2865080 < baseStart_2865080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865093 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_2865093 : Nat := 118140960795 + 2865093 * 2 ^ 59
def prefixEnd_2865093 : Nat := 4983230072969 + 3 ^ 40 * 2865093 * 2
def baseEnd_2865093 : Nat := 1471169828832264044161183

theorem tailTrace_2865093 : CollatzResearch.WordTrace tailWord_2865093 prefixEnd_2865093 1471169828832264044161183 := by
  unfold tailWord_2865093
  simp only [CollatzResearch.WordTrace]
  refine ⟨104498526609264854772839933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69665684406176569848559955 104498526609264854772839933)
  ·
    refine ⟨39186947478474320539814975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104498526609264854772839933 39186947478474320539814975)
    ·
      refine ⟨58780421217711480809722463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39186947478474320539814975 58780421217711480809722463)
      ·
        refine ⟨88170631826567221214583695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58780421217711480809722463 88170631826567221214583695)
        ·
          refine ⟨132255947739850831821875543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88170631826567221214583695 132255947739850831821875543)
          ·
            refine ⟨198383921609776247732813315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132255947739850831821875543 198383921609776247732813315)
            ·
              refine ⟨297575882414664371599219973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198383921609776247732813315 297575882414664371599219973)
              ·
                refine ⟨55795477952749569674853745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297575882414664371599219973 55795477952749569674853745)
                ·
                  refine ⟨41846608464562177256140309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55795477952749569674853745 41846608464562177256140309)
                  ·
                    refine ⟨1961559771776352058881577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41846608464562177256140309 1961559771776352058881577)
                    ·
                      refine ⟨1471169828832264044161183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961559771776352058881577 1471169828832264044161183)
                      ·
                        rfl

theorem cell23_2865093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_2865093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865093 prefixEnd_2865093 := by exact prefixLift 2865093
  have htrace : WordTrace (prefixWord ++ tailWord_2865093) baseStart_2865093 baseEnd_2865093 := by
    simpa [prefixWord, tailWord_2865093, baseEnd_2865093] using wordTrace_append hprefix tailTrace_2865093
  have hstable : (prefixWord ++ tailWord_2865093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865093).length < 2 ^ (prefixWord ++ tailWord_2865093).sum := by decide
  have hdescent : baseEnd_2865093 < baseStart_2865093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865123 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2865123 : Nat := 118140960795 + 2865123 * 2 ^ 59
def prefixEnd_2865123 : Nat := 4983230072969 + 3 ^ 40 * 2865123 * 2
def baseEnd_2865123 : Nat := 1471185233251898926786045

theorem tailTrace_2865123 : CollatzResearch.WordTrace tailWord_2865123 prefixEnd_2865123 1471185233251898926786045 := by
  unfold tailWord_2865123
  simp only [CollatzResearch.WordTrace]
  refine ⟨104499620799156169896432023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69666413866104113264288015 104499620799156169896432023)
  ·
    refine ⟨156749431198734254844648035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104499620799156169896432023 156749431198734254844648035)
    ·
      refine ⟨235124146798101382266972053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156749431198734254844648035 235124146798101382266972053)
      ·
        refine ⟨11021444381161002293764315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235124146798101382266972053 11021444381161002293764315)
        ·
          refine ⟨16532166571741503440646473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11021444381161002293764315 16532166571741503440646473)
          ·
            refine ⟨12399124928806127580484855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16532166571741503440646473 12399124928806127580484855)
            ·
              refine ⟨18598687393209191370727283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12399124928806127580484855 18598687393209191370727283)
              ·
                refine ⟨27898031089813787056090925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18598687393209191370727283 27898031089813787056090925)
                ·
                  refine ⟨10461761658680170146034097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27898031089813787056090925 10461761658680170146034097)
                  ·
                    refine ⟨7846321244010127609525573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10461761658680170146034097 7846321244010127609525573)
                    ·
                      refine ⟨1471185233251898926786045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7846321244010127609525573 1471185233251898926786045)
                      ·
                        rfl

theorem cell23_2865123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2865123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865123 prefixEnd_2865123 := by exact prefixLift 2865123
  have htrace : WordTrace (prefixWord ++ tailWord_2865123) baseStart_2865123 baseEnd_2865123 := by
    simpa [prefixWord, tailWord_2865123, baseEnd_2865123] using wordTrace_append hprefix tailTrace_2865123
  have hstable : (prefixWord ++ tailWord_2865123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865123).length < 2 ^ (prefixWord ++ tailWord_2865123).sum := by decide
  have hdescent : baseEnd_2865123 < baseStart_2865123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865133 : List Nat := [1, 5, 1, 4, 12]
def baseStart_2865133 : Nat := 118140960795 + 2865133 * 2 ^ 59
def prefixEnd_2865133 : Nat := 4983230072969 + 3 ^ 40 * 2865133 * 2
def baseEnd_2865133 : Nat := 2018093783344916169631

theorem tailTrace_2865133 : CollatzResearch.WordTrace tailWord_2865133 prefixEnd_2865133 2018093783344916169631 := by
  unfold tailWord_2865133
  simp only [CollatzResearch.WordTrace]
  refine ⟨104499985529119941604296053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69666657019413294402864035 104499985529119941604296053)
  ·
    refine ⟨9796873643354994525402755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104499985529119941604296053 9796873643354994525402755)
    ·
      refine ⟨14695310465032491788104133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9796873643354994525402755 14695310465032491788104133)
      ·
        refine ⟨2755370712193592210269525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14695310465032491788104133 2755370712193592210269525)
        ·
          refine ⟨2018093783344916169631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2755370712193592210269525 2018093783344916169631)
          ·
            rfl

theorem cell23_2865133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 12].length) (baseStart_2865133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865133 prefixEnd_2865133 := by exact prefixLift 2865133
  have htrace : WordTrace (prefixWord ++ tailWord_2865133) baseStart_2865133 baseEnd_2865133 := by
    simpa [prefixWord, tailWord_2865133, baseEnd_2865133] using wordTrace_append hprefix tailTrace_2865133
  have hstable : (prefixWord ++ tailWord_2865133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865133).length < 2 ^ (prefixWord ++ tailWord_2865133).sum := by decide
  have hdescent : baseEnd_2865133 < baseStart_2865133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865137 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_2865137 : Nat := 118140960795 + 2865137 * 2 ^ 59
def prefixEnd_2865137 : Nat := 4983230072969 + 3 ^ 40 * 2865137 * 2
def baseEnd_2865137 : Nat := 490397473993687290670327

theorem tailTrace_2865137 : CollatzResearch.WordTrace tailWord_2865137 prefixEnd_2865137 490397473993687290670327 := by
  unfold tailWord_2865137
  simp only [CollatzResearch.WordTrace]
  refine ⟨104500131421105450287441665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69666754280736966858294443 104500131421105450287441665)
  ·
    refine ⟨78375098565829087715581249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104500131421105450287441665 78375098565829087715581249)
    ·
      refine ⟨58781323924371815786685937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78375098565829087715581249 58781323924371815786685937)
      ·
        refine ⟨44085992943278861840014453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58781323924371815786685937 44085992943278861840014453)
        ·
          refine ⟨4133061838432393297501355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44085992943278861840014453 4133061838432393297501355)
          ·
            refine ⟨6199592757648589946252033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133061838432393297501355 6199592757648589946252033)
            ·
              refine ⟨4649694568236442459689025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6199592757648589946252033 4649694568236442459689025)
              ·
                refine ⟨3487270926177331844766769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649694568236442459689025 3487270926177331844766769)
                ·
                  refine ⟨2615453194632998883575077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487270926177331844766769 2615453194632998883575077)
                  ·
                    refine ⟨490397473993687290670327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2615453194632998883575077 490397473993687290670327)
                    ·
                      rfl

theorem cell23_2865137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_2865137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865137 prefixEnd_2865137 := by exact prefixLift 2865137
  have htrace : WordTrace (prefixWord ++ tailWord_2865137) baseStart_2865137 baseEnd_2865137 := by
    simpa [prefixWord, tailWord_2865137, baseEnd_2865137] using wordTrace_append hprefix tailTrace_2865137
  have hstable : (prefixWord ++ tailWord_2865137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865137).length < 2 ^ (prefixWord ++ tailWord_2865137).sum := by decide
  have hdescent : baseEnd_2865137 < baseStart_2865137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865150 : List Nat := [4, 2, 2, 2, 1, 1, 3, 8]
def baseStart_2865150 : Nat := 118140960795 + 2865150 * 2 ^ 59
def prefixEnd_2865150 : Nat := 4983230072969 + 3 ^ 40 * 2865150 * 2
def baseEnd_2865150 : Nat := 54488855452947048931423

theorem tailTrace_2865150 : CollatzResearch.WordTrace tailWord_2865150 prefixEnd_2865150 54488855452947048931423 := by
  unfold tailWord_2865150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062575696257294188458113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69667070380038902338443269 13062575696257294188458113)
  ·
    refine ⟨9796931772192970641343585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13062575696257294188458113 9796931772192970641343585)
    ·
      refine ⟨7347698829144727981007689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796931772192970641343585 7347698829144727981007689)
      ·
        refine ⟨5510774121858545985755767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7347698829144727981007689 5510774121858545985755767)
        ·
          refine ⟨8266161182787818978633651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5510774121858545985755767 8266161182787818978633651)
          ·
            refine ⟨12399241774181728467950477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266161182787818978633651 12399241774181728467950477)
            ·
              refine ⟨4649715665318148175481429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12399241774181728467950477 4649715665318148175481429)
              ·
                refine ⟨54488855452947048931423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4649715665318148175481429 54488855452947048931423)
                ·
                  rfl

theorem cell23_2865150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_2865150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865150 prefixEnd_2865150 := by exact prefixLift 2865150
  have htrace : WordTrace (prefixWord ++ tailWord_2865150) baseStart_2865150 baseEnd_2865150 := by
    simpa [prefixWord, tailWord_2865150, baseEnd_2865150] using wordTrace_append hprefix tailTrace_2865150
  have hstable : (prefixWord ++ tailWord_2865150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865150).length < 2 ^ (prefixWord ++ tailWord_2865150).sum := by decide
  have hdescent : baseEnd_2865150 < baseStart_2865150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865160 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2865160 : Nat := 118140960795 + 2865160 * 2 ^ 59
def prefixEnd_2865160 : Nat := 4983230072969 + 3 ^ 40 * 2865160 * 2
def baseEnd_2865160 : Nat := 1471204232036115282023375

theorem tailTrace_2865160 : CollatzResearch.WordTrace tailWord_2865160 prefixEnd_2865160 1471204232036115282023375 := by
  unfold tailWord_2865160
  simp only [CollatzResearch.WordTrace]
  refine ⟨52250485150011062607764467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69667313533348083477019289 52250485150011062607764467)
  ·
    refine ⟨78375727725016593911646701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52250485150011062607764467 78375727725016593911646701)
    ·
      refine ⟨29390897896881222716867513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78375727725016593911646701 29390897896881222716867513)
      ·
        refine ⟨22043173422660917037650635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29390897896881222716867513 22043173422660917037650635)
        ·
          refine ⟨33064760133991375556475953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22043173422660917037650635 33064760133991375556475953)
          ·
            refine ⟨24798570100493531667356965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33064760133991375556475953 24798570100493531667356965)
            ·
              refine ⟨4649731893842537187629431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24798570100493531667356965 4649731893842537187629431)
              ·
                refine ⟨6974597840763805781444147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649731893842537187629431 6974597840763805781444147)
                ·
                  refine ⟨10461896761145708672166221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974597840763805781444147 10461896761145708672166221)
                  ·
                    refine ⟨3923211285429640752062333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10461896761145708672166221 3923211285429640752062333)
                    ·
                      refine ⟨1471204232036115282023375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923211285429640752062333 1471204232036115282023375)
                      ·
                        rfl

theorem cell23_2865160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2865160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865160 prefixEnd_2865160 := by exact prefixLift 2865160
  have htrace : WordTrace (prefixWord ++ tailWord_2865160) baseStart_2865160 baseEnd_2865160 := by
    simpa [prefixWord, tailWord_2865160, baseEnd_2865160] using wordTrace_append hprefix tailTrace_2865160
  have hstable : (prefixWord ++ tailWord_2865160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865160).length < 2 ^ (prefixWord ++ tailWord_2865160).sum := by decide
  have hdescent : baseEnd_2865160 < baseStart_2865160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865165 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2865165 : Nat := 118140960795 + 2865165 * 2 ^ 59
def prefixEnd_2865165 : Nat := 4983230072969 + 3 ^ 40 * 2865165 * 2
def baseEnd_2865165 : Nat := 1471206799439387762460853

theorem tailTrace_2865165 : CollatzResearch.WordTrace tailWord_2865165 prefixEnd_2865165 1471206799439387762460853 := by
  unfold tailWord_2865165
  simp only [CollatzResearch.WordTrace]
  refine ⟨104501152665004011069460949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69667435110002674046307299 104501152665004011069460949)
  ·
    refine ⟨2449245765586031509440491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 104501152665004011069460949 2449245765586031509440491)
    ·
      refine ⟨3673868648379047264160737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2449245765586031509440491 3673868648379047264160737)
      ·
        refine ⟨2755401486284285448120553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3673868648379047264160737 2755401486284285448120553)
        ·
          refine ⟨2066551114713214086090415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755401486284285448120553 2066551114713214086090415)
          ·
            refine ⟨3099826672069821129135623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066551114713214086090415 3099826672069821129135623)
            ·
              refine ⟨4649740008104731693703435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3099826672069821129135623 4649740008104731693703435)
              ·
                refine ⟨6974610012157097540555153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649740008104731693703435 6974610012157097540555153)
                ·
                  refine ⟨5230957509117823155416365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6974610012157097540555153 5230957509117823155416365)
                  ·
                    refine ⟨1961609065919183683281137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5230957509117823155416365 1961609065919183683281137)
                    ·
                      refine ⟨1471206799439387762460853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961609065919183683281137 1471206799439387762460853)
                      ·
                        rfl

theorem cell23_2865165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2865165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865165 prefixEnd_2865165 := by exact prefixLift 2865165
  have htrace : WordTrace (prefixWord ++ tailWord_2865165) baseStart_2865165 baseEnd_2865165 := by
    simpa [prefixWord, tailWord_2865165, baseEnd_2865165] using wordTrace_append hprefix tailTrace_2865165
  have hstable : (prefixWord ++ tailWord_2865165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865165).length < 2 ^ (prefixWord ++ tailWord_2865165).sum := by decide
  have hdescent : baseEnd_2865165 < baseStart_2865165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865187 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 1, 3, 2]
def baseStart_2865187 : Nat := 118140960795 + 2865187 * 2 ^ 59
def prefixEnd_2865187 : Nat := 4983230072969 + 3 ^ 40 * 2865187 * 2
def baseEnd_2865187 : Nat := 1471218096013786676385751

theorem tailTrace_2865187 : CollatzResearch.WordTrace tailWord_2865187 prefixEnd_2865187 1471218096013786676385751 := by
  unfold tailWord_2865187
  simp only [CollatzResearch.WordTrace]
  refine ⟨104501955070924308826761815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69667970047282872551174543 104501955070924308826761815)
  ·
    refine ⟨156752932606386463240142723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104501955070924308826761815 156752932606386463240142723)
    ·
      refine ⟨235129398909579694860214085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156752932606386463240142723 235129398909579694860214085)
      ·
        refine ⟨44086762295546192786290141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235129398909579694860214085 44086762295546192786290141)
        ·
          refine ⟨16532535860829822294858803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44086762295546192786290141 16532535860829822294858803)
          ·
            refine ⟨24798803791244733442288205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16532535860829822294858803 24798803791244733442288205)
            ·
              refine ⟨9299551421716775040858077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24798803791244733442288205 9299551421716775040858077)
              ·
                refine ⟨3487331783143790640321779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9299551421716775040858077 3487331783143790640321779)
                ·
                  refine ⟨5230997674715685960482669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487331783143790640321779 5230997674715685960482669)
                  ·
                    refine ⟨1961624128018382235181001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5230997674715685960482669 1961624128018382235181001)
                    ·
                      refine ⟨1471218096013786676385751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961624128018382235181001 1471218096013786676385751)
                      ·
                        rfl

theorem cell23_2865187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_2865187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865187 prefixEnd_2865187 := by exact prefixLift 2865187
  have htrace : WordTrace (prefixWord ++ tailWord_2865187) baseStart_2865187 baseEnd_2865187 := by
    simpa [prefixWord, tailWord_2865187, baseEnd_2865187] using wordTrace_append hprefix tailTrace_2865187
  have hstable : (prefixWord ++ tailWord_2865187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865187).length < 2 ^ (prefixWord ++ tailWord_2865187).sum := by decide
  have hdescent : baseEnd_2865187 < baseStart_2865187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865194 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2865194 : Nat := 118140960795 + 2865194 * 2 ^ 59
def prefixEnd_2865194 : Nat := 4983230072969 + 3 ^ 40 * 2865194 * 2
def baseEnd_2865194 : Nat := 1471221690378368148998219

theorem tailTrace_2865194 : CollatzResearch.WordTrace tailWord_2865194 prefixEnd_2865194 1471221690378368148998219 := by
  unfold tailWord_2865194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26125552595474737255566659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69668140254599299348177757 26125552595474737255566659)
  ·
    refine ⟨39188328893212105883349989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26125552595474737255566659 39188328893212105883349989)
    ·
      refine ⟨7347811667477269853128123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39188328893212105883349989 7347811667477269853128123)
      ·
        refine ⟨11021717501215904779692185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347811667477269853128123 11021717501215904779692185)
        ·
          refine ⟨8266288125911928584769139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11021717501215904779692185 8266288125911928584769139)
          ·
            refine ⟨12399432188867892877153709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266288125911928584769139 12399432188867892877153709)
            ·
              refine ⟨4649787070825459828932641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12399432188867892877153709 4649787070825459828932641)
              ·
                refine ⟨3487340303119094871699481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649787070825459828932641 3487340303119094871699481)
                ·
                  refine ⟨2615505227339321153774611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487340303119094871699481 2615505227339321153774611)
                  ·
                    refine ⟨3923257841008981730661917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2615505227339321153774611 3923257841008981730661917)
                    ·
                      refine ⟨1471221690378368148998219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923257841008981730661917 1471221690378368148998219)
                      ·
                        rfl

theorem cell23_2865194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2865194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865194 prefixEnd_2865194 := by exact prefixLift 2865194
  have htrace : WordTrace (prefixWord ++ tailWord_2865194) baseStart_2865194 baseEnd_2865194 := by
    simpa [prefixWord, tailWord_2865194, baseEnd_2865194] using wordTrace_append hprefix tailTrace_2865194
  have hstable : (prefixWord ++ tailWord_2865194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865194).length < 2 ^ (prefixWord ++ tailWord_2865194).sum := by decide
  have hdescent : baseEnd_2865194 < baseStart_2865194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865203 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3]
def baseStart_2865203 : Nat := 118140960795 + 2865203 * 2 ^ 59
def prefixEnd_2865203 : Nat := 4983230072969 + 3 ^ 40 * 2865203 * 2
def baseEnd_2865203 : Nat := 1471226311704258613785677

theorem tailTrace_2865203 : CollatzResearch.WordTrace tailWord_2865203 prefixEnd_2865203 1471226311704258613785677 := by
  unfold tailWord_2865203
  simp only [CollatzResearch.WordTrace]
  refine ⟨104502538638866343559344263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69668359092577562372896175 104502538638866343559344263)
  ·
    refine ⟨156753807958299515339016395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104502538638866343559344263 156753807958299515339016395)
    ·
      refine ⟨235130711937449273008524593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156753807958299515339016395 235130711937449273008524593)
      ·
        refine ⟨176348033953086954756393445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235130711937449273008524593 176348033953086954756393445)
        ·
          refine ⟨33065256366203804016823771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176348033953086954756393445 33065256366203804016823771)
          ·
            refine ⟨49597884549305706025235657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33065256366203804016823771 49597884549305706025235657)
            ·
              refine ⟨37198413411979279518926743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49597884549305706025235657 37198413411979279518926743)
              ·
                refine ⟨55797620117968919278390115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37198413411979279518926743 55797620117968919278390115)
                ·
                  refine ⟨83696430176953378917585173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55797620117968919278390115 83696430176953378917585173)
                  ·
                    refine ⟨3923270164544689636761805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83696430176953378917585173 3923270164544689636761805)
                    ·
                      refine ⟨1471226311704258613785677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923270164544689636761805 1471226311704258613785677)
                      ·
                        rfl

theorem cell23_2865203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_2865203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865203 prefixEnd_2865203 := by exact prefixLift 2865203
  have htrace : WordTrace (prefixWord ++ tailWord_2865203) baseStart_2865203 baseEnd_2865203 := by
    simpa [prefixWord, tailWord_2865203, baseEnd_2865203] using wordTrace_append hprefix tailTrace_2865203
  have hstable : (prefixWord ++ tailWord_2865203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865203).length < 2 ^ (prefixWord ++ tailWord_2865203).sum := by decide
  have hdescent : baseEnd_2865203 < baseStart_2865203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865223 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 7]
def baseStart_2865223 : Nat := 118140960795 + 2865223 * 2 ^ 59
def prefixEnd_2865223 : Nat := 4983230072969 + 3 ^ 40 * 2865223 * 2
def baseEnd_2865223 : Nat := 163470731257483170615065

theorem tailTrace_2865223 : CollatzResearch.WordTrace tailWord_2865223 prefixEnd_2865223 163470731257483170615065 := by
  unfold tailWord_2865223
  simp only [CollatzResearch.WordTrace]
  refine ⟨104503268098793886975072323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69668845399195924650048215 104503268098793886975072323)
  ·
    refine ⟨156754902148190830462608485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104503268098793886975072323 156754902148190830462608485)
    ·
      refine ⟨29391544152785780711739091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156754902148190830462608485 29391544152785780711739091)
      ·
        refine ⟨44087316229178671067608637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29391544152785780711739091 44087316229178671067608637)
        ·
          refine ⟨16532743585942001650353239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44087316229178671067608637 16532743585942001650353239)
          ·
            refine ⟨24799115378913002475529859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16532743585942001650353239 24799115378913002475529859)
            ·
              refine ⟨37198673068369503713294789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24799115378913002475529859 37198673068369503713294789)
              ·
                refine ⟨6974751200319281946242773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37198673068369503713294789 6974751200319281946242773)
                ·
                  refine ⟨163470731257483170615065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6974751200319281946242773 163470731257483170615065)
                  ·
                    rfl

theorem cell23_2865223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 7].length) (baseStart_2865223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865223 prefixEnd_2865223 := by exact prefixLift 2865223
  have htrace : WordTrace (prefixWord ++ tailWord_2865223) baseStart_2865223 baseEnd_2865223 := by
    simpa [prefixWord, tailWord_2865223, baseEnd_2865223] using wordTrace_append hprefix tailTrace_2865223
  have hstable : (prefixWord ++ tailWord_2865223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865223).length < 2 ^ (prefixWord ++ tailWord_2865223).sum := by decide
  have hdescent : baseEnd_2865223 < baseStart_2865223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865257 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 5]
def baseStart_2865257 : Nat := 118140960795 + 2865257 * 2 ^ 59
def prefixEnd_2865257 : Nat := 4983230072969 + 3 ^ 40 * 2865257 * 2
def baseEnd_2865257 : Nat := 163472671073289044723381

theorem tailTrace_2865257 : CollatzResearch.WordTrace tailWord_2865257 prefixEnd_2865257 163472671073289044723381 := by
  unfold tailWord_2865257
  simp only [CollatzResearch.WordTrace]
  refine ⟨104504508180670710781810025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69669672120447140521206683 104504508180670710781810025)
  ·
    refine ⟨78378381135503033086357519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104504508180670710781810025 78378381135503033086357519)
    ·
      refine ⟨117567571703254549629536279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78378381135503033086357519 117567571703254549629536279)
      ·
        refine ⟨176351357554881824444304419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117567571703254549629536279 176351357554881824444304419)
        ·
          refine ⟨264527036332322736666456629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176351357554881824444304419 264527036332322736666456629)
          ·
            refine ⟨24799409656155256562480309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264527036332322736666456629 24799409656155256562480309)
            ·
              refine ⟨2324944655264555302732529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24799409656155256562480309 2324944655264555302732529)
              ·
                refine ⟨1743708491448416477049397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324944655264555302732529 1743708491448416477049397)
                ·
                  refine ⟨163472671073289044723381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1743708491448416477049397 163472671073289044723381)
                  ·
                    rfl

theorem cell23_2865257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 5].length) (baseStart_2865257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865257 prefixEnd_2865257 := by exact prefixLift 2865257
  have htrace : WordTrace (prefixWord ++ tailWord_2865257) baseStart_2865257 baseEnd_2865257 := by
    simpa [prefixWord, tailWord_2865257, baseEnd_2865257] using wordTrace_append hprefix tailTrace_2865257
  have hstable : (prefixWord ++ tailWord_2865257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865257).length < 2 ^ (prefixWord ++ tailWord_2865257).sum := by decide
  have hdescent : baseEnd_2865257 < baseStart_2865257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865263 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_2865263 : Nat := 118140960795 + 2865263 * 2 ^ 59
def prefixEnd_2865263 : Nat := 4983230072969 + 3 ^ 40 * 2865263 * 2
def baseEnd_2865263 : Nat := 1471257120543528379035401

theorem tailTrace_2865263 : CollatzResearch.WordTrace tailWord_2865263 prefixEnd_2865263 1471257120543528379035401 := by
  unfold tailWord_2865263
  simp only [CollatzResearch.WordTrace]
  refine ⟨104504727018648973806528443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69669818012432649204352295 104504727018648973806528443)
  ·
    refine ⟨156757090527973460709792665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104504727018648973806528443 156757090527973460709792665)
    ·
      refine ⟨117567817895980095532344499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156757090527973460709792665 117567817895980095532344499)
      ·
        refine ⟨176351726843970143298516749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117567817895980095532344499 176351726843970143298516749)
        ·
          refine ⟨66131897566488803736943781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176351726843970143298516749 66131897566488803736943781)
          ·
            refine ⟨12399730793716650700676959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66131897566488803736943781 12399730793716650700676959)
            ·
              refine ⟨18599596190574976051015439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12399730793716650700676959 18599596190574976051015439)
              ·
                refine ⟨27899394285862464076523159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18599596190574976051015439 27899394285862464076523159)
                ·
                  refine ⟨41849091428793696114784739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27899394285862464076523159 41849091428793696114784739)
                  ·
                    refine ⟨62773637143190544172177109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41849091428793696114784739 62773637143190544172177109)
                    ·
                      refine ⟨1471257120543528379035401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62773637143190544172177109 1471257120543528379035401)
                      ·
                        rfl

theorem cell23_2865263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_2865263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865263 prefixEnd_2865263 := by exact prefixLift 2865263
  have htrace : WordTrace (prefixWord ++ tailWord_2865263) baseStart_2865263 baseEnd_2865263 := by
    simpa [prefixWord, tailWord_2865263, baseEnd_2865263] using wordTrace_append hprefix tailTrace_2865263
  have hstable : (prefixWord ++ tailWord_2865263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865263).length < 2 ^ (prefixWord ++ tailWord_2865263).sum := by decide
  have hdescent : baseEnd_2865263 < baseStart_2865263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865330 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_2865330 : Nat := 118140960795 + 2865330 * 2 ^ 59
def prefixEnd_2865330 : Nat := 4983230072969 + 3 ^ 40 * 2865330 * 2
def baseEnd_2865330 : Nat := 163476835971931068544177

theorem tailTrace_2865330 : CollatzResearch.WordTrace tailWord_2865330 prefixEnd_2865330 163476835971931068544177 := by
  unfold tailWord_2865330
  simp only [CollatzResearch.WordTrace]
  refine ⟨26126792677351561062304361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69671447139604162832811629 26126792677351561062304361)
  ·
    refine ⟨19595094508013670796728271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26126792677351561062304361 19595094508013670796728271)
    ·
      refine ⟨29392641762020506195092407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19595094508013670796728271 29392641762020506195092407)
      ·
        refine ⟨44088962643030759292638611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29392641762020506195092407 44088962643030759292638611)
        ·
          refine ⟨66133443964546138938957917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44088962643030759292638611 66133443964546138938957917)
          ·
            refine ⟨24800041486704802102109219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66133443964546138938957917 24800041486704802102109219)
            ·
              refine ⟨37200062230057203153163829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24800041486704802102109219 37200062230057203153163829)
              ·
                refine ⟨3487505834067862795609109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37200062230057203153163829 3487505834067862795609109)
                ·
                  refine ⟨163476835971931068544177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3487505834067862795609109 163476835971931068544177)
                  ·
                    rfl

theorem cell23_2865330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_2865330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865330 prefixEnd_2865330 := by exact prefixLift 2865330
  have htrace : WordTrace (prefixWord ++ tailWord_2865330) baseStart_2865330 baseEnd_2865330 := by
    simpa [prefixWord, tailWord_2865330, baseEnd_2865330] using wordTrace_append hprefix tailTrace_2865330
  have hstable : (prefixWord ++ tailWord_2865330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865330).length < 2 ^ (prefixWord ++ tailWord_2865330).sum := by decide
  have hdescent : baseEnd_2865330 < baseStart_2865330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865344 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_2865344 : Nat := 118140960795 + 2865344 * 2 ^ 59
def prefixEnd_2865344 : Nat := 4983230072969 + 3 ^ 40 * 2865344 * 2
def baseEnd_2865344 : Nat := 1471298712476542562122529

theorem tailTrace_2865344 : CollatzResearch.WordTrace tailWord_2865344 prefixEnd_2865344 1471298712476542562122529 := by
  unfold tailWord_2865344
  simp only [CollatzResearch.WordTrace]
  refine ⟨52253840665677762320113543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69671787554237016426818057 52253840665677762320113543)
  ·
    refine ⟨78380760998516643480170315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52253840665677762320113543 78380760998516643480170315)
    ·
      refine ⟨117571141497774965220255473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78380760998516643480170315 117571141497774965220255473)
      ·
        refine ⟨88178356123331223915191605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117571141497774965220255473 88178356123331223915191605)
        ·
          refine ⟨8266720886562302242049213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88178356123331223915191605 8266720886562302242049213)
          ·
            refine ⟨3100020332460863340768455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8266720886562302242049213 3100020332460863340768455)
            ·
              refine ⟨4650030498691295011152683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100020332460863340768455 4650030498691295011152683)
              ·
                refine ⟨6975045748036942516729025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650030498691295011152683 6975045748036942516729025)
                ·
                  refine ⟨5231284311027706887546769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6975045748036942516729025 5231284311027706887546769)
                  ·
                    refine ⟨3923463233270780165660077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231284311027706887546769 3923463233270780165660077)
                    ·
                      refine ⟨1471298712476542562122529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923463233270780165660077 1471298712476542562122529)
                      ·
                        rfl

theorem cell23_2865344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_2865344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865344 prefixEnd_2865344 := by exact prefixLift 2865344
  have htrace : WordTrace (prefixWord ++ tailWord_2865344) baseStart_2865344 baseEnd_2865344 := by
    simpa [prefixWord, tailWord_2865344, baseEnd_2865344] using wordTrace_append hprefix tailTrace_2865344
  have hstable : (prefixWord ++ tailWord_2865344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865344).length < 2 ^ (prefixWord ++ tailWord_2865344).sum := by decide
  have hdescent : baseEnd_2865344 < baseStart_2865344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865367 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_2865367 : Nat := 118140960795 + 2865367 * 2 ^ 59
def prefixEnd_2865367 : Nat := 4983230072969 + 3 ^ 40 * 2865367 * 2
def baseEnd_2865367 : Nat := 1471310522531595972134923

theorem tailTrace_2865367 : CollatzResearch.WordTrace tailWord_2865367 prefixEnd_2865367 1471310522531595972134923 := by
  unfold tailWord_2865367
  simp only [CollatzResearch.WordTrace]
  refine ⟨104508520210272199568314355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69672346806848133045542903 104508520210272199568314355)
  ·
    refine ⟨156762780315408299352471533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104508520210272199568314355 156762780315408299352471533)
    ·
      refine ⟨58786042618278112257176825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156762780315408299352471533 58786042618278112257176825)
      ·
        refine ⟨44089531963708584192882619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58786042618278112257176825 44089531963708584192882619)
        ·
          refine ⟨66134297945562876289323929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44089531963708584192882619 66134297945562876289323929)
          ·
            refine ⟨49600723459172157216992947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66134297945562876289323929 49600723459172157216992947)
            ·
              refine ⟨74401085188758235825489421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49600723459172157216992947 74401085188758235825489421)
              ·
                refine ⟨27900406945784338434558533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74401085188758235825489421 27900406945784338434558533)
                ·
                  refine ⟨5231326302334563456479725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27900406945784338434558533 5231326302334563456479725)
                  ·
                    refine ⟨1961747363375461296179897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5231326302334563456479725 1961747363375461296179897)
                    ·
                      refine ⟨1471310522531595972134923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961747363375461296179897 1471310522531595972134923)
                      ·
                        rfl

theorem cell23_2865367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_2865367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865367 prefixEnd_2865367 := by exact prefixLift 2865367
  have htrace : WordTrace (prefixWord ++ tailWord_2865367) baseStart_2865367 baseEnd_2865367 := by
    simpa [prefixWord, tailWord_2865367, baseEnd_2865367] using wordTrace_append hprefix tailTrace_2865367
  have hstable : (prefixWord ++ tailWord_2865367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865367).length < 2 ^ (prefixWord ++ tailWord_2865367).sum := by decide
  have hdescent : baseEnd_2865367 < baseStart_2865367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865394 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_2865394 : Nat := 118140960795 + 2865394 * 2 ^ 59
def prefixEnd_2865394 : Nat := 4983230072969 + 3 ^ 40 * 2865394 * 2
def baseEnd_2865394 : Nat := 490441462169755788832433

theorem tailTrace_2865394 : CollatzResearch.WordTrace tailWord_2865394 prefixEnd_2865394 490441462169755788832433 := by
  unfold tailWord_2865394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26127376245293595794886809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69673003320782922119698157 26127376245293595794886809)
  ·
    refine ⟨19595532183970196846165107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26127376245293595794886809 19595532183970196846165107)
    ·
      refine ⟨29393298275955295269247661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19595532183970196846165107 29393298275955295269247661)
      ·
        refine ⟨11022486853483235725967873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29393298275955295269247661 11022486853483235725967873)
        ·
          refine ⟨8266865140112426794475905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11022486853483235725967873 8266865140112426794475905)
          ·
            refine ⟨6200148855084320095856929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8266865140112426794475905 6200148855084320095856929)
            ·
              refine ⟨4650111641313240071892697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200148855084320095856929 4650111641313240071892697)
              ·
                refine ⟨3487583730984930053919523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650111641313240071892697 3487583730984930053919523)
                ·
                  refine ⟨5231375596477395080879285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487583730984930053919523 5231375596477395080879285)
                  ·
                    refine ⟨490441462169755788832433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5231375596477395080879285 490441462169755788832433)
                    ·
                      rfl

theorem cell23_2865394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_2865394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865394 prefixEnd_2865394 := by exact prefixLift 2865394
  have htrace : WordTrace (prefixWord ++ tailWord_2865394) baseStart_2865394 baseEnd_2865394 := by
    simpa [prefixWord, tailWord_2865394, baseEnd_2865394] using wordTrace_append hprefix tailTrace_2865394
  have hstable : (prefixWord ++ tailWord_2865394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865394).length < 2 ^ (prefixWord ++ tailWord_2865394).sum := by decide
  have hdescent : baseEnd_2865394 < baseStart_2865394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865400 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_2865400 : Nat := 118140960795 + 2865400 * 2 ^ 59
def prefixEnd_2865400 : Nat := 4983230072969 + 3 ^ 40 * 2865400 * 2
def baseEnd_2865400 : Nat := 1471327467393194343022271

theorem tailTrace_2865400 : CollatzResearch.WordTrace tailWord_2865400 prefixEnd_2865400 1471327467393194343022271 := by
  unfold tailWord_2865400
  simp only [CollatzResearch.WordTrace]
  refine ⟨52254861909576323102132827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69673149212768430802843769 52254861909576323102132827)
  ·
    refine ⟨78382292864364484653199241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52254861909576323102132827 78382292864364484653199241)
    ·
      refine ⟨58786719648273363489899431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78382292864364484653199241 58786719648273363489899431)
      ·
        refine ⟨88180079472410045234849147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58786719648273363489899431 88180079472410045234849147)
        ·
          refine ⟨132270119208615067852273721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88180079472410045234849147 132270119208615067852273721)
          ·
            refine ⟨99202589406461300889205291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132270119208615067852273721 99202589406461300889205291)
            ·
              refine ⟨148803884109691951333807937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99202589406461300889205291 148803884109691951333807937)
              ·
                refine ⟨111602913082268963500355953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148803884109691951333807937 111602913082268963500355953)
                ·
                  refine ⟨83702184811701722625266965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111602913082268963500355953 83702184811701722625266965)
                  ·
                    refine ⟨3923539913048518248059389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83702184811701722625266965 3923539913048518248059389)
                    ·
                      refine ⟨1471327467393194343022271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923539913048518248059389 1471327467393194343022271)
                      ·
                        rfl

theorem cell23_2865400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_2865400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865400 prefixEnd_2865400 := by exact prefixLift 2865400
  have htrace : WordTrace (prefixWord ++ tailWord_2865400) baseStart_2865400 baseEnd_2865400 := by
    simpa [prefixWord, tailWord_2865400, baseEnd_2865400] using wordTrace_append hprefix tailTrace_2865400
  have hstable : (prefixWord ++ tailWord_2865400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865400).length < 2 ^ (prefixWord ++ tailWord_2865400).sum := by decide
  have hdescent : baseEnd_2865400 < baseStart_2865400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865417 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_2865417 : Nat := 118140960795 + 2865417 * 2 ^ 59
def prefixEnd_2865417 : Nat := 4983230072969 + 3 ^ 40 * 2865417 * 2
def baseEnd_2865417 : Nat := 1471336196564320776509693

theorem tailTrace_2865417 : CollatzResearch.WordTrace tailWord_2865417 prefixEnd_2865417 1471336196564320776509693 := by
  unfold tailWord_2865417
  simp only [CollatzResearch.WordTrace]
  refine ⟨104510343860091058107634505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69673562573394038738423003 104510343860091058107634505)
  ·
    refine ⟨78382757895068293580725879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104510343860091058107634505 78382757895068293580725879)
    ·
      refine ⟨117574136842602440371088819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78382757895068293580725879 117574136842602440371088819)
      ·
        refine ⟨176361205263903660556633229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117574136842602440371088819 176361205263903660556633229)
        ·
          refine ⟨66135451973963872708737461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176361205263903660556633229 66135451973963872708737461)
          ·
            refine ⟨6200198622559113066444137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66135451973963872708737461 6200198622559113066444137)
            ·
              refine ⟨4650148966919334799833103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200198622559113066444137 4650148966919334799833103)
              ·
                refine ⟨6975223450379002199749655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650148966919334799833103 6975223450379002199749655)
                ·
                  refine ⟨10462835175568503299624483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6975223450379002199749655 10462835175568503299624483)
                  ·
                    refine ⟨15694252763352754949436725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10462835175568503299624483 15694252763352754949436725)
                    ·
                      refine ⟨1471336196564320776509693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15694252763352754949436725 1471336196564320776509693)
                      ·
                        rfl

theorem cell23_2865417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_2865417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865417 prefixEnd_2865417 := by exact prefixLift 2865417
  have htrace : WordTrace (prefixWord ++ tailWord_2865417) baseStart_2865417 baseEnd_2865417 := by
    simpa [prefixWord, tailWord_2865417, baseEnd_2865417] using wordTrace_append hprefix tailTrace_2865417
  have hstable : (prefixWord ++ tailWord_2865417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865417).length < 2 ^ (prefixWord ++ tailWord_2865417).sum := by decide
  have hdescent : baseEnd_2865417 < baseStart_2865417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865431 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2865431 : Nat := 118140960795 + 2865431 * 2 ^ 59
def prefixEnd_2865431 : Nat := 4983230072969 + 3 ^ 40 * 2865431 * 2
def baseEnd_2865431 : Nat := 1471343385293483721734629

theorem tailTrace_2865431 : CollatzResearch.WordTrace tailWord_2865431 prefixEnd_2865431 1471343385293483721734629 := by
  unfold tailWord_2865431
  simp only [CollatzResearch.WordTrace]
  refine ⟨104510854482040338498644147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69673902988026892332429431 104510854482040338498644147)
  ·
    refine ⟨156766281723060507747966221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104510854482040338498644147 156766281723060507747966221)
    ·
      refine ⟨58787355646147690405487333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156766281723060507747966221 58787355646147690405487333)
      ·
        refine ⟨11022629183652691951028875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58787355646147690405487333 11022629183652691951028875)
        ·
          refine ⟨16533943775479037926543313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11022629183652691951028875 16533943775479037926543313)
          ·
            refine ⟨12400457831609278444907485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16533943775479037926543313 12400457831609278444907485)
            ·
              refine ⟨4650171686853479416840307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12400457831609278444907485 4650171686853479416840307)
              ·
                refine ⟨6975257530280219125260461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650171686853479416840307 6975257530280219125260461)
                ·
                  refine ⟨2615721573855082171972673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6975257530280219125260461 2615721573855082171972673)
                  ·
                    refine ⟨1961791180391311628979505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2615721573855082171972673 1961791180391311628979505)
                    ·
                      refine ⟨1471343385293483721734629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961791180391311628979505 1471343385293483721734629)
                      ·
                        rfl

theorem cell23_2865431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2865431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865431 prefixEnd_2865431 := by exact prefixLift 2865431
  have htrace : WordTrace (prefixWord ++ tailWord_2865431) baseStart_2865431 baseEnd_2865431 := by
    simpa [prefixWord, tailWord_2865431, baseEnd_2865431] using wordTrace_append hprefix tailTrace_2865431
  have hstable : (prefixWord ++ tailWord_2865431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865431).length < 2 ^ (prefixWord ++ tailWord_2865431).sum := by decide
  have hdescent : baseEnd_2865431 < baseStart_2865431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865448 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2865448 : Nat := 118140960795 + 2865448 * 2 ^ 59
def prefixEnd_2865448 : Nat := 4983230072969 + 3 ^ 40 * 2865448 * 2
def baseEnd_2865448 : Nat := 1471352114464610155222051

theorem tailTrace_2865448 : CollatzResearch.WordTrace tailWord_2865448 prefixEnd_2865448 1471352114464610155222051 := by
  unfold tailWord_2865448
  simp only [CollatzResearch.WordTrace]
  refine ⟨52255737261489375201006499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69674316348652500268008665 52255737261489375201006499)
  ·
    refine ⟨78383605892234062801509749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52255737261489375201006499 78383605892234062801509749)
    ·
      refine ⟨7348463052396943387641539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78383605892234062801509749 7348463052396943387641539)
      ·
        refine ⟨11022694578595415081462309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348463052396943387641539 11022694578595415081462309)
        ·
          refine ⟨2066755233486640327774183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11022694578595415081462309 2066755233486640327774183)
          ·
            refine ⟨3100132850229960491661275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066755233486640327774183 3100132850229960491661275)
            ·
              refine ⟨4650199275344940737491913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100132850229960491661275 4650199275344940737491913)
              ·
                refine ⟨3487649456508705553118935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650199275344940737491913 3487649456508705553118935)
                ·
                  refine ⟨5231474184763058329678403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487649456508705553118935 5231474184763058329678403)
                  ·
                    refine ⟨7847211277144587494517605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5231474184763058329678403 7847211277144587494517605)
                    ·
                      refine ⟨1471352114464610155222051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7847211277144587494517605 1471352114464610155222051)
                      ·
                        rfl

theorem cell23_2865448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2865448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865448 prefixEnd_2865448 := by exact prefixLift 2865448
  have htrace : WordTrace (prefixWord ++ tailWord_2865448) baseStart_2865448 baseEnd_2865448 := by
    simpa [prefixWord, tailWord_2865448, baseEnd_2865448] using wordTrace_append hprefix tailTrace_2865448
  have hstable : (prefixWord ++ tailWord_2865448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865448).length < 2 ^ (prefixWord ++ tailWord_2865448).sum := by decide
  have hdescent : baseEnd_2865448 < baseStart_2865448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865507 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2865507 : Nat := 118140960795 + 2865507 * 2 ^ 59
def prefixEnd_2865507 : Nat := 4983230072969 + 3 ^ 40 * 2865507 * 2
def baseEnd_2865507 : Nat := 1471382409823225424384279

theorem tailTrace_2865507 : CollatzResearch.WordTrace tailWord_2865507 prefixEnd_2865507 1471382409823225424384279 := by
  unfold tailWord_2865507
  simp only [CollatzResearch.WordTrace]
  refine ⟨104513626429765003478410775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69675750953176668985607183 104513626429765003478410775)
  ·
    refine ⟨156770439644647505217616163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104513626429765003478410775 156770439644647505217616163)
    ·
      refine ⟨235155659466971257826424245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156770439644647505217616163 235155659466971257826424245)
      ·
        refine ⟨22045843075028555421227273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235155659466971257826424245 22045843075028555421227273)
        ·
          refine ⟨16534382306271416565920455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22045843075028555421227273 16534382306271416565920455)
          ·
            refine ⟨24801573459407124848880683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16534382306271416565920455 24801573459407124848880683)
            ·
              refine ⟨37202360189110687273321025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24801573459407124848880683 37202360189110687273321025)
              ·
                refine ⟨27901770141833015454990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37202360189110687273321025 27901770141833015454990769)
                ·
                  refine ⟨20926327606374761591243077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27901770141833015454990769 20926327606374761591243077)
                  ·
                    refine ⟨3923686426195267798358077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20926327606374761591243077 3923686426195267798358077)
                    ·
                      refine ⟨1471382409823225424384279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923686426195267798358077 1471382409823225424384279)
                      ·
                        rfl

theorem cell23_2865507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2865507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865507 prefixEnd_2865507 := by exact prefixLift 2865507
  have htrace : WordTrace (prefixWord ++ tailWord_2865507) baseStart_2865507 baseEnd_2865507 := by
    simpa [prefixWord, tailWord_2865507, baseEnd_2865507] using wordTrace_append hprefix tailTrace_2865507
  have hstable : (prefixWord ++ tailWord_2865507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865507).length < 2 ^ (prefixWord ++ tailWord_2865507).sum := by decide
  have hdescent : baseEnd_2865507 < baseStart_2865507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865517 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2865517 : Nat := 118140960795 + 2865517 * 2 ^ 59
def prefixEnd_2865517 : Nat := 4983230072969 + 3 ^ 40 * 2865517 * 2
def baseEnd_2865517 : Nat := 1471387544629770385259233

theorem tailTrace_2865517 : CollatzResearch.WordTrace tailWord_2865517 prefixEnd_2865517 1471387544629770385259233 := by
  unfold tailWord_2865517
  simp only [CollatzResearch.WordTrace]
  refine ⟨104513991159728775186274805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69675994106485850124183203 104513991159728775186274805)
  ·
    refine ⟨9798186671224572673713263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104513991159728775186274805 9798186671224572673713263)
    ·
      refine ⟨14697280006836859010569895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9798186671224572673713263 14697280006836859010569895)
      ·
        refine ⟨22045920010255288515854843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14697280006836859010569895 22045920010255288515854843)
        ·
          refine ⟨33068880015382932773782265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22045920010255288515854843 33068880015382932773782265)
          ·
            refine ⟨24801660011537199580336699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33068880015382932773782265 24801660011537199580336699)
            ·
              refine ⟨37202490017305799370505049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24801660011537199580336699 37202490017305799370505049)
              ·
                refine ⟨27901867512979349527878787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37202490017305799370505049 27901867512979349527878787)
                ·
                  refine ⟨41852801269469024291818181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27901867512979349527878787 41852801269469024291818181)
                  ·
                    refine ⟨7847400238025442054715909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41852801269469024291818181 7847400238025442054715909)
                    ·
                      refine ⟨1471387544629770385259233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7847400238025442054715909 1471387544629770385259233)
                      ·
                        rfl

theorem cell23_2865517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2865517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865517 prefixEnd_2865517 := by exact prefixLift 2865517
  have htrace : WordTrace (prefixWord ++ tailWord_2865517) baseStart_2865517 baseEnd_2865517 := by
    simpa [prefixWord, tailWord_2865517, baseEnd_2865517] using wordTrace_append hprefix tailTrace_2865517
  have hstable : (prefixWord ++ tailWord_2865517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865517).length < 2 ^ (prefixWord ++ tailWord_2865517).sum := by decide
  have hdescent : baseEnd_2865517 < baseStart_2865517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865525 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2865525 : Nat := 118140960795 + 2865525 * 2 ^ 59
def prefixEnd_2865525 : Nat := 4983230072969 + 3 ^ 40 * 2865525 * 2
def baseEnd_2865525 : Nat := 1471391652475006353959197

theorem tailTrace_2865525 : CollatzResearch.WordTrace tailWord_2865525 prefixEnd_2865525 1471391652475006353959197 := by
  unfold tailWord_2865525
  simp only [CollatzResearch.WordTrace]
  refine ⟨104514282943699792552566029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69676188629133195035044019 104514282943699792552566029)
  ·
    refine ⟨39192856103887422207212261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104514282943699792552566029 39192856103887422207212261)
    ·
      refine ⟨7348660519478891663852299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39192856103887422207212261 7348660519478891663852299)
      ·
        refine ⟨11022990779218337495778449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348660519478891663852299 11022990779218337495778449)
        ·
          refine ⟨8267243084413753121833837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11022990779218337495778449 8267243084413753121833837)
          ·
            refine ⟨3100216156655157420687689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8267243084413753121833837 3100216156655157420687689)
            ·
              refine ⟨2325162117491368065515767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3100216156655157420687689 2325162117491368065515767)
              ·
                refine ⟨3487743176237052098273651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325162117491368065515767 3487743176237052098273651)
                ·
                  refine ⟨5231614764355578147410477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487743176237052098273651 5231614764355578147410477)
                  ·
                    refine ⟨1961855536633341805278929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5231614764355578147410477 1961855536633341805278929)
                    ·
                      refine ⟨1471391652475006353959197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961855536633341805278929 1471391652475006353959197)
                      ·
                        rfl

theorem cell23_2865525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2865525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865525 prefixEnd_2865525 := by exact prefixLift 2865525
  have htrace : WordTrace (prefixWord ++ tailWord_2865525) baseStart_2865525 baseEnd_2865525 := by
    simpa [prefixWord, tailWord_2865525, baseEnd_2865525] using wordTrace_append hprefix tailTrace_2865525
  have hstable : (prefixWord ++ tailWord_2865525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865525).length < 2 ^ (prefixWord ++ tailWord_2865525).sum := by decide
  have hdescent : baseEnd_2865525 < baseStart_2865525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865544 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 5]
def baseStart_2865544 : Nat := 118140960795 + 2865544 * 2 ^ 59
def prefixEnd_2865544 : Nat := 4983230072969 + 3 ^ 40 * 2865544 * 2
def baseEnd_2865544 : Nat := 163489045400826864402401

theorem tailTrace_2865544 : CollatzResearch.WordTrace tailWord_2865544 prefixEnd_2865544 163489045400826864402401 := by
  unfold tailWord_2865544
  simp only [CollatzResearch.WordTrace]
  refine ⟨52257487965315479398753843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69676650620420639198338457 52257487965315479398753843)
  ·
    refine ⟨78386231947973219098130765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52257487965315479398753843 78386231947973219098130765)
    ·
      refine ⟨29394836980489957161799037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78386231947973219098130765 29394836980489957161799037)
      ·
        refine ⟨11023063867683733935674639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29394836980489957161799037 11023063867683733935674639)
        ·
          refine ⟨16534595801525600903511959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023063867683733935674639 16534595801525600903511959)
          ·
            refine ⟨24801893702288401355267939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16534595801525600903511959 24801893702288401355267939)
            ·
              refine ⟨37202840553432602032901909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24801893702288401355267939 37202840553432602032901909)
              ·
                refine ⟨1743883150942153220292277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37202840553432602032901909 1743883150942153220292277)
                ·
                  refine ⟨163489045400826864402401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1743883150942153220292277 163489045400826864402401)
                  ·
                    rfl

theorem cell23_2865544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 5].length) (baseStart_2865544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865544 prefixEnd_2865544 := by exact prefixLift 2865544
  have htrace : WordTrace (prefixWord ++ tailWord_2865544) baseStart_2865544 baseEnd_2865544 := by
    simpa [prefixWord, tailWord_2865544, baseEnd_2865544] using wordTrace_append hprefix tailTrace_2865544
  have hstable : (prefixWord ++ tailWord_2865544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865544).length < 2 ^ (prefixWord ++ tailWord_2865544).sum := by decide
  have hdescent : baseEnd_2865544 < baseStart_2865544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865577 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_2865577 : Nat := 118140960795 + 2865577 * 2 ^ 59
def prefixEnd_2865577 : Nat := 4983230072969 + 3 ^ 40 * 2865577 * 2
def baseEnd_2865577 : Nat := 1471418353469040150508957

theorem tailTrace_2865577 : CollatzResearch.WordTrace tailWord_2865577 prefixEnd_2865577 1471418353469040150508957 := by
  unfold tailWord_2865577
  simp only [CollatzResearch.WordTrace]
  refine ⟨104516179539511405433458985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69677453026340936955639323 104516179539511405433458985)
  ·
    refine ⟨78387134654633554075094239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104516179539511405433458985 78387134654633554075094239)
    ·
      refine ⟨117580701981950331112641359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78387134654633554075094239 117580701981950331112641359)
      ·
        refine ⟨176371052972925496668962039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117580701981950331112641359 176371052972925496668962039)
        ·
          refine ⟨264556579459388245003443059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176371052972925496668962039 264556579459388245003443059)
          ·
            refine ⟨396834869189082367505164589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264556579459388245003443059 396834869189082367505164589)
            ·
              refine ⟨148813075945905887814436721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396834869189082367505164589 148813075945905887814436721)
              ·
                refine ⟨111609806959429415860827541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148813075945905887814436721 111609806959429415860827541)
                ·
                  refine ⟨5231709701223253868476291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111609806959429415860827541 5231709701223253868476291)
                  ·
                    refine ⟨7847564551834880802714437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5231709701223253868476291 7847564551834880802714437)
                    ·
                      refine ⟨1471418353469040150508957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7847564551834880802714437 1471418353469040150508957)
                      ·
                        rfl

theorem cell23_2865577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_2865577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865577 prefixEnd_2865577 := by exact prefixLift 2865577
  have htrace : WordTrace (prefixWord ++ tailWord_2865577) baseStart_2865577 baseEnd_2865577 := by
    simpa [prefixWord, tailWord_2865577, baseEnd_2865577] using wordTrace_append hprefix tailTrace_2865577
  have hstable : (prefixWord ++ tailWord_2865577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865577).length < 2 ^ (prefixWord ++ tailWord_2865577).sum := by decide
  have hdescent : baseEnd_2865577 < baseStart_2865577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865594 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_2865594 : Nat := 118140960795 + 2865594 * 2 ^ 59
def prefixEnd_2865594 : Nat := 4983230072969 + 3 ^ 40 * 2865594 * 2
def baseEnd_2865594 : Nat := 1471427082640166583996379

theorem tailTrace_2865594 : CollatzResearch.WordTrace tailWord_2865594 prefixEnd_2865594 1471427082640166583996379 := by
  unfold tailWord_2865594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26129199895112454334206959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69677866386966544891218557 26129199895112454334206959)
  ·
    refine ⟨39193799842668681501310439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26129199895112454334206959 39193799842668681501310439)
    ·
      refine ⟨58790699764003022251965659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39193799842668681501310439 58790699764003022251965659)
      ·
        refine ⟨88186049646004533377948489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58790699764003022251965659 88186049646004533377948489)
        ·
          refine ⟨66139537234503400033461367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88186049646004533377948489 66139537234503400033461367)
          ·
            refine ⟨99209305851755100050192051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66139537234503400033461367 99209305851755100050192051)
            ·
              refine ⟨148813958777632650075288077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99209305851755100050192051 148813958777632650075288077)
              ·
                refine ⟨55805234541612243778233029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148813958777632650075288077 55805234541612243778233029)
                ·
                  refine ⟨10463481476552295708418693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55805234541612243778233029 10463481476552295708418693)
                  ·
                    refine ⟨1961902776853555445328505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10463481476552295708418693 1961902776853555445328505)
                    ·
                      refine ⟨1471427082640166583996379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961902776853555445328505 1471427082640166583996379)
                      ·
                        rfl

theorem cell23_2865594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_2865594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865594 prefixEnd_2865594 := by exact prefixLift 2865594
  have htrace : WordTrace (prefixWord ++ tailWord_2865594) baseStart_2865594 baseEnd_2865594 := by
    simpa [prefixWord, tailWord_2865594, baseEnd_2865594] using wordTrace_append hprefix tailTrace_2865594
  have hstable : (prefixWord ++ tailWord_2865594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865594).length < 2 ^ (prefixWord ++ tailWord_2865594).sum := by decide
  have hdescent : baseEnd_2865594 < baseStart_2865594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865614 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2865614 : Nat := 118140960795 + 2865614 * 2 ^ 59
def prefixEnd_2865614 : Nat := 4983230072969 + 3 ^ 40 * 2865614 * 2
def baseEnd_2865614 : Nat := 1471437352253256505746287

theorem tailTrace_2865614 : CollatzResearch.WordTrace tailWord_2865614 prefixEnd_2865614 1471437352253256505746287 := by
  unfold tailWord_2865614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13064691130047170094069487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69678352693584907168370597 13064691130047170094069487)
  ·
    refine ⟨19597036695070755141104231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13064691130047170094069487 19597036695070755141104231)
    ·
      refine ⟨29395555042606132711656347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597036695070755141104231 29395555042606132711656347)
      ·
        refine ⟨44093332563909199067484521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29395555042606132711656347 44093332563909199067484521)
        ·
          refine ⟨33069999422931899300613391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44093332563909199067484521 33069999422931899300613391)
          ·
            refine ⟨49604999134397848950920087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33069999422931899300613391 49604999134397848950920087)
            ·
              refine ⟨74407498701596773426380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49604999134397848950920087 74407498701596773426380131)
              ·
                refine ⟨111611248052395160139570197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74407498701596773426380131 111611248052395160139570197)
                ·
                  refine ⟨5231777252456023131542353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111611248052395160139570197 5231777252456023131542353)
                  ·
                    refine ⟨3923832939342017348656765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231777252456023131542353 3923832939342017348656765)
                    ·
                      refine ⟨1471437352253256505746287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923832939342017348656765 1471437352253256505746287)
                      ·
                        rfl

theorem cell23_2865614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2865614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865614 prefixEnd_2865614 := by exact prefixLift 2865614
  have htrace : WordTrace (prefixWord ++ tailWord_2865614) baseStart_2865614 baseEnd_2865614 := by
    simpa [prefixWord, tailWord_2865614, baseEnd_2865614] using wordTrace_append hprefix tailTrace_2865614
  have hstable : (prefixWord ++ tailWord_2865614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865614).length < 2 ^ (prefixWord ++ tailWord_2865614).sum := by decide
  have hdescent : baseEnd_2865614 < baseStart_2865614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865631 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_2865631 : Nat := 118140960795 + 2865631 * 2 ^ 59
def prefixEnd_2865631 : Nat := 4983230072969 + 3 ^ 40 * 2865631 * 2
def baseEnd_2865631 : Nat := 1471446081424382939233709

theorem tailTrace_2865631 : CollatzResearch.WordTrace tailWord_2865631 prefixEnd_2865631 1471446081424382939233709 := by
  unfold tailWord_2865631
  simp only [CollatzResearch.WordTrace]
  refine ⟨104518149081315772655924747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69678766054210515103949831 104518149081315772655924747)
  ·
    refine ⟨156777223621973658983887121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104518149081315772655924747 156777223621973658983887121)
    ·
      refine ⟨117582917716480244237915341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156777223621973658983887121 117582917716480244237915341)
      ·
        refine ⟨44093594143680091589218253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117582917716480244237915341 44093594143680091589218253)
        ·
          refine ⟨16535097803880034345956845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44093594143680091589218253 16535097803880034345956845)
          ·
            refine ⟨6200661676455012879733817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16535097803880034345956845 6200661676455012879733817)
            ·
              refine ⟨4650496257341259659800363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200661676455012879733817 4650496257341259659800363)
              ·
                refine ⟨6975744386011889489700545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650496257341259659800363 6975744386011889489700545)
                ·
                  refine ⟨5231808289508917117275409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6975744386011889489700545 5231808289508917117275409)
                  ·
                    refine ⟨3923856217131687837956557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231808289508917117275409 3923856217131687837956557)
                    ·
                      refine ⟨1471446081424382939233709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923856217131687837956557 1471446081424382939233709)
                      ·
                        rfl

theorem cell23_2865631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_2865631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865631 prefixEnd_2865631 := by exact prefixLift 2865631
  have htrace : WordTrace (prefixWord ++ tailWord_2865631) baseStart_2865631 baseEnd_2865631 := by
    simpa [prefixWord, tailWord_2865631, baseEnd_2865631] using wordTrace_append hprefix tailTrace_2865631
  have hstable : (prefixWord ++ tailWord_2865631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865631).length < 2 ^ (prefixWord ++ tailWord_2865631).sum := by decide
  have hdescent : baseEnd_2865631 < baseStart_2865631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865654 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2865654 : Nat := 118140960795 + 2865654 * 2 ^ 59
def prefixEnd_2865654 : Nat := 4983230072969 + 3 ^ 40 * 2865654 * 2
def baseEnd_2865654 : Nat := 1471457891479436349246103

theorem tailTrace_2865654 : CollatzResearch.WordTrace tailWord_2865654 prefixEnd_2865654 1471457891479436349246103 := by
  unfold tailWord_2865654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532436747514527974000751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69679325306821631722674677 6532436747514527974000751)
  ·
    refine ⟨9798655121271791961001127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6532436747514527974000751 9798655121271791961001127)
    ·
      refine ⟨14697982681907687941501691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9798655121271791961001127 14697982681907687941501691)
      ·
        refine ⟨22046974022861531912252537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14697982681907687941501691 22046974022861531912252537)
        ·
          refine ⟨16535230517146148934189403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22046974022861531912252537 16535230517146148934189403)
          ·
            refine ⟨24802845775719223401284105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16535230517146148934189403 24802845775719223401284105)
            ·
              refine ⟨18602134331789417550963079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24802845775719223401284105 18602134331789417550963079)
              ·
                refine ⟨27903201497684126326444619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18602134331789417550963079 27903201497684126326444619)
                ·
                  refine ⟨41854802246526189489666929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27903201497684126326444619 41854802246526189489666929)
                  ·
                    refine ⟨31391101684894642117250197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41854802246526189489666929 31391101684894642117250197)
                    ·
                      refine ⟨1471457891479436349246103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31391101684894642117250197 1471457891479436349246103)
                      ·
                        rfl

theorem cell23_2865654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2865654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865654 prefixEnd_2865654 := by exact prefixLift 2865654
  have htrace : WordTrace (prefixWord ++ tailWord_2865654) baseStart_2865654 baseEnd_2865654 := by
    simpa [prefixWord, tailWord_2865654, baseEnd_2865654] using wordTrace_append hprefix tailTrace_2865654
  have hstable : (prefixWord ++ tailWord_2865654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865654).length < 2 ^ (prefixWord ++ tailWord_2865654).sum := by decide
  have hdescent : baseEnd_2865654 < baseStart_2865654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865661 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_2865661 : Nat := 118140960795 + 2865661 * 2 ^ 59
def prefixEnd_2865661 : Nat := 4983230072969 + 3 ^ 40 * 2865661 * 2
def baseEnd_2865661 : Nat := 1471461485844017821858571

theorem tailTrace_2865661 : CollatzResearch.WordTrace tailWord_2865661 prefixEnd_2865661 1471461485844017821858571 := by
  unfold tailWord_2865661
  simp only [CollatzResearch.WordTrace]
  refine ⟨104519243271207087779516837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69679495514138058519677891 104519243271207087779516837)
  ·
    refine ⟨19597358113351328958659407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104519243271207087779516837 19597358113351328958659407)
    ·
      refine ⟨29396037170026993437989111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597358113351328958659407 29396037170026993437989111)
      ·
        refine ⟨44094055755040490156983667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29396037170026993437989111 44094055755040490156983667)
        ·
          refine ⟨66141083632560735235475501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44094055755040490156983667 66141083632560735235475501)
          ·
            refine ⟨24802906362210275713303313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66141083632560735235475501 24802906362210275713303313)
            ·
              refine ⟨18602179771657706784977485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24802906362210275713303313 18602179771657706784977485)
              ·
                refine ⟨6975817414371640044366557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18602179771657706784977485 6975817414371640044366557)
                ·
                  refine ⟨2615931530389365016637459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6975817414371640044366557 2615931530389365016637459)
                  ·
                    refine ⟨3923897295584047524956189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2615931530389365016637459 3923897295584047524956189)
                    ·
                      refine ⟨1471461485844017821858571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923897295584047524956189 1471461485844017821858571)
                      ·
                        rfl

theorem cell23_2865661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_2865661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865661 prefixEnd_2865661 := by exact prefixLift 2865661
  have htrace : WordTrace (prefixWord ++ tailWord_2865661) baseStart_2865661 baseEnd_2865661 := by
    simpa [prefixWord, tailWord_2865661, baseEnd_2865661] using wordTrace_append hprefix tailTrace_2865661
  have hstable : (prefixWord ++ tailWord_2865661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865661).length < 2 ^ (prefixWord ++ tailWord_2865661).sum := by decide
  have hdescent : baseEnd_2865661 < baseStart_2865661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865678 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2865678 : Nat := 118140960795 + 2865678 * 2 ^ 59
def prefixEnd_2865678 : Nat := 4983230072969 + 3 ^ 40 * 2865678 * 2
def baseEnd_2865678 : Nat := 1471470215015144255345993

theorem tailTrace_2865678 : CollatzResearch.WordTrace tailWord_2865678 prefixEnd_2865678 1471470215015144255345993 := by
  unfold tailWord_2865678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13064982914018187460360711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69679908874763666455257125 13064982914018187460360711)
  ·
    refine ⟨19597474371027281190541067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13064982914018187460360711 19597474371027281190541067)
    ·
      refine ⟨29396211556540921785811601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597474371027281190541067 29396211556540921785811601)
      ·
        refine ⟨22047158667405691339358701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29396211556540921785811601 22047158667405691339358701)
        ·
          refine ⟨8267684500277134252259513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22047158667405691339358701 8267684500277134252259513)
          ·
            refine ⟨6200763375207850689194635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8267684500277134252259513 6200763375207850689194635)
            ·
              refine ⟨9301145062811776033791953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200763375207850689194635 9301145062811776033791953)
              ·
                refine ⟨6975858797108832025343965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9301145062811776033791953 6975858797108832025343965)
                ·
                  refine ⟨2615947048915812009503987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6975858797108832025343965 2615947048915812009503987)
                  ·
                    refine ⟨3923920573373718014255981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2615947048915812009503987 3923920573373718014255981)
                    ·
                      refine ⟨1471470215015144255345993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3923920573373718014255981 1471470215015144255345993)
                      ·
                        rfl

theorem cell23_2865678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2865678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865678 prefixEnd_2865678 := by exact prefixLift 2865678
  have htrace : WordTrace (prefixWord ++ tailWord_2865678) baseStart_2865678 baseEnd_2865678 := by
    simpa [prefixWord, tailWord_2865678, baseEnd_2865678] using wordTrace_append hprefix tailTrace_2865678
  have hstable : (prefixWord ++ tailWord_2865678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865678).length < 2 ^ (prefixWord ++ tailWord_2865678).sum := by decide
  have hdescent : baseEnd_2865678 < baseStart_2865678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865688 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_2865688 : Nat := 118140960795 + 2865688 * 2 ^ 59
def prefixEnd_2865688 : Nat := 4983230072969 + 3 ^ 40 * 2865688 * 2
def baseEnd_2865688 : Nat := 1471475349821689216220947

theorem tailTrace_2865688 : CollatzResearch.WordTrace tailWord_2865688 prefixEnd_2865688 1471475349821689216220947 := by
  unfold tailWord_2865688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52260114021054635695374859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69680152028072847593833145 52260114021054635695374859)
  ·
    refine ⟨78390171031581953543062289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52260114021054635695374859 78390171031581953543062289)
    ·
      refine ⟨58792628273686465157296717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78390171031581953543062289 58792628273686465157296717)
      ·
        refine ⟨22047235602632424433986269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58792628273686465157296717 22047235602632424433986269)
        ·
          refine ⟨8267713350987159162744851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22047235602632424433986269 8267713350987159162744851)
          ·
            refine ⟨12401570026480738744117277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8267713350987159162744851 12401570026480738744117277)
            ·
              refine ⟨4650588759930277029043979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12401570026480738744117277 4650588759930277029043979)
              ·
                refine ⟨6975883139895415543565969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650588759930277029043979 6975883139895415543565969)
                ·
                  refine ⟨5231912354921561657674477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6975883139895415543565969 5231912354921561657674477)
                  ·
                    refine ⟨1961967133095585621627929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5231912354921561657674477 1961967133095585621627929)
                    ·
                      refine ⟨1471475349821689216220947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1961967133095585621627929 1471475349821689216220947)
                      ·
                        rfl

theorem cell23_2865688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_2865688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865688 prefixEnd_2865688 := by exact prefixLift 2865688
  have htrace : WordTrace (prefixWord ++ tailWord_2865688) baseStart_2865688 baseEnd_2865688 := by
    simpa [prefixWord, tailWord_2865688, baseEnd_2865688] using wordTrace_append hprefix tailTrace_2865688
  have hstable : (prefixWord ++ tailWord_2865688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865688).length < 2 ^ (prefixWord ++ tailWord_2865688).sum := by decide
  have hdescent : baseEnd_2865688 < baseStart_2865688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865714 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2865714 : Nat := 118140960795 + 2865714 * 2 ^ 59
def prefixEnd_2865714 : Nat := 4983230072969 + 3 ^ 40 * 2865714 * 2
def baseEnd_2865714 : Nat := 1471488700318706114495827

theorem tailTrace_2865714 : CollatzResearch.WordTrace tailWord_2865714 prefixEnd_2865714 1471488700318706114495827 := by
  unfold tailWord_2865714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130294085003769457799049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69680784226676718554130797 26130294085003769457799049)
  ·
    refine ⟨19597720563752827093349287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26130294085003769457799049 19597720563752827093349287)
    ·
      refine ⟨29396580845629240640023931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597720563752827093349287 29396580845629240640023931)
      ·
        refine ⟨44094871268443860960035897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29396580845629240640023931 44094871268443860960035897)
        ·
          refine ⟨33071153451332895720026923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44094871268443860960035897 33071153451332895720026923)
          ·
            refine ⟨49606730176999343580040385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33071153451332895720026923 49606730176999343580040385)
            ·
              refine ⟨37205047632749507685030289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49606730176999343580040385 37205047632749507685030289)
              ·
                refine ⟨27903785724562130763772717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37205047632749507685030289 27903785724562130763772717)
                ·
                  refine ⟨10463919646710799036414769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27903785724562130763772717 10463919646710799036414769)
                  ·
                    refine ⟨7847939735033099277311077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10463919646710799036414769 7847939735033099277311077)
                    ·
                      refine ⟨1471488700318706114495827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7847939735033099277311077 1471488700318706114495827)
                      ·
                        rfl

theorem cell23_2865714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2865714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865714 prefixEnd_2865714 := by exact prefixLift 2865714
  have htrace : WordTrace (prefixWord ++ tailWord_2865714) baseStart_2865714 baseEnd_2865714 := by
    simpa [prefixWord, tailWord_2865714, baseEnd_2865714] using wordTrace_append hprefix tailTrace_2865714
  have hstable : (prefixWord ++ tailWord_2865714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865714).length < 2 ^ (prefixWord ++ tailWord_2865714).sum := by decide
  have hdescent : baseEnd_2865714 < baseStart_2865714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865732 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2865732 : Nat := 118140960795 + 2865732 * 2 ^ 59
def prefixEnd_2865732 : Nat := 4983230072969 + 3 ^ 40 * 2865732 * 2
def baseEnd_2865732 : Nat := 490499314323495681356915

theorem tailTrace_2865732 : CollatzResearch.WordTrace tailWord_2865732 prefixEnd_2865732 490499314323495681356915 := by
  unfold tailWord_2865732
  simp only [CollatzResearch.WordTrace]
  refine ⟨52260916426974933452675725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69681221902633244603567633 52260916426974933452675725)
  ·
    refine ⟨19597843660115600044753397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52260916426974933452675725 19597843660115600044753397)
    ·
      refine ⟨1837297843135837504195631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19597843660115600044753397 1837297843135837504195631)
      ·
        refine ⟨2755946764703756256293447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837297843135837504195631 2755946764703756256293447)
        ·
          refine ⟨4133920147055634384440171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755946764703756256293447 4133920147055634384440171)
          ·
            refine ⟨6200880220583451576660257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133920147055634384440171 6200880220583451576660257)
            ·
              refine ⟨4650660165437588682495193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200880220583451576660257 4650660165437588682495193)
              ·
                refine ⟨3487995124078191511871395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650660165437588682495193 3487995124078191511871395)
                ·
                  refine ⟨5231992686117287267807093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487995124078191511871395 5231992686117287267807093)
                  ·
                    refine ⟨490499314323495681356915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5231992686117287267807093 490499314323495681356915)
                    ·
                      rfl

theorem cell23_2865732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2865732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865732 prefixEnd_2865732 := by exact prefixLift 2865732
  have htrace : WordTrace (prefixWord ++ tailWord_2865732) baseStart_2865732 baseEnd_2865732 := by
    simpa [prefixWord, tailWord_2865732, baseEnd_2865732] using wordTrace_append hprefix tailTrace_2865732
  have hstable : (prefixWord ++ tailWord_2865732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865732).length < 2 ^ (prefixWord ++ tailWord_2865732).sum := by decide
  have hdescent : baseEnd_2865732 < baseStart_2865732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865738 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_2865738 : Nat := 118140960795 + 2865738 * 2 ^ 59
def prefixEnd_2865738 : Nat := 4983230072969 + 3 ^ 40 * 2865738 * 2
def baseEnd_2865738 : Nat := 1471501023854414020595717

theorem tailTrace_2865738 : CollatzResearch.WordTrace tailWord_2865738 prefixEnd_2865738 1471501023854414020595717 := by
  unfold tailWord_2865738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130512922982032482517467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69681367794618753286713245 26130512922982032482517467)
  ·
    refine ⟨39195769384473048723776201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26130512922982032482517467 39195769384473048723776201)
    ·
      refine ⟨29396827038354786542832151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39195769384473048723776201 29396827038354786542832151)
      ·
        refine ⟨44095240557532179814248227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29396827038354786542832151 44095240557532179814248227)
        ·
          refine ⟨66142860836298269721372341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44095240557532179814248227 66142860836298269721372341)
          ·
            refine ⟨6200893203402962786378657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66142860836298269721372341 6200893203402962786378657)
            ·
              refine ⟨4650669902552222089783993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200893203402962786378657 4650669902552222089783993)
              ·
                refine ⟨3488002426914166567337995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650669902552222089783993 3488002426914166567337995)
                ·
                  refine ⟨5232003640371249851006993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488002426914166567337995 5232003640371249851006993)
                  ·
                    refine ⟨3924002730278437388255245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232003640371249851006993 3924002730278437388255245)
                    ·
                      refine ⟨1471501023854414020595717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924002730278437388255245 1471501023854414020595717)
                      ·
                        rfl

theorem cell23_2865738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_2865738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865738 prefixEnd_2865738 := by exact prefixLift 2865738
  have htrace : WordTrace (prefixWord ++ tailWord_2865738) baseStart_2865738 baseEnd_2865738 := by
    simpa [prefixWord, tailWord_2865738, baseEnd_2865738] using wordTrace_append hprefix tailTrace_2865738
  have hstable : (prefixWord ++ tailWord_2865738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865738).length < 2 ^ (prefixWord ++ tailWord_2865738).sum := by decide
  have hdescent : baseEnd_2865738 < baseStart_2865738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865741 : List Nat := [1, 6, 1, 1, 2, 2, 1, 9]
def baseStart_2865741 : Nat := 118140960795 + 2865741 * 2 ^ 59
def prefixEnd_2865741 : Nat := 4983230072969 + 3 ^ 40 * 2865741 * 2
def baseEnd_2865741 : Nat := 54500094973939907735489

theorem tailTrace_2865741 : CollatzResearch.WordTrace tailWord_2865741 prefixEnd_2865741 54500094973939907735489 := by
  unfold tailWord_2865741
  simp only [CollatzResearch.WordTrace]
  refine ⟨104522161110917261442429077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69681440740611507628286051 104522161110917261442429077)
  ·
    refine ⟨4899476302074246630113863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104522161110917261442429077 4899476302074246630113863)
    ·
      refine ⟨7349214453111369945170795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899476302074246630113863 7349214453111369945170795)
      ·
        refine ⟨11023821679667054917756193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7349214453111369945170795 11023821679667054917756193)
        ·
          refine ⟨8267866259750291188317145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11023821679667054917756193 8267866259750291188317145)
          ·
            refine ⟨6200899694812718391237859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8267866259750291188317145 6200899694812718391237859)
            ·
              refine ⟨9301349542219077586856789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200899694812718391237859 9301349542219077586856789)
              ·
                refine ⟨54500094973939907735489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9301349542219077586856789 54500094973939907735489)
                ·
                  rfl

theorem cell23_2865741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 9].length) (baseStart_2865741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865741 prefixEnd_2865741 := by exact prefixLift 2865741
  have htrace : WordTrace (prefixWord ++ tailWord_2865741) baseStart_2865741 baseEnd_2865741 := by
    simpa [prefixWord, tailWord_2865741, baseEnd_2865741] using wordTrace_append hprefix tailTrace_2865741
  have hstable : (prefixWord ++ tailWord_2865741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865741).length < 2 ^ (prefixWord ++ tailWord_2865741).sum := by decide
  have hdescent : baseEnd_2865741 < baseStart_2865741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865751 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_2865751 : Nat := 118140960795 + 2865751 * 2 ^ 59
def prefixEnd_2865751 : Nat := 4983230072969 + 3 ^ 40 * 2865751 * 2
def baseEnd_2865751 : Nat := 1471507699102922469733157

theorem tailTrace_2865751 : CollatzResearch.WordTrace tailWord_2865751 prefixEnd_2865751 1471507699102922469733157 := by
  unfold tailWord_2865751
  simp only [CollatzResearch.WordTrace]
  refine ⟨104522525840881033150293107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69681683893920688766862071 104522525840881033150293107)
  ·
    refine ⟨156783788761321549725439661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104522525840881033150293107 156783788761321549725439661)
    ·
      refine ⟨58793920785495581147039873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156783788761321549725439661 58793920785495581147039873)
      ·
        refine ⟨44095440589121685860279905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58793920785495581147039873 44095440589121685860279905)
        ·
          refine ⟨33071580441841264395209929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44095440589121685860279905 33071580441841264395209929)
          ·
            refine ⟨24803685331380948296407447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33071580441841264395209929 24803685331380948296407447)
            ·
              refine ⟨37205527997071422444611171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24803685331380948296407447 37205527997071422444611171)
              ·
                refine ⟨55808291995607133666916757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37205527997071422444611171 55808291995607133666916757)
                ·
                  refine ⟨2616013687294084390636723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55808291995607133666916757 2616013687294084390636723)
                  ·
                    refine ⟨3924020530941126585955085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616013687294084390636723 3924020530941126585955085)
                    ·
                      refine ⟨1471507699102922469733157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924020530941126585955085 1471507699102922469733157)
                      ·
                        rfl

theorem cell23_2865751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_2865751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865751 prefixEnd_2865751 := by exact prefixLift 2865751
  have htrace : WordTrace (prefixWord ++ tailWord_2865751) baseStart_2865751 baseEnd_2865751 := by
    simpa [prefixWord, tailWord_2865751, baseEnd_2865751] using wordTrace_append hprefix tailTrace_2865751
  have hstable : (prefixWord ++ tailWord_2865751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865751).length < 2 ^ (prefixWord ++ tailWord_2865751).sum := by decide
  have hdescent : baseEnd_2865751 < baseStart_2865751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865764 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2865764 : Nat := 118140960795 + 2865764 * 2 ^ 59
def prefixEnd_2865764 : Nat := 4983230072969 + 3 ^ 40 * 2865764 * 2
def baseEnd_2865764 : Nat := 1471514374351430918870597

theorem tailTrace_2865764 : CollatzResearch.WordTrace tailWord_2865764 prefixEnd_2865764 1471514374351430918870597 := by
  unfold tailWord_2865764
  simp only [CollatzResearch.WordTrace]
  refine ⟨52261499994916968185258173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69681999993222624247010897 52261499994916968185258173)
  ·
    refine ⟨19598062498093863069471815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52261499994916968185258173 19598062498093863069471815)
    ·
      refine ⟨29397093747140794604207723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19598062498093863069471815 29397093747140794604207723)
      ·
        refine ⟨44095640620711191906311585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29397093747140794604207723 44095640620711191906311585)
        ·
          refine ⟨33071730465533393929733689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44095640620711191906311585 33071730465533393929733689)
          ·
            refine ⟨24803797849150045447300267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33071730465533393929733689 24803797849150045447300267)
            ·
              refine ⟨37205696773725068170950401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24803797849150045447300267 37205696773725068170950401)
              ·
                refine ⟨27904272580293801128212801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37205696773725068170950401 27904272580293801128212801)
                ·
                  refine ⟨20928204435220350846159601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27904272580293801128212801 20928204435220350846159601)
                  ·
                    refine ⟨15696153326415263134619701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20928204435220350846159601 15696153326415263134619701)
                    ·
                      refine ⟨1471514374351430918870597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15696153326415263134619701 1471514374351430918870597)
                      ·
                        rfl

theorem cell23_2865764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2865764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865764 prefixEnd_2865764 := by exact prefixLift 2865764
  have htrace : WordTrace (prefixWord ++ tailWord_2865764) baseStart_2865764 baseEnd_2865764 := by
    simpa [prefixWord, tailWord_2865764, baseEnd_2865764] using wordTrace_append hprefix tailTrace_2865764
  have hstable : (prefixWord ++ tailWord_2865764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865764).length < 2 ^ (prefixWord ++ tailWord_2865764).sum := by decide
  have hdescent : baseEnd_2865764 < baseStart_2865764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865785 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 2, 1, 3]
def baseStart_2865785 : Nat := 118140960795 + 2865785 * 2 ^ 59
def prefixEnd_2865785 : Nat := 4983230072969 + 3 ^ 40 * 2865785 * 2
def baseEnd_2865785 : Nat := 1471525157445175336708001

theorem tailTrace_2865785 : CollatzResearch.WordTrace tailWord_2865785 prefixEnd_2865785 1471525157445175336708001 := by
  unfold tailWord_2865785
  simp only [CollatzResearch.WordTrace]
  refine ⟨104523765922757856957030809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69682510615171904638020539 104523765922757856957030809)
  ·
    refine ⟨78392824442068392717773107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104523765922757856957030809 78392824442068392717773107)
    ·
      refine ⟨117589236663102589076659661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78392824442068392717773107 117589236663102589076659661)
      ·
        refine ⟨44095963748663470903747373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117589236663102589076659661 44095963748663470903747373)
        ·
          refine ⟨16535986405748801588905265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44095963748663470903747373 16535986405748801588905265)
          ·
            refine ⟨12401989804311601191678949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16535986405748801588905265 12401989804311601191678949)
            ·
              refine ⟨2325373088308425223439803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12401989804311601191678949 2325373088308425223439803)
              ·
                refine ⟨3488059632462637835159705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325373088308425223439803 3488059632462637835159705)
                ·
                  refine ⟨2616044724346978376369779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488059632462637835159705 2616044724346978376369779)
                  ·
                    refine ⟨3924067086520467564554669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616044724346978376369779 3924067086520467564554669)
                    ·
                      refine ⟨1471525157445175336708001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924067086520467564554669 1471525157445175336708001)
                      ·
                        rfl

theorem cell23_2865785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_2865785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865785 prefixEnd_2865785 := by exact prefixLift 2865785
  have htrace : WordTrace (prefixWord ++ tailWord_2865785) baseStart_2865785 baseEnd_2865785 := by
    simpa [prefixWord, tailWord_2865785, baseEnd_2865785] using wordTrace_append hprefix tailTrace_2865785
  have hstable : (prefixWord ++ tailWord_2865785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865785).length < 2 ^ (prefixWord ++ tailWord_2865785).sum := by decide
  have hdescent : baseEnd_2865785 < baseStart_2865785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865804 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2865804 : Nat := 118140960795 + 2865804 * 2 ^ 59
def prefixEnd_2865804 : Nat := 4983230072969 + 3 ^ 40 * 2865804 * 2
def baseEnd_2865804 : Nat := 1471534913577610762370413

theorem tailTrace_2865804 : CollatzResearch.WordTrace tailWord_2865804 prefixEnd_2865804 1471534913577610762370413 := by
  unfold tailWord_2865804
  simp only [CollatzResearch.WordTrace]
  refine ⟨52262229454844511600986233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69682972606459348801314977 52262229454844511600986233)
  ·
    refine ⟨39196672091133383700739675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52262229454844511600986233 39196672091133383700739675)
    ·
      refine ⟨58795008136700075551109513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39196672091133383700739675 58795008136700075551109513)
      ·
        refine ⟨44096256102525056663332135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58795008136700075551109513 44096256102525056663332135)
        ·
          refine ⟨66144384153787584994998203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44096256102525056663332135 66144384153787584994998203)
          ·
            refine ⟨99216576230681377492497305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66144384153787584994998203 99216576230681377492497305)
            ·
              refine ⟨74412432173011033119372979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99216576230681377492497305 74412432173011033119372979)
              ·
                refine ⟨111618648259516549679059469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74412432173011033119372979 111618648259516549679059469)
                ·
                  refine ⟨41856993097318706129647301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111618648259516549679059469 41856993097318706129647301)
                  ·
                    refine ⟨7848186205747257399308869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41856993097318706129647301 7848186205747257399308869)
                    ·
                      refine ⟨1471534913577610762370413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7848186205747257399308869 1471534913577610762370413)
                      ·
                        rfl

theorem cell23_2865804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2865804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865804 prefixEnd_2865804 := by exact prefixLift 2865804
  have htrace : WordTrace (prefixWord ++ tailWord_2865804) baseStart_2865804 baseEnd_2865804 := by
    simpa [prefixWord, tailWord_2865804, baseEnd_2865804] using wordTrace_append hprefix tailTrace_2865804
  have hstable : (prefixWord ++ tailWord_2865804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865804).length < 2 ^ (prefixWord ++ tailWord_2865804).sum := by decide
  have hdescent : baseEnd_2865804 < baseStart_2865804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865838 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2865838 : Nat := 118140960795 + 2865838 * 2 ^ 59
def prefixEnd_2865838 : Nat := 4983230072969 + 3 ^ 40 * 2865838 * 2
def baseEnd_2865838 : Nat := 1471552371919863629345257

theorem tailTrace_2865838 : CollatzResearch.WordTrace tailWord_2865838 prefixEnd_2865838 1471552371919863629345257 := by
  unfold tailWord_2865838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13065712373945730876088771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69683799327710564672473445 13065712373945730876088771)
  ·
    refine ⟨19598568560918596314133157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13065712373945730876088771 19598568560918596314133157)
    ·
      refine ⟨3674731605172236808899967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19598568560918596314133157 3674731605172236808899967)
      ·
        refine ⟨5512097407758355213349951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3674731605172236808899967 5512097407758355213349951)
        ·
          refine ⟨8268146111637532820024927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512097407758355213349951 8268146111637532820024927)
          ·
            refine ⟨12402219167456299230037391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8268146111637532820024927 12402219167456299230037391)
            ·
              refine ⟨18603328751184448845056087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12402219167456299230037391 18603328751184448845056087)
              ·
                refine ⟨27904993126776673267584131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18603328751184448845056087 27904993126776673267584131)
                ·
                  refine ⟨41857489690165009901376197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27904993126776673267584131 41857489690165009901376197)
                  ·
                    refine ⟨7848279316905939356508037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41857489690165009901376197 7848279316905939356508037)
                    ·
                      refine ⟨1471552371919863629345257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7848279316905939356508037 1471552371919863629345257)
                      ·
                        rfl

theorem cell23_2865838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2865838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865838 prefixEnd_2865838 := by exact prefixLift 2865838
  have htrace : WordTrace (prefixWord ++ tailWord_2865838) baseStart_2865838 baseEnd_2865838 := by
    simpa [prefixWord, tailWord_2865838, baseEnd_2865838] using wordTrace_append hprefix tailTrace_2865838
  have hstable : (prefixWord ++ tailWord_2865838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865838).length < 2 ^ (prefixWord ++ tailWord_2865838).sum := by decide
  have hdescent : baseEnd_2865838 < baseStart_2865838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865876 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2865876 : Nat := 118140960795 + 2865876 * 2 ^ 59
def prefixEnd_2865876 : Nat := 4983230072969 + 3 ^ 40 * 2865876 * 2
def baseEnd_2865876 : Nat := 1471571884184734480670083

theorem tailTrace_2865876 : CollatzResearch.WordTrace tailWord_2865876 prefixEnd_2865876 1471571884184734480670083 := by
  unfold tailWord_2865876
  simp only [CollatzResearch.WordTrace]
  refine ⟨52263542482714089749296741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69684723310285452999062321 52263542482714089749296741)
  ·
    refine ⟨9799414215508891827993139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52263542482714089749296741 9799414215508891827993139)
    ·
      refine ⟨14699121323263337741989709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9799414215508891827993139 14699121323263337741989709)
      ·
        refine ⟨5512170496223751653246141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14699121323263337741989709 5512170496223751653246141)
        ·
          refine ⟨2067063936083906869967303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5512170496223751653246141 2067063936083906869967303)
          ·
            refine ⟨3100595904125860304950955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067063936083906869967303 3100595904125860304950955)
            ·
              refine ⟨4650893856188790457426433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100595904125860304950955 4650893856188790457426433)
              ·
                refine ⟨3488170392141592843069825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650893856188790457426433 3488170392141592843069825)
                ·
                  refine ⟨2616127794106194632302369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488170392141592843069825 2616127794106194632302369)
                  ·
                    refine ⟨1962095845579645974226777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2616127794106194632302369 1962095845579645974226777)
                    ·
                      refine ⟨1471571884184734480670083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962095845579645974226777 1471571884184734480670083)
                      ·
                        rfl

theorem cell23_2865876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2865876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865876 prefixEnd_2865876 := by exact prefixLift 2865876
  have htrace : WordTrace (prefixWord ++ tailWord_2865876) baseStart_2865876 baseEnd_2865876 := by
    simpa [prefixWord, tailWord_2865876, baseEnd_2865876] using wordTrace_append hprefix tailTrace_2865876
  have hstable : (prefixWord ++ tailWord_2865876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865876).length < 2 ^ (prefixWord ++ tailWord_2865876).sum := by decide
  have hdescent : baseEnd_2865876 < baseStart_2865876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865881 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2865881 : Nat := 118140960795 + 2865881 * 2 ^ 59
def prefixEnd_2865881 : Nat := 4983230072969 + 3 ^ 40 * 2865881 * 2
def baseEnd_2865881 : Nat := 1471574451588006961107559

theorem tailTrace_2865881 : CollatzResearch.WordTrace tailWord_2865881 prefixEnd_2865881 1471574451588006961107559 := by
  unfold tailWord_2865881
  simp only [CollatzResearch.WordTrace]
  refine ⟨104527267330410065352525497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69684844886940043568350331 104527267330410065352525497)
  ·
    refine ⟨78395450497807549014394123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104527267330410065352525497 78395450497807549014394123)
    ·
      refine ⟨117593175746711323521591185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78395450497807549014394123 117593175746711323521591185)
      ·
        refine ⟨88194881810033492641193389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117593175746711323521591185 88194881810033492641193389)
        ·
          refine ⟨33073080678762559740447521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88194881810033492641193389 33073080678762559740447521)
          ·
            refine ⟨24804810509071919805335641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33073080678762559740447521 24804810509071919805335641)
            ·
              refine ⟨18603607881803939854001731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24804810509071919805335641 18603607881803939854001731)
              ·
                refine ⟨27905411822705909781002597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18603607881803939854001731 27905411822705909781002597)
                ·
                  refine ⟨5232264716757358083937987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27905411822705909781002597 5232264716757358083937987)
                  ·
                    refine ⟨7848397075136037125906981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5232264716757358083937987 7848397075136037125906981)
                    ·
                      refine ⟨1471574451588006961107559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7848397075136037125906981 1471574451588006961107559)
                      ·
                        rfl

theorem cell23_2865881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2865881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865881 prefixEnd_2865881 := by exact prefixLift 2865881
  have htrace : WordTrace (prefixWord ++ tailWord_2865881) baseStart_2865881 baseEnd_2865881 := by
    simpa [prefixWord, tailWord_2865881, baseEnd_2865881] using wordTrace_append hprefix tailTrace_2865881
  have hstable : (prefixWord ++ tailWord_2865881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865881).length < 2 ^ (prefixWord ++ tailWord_2865881).sum := by decide
  have hdescent : baseEnd_2865881 < baseStart_2865881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865975 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_2865975 : Nat := 118140960795 + 2865975 * 2 ^ 59
def prefixEnd_2865975 : Nat := 4983230072969 + 3 ^ 40 * 2865975 * 2
def baseEnd_2865975 : Nat := 1471622718769529593332127

theorem tailTrace_2865975 : CollatzResearch.WordTrace tailWord_2865975 prefixEnd_2865975 1471622718769529593332127 := by
  unfold tailWord_2865975
  simp only [CollatzResearch.WordTrace]
  refine ⟨104530695792069519406447379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69687130528046346270964919 104530695792069519406447379)
  ·
    refine ⟨156796043688104279109671069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104530695792069519406447379 156796043688104279109671069)
    ·
      refine ⟨58798516383039104666126651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156796043688104279109671069 58798516383039104666126651)
      ·
        refine ⟨88197774574558656999189977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58798516383039104666126651 88197774574558656999189977)
        ·
          refine ⟨66148330930918992749392483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88197774574558656999189977 66148330930918992749392483)
          ·
            refine ⟨99222496396378489124088725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66148330930918992749392483 99222496396378489124088725)
            ·
              refine ⟨4651054518580241677691659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99222496396378489124088725 4651054518580241677691659)
              ·
                refine ⟨6976581777870362516537489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651054518580241677691659 6976581777870362516537489)
                ·
                  refine ⟨5232436333402771887403117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6976581777870362516537489 5232436333402771887403117)
                  ·
                    refine ⟨1962163625026039457776169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5232436333402771887403117 1962163625026039457776169)
                    ·
                      refine ⟨1471622718769529593332127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962163625026039457776169 1471622718769529593332127)
                      ·
                        rfl

theorem cell23_2865975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_2865975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865975 prefixEnd_2865975 := by exact prefixLift 2865975
  have htrace : WordTrace (prefixWord ++ tailWord_2865975) baseStart_2865975 baseEnd_2865975 := by
    simpa [prefixWord, tailWord_2865975, baseEnd_2865975] using wordTrace_append hprefix tailTrace_2865975
  have hstable : (prefixWord ++ tailWord_2865975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865975).length < 2 ^ (prefixWord ++ tailWord_2865975).sum := by decide
  have hdescent : baseEnd_2865975 < baseStart_2865975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865998 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_2865998 : Nat := 118140960795 + 2865998 * 2 ^ 59
def prefixEnd_2865998 : Nat := 4983230072969 + 3 ^ 40 * 2865998 * 2
def baseEnd_2865998 : Nat := 490544842941527667781507

theorem tailTrace_2865998 : CollatzResearch.WordTrace tailWord_2865998 prefixEnd_2865998 490544842941527667781507 := by
  unfold tailWord_2865998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066441833873274291816831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69687689780657462889689765 13066441833873274291816831)
  ·
    refine ⟨19599662750809911437725247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13066441833873274291816831 19599662750809911437725247)
    ·
      refine ⟨29399494126214867156587871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19599662750809911437725247 29399494126214867156587871)
      ·
        refine ⟨44099241189322300734881807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29399494126214867156587871 44099241189322300734881807)
        ·
          refine ⟨66148861783983451102322711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44099241189322300734881807 66148861783983451102322711)
          ·
            refine ⟨99223292675975176653484067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66148861783983451102322711 99223292675975176653484067)
            ·
              refine ⟨148834939013962764980226101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99223292675975176653484067 148834939013962764980226101)
              ·
                refine ⟨13953275532559009216896197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148834939013962764980226101 13953275532559009216896197)
                ·
                  refine ⟨2616239162354814228168037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13953275532559009216896197 2616239162354814228168037)
                  ·
                    refine ⟨490544842941527667781507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2616239162354814228168037 490544842941527667781507)
                    ·
                      rfl

theorem cell23_2865998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_2865998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2865998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2865998 prefixEnd_2865998 := by exact prefixLift 2865998
  have htrace : WordTrace (prefixWord ++ tailWord_2865998) baseStart_2865998 baseEnd_2865998 := by
    simpa [prefixWord, tailWord_2865998, baseEnd_2865998] using wordTrace_append hprefix tailTrace_2865998
  have hstable : (prefixWord ++ tailWord_2865998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865998).length < 2 ^ (prefixWord ++ tailWord_2865998).sum := by decide
  have hdescent : baseEnd_2865998 < baseStart_2865998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866028 : List Nat := [2, 2, 1, 1, 4, 1, 5, 7]
def baseStart_2866028 : Nat := 118140960795 + 2866028 * 2 ^ 59
def prefixEnd_2866028 : Nat := 4983230072969 + 3 ^ 40 * 2866028 * 2
def baseEnd_2866028 : Nat := 54505553083119180961829

theorem tailTrace_2866028 : CollatzResearch.WordTrace tailWord_2866028 prefixEnd_2866028 54505553083119180961829 := by
  unfold tailWord_2866028
  simp only [CollatzResearch.WordTrace]
  refine ⟨52266314430438754729063369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69688419240585006305417825 52266314430438754729063369)
  ·
    refine ⟨39199735822829066046797527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52266314430438754729063369 39199735822829066046797527)
    ·
      refine ⟨58799603734243599070196291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39199735822829066046797527 58799603734243599070196291)
      ·
        refine ⟨88199405601365398605294437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58799603734243599070196291 88199405601365398605294437)
        ·
          refine ⟨16537388550256012238492707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88199405601365398605294437 16537388550256012238492707)
          ·
            refine ⟨24806082825384018357739061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16537388550256012238492707 24806082825384018357739061)
            ·
              refine ⟨2325570264879751721038037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24806082825384018357739061 2325570264879751721038037)
              ·
                refine ⟨54505553083119180961829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2325570264879751721038037 54505553083119180961829)
                ·
                  rfl

theorem cell23_2866028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 7].length) (baseStart_2866028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866028 prefixEnd_2866028 := by exact prefixLift 2866028
  have htrace : WordTrace (prefixWord ++ tailWord_2866028) baseStart_2866028 baseEnd_2866028 := by
    simpa [prefixWord, tailWord_2866028, baseEnd_2866028] using wordTrace_append hprefix tailTrace_2866028
  have hstable : (prefixWord ++ tailWord_2866028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866028).length < 2 ^ (prefixWord ++ tailWord_2866028).sum := by decide
  have hdescent : baseEnd_2866028 < baseStart_2866028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866098 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_2866098 : Nat := 118140960795 + 2866098 * 2 ^ 59
def prefixEnd_2866098 : Nat := 4983230072969 + 3 ^ 40 * 2866098 * 2
def baseEnd_2866098 : Nat := 1471685876890032612094061

theorem tailTrace_2866098 : CollatzResearch.WordTrace tailWord_2866098 prefixEnd_2866098 1471685876890032612094061 := by
  unfold tailWord_2866098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26133795492655977853293737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69690121313749274275449965 26133795492655977853293737)
  ·
    refine ⟨19600346619491983389970303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26133795492655977853293737 19600346619491983389970303)
    ·
      refine ⟨29400519929237975084955455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19600346619491983389970303 29400519929237975084955455)
      ·
        refine ⟨44100779893856962627433183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29400519929237975084955455 44100779893856962627433183)
        ·
          refine ⟨66151169840785443941149775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44100779893856962627433183 66151169840785443941149775)
          ·
            refine ⟨99226754761178165911724663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66151169840785443941149775 99226754761178165911724663)
            ·
              refine ⟨148840132141767248867586995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99226754761178165911724663 148840132141767248867586995)
              ·
                refine ⟨223260198212650873301380493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148840132141767248867586995 223260198212650873301380493)
                ·
                  refine ⟨83722574329744077488017685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223260198212650873301380493 83722574329744077488017685)
                  ·
                    refine ⟨3924495671706753632250829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83722574329744077488017685 3924495671706753632250829)
                    ·
                      refine ⟨1471685876890032612094061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924495671706753632250829 1471685876890032612094061)
                      ·
                        rfl

theorem cell23_2866098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_2866098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866098 prefixEnd_2866098 := by exact prefixLift 2866098
  have htrace : WordTrace (prefixWord ++ tailWord_2866098) baseStart_2866098 baseEnd_2866098 := by
    simpa [prefixWord, tailWord_2866098, baseEnd_2866098] using wordTrace_append hprefix tailTrace_2866098
  have hstable : (prefixWord ++ tailWord_2866098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866098).length < 2 ^ (prefixWord ++ tailWord_2866098).sum := by decide
  have hdescent : baseEnd_2866098 < baseStart_2866098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866112 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2]
def baseStart_2866112 : Nat := 118140960795 + 2866112 * 2 ^ 59
def prefixEnd_2866112 : Nat := 4983230072969 + 3 ^ 40 * 2866112 * 2
def baseEnd_2866112 : Nat := 1471693065619195557318997

theorem tailTrace_2866112 : CollatzResearch.WordTrace tailWord_2866112 prefixEnd_2866112 1471693065619195557318997 := by
  unfold tailWord_2866112
  simp only [CollatzResearch.WordTrace]
  refine ⟨52267846296286595902092295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69690461728382127869456393 52267846296286595902092295)
  ·
    refine ⟨78401769444429893853138443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52267846296286595902092295 78401769444429893853138443)
    ·
      refine ⟨117602654166644840779707665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78401769444429893853138443 117602654166644840779707665)
      ·
        refine ⟨88201990624983630584780749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117602654166644840779707665 88201990624983630584780749)
        ·
          refine ⟨33075746484368861469292781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88201990624983630584780749 33075746484368861469292781)
          ·
            refine ⟨12403404931638323050984793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33075746484368861469292781 12403404931638323050984793)
            ·
              refine ⟨9302553698728742288238595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12403404931638323050984793 9302553698728742288238595)
              ·
                refine ⟨13953830548093113432357893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9302553698728742288238595 13953830548093113432357893)
                ·
                  refine ⟨2616343227767458768567105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13953830548093113432357893 2616343227767458768567105)
                  ·
                    refine ⟨1962257420825594076425329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2616343227767458768567105 1962257420825594076425329)
                    ·
                      refine ⟨1471693065619195557318997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962257420825594076425329 1471693065619195557318997)
                      ·
                        rfl

theorem cell23_2866112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_2866112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866112 prefixEnd_2866112 := by exact prefixLift 2866112
  have htrace : WordTrace (prefixWord ++ tailWord_2866112) baseStart_2866112 baseEnd_2866112 := by
    simpa [prefixWord, tailWord_2866112, baseEnd_2866112] using wordTrace_append hprefix tailTrace_2866112
  have hstable : (prefixWord ++ tailWord_2866112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866112).length < 2 ^ (prefixWord ++ tailWord_2866112).sum := by decide
  have hdescent : baseEnd_2866112 < baseStart_2866112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866128 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_2866128 : Nat := 118140960795 + 2866128 * 2 ^ 59
def prefixEnd_2866128 : Nat := 4983230072969 + 3 ^ 40 * 2866128 * 2
def baseEnd_2866128 : Nat := 1471701281309667494718923

theorem tailTrace_2866128 : CollatzResearch.WordTrace tailWord_2866128 prefixEnd_2866128 1471701281309667494718923 := by
  unfold tailWord_2866128
  simp only [CollatzResearch.WordTrace]
  refine ⟨52268138080257613268383519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69690850773676817691178025 52268138080257613268383519)
  ·
    refine ⟨78402207120386419902575279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52268138080257613268383519 78402207120386419902575279)
    ·
      refine ⟨117603310680579629853862919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78402207120386419902575279 117603310680579629853862919)
      ·
        refine ⟨176404966020869444780794379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117603310680579629853862919 176404966020869444780794379)
        ·
          refine ⟨264607449031304167171191569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176404966020869444780794379 264607449031304167171191569)
          ·
            refine ⟨198455586773478125378393677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264607449031304167171191569 198455586773478125378393677)
            ·
              refine ⟨74420845040054297016897629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198455586773478125378393677 74420845040054297016897629)
              ·
                refine ⟨27907816890020361381336611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74420845040054297016897629 27907816890020361381336611)
                ·
                  refine ⟨41861725335030542072004917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27907816890020361381336611 41861725335030542072004917)
                  ·
                    refine ⟨3924536750159113319250461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41861725335030542072004917 3924536750159113319250461)
                    ·
                      refine ⟨1471701281309667494718923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924536750159113319250461 1471701281309667494718923)
                      ·
                        rfl

theorem cell23_2866128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_2866128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866128 prefixEnd_2866128 := by exact prefixLift 2866128
  have htrace : WordTrace (prefixWord ++ tailWord_2866128) baseStart_2866128 baseEnd_2866128 := by
    simpa [prefixWord, tailWord_2866128, baseEnd_2866128] using wordTrace_append hprefix tailTrace_2866128
  have hstable : (prefixWord ++ tailWord_2866128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866128).length < 2 ^ (prefixWord ++ tailWord_2866128).sum := by decide
  have hdescent : baseEnd_2866128 < baseStart_2866128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866168 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_2866168 : Nat := 118140960795 + 2866168 * 2 ^ 59
def prefixEnd_2866168 : Nat := 4983230072969 + 3 ^ 40 * 2866168 * 2
def baseEnd_2866168 : Nat := 1471721820535847338218739

theorem tailTrace_2866168 : CollatzResearch.WordTrace tailWord_2866168 prefixEnd_2866168 1471721820535847338218739 := by
  unfold tailWord_2866168
  simp only [CollatzResearch.WordTrace]
  refine ⟨52268867540185156684111579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69691823386913542245482105 52268867540185156684111579)
  ·
    refine ⟨78403301310277735026167369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52268867540185156684111579 78403301310277735026167369)
    ·
      refine ⟨58802475982708301269625527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78403301310277735026167369 58802475982708301269625527)
      ·
        refine ⟨88203713974062451904438291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58802475982708301269625527 88203713974062451904438291)
        ·
          refine ⟨132305570961093677856657437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88203713974062451904438291 132305570961093677856657437)
          ·
            refine ⟨49614589110410129196246539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132305570961093677856657437 49614589110410129196246539)
            ·
              refine ⟨74421883665615193794369809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49614589110410129196246539 74421883665615193794369809)
              ·
                refine ⟨55816412749211395345777357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74421883665615193794369809 55816412749211395345777357)
                ·
                  refine ⟨20931154780954273254666509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55816412749211395345777357 20931154780954273254666509)
                  ·
                    refine ⟨7849183042857852470499941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20931154780954273254666509 7849183042857852470499941)
                    ·
                      refine ⟨1471721820535847338218739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7849183042857852470499941 1471721820535847338218739)
                      ·
                        rfl

theorem cell23_2866168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_2866168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866168 prefixEnd_2866168 := by exact prefixLift 2866168
  have htrace : WordTrace (prefixWord ++ tailWord_2866168) baseStart_2866168 baseEnd_2866168 := by
    simpa [prefixWord, tailWord_2866168, baseEnd_2866168] using wordTrace_append hprefix tailTrace_2866168
  have hstable : (prefixWord ++ tailWord_2866168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866168).length < 2 ^ (prefixWord ++ tailWord_2866168).sum := by decide
  have hdescent : baseEnd_2866168 < baseStart_2866168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866222 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2866222 : Nat := 118140960795 + 2866222 * 2 ^ 59
def prefixEnd_2866222 : Nat := 4983230072969 + 3 ^ 40 * 2866222 * 2
def baseEnd_2866222 : Nat := 1471749548491190126943491

theorem tailTrace_2866222 : CollatzResearch.WordTrace tailWord_2866222 prefixEnd_2866222 1471749548491190126943491 := by
  unfold tailWord_2866222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067463077771835073836115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69693136414783120393792613 13067463077771835073836115)
  ·
    refine ⟨19601194616657752610754173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067463077771835073836115 19601194616657752610754173)
    ·
      refine ⟨7350447981246657229032815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19601194616657752610754173 7350447981246657229032815)
      ·
        refine ⟨11025671971869985843549223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350447981246657229032815 11025671971869985843549223)
        ·
          refine ⟨16538507957804978765323835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11025671971869985843549223 16538507957804978765323835)
          ·
            refine ⟨24807761936707468147985753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16538507957804978765323835 24807761936707468147985753)
            ·
              refine ⟨18605821452530601110989315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24807761936707468147985753 18605821452530601110989315)
              ·
                refine ⟨27908732178795901666483973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18605821452530601110989315 27908732178795901666483973)
                ·
                  refine ⟨5232887283524231562465745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27908732178795901666483973 5232887283524231562465745)
                  ·
                    refine ⟨3924665462643173671849309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232887283524231562465745 3924665462643173671849309)
                    ·
                      refine ⟨1471749548491190126943491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924665462643173671849309 1471749548491190126943491)
                      ·
                        rfl

theorem cell23_2866222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2866222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866222 prefixEnd_2866222 := by exact prefixLift 2866222
  have htrace : WordTrace (prefixWord ++ tailWord_2866222) baseStart_2866222 baseEnd_2866222 := by
    simpa [prefixWord, tailWord_2866222, baseEnd_2866222] using wordTrace_append hprefix tailTrace_2866222
  have hstable : (prefixWord ++ tailWord_2866222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866222).length < 2 ^ (prefixWord ++ tailWord_2866222).sum := by decide
  have hdescent : baseEnd_2866222 < baseStart_2866222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866275 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2866275 : Nat := 118140960795 + 2866275 * 2 ^ 59
def prefixEnd_2866275 : Nat := 4983230072969 + 3 ^ 40 * 2866275 * 2
def baseEnd_2866275 : Nat := 1471776762965878419580747

theorem tailTrace_2866275 : CollatzResearch.WordTrace tailWord_2866275 prefixEnd_2866275 1471776762965878419580747 := by
  unfold tailWord_2866275
  simp only [CollatzResearch.WordTrace]
  refine ⟨104541637690982670642368279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69694425127321780428245519 104541637690982670642368279)
  ·
    refine ⟨156812456536474005963552419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104541637690982670642368279 156812456536474005963552419)
    ·
      refine ⟨235218684804711008945328629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156812456536474005963552419 235218684804711008945328629)
      ·
        refine ⟨22051751700441657088624559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235218684804711008945328629 22051751700441657088624559)
        ·
          refine ⟨33077627550662485632936839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22051751700441657088624559 33077627550662485632936839)
          ·
            refine ⟨49616441325993728449405259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33077627550662485632936839 49616441325993728449405259)
            ·
              refine ⟨74424661988990592674107889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49616441325993728449405259 74424661988990592674107889)
              ·
                refine ⟨55818496491742944505580917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74424661988990592674107889 55818496491742944505580917)
                ·
                  refine ⟨5232984046100901047398211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55818496491742944505580917 5232984046100901047398211)
                  ·
                    refine ⟨7849476069151351571097317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5232984046100901047398211 7849476069151351571097317)
                    ·
                      refine ⟨1471776762965878419580747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7849476069151351571097317 1471776762965878419580747)
                      ·
                        rfl

theorem cell23_2866275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2866275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866275 prefixEnd_2866275 := by exact prefixLift 2866275
  have htrace : WordTrace (prefixWord ++ tailWord_2866275) baseStart_2866275 baseEnd_2866275 := by
    simpa [prefixWord, tailWord_2866275, baseEnd_2866275] using wordTrace_append hprefix tailTrace_2866275
  have hstable : (prefixWord ++ tailWord_2866275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866275).length < 2 ^ (prefixWord ++ tailWord_2866275).sum := by decide
  have hdescent : baseEnd_2866275 < baseStart_2866275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866279 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_2866279 : Nat := 118140960795 + 2866279 * 2 ^ 59
def prefixEnd_2866279 : Nat := 4983230072969 + 3 ^ 40 * 2866279 * 2
def baseEnd_2866279 : Nat := 1471778816888496403930729

theorem tailTrace_2866279 : CollatzResearch.WordTrace tailWord_2866279 prefixEnd_2866279 1471778816888496403930729 := by
  unfold tailWord_2866279
  simp only [CollatzResearch.WordTrace]
  refine ⟨104541783582968179325513891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69694522388645452883675927 104541783582968179325513891)
  ·
    refine ⟨156812675374452268988270837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104541783582968179325513891 156812675374452268988270837)
    ·
      refine ⟨14701188316354900217650391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156812675374452268988270837 14701188316354900217650391)
      ·
        refine ⟨22051782474532350326475587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14701188316354900217650391 22051782474532350326475587)
        ·
          refine ⟨33077673711798525489713381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22051782474532350326475587 33077673711798525489713381)
          ·
            refine ⟨6202063820962223529321259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33077673711798525489713381 6202063820962223529321259)
            ·
              refine ⟨9303095731443335293981889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202063820962223529321259 9303095731443335293981889)
              ·
                refine ⟨6977321798582501470486417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9303095731443335293981889 6977321798582501470486417)
                ·
                  refine ⟨5232991348936876102864813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6977321798582501470486417 5232991348936876102864813)
                  ·
                    refine ⟨1962371755851328538574305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5232991348936876102864813 1962371755851328538574305)
                    ·
                      refine ⟨1471778816888496403930729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962371755851328538574305 1471778816888496403930729)
                      ·
                        rfl

theorem cell23_2866279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_2866279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866279 prefixEnd_2866279 := by exact prefixLift 2866279
  have htrace : WordTrace (prefixWord ++ tailWord_2866279) baseStart_2866279 baseEnd_2866279 := by
    simpa [prefixWord, tailWord_2866279, baseEnd_2866279] using wordTrace_append hprefix tailTrace_2866279
  have hstable : (prefixWord ++ tailWord_2866279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866279).length < 2 ^ (prefixWord ++ tailWord_2866279).sum := by decide
  have hdescent : baseEnd_2866279 < baseStart_2866279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866286 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2866286 : Nat := 118140960795 + 2866286 * 2 ^ 59
def prefixEnd_2866286 : Nat := 4983230072969 + 3 ^ 40 * 2866286 * 2
def baseEnd_2866286 : Nat := 1471782411253077876543197

theorem tailTrace_2866286 : CollatzResearch.WordTrace tailWord_2866286 prefixEnd_2866286 1471782411253077876543197 := by
  unfold tailWord_2866286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067754861742852440127339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69694692595961879680679141 13067754861742852440127339)
  ·
    refine ⟨19601632292614278660191009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067754861742852440127339 19601632292614278660191009)
    ·
      refine ⟨14701224219460708995143257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19601632292614278660191009 14701224219460708995143257)
      ·
        refine ⟨11025918164595531746357443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14701224219460708995143257 11025918164595531746357443)
        ·
          refine ⟨16538877246893297619536165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11025918164595531746357443 16538877246893297619536165)
          ·
            refine ⟨3101039483792493303663031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16538877246893297619536165 3101039483792493303663031)
            ·
              refine ⟨4651559225688739955494547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101039483792493303663031 4651559225688739955494547)
              ·
                refine ⟨6977338838533109933241821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651559225688739955494547 6977338838533109933241821)
                ·
                  refine ⟨2616502064449916224965683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6977338838533109933241821 2616502064449916224965683)
                  ·
                    refine ⟨3924753096674874337448525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616502064449916224965683 3924753096674874337448525)
                    ·
                      refine ⟨1471782411253077876543197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924753096674874337448525 1471782411253077876543197)
                      ·
                        rfl

theorem cell23_2866286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2866286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866286 prefixEnd_2866286 := by exact prefixLift 2866286
  have htrace : WordTrace (prefixWord ++ tailWord_2866286) baseStart_2866286 baseEnd_2866286 := by
    simpa [prefixWord, tailWord_2866286, baseEnd_2866286] using wordTrace_append hprefix tailTrace_2866286
  have hstable : (prefixWord ++ tailWord_2866286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866286).length < 2 ^ (prefixWord ++ tailWord_2866286).sum := by decide
  have hdescent : baseEnd_2866286 < baseStart_2866286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866293 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 6]
def baseStart_2866293 : Nat := 118140960795 + 2866293 * 2 ^ 59
def prefixEnd_2866293 : Nat := 4983230072969 + 3 ^ 40 * 2866293 * 2
def baseEnd_2866293 : Nat := 163531778401962149906185

theorem tailTrace_2866293 : CollatzResearch.WordTrace tailWord_2866293 prefixEnd_2866293 163531778401962149906185 := by
  unfold tailWord_2866293
  simp only [CollatzResearch.WordTrace]
  refine ⟨104542294204917459716523533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69694862803278306477682355 104542294204917459716523533)
  ·
    refine ⟨39203360326844047393696325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104542294204917459716523533 39203360326844047393696325)
    ·
      refine ⟨7350630061283258886318061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39203360326844047393696325 7350630061283258886318061)
      ·
        refine ⟨2756486272981222082369273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7350630061283258886318061 2756486272981222082369273)
        ·
          refine ⟨2067364704735916561776955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756486272981222082369273 2067364704735916561776955)
          ·
            refine ⟨3101047057103874842665433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067364704735916561776955 3101047057103874842665433)
            ·
              refine ⟨2325785292827906131999075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3101047057103874842665433 2325785292827906131999075)
              ·
                refine ⟨3488677939241859197998613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325785292827906131999075 3488677939241859197998613)
                ·
                  refine ⟨163531778401962149906185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3488677939241859197998613 163531778401962149906185)
                  ·
                    rfl

theorem cell23_2866293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_2866293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866293 prefixEnd_2866293 := by exact prefixLift 2866293
  have htrace : WordTrace (prefixWord ++ tailWord_2866293) baseStart_2866293 baseEnd_2866293 := by
    simpa [prefixWord, tailWord_2866293, baseEnd_2866293] using wordTrace_append hprefix tailTrace_2866293
  have hstable : (prefixWord ++ tailWord_2866293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866293).length < 2 ^ (prefixWord ++ tailWord_2866293).sum := by decide
  have hdescent : baseEnd_2866293 < baseStart_2866293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866295 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_2866295 : Nat := 118140960795 + 2866295 * 2 ^ 59
def prefixEnd_2866295 : Nat := 4983230072969 + 3 ^ 40 * 2866295 * 2
def baseEnd_2866295 : Nat := 1471787032578968341330655

theorem tailTrace_2866295 : CollatzResearch.WordTrace tailWord_2866295 prefixEnd_2866295 1471787032578968341330655 := by
  unfold tailWord_2866295
  simp only [CollatzResearch.WordTrace]
  refine ⟨104542367150910214058096339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69694911433940142705397559 104542367150910214058096339)
  ·
    refine ⟨156813550726365321087144509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104542367150910214058096339 156813550726365321087144509)
    ·
      refine ⟨58805081522386995407679191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156813550726365321087144509 58805081522386995407679191)
      ·
        refine ⟨88207622283580493111518787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58805081522386995407679191 88207622283580493111518787)
        ·
          refine ⟨132311433425370739667278181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88207622283580493111518787 132311433425370739667278181)
          ·
            refine ⟨24808393767257013687614659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132311433425370739667278181 24808393767257013687614659)
            ·
              refine ⟨37212590650885520531421989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24808393767257013687614659 37212590650885520531421989)
              ·
                refine ⟨6977360747041035099641623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37212590650885520531421989 6977360747041035099641623)
                ·
                  refine ⟨10466041120561552649462435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977360747041035099641623 10466041120561552649462435)
                  ·
                    refine ⟨15699061680842328974193653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10466041120561552649462435 15699061680842328974193653)
                    ·
                      refine ⟨1471787032578968341330655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15699061680842328974193653 1471787032578968341330655)
                      ·
                        rfl

theorem cell23_2866295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_2866295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866295 prefixEnd_2866295 := by exact prefixLift 2866295
  have htrace : WordTrace (prefixWord ++ tailWord_2866295) baseStart_2866295 baseEnd_2866295 := by
    simpa [prefixWord, tailWord_2866295, baseEnd_2866295] using wordTrace_append hprefix tailTrace_2866295
  have hstable : (prefixWord ++ tailWord_2866295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866295).length < 2 ^ (prefixWord ++ tailWord_2866295).sum := by decide
  have hdescent : baseEnd_2866295 < baseStart_2866295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866322 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2866322 : Nat := 118140960795 + 2866322 * 2 ^ 59
def prefixEnd_2866322 : Nat := 4983230072969 + 3 ^ 40 * 2866322 * 2
def baseEnd_2866322 : Nat := 1471800896556639735693031

theorem tailTrace_2866322 : CollatzResearch.WordTrace tailWord_2866322 prefixEnd_2866322 1471800896556639735693031 := by
  unfold tailWord_2866322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26135837980453099417332305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69695567947874931779552813 26135837980453099417332305)
  ·
    refine ⟨19601878485339824562999229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26135837980453099417332305 19601878485339824562999229)
    ·
      refine ⟨7350704432002434211124711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19601878485339824562999229 7350704432002434211124711)
      ·
        refine ⟨11026056648003651316687067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350704432002434211124711 11026056648003651316687067)
        ·
          refine ⟨16539084972005476975030601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026056648003651316687067 16539084972005476975030601)
          ·
            refine ⟨12404313729004107731272951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16539084972005476975030601 12404313729004107731272951)
            ·
              refine ⟨18606470593506161596909427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404313729004107731272951 18606470593506161596909427)
              ·
                refine ⟨27909705890259242395364141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18606470593506161596909427 27909705890259242395364141)
                ·
                  refine ⟨10466139708847215898261553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27909705890259242395364141 10466139708847215898261553)
                  ·
                    refine ⟨7849604781635411923696165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10466139708847215898261553 7849604781635411923696165)
                    ·
                      refine ⟨1471800896556639735693031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7849604781635411923696165 1471800896556639735693031)
                      ·
                        rfl

theorem cell23_2866322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2866322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866322 prefixEnd_2866322 := by exact prefixLift 2866322
  have htrace : WordTrace (prefixWord ++ tailWord_2866322) baseStart_2866322 baseEnd_2866322 := by
    simpa [prefixWord, tailWord_2866322, baseEnd_2866322] using wordTrace_append hprefix tailTrace_2866322
  have hstable : (prefixWord ++ tailWord_2866322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866322).length < 2 ^ (prefixWord ++ tailWord_2866322).sum := by decide
  have hdescent : baseEnd_2866322 < baseStart_2866322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866349 : List Nat := [1, 5, 2, 1, 3, 2, 1, 8]
def baseStart_2866349 : Nat := 118140960795 + 2866349 * 2 ^ 59
def prefixEnd_2866349 : Nat := 4983230072969 + 3 ^ 40 * 2866349 * 2
def baseEnd_2866349 : Nat := 54511657797567078890941

theorem tailTrace_2866349 : CollatzResearch.WordTrace tailWord_2866349 prefixEnd_2866349 54511657797567078890941 := by
  unfold tailWord_2866349
  simp only [CollatzResearch.WordTrace]
  refine ⟨104544336692714581280562101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69696224461809720853708067 104544336692714581280562101)
  ·
    refine ⟨9801031564941991995052697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104544336692714581280562101 9801031564941991995052697)
    ·
      refine ⟨7350773673706493996289523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9801031564941991995052697 7350773673706493996289523)
      ·
        refine ⟨11026160510559740994434285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350773673706493996289523 11026160510559740994434285)
        ·
          refine ⟨4134810191459902872912857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11026160510559740994434285 4134810191459902872912857)
          ·
            refine ⟨3101107643594927154684643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4134810191459902872912857 3101107643594927154684643)
            ·
              refine ⟨4651661465392390732026965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101107643594927154684643 4651661465392390732026965)
              ·
                refine ⟨54511657797567078890941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4651661465392390732026965 54511657797567078890941)
                ·
                  rfl

theorem cell23_2866349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 8].length) (baseStart_2866349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866349 prefixEnd_2866349 := by exact prefixLift 2866349
  have htrace : WordTrace (prefixWord ++ tailWord_2866349) baseStart_2866349 baseEnd_2866349 := by
    simpa [prefixWord, tailWord_2866349, baseEnd_2866349] using wordTrace_append hprefix tailTrace_2866349
  have hstable : (prefixWord ++ tailWord_2866349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866349).length < 2 ^ (prefixWord ++ tailWord_2866349).sum := by decide
  have hdescent : baseEnd_2866349 < baseStart_2866349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866359 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_2866359 : Nat := 118140960795 + 2866359 * 2 ^ 59
def prefixEnd_2866359 : Nat := 4983230072969 + 3 ^ 40 * 2866359 * 2
def baseEnd_2866359 : Nat := 1471819895340856090930361

theorem tailTrace_2866359 : CollatzResearch.WordTrace tailWord_2866359 prefixEnd_2866359 1471819895340856090930361 := by
  unfold tailWord_2866359
  simp only [CollatzResearch.WordTrace]
  refine ⟨104544701422678352988426131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69696467615118901992284087 104544701422678352988426131)
  ·
    refine ⟨156817052134017529482639197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104544701422678352988426131 156817052134017529482639197)
    ·
      refine ⟨58806394550256573555989699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156817052134017529482639197 58806394550256573555989699)
      ·
        refine ⟨88209591825384860333984549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58806394550256573555989699 88209591825384860333984549)
        ·
          refine ⟨16539298467259661312622103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88209591825384860333984549 16539298467259661312622103)
          ·
            refine ⟨24808947700889491968933155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16539298467259661312622103 24808947700889491968933155)
            ·
              refine ⟨37213421551334237953399733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24808947700889491968933155 37213421551334237953399733)
              ·
                refine ⟨3488758270437584808131225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37213421551334237953399733 3488758270437584808131225)
                ·
                  refine ⟨2616568702828188606098419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488758270437584808131225 2616568702828188606098419)
                  ·
                    refine ⟨3924853054242282909147629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2616568702828188606098419 3924853054242282909147629)
                    ·
                      refine ⟨1471819895340856090930361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3924853054242282909147629 1471819895340856090930361)
                      ·
                        rfl

theorem cell23_2866359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_2866359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866359 prefixEnd_2866359 := by exact prefixLift 2866359
  have htrace : WordTrace (prefixWord ++ tailWord_2866359) baseStart_2866359 baseEnd_2866359 := by
    simpa [prefixWord, tailWord_2866359, baseEnd_2866359] using wordTrace_append hprefix tailTrace_2866359
  have hstable : (prefixWord ++ tailWord_2866359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866359).length < 2 ^ (prefixWord ++ tailWord_2866359).sum := by decide
  have hdescent : baseEnd_2866359 < baseStart_2866359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866385 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2866385 : Nat := 118140960795 + 2866385 * 2 ^ 59
def prefixEnd_2866385 : Nat := 4983230072969 + 3 ^ 40 * 2866385 * 2
def baseEnd_2866385 : Nat := 1471833245837872989205241

theorem tailTrace_2866385 : CollatzResearch.WordTrace tailWord_2866385 prefixEnd_2866385 1471833245837872989205241 := by
  unfold tailWord_2866385
  simp only [CollatzResearch.WordTrace]
  refine ⟨104545649720584159428872609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69697099813722772952581739 104545649720584159428872609)
  ·
    refine ⟨78409237290438119571654457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104545649720584159428872609 78409237290438119571654457)
    ·
      refine ⟨58806927967828589678740843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78409237290438119571654457 58806927967828589678740843)
      ·
        refine ⟨88210391951742884518111265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58806927967828589678740843 88210391951742884518111265)
        ·
          refine ⟨66157793963807163388583449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88210391951742884518111265 66157793963807163388583449)
          ·
            refine ⟨49618345472855372541437587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66157793963807163388583449 49618345472855372541437587)
            ·
              refine ⟨74427518209283058812156381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49618345472855372541437587 74427518209283058812156381)
              ·
                refine ⟨27910319328481147054558643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74427518209283058812156381 27910319328481147054558643)
                ·
                  refine ⟨41865478992721720581837965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27910319328481147054558643 41865478992721720581837965)
                  ·
                    refine ⟨15699554622270645218189237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41865478992721720581837965 15699554622270645218189237)
                    ·
                      refine ⟨1471833245837872989205241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15699554622270645218189237 1471833245837872989205241)
                      ·
                        rfl

theorem cell23_2866385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2866385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866385 prefixEnd_2866385 := by exact prefixLift 2866385
  have htrace : WordTrace (prefixWord ++ tailWord_2866385) baseStart_2866385 baseEnd_2866385 := by
    simpa [prefixWord, tailWord_2866385, baseEnd_2866385] using wordTrace_append hprefix tailTrace_2866385
  have hstable : (prefixWord ++ tailWord_2866385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866385).length < 2 ^ (prefixWord ++ tailWord_2866385).sum := by decide
  have hdescent : baseEnd_2866385 < baseStart_2866385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866386 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_2866386 : Nat := 118140960795 + 2866386 * 2 ^ 59
def prefixEnd_2866386 : Nat := 4983230072969 + 3 ^ 40 * 2866386 * 2
def baseEnd_2866386 : Nat := 1471833759318527485292737

theorem tailTrace_2866386 : CollatzResearch.WordTrace tailWord_2866386 prefixEnd_2866386 1471833759318527485292737 := by
  unfold tailWord_2866386
  simp only [CollatzResearch.WordTrace]
  refine ⟨26136421548395134149914753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69697124129053691066439341 26136421548395134149914753)
  ·
    refine ⟨19602316161296350612436065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26136421548395134149914753 19602316161296350612436065)
    ·
      refine ⟨14701737120972262959327049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19602316161296350612436065 14701737120972262959327049)
      ·
        refine ⟨11026302840729197219495287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14701737120972262959327049 11026302840729197219495287)
        ·
          refine ⟨16539454261093795829242931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026302840729197219495287 16539454261093795829242931)
          ·
            refine ⟨24809181391640693743864397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16539454261093795829242931 24809181391640693743864397)
            ·
              refine ⟨9303443021865260153949149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24809181391640693743864397 9303443021865260153949149)
              ·
                refine ⟨3488791133199472557730931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9303443021865260153949149 3488791133199472557730931)
                ·
                  refine ⟨5233186699799208836596397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488791133199472557730931 5233186699799208836596397)
                  ·
                    refine ⟨1962445012424703313723649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5233186699799208836596397 1962445012424703313723649)
                    ·
                      refine ⟨1471833759318527485292737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962445012424703313723649 1471833759318527485292737)
                      ·
                        rfl

theorem cell23_2866386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_2866386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866386 prefixEnd_2866386 := by exact prefixLift 2866386
  have htrace : WordTrace (prefixWord ++ tailWord_2866386) baseStart_2866386 baseEnd_2866386 := by
    simpa [prefixWord, tailWord_2866386, baseEnd_2866386] using wordTrace_append hprefix tailTrace_2866386
  have hstable : (prefixWord ++ tailWord_2866386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866386).length < 2 ^ (prefixWord ++ tailWord_2866386).sum := by decide
  have hdescent : baseEnd_2866386 < baseStart_2866386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866412 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2866412 : Nat := 118140960795 + 2866412 * 2 ^ 59
def prefixEnd_2866412 : Nat := 4983230072969 + 3 ^ 40 * 2866412 * 2
def baseEnd_2866412 : Nat := 1471847109815544383567617

theorem tailTrace_2866412 : CollatzResearch.WordTrace tailWord_2866412 prefixEnd_2866412 1471847109815544383567617 := by
  unfold tailWord_2866412
  simp only [CollatzResearch.WordTrace]
  refine ⟨52273317245743171520052745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69697756327657562026736993 52273317245743171520052745)
  ·
    refine ⟨39204987934307378640039559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52273317245743171520052745 39204987934307378640039559)
    ·
      refine ⟨58807481901461067960059339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39204987934307378640039559 58807481901461067960059339)
      ·
        refine ⟨88211222852191601940089009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58807481901461067960059339 88211222852191601940089009)
        ·
          refine ⟨66158417139143701455066757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88211222852191601940089009 66158417139143701455066757)
          ·
            refine ⟨12404703213589444022825017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66158417139143701455066757 12404703213589444022825017)
            ·
              refine ⟨9303527410192083017118763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12404703213589444022825017 9303527410192083017118763)
              ·
                refine ⟨13955291115288124525678145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9303527410192083017118763 13955291115288124525678145)
                ·
                  refine ⟨10466468336466093394258609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13955291115288124525678145 10466468336466093394258609)
                  ·
                    refine ⟨7849851252349570045693957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10466468336466093394258609 7849851252349570045693957)
                    ·
                      refine ⟨1471847109815544383567617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7849851252349570045693957 1471847109815544383567617)
                      ·
                        rfl

theorem cell23_2866412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2866412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866412 prefixEnd_2866412 := by exact prefixLift 2866412
  have htrace : WordTrace (prefixWord ++ tailWord_2866412) baseStart_2866412 baseEnd_2866412 := by
    simpa [prefixWord, tailWord_2866412, baseEnd_2866412] using wordTrace_append hprefix tailTrace_2866412
  have hstable : (prefixWord ++ tailWord_2866412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866412).length < 2 ^ (prefixWord ++ tailWord_2866412).sum := by decide
  have hdescent : baseEnd_2866412 < baseStart_2866412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866456 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 5]
def baseStart_2866456 : Nat := 118140960795 + 2866456 * 2 ^ 59
def prefixEnd_2866456 : Nat := 4983230072969 + 3 ^ 40 * 2866456 * 2
def baseEnd_2866456 : Nat := 163541078107149134601935

theorem tailTrace_2866456 : CollatzResearch.WordTrace tailWord_2866456 prefixEnd_2866456 163541078107149134601935 := by
  unfold tailWord_2866456
  simp only [CollatzResearch.WordTrace]
  refine ⟨52274119651663469277353611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69698826202217959036471481 52274119651663469277353611)
  ·
    refine ⟨78411179477495203916030417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52274119651663469277353611 78411179477495203916030417)
    ·
      refine ⟨58808384608121402937022813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78411179477495203916030417 58808384608121402937022813)
      ·
        refine ⟨22053144228045526101383555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58808384608121402937022813 22053144228045526101383555)
        ·
          refine ⟨33079716342068289152075333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22053144228045526101383555 33079716342068289152075333)
          ·
            refine ⟨6202446814137804216014125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33079716342068289152075333 6202446814137804216014125)
            ·
              refine ⟨2325917555301676581005297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6202446814137804216014125 2325917555301676581005297)
              ·
                refine ⟨1744438166476257435753973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325917555301676581005297 1744438166476257435753973)
                ·
                  refine ⟨163541078107149134601935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1744438166476257435753973 163541078107149134601935)
                  ·
                    rfl

theorem cell23_2866456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 5].length) (baseStart_2866456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866456 prefixEnd_2866456 := by exact prefixLift 2866456
  have htrace : WordTrace (prefixWord ++ tailWord_2866456) baseStart_2866456 baseEnd_2866456 := by
    simpa [prefixWord, tailWord_2866456, baseEnd_2866456] using wordTrace_append hprefix tailTrace_2866456
  have hstable : (prefixWord ++ tailWord_2866456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866456).length < 2 ^ (prefixWord ++ tailWord_2866456).sum := by decide
  have hdescent : baseEnd_2866456 < baseStart_2866456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866599 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2866599 : Nat := 118140960795 + 2866599 * 2 ^ 59
def prefixEnd_2866599 : Nat := 4983230072969 + 3 ^ 40 * 2866599 * 2
def baseEnd_2866599 : Nat := 1471943130697935151929257

theorem tailTrace_2866599 : CollatzResearch.WordTrace tailWord_2866599 prefixEnd_2866599 1471943130697935151929257 := by
  unfold tailWord_2866599
  simp only [CollatzResearch.WordTrace]
  refine ⟨104553454941808873977162851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69702303294539249318108567 104553454941808873977162851)
  ·
    refine ⟨156830182412713310965744277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104553454941808873977162851 156830182412713310965744277)
    ·
      refine ⟨7351414800595936451519263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156830182412713310965744277 7351414800595936451519263)
      ·
        refine ⟨11027122200893904677278895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7351414800595936451519263 11027122200893904677278895)
        ·
          refine ⟨16540683301340857015918343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11027122200893904677278895 16540683301340857015918343)
          ·
            refine ⟨24811024952011285523877515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16540683301340857015918343 24811024952011285523877515)
            ·
              refine ⟨37216537428016928285816273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24811024952011285523877515 37216537428016928285816273)
              ·
                refine ⟨27912403071012696214362205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37216537428016928285816273 27912403071012696214362205)
                ·
                  refine ⟨10467151151629761080385827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27912403071012696214362205 10467151151629761080385827)
                  ·
                    refine ⟨15700726727444641620578741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10467151151629761080385827 15700726727444641620578741)
                    ·
                      refine ⟨1471943130697935151929257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15700726727444641620578741 1471943130697935151929257)
                      ·
                        rfl

theorem cell23_2866599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2866599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866599 prefixEnd_2866599 := by exact prefixLift 2866599
  have htrace : WordTrace (prefixWord ++ tailWord_2866599) baseStart_2866599 baseEnd_2866599 := by
    simpa [prefixWord, tailWord_2866599, baseEnd_2866599] using wordTrace_append hprefix tailTrace_2866599
  have hstable : (prefixWord ++ tailWord_2866599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866599).length < 2 ^ (prefixWord ++ tailWord_2866599).sum := by decide
  have hdescent : baseEnd_2866599 < baseStart_2866599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866609 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2866609 : Nat := 118140960795 + 2866609 * 2 ^ 59
def prefixEnd_2866609 : Nat := 4983230072969 + 3 ^ 40 * 2866609 * 2
def baseEnd_2866609 : Nat := 1471948265504480112804211

theorem tailTrace_2866609 : CollatzResearch.WordTrace tailWord_2866609 prefixEnd_2866609 1471948265504480112804211 := by
  unfold tailWord_2866609
  simp only [CollatzResearch.WordTrace]
  refine ⟨104553819671772645685026881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69702546447848430456684587 104553819671772645685026881)
  ·
    refine ⟨78415364753829484263770161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104553819671772645685026881 78415364753829484263770161)
    ·
      refine ⟨58811523565372113197827621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78415364753829484263770161 58811523565372113197827621)
      ·
        refine ⟨11027160668507271224592679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58811523565372113197827621 11027160668507271224592679)
        ·
          refine ⟨16540741002760906836889019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11027160668507271224592679 16540741002760906836889019)
          ·
            refine ⟨24811111504141360255333529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16540741002760906836889019 24811111504141360255333529)
            ·
              refine ⟨18608333628106020191500147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24811111504141360255333529 18608333628106020191500147)
              ·
                refine ⟨27912500442159030287250221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18608333628106020191500147 27912500442159030287250221)
                ·
                  refine ⟨10467187665809636357718833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27912500442159030287250221 10467187665809636357718833)
                  ·
                    refine ⟨7850390749357227268289125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10467187665809636357718833 7850390749357227268289125)
                    ·
                      refine ⟨1471948265504480112804211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7850390749357227268289125 1471948265504480112804211)
                      ·
                        rfl

theorem cell23_2866609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2866609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866609 prefixEnd_2866609 := by exact prefixLift 2866609
  have htrace : WordTrace (prefixWord ++ tailWord_2866609) baseStart_2866609 baseEnd_2866609 := by
    simpa [prefixWord, tailWord_2866609, baseEnd_2866609] using wordTrace_append hprefix tailTrace_2866609
  have hstable : (prefixWord ++ tailWord_2866609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866609).length < 2 ^ (prefixWord ++ tailWord_2866609).sum := by decide
  have hdescent : baseEnd_2866609 < baseStart_2866609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866616 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_2866616 : Nat := 118140960795 + 2866616 * 2 ^ 59
def prefixEnd_2866616 : Nat := 4983230072969 + 3 ^ 40 * 2866616 * 2
def baseEnd_2866616 : Nat := 1471951859869061585416679

theorem tailTrace_2866616 : CollatzResearch.WordTrace tailWord_2866616 prefixEnd_2866616 1471951859869061585416679 := by
  unfold tailWord_2866616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52277037491373642940265851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69702716655164857253687801 52277037491373642940265851)
  ·
    refine ⟨78415556237060464410398777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52277037491373642940265851 78415556237060464410398777)
    ·
      refine ⟨58811667177795348307799083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78415556237060464410398777 58811667177795348307799083)
      ·
        refine ⟨88217500766693022461698625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58811667177795348307799083 88217500766693022461698625)
        ·
          refine ⟨66163125575019766846273969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88217500766693022461698625 66163125575019766846273969)
          ·
            refine ⟨49622344181264825134705477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66163125575019766846273969 49622344181264825134705477)
            ·
              refine ⟨9304189533987154712757277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49622344181264825134705477 9304189533987154712757277)
              ·
                refine ⟨3489071075245183017283979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9304189533987154712757277 3489071075245183017283979)
                ·
                  refine ⟨5233606612867774525925969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489071075245183017283979 5233606612867774525925969)
                  ·
                    refine ⟨3925204959650830894444477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5233606612867774525925969 3925204959650830894444477)
                    ·
                      refine ⟨1471951859869061585416679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3925204959650830894444477 1471951859869061585416679)
                      ·
                        rfl

theorem cell23_2866616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_2866616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866616 prefixEnd_2866616 := by exact prefixLift 2866616
  have htrace : WordTrace (prefixWord ++ tailWord_2866616) baseStart_2866616 baseEnd_2866616 := by
    simpa [prefixWord, tailWord_2866616, baseEnd_2866616] using wordTrace_append hprefix tailTrace_2866616
  have hstable : (prefixWord ++ tailWord_2866616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866616).length < 2 ^ (prefixWord ++ tailWord_2866616).sum := by decide
  have hdescent : baseEnd_2866616 < baseStart_2866616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866690 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2866690 : Nat := 118140960795 + 2866690 * 2 ^ 59
def prefixEnd_2866690 : Nat := 4983230072969 + 3 ^ 40 * 2866690 * 2
def baseEnd_2866690 : Nat := 1471989857437494295891339

theorem tailTrace_2866690 : CollatzResearch.WordTrace tailWord_2866690 prefixEnd_2866690 1471989857437494295891339 := by
  unfold tailWord_2866690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26139193496119799129681381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69704515989652797679150349 26139193496119799129681381)
  ·
    refine ⟨4901098780522462336815259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26139193496119799129681381 4901098780522462336815259)
    ·
      refine ⟨7351648170783693505222889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901098780522462336815259 7351648170783693505222889)
      ·
        refine ⟨5513736128087770128917167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7351648170783693505222889 5513736128087770128917167)
        ·
          refine ⟨8270604192131655193375751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513736128087770128917167 8270604192131655193375751)
          ·
            refine ⟨12405906288197482790063627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270604192131655193375751 12405906288197482790063627)
            ·
              refine ⟨18608859432296224185095441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12405906288197482790063627 18608859432296224185095441)
              ·
                refine ⟨13956644574222168138821581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18608859432296224185095441 13956644574222168138821581)
                ·
                  refine ⟨5233741715333313052058093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13956644574222168138821581 5233741715333313052058093)
                  ·
                    refine ⟨1962653143249992394521785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5233741715333313052058093 1962653143249992394521785)
                    ·
                      refine ⟨1471989857437494295891339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962653143249992394521785 1471989857437494295891339)
                      ·
                        rfl

theorem cell23_2866690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2866690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866690 prefixEnd_2866690 := by exact prefixLift 2866690
  have htrace : WordTrace (prefixWord ++ tailWord_2866690) baseStart_2866690 baseEnd_2866690 := by
    simpa [prefixWord, tailWord_2866690, baseEnd_2866690] using wordTrace_append hprefix tailTrace_2866690
  have hstable : (prefixWord ++ tailWord_2866690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866690).length < 2 ^ (prefixWord ++ tailWord_2866690).sum := by decide
  have hdescent : baseEnd_2866690 < baseStart_2866690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866709 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 9]
def baseStart_2866709 : Nat := 118140960795 + 2866709 * 2 ^ 59
def prefixEnd_2866709 : Nat := 4983230072969 + 3 ^ 40 * 2866709 * 2
def baseEnd_2866709 : Nat := 163555512618881080172639

theorem tailTrace_2866709 : CollatzResearch.WordTrace tailWord_2866709 prefixEnd_2866709 163555512618881080172639 := by
  unfold tailWord_2866709
  simp only [CollatzResearch.WordTrace]
  refine ⟨104557466971410362763667181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69704977980940241842444787 104557466971410362763667181)
  ·
    refine ⟨39209050114278886036375193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104557466971410362763667181 39209050114278886036375193)
    ·
      refine ⟨29406787585709164527281395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39209050114278886036375193 29406787585709164527281395)
      ·
        refine ⟨44110181378563746790922093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29406787585709164527281395 44110181378563746790922093)
        ·
          refine ⟨16541318016961405046595785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44110181378563746790922093 16541318016961405046595785)
          ·
            refine ⟨12405988512721053784946839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16541318016961405046595785 12405988512721053784946839)
            ·
              refine ⟨18608982769081580677420259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12405988512721053784946839 18608982769081580677420259)
              ·
                refine ⟨27913474153622371016130389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18608982769081580677420259 27913474153622371016130389)
                ·
                  refine ⟨163555512618881080172639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27913474153622371016130389 163555512618881080172639)
                  ·
                    rfl

theorem cell23_2866709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_2866709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866709 prefixEnd_2866709 := by exact prefixLift 2866709
  have htrace : WordTrace (prefixWord ++ tailWord_2866709) baseStart_2866709 baseEnd_2866709 := by
    simpa [prefixWord, tailWord_2866709, baseEnd_2866709] using wordTrace_append hprefix tailTrace_2866709
  have hstable : (prefixWord ++ tailWord_2866709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866709).length < 2 ^ (prefixWord ++ tailWord_2866709).sum := by decide
  have hdescent : baseEnd_2866709 < baseStart_2866709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866718 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2866718 : Nat := 118140960795 + 2866718 * 2 ^ 59
def prefixEnd_2866718 : Nat := 4983230072969 + 3 ^ 40 * 2866718 * 2
def baseEnd_2866718 : Nat := 1472004234895820186341211

theorem tailTrace_2866718 : CollatzResearch.WordTrace tailWord_2866718 prefixEnd_2866718 1472004234895820186341211 := by
  unfold tailWord_2866718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069724403547219662593101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69705196818918504867163205 13069724403547219662593101)
  ·
    refine ⟨4901146651330207373472413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13069724403547219662593101 4901146651330207373472413)
    ·
      refine ⟨1837929994248827765052155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4901146651330207373472413 1837929994248827765052155)
      ·
        refine ⟨2756894991373241647578233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837929994248827765052155 2756894991373241647578233)
        ·
          refine ⟨2067671243529931235683675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756894991373241647578233 2067671243529931235683675)
          ·
            refine ⟨3101506865294896853525513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067671243529931235683675 3101506865294896853525513)
            ·
              refine ⟨2326130148971172640144135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3101506865294896853525513 2326130148971172640144135)
              ·
                refine ⟨3489195223456758960216203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326130148971172640144135 3489195223456758960216203)
                ·
                  refine ⟨5233792835185138440324305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489195223456758960216203 5233792835185138440324305)
                  ·
                    refine ⟨3925344626388853830243229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5233792835185138440324305 3925344626388853830243229)
                    ·
                      refine ⟨1472004234895820186341211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3925344626388853830243229 1472004234895820186341211)
                      ·
                        rfl

theorem cell23_2866718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2866718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866718 prefixEnd_2866718 := by exact prefixLift 2866718
  have htrace : WordTrace (prefixWord ++ tailWord_2866718) baseStart_2866718 baseEnd_2866718 := by
    simpa [prefixWord, tailWord_2866718, baseEnd_2866718] using wordTrace_append hprefix tailTrace_2866718
  have hstable : (prefixWord ++ tailWord_2866718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866718).length < 2 ^ (prefixWord ++ tailWord_2866718).sum := by decide
  have hdescent : baseEnd_2866718 < baseStart_2866718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866769 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_2866769 : Nat := 118140960795 + 2866769 * 2 ^ 59
def prefixEnd_2866769 : Nat := 4983230072969 + 3 ^ 40 * 2866769 * 2
def baseEnd_2866769 : Nat := 490676807469733162267825

theorem tailTrace_2866769 : CollatzResearch.WordTrace tailWord_2866769 prefixEnd_2866769 490676807469733162267825 := by
  unfold tailWord_2866769
  simp only [CollatzResearch.WordTrace]
  refine ⟨104559655351192993010851361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69706436900795328673900907 104559655351192993010851361)
  ·
    refine ⟨78419741513394744758138521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104559655351192993010851361 78419741513394744758138521)
    ·
      refine ⟨58814806135046058568603891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78419741513394744758138521 58814806135046058568603891)
      ·
        refine ⟨88222209202569087852905837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58814806135046058568603891 88222209202569087852905837)
        ·
          refine ⟨33083328450963407944839689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88222209202569087852905837 33083328450963407944839689)
          ·
            refine ⟨24812496338222555958629767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33083328450963407944839689 24812496338222555958629767)
            ·
              refine ⟨37218744507333833937944651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24812496338222555958629767 37218744507333833937944651)
              ·
                refine ⟨55828116761000750906916977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37218744507333833937944651 55828116761000750906916977)
                ·
                  refine ⟨41871087570750563180187733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55828116761000750906916977 41871087570750563180187733)
                  ·
                    refine ⟨490676807469733162267825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41871087570750563180187733 490676807469733162267825)
                    ·
                      rfl

theorem cell23_2866769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_2866769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866769 prefixEnd_2866769 := by exact prefixLift 2866769
  have htrace : WordTrace (prefixWord ++ tailWord_2866769) baseStart_2866769 baseEnd_2866769 := by
    simpa [prefixWord, tailWord_2866769, baseEnd_2866769] using wordTrace_append hprefix tailTrace_2866769
  have hstable : (prefixWord ++ tailWord_2866769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866769).length < 2 ^ (prefixWord ++ tailWord_2866769).sum := by decide
  have hdescent : baseEnd_2866769 < baseStart_2866769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866776 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2866776 : Nat := 118140960795 + 2866776 * 2 ^ 59
def prefixEnd_2866776 : Nat := 4983230072969 + 3 ^ 40 * 2866776 * 2
def baseEnd_2866776 : Nat := 1472034016773780959415943

theorem tailTrace_2866776 : CollatzResearch.WordTrace tailWord_2866776 prefixEnd_2866776 1472034016773780959415943 := by
  unfold tailWord_2866776
  simp only [CollatzResearch.WordTrace]
  refine ⟨52279955331083816603178091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69706607108111755470904121 52279955331083816603178091)
  ·
    refine ⟨78419932996625724904767137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52279955331083816603178091 78419932996625724904767137)
    ·
      refine ⟨58814949747469293678575353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78419932996625724904767137 58814949747469293678575353)
      ·
        refine ⟨44111212310601970258931515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58814949747469293678575353 44111212310601970258931515)
        ·
          refine ⟨66166818465902955388397273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44111212310601970258931515 66166818465902955388397273)
          ·
            refine ⟨49625113849427216541297955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66166818465902955388397273 49625113849427216541297955)
            ·
              refine ⟨74437670774140824811946933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49625113849427216541297955 74437670774140824811946933)
              ·
                refine ⟨6978531635075702326120025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74437670774140824811946933 6978531635075702326120025)
                ·
                  refine ⟨5233898726306776744590019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978531635075702326120025 5233898726306776744590019)
                  ·
                    refine ⟨7850848089460165116885029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5233898726306776744590019 7850848089460165116885029)
                    ·
                      refine ⟨1472034016773780959415943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7850848089460165116885029 1472034016773780959415943)
                      ·
                        rfl

theorem cell23_2866776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2866776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866776 prefixEnd_2866776 := by exact prefixLift 2866776
  have htrace : WordTrace (prefixWord ++ tailWord_2866776) baseStart_2866776 baseEnd_2866776 := by
    simpa [prefixWord, tailWord_2866776, baseEnd_2866776] using wordTrace_append hprefix tailTrace_2866776
  have hstable : (prefixWord ++ tailWord_2866776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866776).length < 2 ^ (prefixWord ++ tailWord_2866776).sum := by decide
  have hdescent : baseEnd_2866776 < baseStart_2866776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866816 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 6]
def baseStart_2866816 : Nat := 118140960795 + 2866816 * 2 ^ 59
def prefixEnd_2866816 : Nat := 4983230072969 + 3 ^ 40 * 2866816 * 2
def baseEnd_2866816 : Nat := 163561617333328978101751

theorem tailTrace_2866816 : CollatzResearch.WordTrace tailWord_2866816 prefixEnd_2866816 163561617333328978101751 := by
  unfold tailWord_2866816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52280684791011360018906151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69707579721348480025208201 52280684791011360018906151)
  ·
    refine ⟨78421027186517040028359227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52280684791011360018906151 78421027186517040028359227)
    ·
      refine ⟨117631540779775560042538841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78421027186517040028359227 117631540779775560042538841)
      ·
        refine ⟨88223655584831670031904131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117631540779775560042538841 88223655584831670031904131)
        ·
          refine ⟨132335483377247505047856197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88223655584831670031904131 132335483377247505047856197)
          ·
            refine ⟨24812903133233907196473037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132335483377247505047856197 24812903133233907196473037)
            ·
              refine ⟨9304838674962715198677389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24812903133233907196473037 9304838674962715198677389)
              ·
                refine ⟨3489314503111018199504021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9304838674962715198677389 3489314503111018199504021)
                ·
                  refine ⟨163561617333328978101751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3489314503111018199504021 163561617333328978101751)
                  ·
                    rfl

theorem cell23_2866816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_2866816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866816 prefixEnd_2866816 := by exact prefixLift 2866816
  have htrace : WordTrace (prefixWord ++ tailWord_2866816) baseStart_2866816 baseEnd_2866816 := by
    simpa [prefixWord, tailWord_2866816, baseEnd_2866816] using wordTrace_append hprefix tailTrace_2866816
  have hstable : (prefixWord ++ tailWord_2866816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866816).length < 2 ^ (prefixWord ++ tailWord_2866816).sum := by decide
  have hdescent : baseEnd_2866816 < baseStart_2866816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866830 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2866830 : Nat := 118140960795 + 2866830 * 2 ^ 59
def prefixEnd_2866830 : Nat := 4983230072969 + 3 ^ 40 * 2866830 * 2
def baseEnd_2866830 : Nat := 1472061744729123748140695

theorem tailTrace_2866830 : CollatzResearch.WordTrace tailWord_2866830 prefixEnd_2866830 1472061744729123748140695 := by
  unfold tailWord_2866830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070235025496500053602743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69707920135981333619214629 13070235025496500053602743)
  ·
    refine ⟨19605352538244750080404115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13070235025496500053602743 19605352538244750080404115)
    ·
      refine ⟨29408028807367125120606173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19605352538244750080404115 29408028807367125120606173)
      ·
        refine ⟨11028010802762671920227315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29408028807367125120606173 11028010802762671920227315)
        ·
          refine ⟨16542016204144007880340973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028010802762671920227315 16542016204144007880340973)
          ·
            refine ⟨6203256076554002955127865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16542016204144007880340973 6203256076554002955127865)
            ·
              refine ⟨4652442057415502216345899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203256076554002955127865 4652442057415502216345899)
              ·
                refine ⟨6978663086123253324518849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652442057415502216345899 6978663086123253324518849)
                ·
                  refine ⟨5233997314592439993389137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978663086123253324518849 5233997314592439993389137)
                  ·
                    refine ⟨3925497985944329995041853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5233997314592439993389137 3925497985944329995041853)
                    ·
                      refine ⟨1472061744729123748140695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3925497985944329995041853 1472061744729123748140695)
                      ·
                        rfl

theorem cell23_2866830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2866830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866830 prefixEnd_2866830 := by exact prefixLift 2866830
  have htrace : WordTrace (prefixWord ++ tailWord_2866830) baseStart_2866830 baseEnd_2866830 := by
    simpa [prefixWord, tailWord_2866830, baseEnd_2866830] using wordTrace_append hprefix tailTrace_2866830
  have hstable : (prefixWord ++ tailWord_2866830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866830).length < 2 ^ (prefixWord ++ tailWord_2866830).sum := by decide
  have hdescent : baseEnd_2866830 < baseStart_2866830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866896 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_2866896 : Nat := 118140960795 + 2866896 * 2 ^ 59
def prefixEnd_2866896 : Nat := 4983230072969 + 3 ^ 40 * 2866896 * 2
def baseEnd_2866896 : Nat := 1472095634452320489915391

theorem tailTrace_2866896 : CollatzResearch.WordTrace tailWord_2866896 prefixEnd_2866896 1472095634452320489915391 := by
  unfold tailWord_2866896
  simp only [CollatzResearch.WordTrace]
  refine ⟨52282143710866446850362271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69709524947821929133816361 52282143710866446850362271)
  ·
    refine ⟨78423215566299670275543407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52282143710866446850362271 78423215566299670275543407)
    ·
      refine ⟨117634823349449505413315111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78423215566299670275543407 117634823349449505413315111)
      ·
        refine ⟨176452235024174258119972667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117634823349449505413315111 176452235024174258119972667)
        ·
          refine ⟨264678352536261387179959001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176452235024174258119972667 264678352536261387179959001)
          ·
            refine ⟨198508764402196040384969251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264678352536261387179959001 198508764402196040384969251)
            ·
              refine ⟨297763146603294060577453877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198508764402196040384969251 297763146603294060577453877)
              ·
                refine ⟨27915294994058818179136301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297763146603294060577453877 27915294994058818179136301)
                ·
                  refine ⟨10468235622772056817176113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27915294994058818179136301 10468235622772056817176113)
                  ·
                    refine ⟨7851176717079042612882085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10468235622772056817176113 7851176717079042612882085)
                    ·
                      refine ⟨1472095634452320489915391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7851176717079042612882085 1472095634452320489915391)
                      ·
                        rfl

theorem cell23_2866896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_2866896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866896 prefixEnd_2866896 := by exact prefixLift 2866896
  have htrace : WordTrace (prefixWord ++ tailWord_2866896) baseStart_2866896 baseEnd_2866896 := by
    simpa [prefixWord, tailWord_2866896, baseEnd_2866896] using wordTrace_append hprefix tailTrace_2866896
  have hstable : (prefixWord ++ tailWord_2866896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866896).length < 2 ^ (prefixWord ++ tailWord_2866896).sum := by decide
  have hdescent : baseEnd_2866896 < baseStart_2866896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866906 : List Nat := [3, 1, 1, 2, 2, 4, 10]
def baseStart_2866906 : Nat := 118140960795 + 2866906 * 2 ^ 59
def prefixEnd_2866906 : Nat := 4983230072969 + 3 ^ 40 * 2866906 * 2
def baseEnd_2866906 : Nat := 18174083571097104330745

theorem tailTrace_2866906 : CollatzResearch.WordTrace tailWord_2866906 prefixEnd_2866906 18174083571097104330745 := by
  unfold tailWord_2866906
  simp only [CollatzResearch.WordTrace]
  refine ⟨26141163037924166352147143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69709768101131110272392381 26141163037924166352147143)
  ·
    refine ⟨39211744556886249528220715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26141163037924166352147143 39211744556886249528220715)
    ·
      refine ⟨58817616835329374292331073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39211744556886249528220715 58817616835329374292331073)
      ·
        refine ⟨44113212626497030719248305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58817616835329374292331073 44113212626497030719248305)
        ·
          refine ⟨33084909469872773039436229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44113212626497030719248305 33084909469872773039436229)
          ·
            refine ⟨6203420525601144944894293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33084909469872773039436229 6203420525601144944894293)
            ·
              refine ⟨18174083571097104330745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6203420525601144944894293 18174083571097104330745)
              ·
                rfl

theorem cell23_2866906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 10].length) (baseStart_2866906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866906 prefixEnd_2866906 := by exact prefixLift 2866906
  have htrace : WordTrace (prefixWord ++ tailWord_2866906) baseStart_2866906 baseEnd_2866906 := by
    simpa [prefixWord, tailWord_2866906, baseEnd_2866906] using wordTrace_append hprefix tailTrace_2866906
  have hstable : (prefixWord ++ tailWord_2866906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866906).length < 2 ^ (prefixWord ++ tailWord_2866906).sum := by decide
  have hdescent : baseEnd_2866906 < baseStart_2866906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866917 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2866917 : Nat := 118140960795 + 2866917 * 2 ^ 59
def prefixEnd_2866917 : Nat := 4983230072969 + 3 ^ 40 * 2866917 * 2
def baseEnd_2866917 : Nat := 1472106417546064907752795

theorem tailTrace_2866917 : CollatzResearch.WordTrace tailWord_2866917 prefixEnd_2866917 1472106417546064907752795 := by
  unfold tailWord_2866917
  simp only [CollatzResearch.WordTrace]
  refine ⟨104565053354656814287239005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69710035569771209524826003 104565053354656814287239005)
  ·
    refine ⟨39211895007996305357714627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104565053354656814287239005 39211895007996305357714627)
    ·
      refine ⟨58817842511994458036571941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39211895007996305357714627 58817842511994458036571941)
      ·
        refine ⟨11028345470998960881857239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58817842511994458036571941 11028345470998960881857239)
        ·
          refine ⟨16542518206498441322785859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028345470998960881857239 16542518206498441322785859)
          ·
            refine ⟨24813777309747661984178789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16542518206498441322785859 24813777309747661984178789)
            ·
              refine ⟨4652583245577686622033523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24813777309747661984178789 4652583245577686622033523)
              ·
                refine ⟨6978874868366529933050285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652583245577686622033523 6978874868366529933050285)
                ·
                  refine ⟨2617078075637448724893857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6978874868366529933050285 2617078075637448724893857)
                  ·
                    refine ⟨1962808556728086543670393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2617078075637448724893857 1962808556728086543670393)
                    ·
                      refine ⟨1472106417546064907752795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962808556728086543670393 1472106417546064907752795)
                      ·
                        rfl

theorem cell23_2866917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2866917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866917 prefixEnd_2866917 := by exact prefixLift 2866917
  have htrace : WordTrace (prefixWord ++ tailWord_2866917) baseStart_2866917 baseEnd_2866917 := by
    simpa [prefixWord, tailWord_2866917, baseEnd_2866917] using wordTrace_append hprefix tailTrace_2866917
  have hstable : (prefixWord ++ tailWord_2866917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866917).length < 2 ^ (prefixWord ++ tailWord_2866917).sum := by decide
  have hdescent : baseEnd_2866917 < baseStart_2866917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866984 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2866984 : Nat := 118140960795 + 2866984 * 2 ^ 59
def prefixEnd_2866984 : Nat := 4983230072969 + 3 ^ 40 * 2866984 * 2
def baseEnd_2866984 : Nat := 1472140820749916145614987

theorem tailTrace_2866984 : CollatzResearch.WordTrace tailWord_2866984 prefixEnd_2866984 1472140820749916145614987 := by
  unfold tailWord_2866984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52283748522707042364964003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69711664696942723153285337 52283748522707042364964003)
  ·
    refine ⟨78425622784060563547446005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52283748522707042364964003 78425622784060563547446005)
    ·
      refine ⟨7352402136005677832573063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78425622784060563547446005 7352402136005677832573063)
      ·
        refine ⟨11028603204008516748859595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352402136005677832573063 11028603204008516748859595)
        ·
          refine ⟨16542904806012775123289393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028603204008516748859595 16542904806012775123289393)
          ·
            refine ⟨12407178604509581342467045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16542904806012775123289393 12407178604509581342467045)
            ·
              refine ⟨2326345988345546501712571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12407178604509581342467045 2326345988345546501712571)
              ·
                refine ⟨3489518982518319752568857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326345988345546501712571 3489518982518319752568857)
                ·
                  refine ⟨2617139236888739814426643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489518982518319752568857 2617139236888739814426643)
                  ·
                    refine ⟨3925708855333109721639965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617139236888739814426643 3925708855333109721639965)
                    ·
                      refine ⟨1472140820749916145614987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3925708855333109721639965 1472140820749916145614987)
                      ·
                        rfl

theorem cell23_2866984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2866984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866984 prefixEnd_2866984 := by exact prefixLift 2866984
  have htrace : WordTrace (prefixWord ++ tailWord_2866984) baseStart_2866984 baseEnd_2866984 := by
    simpa [prefixWord, tailWord_2866984, baseEnd_2866984] using wordTrace_append hprefix tailTrace_2866984
  have hstable : (prefixWord ++ tailWord_2866984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866984).length < 2 ^ (prefixWord ++ tailWord_2866984).sum := by decide
  have hdescent : baseEnd_2866984 < baseStart_2866984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866993 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2866993 : Nat := 118140960795 + 2866993 * 2 ^ 59
def prefixEnd_2866993 : Nat := 4983230072969 + 3 ^ 40 * 2866993 * 2
def baseEnd_2866993 : Nat := 1472145442075806610402445

theorem tailTrace_2866993 : CollatzResearch.WordTrace tailWord_2866993 prefixEnd_2866993 1472145442075806610402445 := by
  unfold tailWord_2866993
  simp only [CollatzResearch.WordTrace]
  refine ⟨104567825302381479267005633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69711883534920986178003755 104567825302381479267005633)
  ·
    refine ⟨78425868976786109450254225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104567825302381479267005633 78425868976786109450254225)
    ·
      refine ⟨58819401732589582087690669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78425868976786109450254225 58819401732589582087690669)
      ·
        refine ⟨22057275649721093282884001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58819401732589582087690669 22057275649721093282884001)
        ·
          refine ⟨16542956737290819962163001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22057275649721093282884001 16542956737290819962163001)
          ·
            refine ⟨12407217552968114971622251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16542956737290819962163001 12407217552968114971622251)
            ·
              refine ⟨18610826329452172457433377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407217552968114971622251 18610826329452172457433377)
              ·
                refine ⟨13958119747089129343075033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18610826329452172457433377 13958119747089129343075033)
                ·
                  refine ⟨10468589810316847007306275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13958119747089129343075033 10468589810316847007306275)
                  ·
                    refine ⟨15702884715475270510959413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10468589810316847007306275 15702884715475270510959413)
                    ·
                      refine ⟨1472145442075806610402445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15702884715475270510959413 1472145442075806610402445)
                      ·
                        rfl

theorem cell23_2866993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2866993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866993 prefixEnd_2866993 := by exact prefixLift 2866993
  have htrace : WordTrace (prefixWord ++ tailWord_2866993) baseStart_2866993 baseEnd_2866993 := by
    simpa [prefixWord, tailWord_2866993, baseEnd_2866993] using wordTrace_append hprefix tailTrace_2866993
  have hstable : (prefixWord ++ tailWord_2866993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866993).length < 2 ^ (prefixWord ++ tailWord_2866993).sum := by decide
  have hdescent : baseEnd_2866993 < baseStart_2866993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866994 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_2866994 : Nat := 118140960795 + 2866994 * 2 ^ 59
def prefixEnd_2866994 : Nat := 4983230072969 + 3 ^ 40 * 2866994 * 2
def baseEnd_2866994 : Nat := 1472145955556461106489941

theorem tailTrace_2866994 : CollatzResearch.WordTrace tailWord_2866994 prefixEnd_2866994 1472145955556461106489941 := by
  unfold tailWord_2866994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26141965443844464109448009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69711907850251904291861357 26141965443844464109448009)
  ·
    refine ⟨19606474082883348082086007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26141965443844464109448009 19606474082883348082086007)
    ·
      refine ⟨29409711124325022123129011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19606474082883348082086007 29409711124325022123129011)
      ·
        refine ⟨44114566686487533184693517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29409711124325022123129011 44114566686487533184693517)
        ·
          refine ⟨16542962507432824944260069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44114566686487533184693517 16542962507432824944260069)
          ·
            refine ⟨3101805470143654677048763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16542962507432824944260069 3101805470143654677048763)
            ·
              refine ⟨4652708205215482015573145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101805470143654677048763 4652708205215482015573145)
              ·
                refine ⟨3489531153911611511679859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652708205215482015573145 3489531153911611511679859)
                ·
                  refine ⟨5234296730867417267519789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489531153911611511679859 5234296730867417267519789)
                  ·
                    refine ⟨1962861274075281475319921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5234296730867417267519789 1962861274075281475319921)
                    ·
                      refine ⟨1472145955556461106489941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962861274075281475319921 1472145955556461106489941)
                      ·
                        rfl

theorem cell23_2866994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_2866994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2866994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2866994 prefixEnd_2866994 := by exact prefixLift 2866994
  have htrace : WordTrace (prefixWord ++ tailWord_2866994) baseStart_2866994 baseEnd_2866994 := by
    simpa [prefixWord, tailWord_2866994, baseEnd_2866994] using wordTrace_append hprefix tailTrace_2866994
  have hstable : (prefixWord ++ tailWord_2866994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866994).length < 2 ^ (prefixWord ++ tailWord_2866994).sum := by decide
  have hdescent : baseEnd_2866994 < baseStart_2866994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867007 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 1, 4, 2]
def baseStart_2867007 : Nat := 118140960795 + 2867007 * 2 ^ 59
def prefixEnd_2867007 : Nat := 4983230072969 + 3 ^ 40 * 2867007 * 2
def baseEnd_2867007 : Nat := 1472152630804969555627381

theorem tailTrace_2867007 : CollatzResearch.WordTrace tailWord_2867007 prefixEnd_2867007 1472152630804969555627381 := by
  unfold tailWord_2867007
  simp only [CollatzResearch.WordTrace]
  refine ⟨104568335924330759658015275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69712223949553839772010183 104568335924330759658015275)
  ·
    refine ⟨156852503886496139487022913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104568335924330759658015275 156852503886496139487022913)
    ·
      refine ⟨117639377914872104615267185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156852503886496139487022913 117639377914872104615267185)
      ·
        refine ⟨88229533436154078461450389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117639377914872104615267185 88229533436154078461450389)
        ·
          refine ⟨4135759379819722427880487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88229533436154078461450389 4135759379819722427880487)
          ·
            refine ⟨6203639069729583641820731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135759379819722427880487 6203639069729583641820731)
            ·
              refine ⟨9305458604594375462731097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203639069729583641820731 9305458604594375462731097)
              ·
                refine ⟨6979093953445781597048323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9305458604594375462731097 6979093953445781597048323)
                ·
                  refine ⟨10468640930168672395572485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6979093953445781597048323 10468640930168672395572485)
                  ·
                    refine ⟨1962870174406626074169841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10468640930168672395572485 1962870174406626074169841)
                    ·
                      refine ⟨1472152630804969555627381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1962870174406626074169841 1472152630804969555627381)
                      ·
                        rfl

theorem cell23_2867007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_2867007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867007 prefixEnd_2867007 := by exact prefixLift 2867007
  have htrace : WordTrace (prefixWord ++ tailWord_2867007) baseStart_2867007 baseEnd_2867007 := by
    simpa [prefixWord, tailWord_2867007, baseEnd_2867007] using wordTrace_append hprefix tailTrace_2867007
  have hstable : (prefixWord ++ tailWord_2867007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867007).length < 2 ^ (prefixWord ++ tailWord_2867007).sum := by decide
  have hdescent : baseEnd_2867007 < baseStart_2867007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867040 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_2867040 : Nat := 118140960795 + 2867040 * 2 ^ 59
def prefixEnd_2867040 : Nat := 4983230072969 + 3 ^ 40 * 2867040 * 2
def baseEnd_2867040 : Nat := 1472169575666567926514729

theorem tailTrace_2867040 : CollatzResearch.WordTrace tailWord_2867040 prefixEnd_2867040 1472169575666567926514729 := by
  unfold tailWord_2867040
  simp only [CollatzResearch.WordTrace]
  refine ⟨52284769766605603146983287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69713026355474137529311049 52284769766605603146983287)
  ·
    refine ⟨78427154649908404720474931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52284769766605603146983287 78427154649908404720474931)
    ·
      refine ⟨117640731974862607080712397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78427154649908404720474931 117640731974862607080712397)
      ·
        refine ⟨44115274490573477655267149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117640731974862607080712397 44115274490573477655267149)
        ·
          refine ⟨16543227933965054120725181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44115274490573477655267149 16543227933965054120725181)
          ·
            refine ⟨6203710475236895295271943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16543227933965054120725181 6203710475236895295271943)
            ·
              refine ⟨9305565712855342942907915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203710475236895295271943 9305565712855342942907915)
              ·
                refine ⟨13958348569283014414361873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9305565712855342942907915 13958348569283014414361873)
                ·
                  refine ⟨10468761426962260810771405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13958348569283014414361873 10468761426962260810771405)
                  ·
                    refine ⟨3925785535110847804039277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10468761426962260810771405 3925785535110847804039277)
                    ·
                      refine ⟨1472169575666567926514729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3925785535110847804039277 1472169575666567926514729)
                      ·
                        rfl

theorem cell23_2867040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_2867040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867040 prefixEnd_2867040 := by exact prefixLift 2867040
  have htrace : WordTrace (prefixWord ++ tailWord_2867040) baseStart_2867040 baseEnd_2867040 := by
    simpa [prefixWord, tailWord_2867040, baseEnd_2867040] using wordTrace_append hprefix tailTrace_2867040
  have hstable : (prefixWord ++ tailWord_2867040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867040).length < 2 ^ (prefixWord ++ tailWord_2867040).sum := by decide
  have hdescent : baseEnd_2867040 < baseStart_2867040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867053 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2867053 : Nat := 118140960795 + 2867053 * 2 ^ 59
def prefixEnd_2867053 : Nat := 4983230072969 + 3 ^ 40 * 2867053 * 2
def baseEnd_2867053 : Nat := 1472176250915076375652169

theorem tailTrace_2867053 : CollatzResearch.WordTrace tailWord_2867053 prefixEnd_2867053 1472176250915076375652169 := by
  unfold tailWord_2867053
  simp only [CollatzResearch.WordTrace]
  refine ⟨104570013682164109514189813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69713342454776073009459875 104570013682164109514189813)
  ·
    refine ⟨9803438782702885266955295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104570013682164109514189813 9803438782702885266955295)
    ·
      refine ⟨14705158174054327900432943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9803438782702885266955295 14705158174054327900432943)
      ·
        refine ⟨22057737261081491850649415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14705158174054327900432943 22057737261081491850649415)
        ·
          refine ⟨33086605891622237775974123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22057737261081491850649415 33086605891622237775974123)
          ·
            refine ⟨49629908837433356663961185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33086605891622237775974123 49629908837433356663961185)
            ·
              refine ⟨37222431628075017497970889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49629908837433356663961185 37222431628075017497970889)
              ·
                refine ⟨27916823721056263123478167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37222431628075017497970889 27916823721056263123478167)
                ·
                  refine ⟨41875235581584394685217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27916823721056263123478167 41875235581584394685217251)
                  ·
                    refine ⟨62812853372376592027825877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41875235581584394685217251 62812853372376592027825877)
                    ·
                      refine ⟨1472176250915076375652169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62812853372376592027825877 1472176250915076375652169)
                      ·
                        rfl

theorem cell23_2867053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2867053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867053 prefixEnd_2867053 := by exact prefixLift 2867053
  have htrace : WordTrace (prefixWord ++ tailWord_2867053) baseStart_2867053 baseEnd_2867053 := by
    simpa [prefixWord, tailWord_2867053, baseEnd_2867053] using wordTrace_append hprefix tailTrace_2867053
  have hstable : (prefixWord ++ tailWord_2867053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867053).length < 2 ^ (prefixWord ++ tailWord_2867053).sum := by decide
  have hdescent : baseEnd_2867053 < baseStart_2867053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867093 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2867093 : Nat := 118140960795 + 2867093 * 2 ^ 59
def prefixEnd_2867093 : Nat := 4983230072969 + 3 ^ 40 * 2867093 * 2
def baseEnd_2867093 : Nat := 1472196790141256219151985

theorem tailTrace_2867093 : CollatzResearch.WordTrace tailWord_2867093 prefixEnd_2867093 1472196790141256219151985 := by
  unfold tailWord_2867093
  simp only [CollatzResearch.WordTrace]
  refine ⟨104571472602019196345645933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69714315068012797563763955 104571472602019196345645933)
  ·
    refine ⟨39214302225757198629617225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104571472602019196345645933 39214302225757198629617225)
    ·
      refine ⟨29410726669317898972212919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39214302225757198629617225 29410726669317898972212919)
      ·
        refine ⟨44116090003976848458319379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29410726669317898972212919 44116090003976848458319379)
        ·
          refine ⟨66174135005965272687479069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44116090003976848458319379 66174135005965272687479069)
          ·
            refine ⟨24815300627236977257804651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66174135005965272687479069 24815300627236977257804651)
            ·
              refine ⟨37222950940855465886706977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24815300627236977257804651 37222950940855465886706977)
              ·
                refine ⟨27917213205641599415030233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37222950940855465886706977 27917213205641599415030233)
                ·
                  refine ⟨20937909904231199561272675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27917213205641599415030233 20937909904231199561272675)
                  ·
                    refine ⟨31406864856346799341909013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20937909904231199561272675 31406864856346799341909013)
                    ·
                      refine ⟨1472196790141256219151985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31406864856346799341909013 1472196790141256219151985)
                      ·
                        rfl

theorem cell23_2867093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2867093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867093 prefixEnd_2867093 := by exact prefixLift 2867093
  have htrace : WordTrace (prefixWord ++ tailWord_2867093) baseStart_2867093 baseEnd_2867093 := by
    simpa [prefixWord, tailWord_2867093, baseEnd_2867093] using wordTrace_append hprefix tailTrace_2867093
  have hstable : (prefixWord ++ tailWord_2867093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867093).length < 2 ^ (prefixWord ++ tailWord_2867093).sum := by decide
  have hdescent : baseEnd_2867093 < baseStart_2867093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867143 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2867143 : Nat := 118140960795 + 2867143 * 2 ^ 59
def prefixEnd_2867143 : Nat := 4983230072969 + 3 ^ 40 * 2867143 * 2
def baseEnd_2867143 : Nat := 1472222464173981023526755

theorem tailTrace_2867143 : CollatzResearch.WordTrace tailWord_2867143 prefixEnd_2867143 1472222464173981023526755 := by
  unfold tailWord_2867143
  simp only [CollatzResearch.WordTrace]
  refine ⟨104573296251838054884966083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69715530834558703256644055 104573296251838054884966083)
  ·
    refine ⟨156859944377757082327449125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104573296251838054884966083 156859944377757082327449125)
    ·
      refine ⟨29411239570829452936396711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156859944377757082327449125 29411239570829452936396711)
      ·
        refine ⟨44116859356244179404595067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411239570829452936396711 44116859356244179404595067)
        ·
          refine ⟨66175289034366269106892601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44116859356244179404595067 66175289034366269106892601)
          ·
            refine ⟨49631466775774701830169451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66175289034366269106892601 49631466775774701830169451)
            ·
              refine ⟨74447200163662052745254177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49631466775774701830169451 74447200163662052745254177)
              ·
                refine ⟨55835400122746539558940633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74447200163662052745254177 55835400122746539558940633)
                ·
                  refine ⟨41876550092059904669205475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55835400122746539558940633 41876550092059904669205475)
                  ·
                    refine ⟨62814825138089857003808213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41876550092059904669205475 62814825138089857003808213)
                    ·
                      refine ⟨1472222464173981023526755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62814825138089857003808213 1472222464173981023526755)
                      ·
                        rfl

theorem cell23_2867143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2867143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867143 prefixEnd_2867143 := by exact prefixLift 2867143
  have htrace : WordTrace (prefixWord ++ tailWord_2867143) baseStart_2867143 baseEnd_2867143 := by
    simpa [prefixWord, tailWord_2867143, baseEnd_2867143] using wordTrace_append hprefix tailTrace_2867143
  have hstable : (prefixWord ++ tailWord_2867143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867143).length < 2 ^ (prefixWord ++ tailWord_2867143).sum := by decide
  have hdescent : baseEnd_2867143 < baseStart_2867143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867150 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_2867150 : Nat := 118140960795 + 2867150 * 2 ^ 59
def prefixEnd_2867150 : Nat := 4983230072969 + 3 ^ 40 * 2867150 * 2
def baseEnd_2867150 : Nat := 490742019512854165379741

theorem tailTrace_2867150 : CollatzResearch.WordTrace tailWord_2867150 prefixEnd_2867150 490742019512854165379741 := by
  unfold tailWord_2867150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071693945351586885058863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69715701041875130053647269 13071693945351586885058863)
  ·
    refine ⟨19607540918027380327588295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13071693945351586885058863 19607540918027380327588295)
    ·
      refine ⟨29411311377041070491382443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19607540918027380327588295 29411311377041070491382443)
      ·
        refine ⟨44116967065561605737073665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411311377041070491382443 44116967065561605737073665)
        ·
          refine ⟨33087725299171204302805249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44116967065561605737073665 33087725299171204302805249)
          ·
            refine ⟨24815793974378403227103937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33087725299171204302805249 24815793974378403227103937)
            ·
              refine ⟨18611845480783802420327953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24815793974378403227103937 18611845480783802420327953)
              ·
                refine ⟨13958884110587851815245965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18611845480783802420327953 13958884110587851815245965)
                ·
                  refine ⟨5234581541470444430717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13958884110587851815245965 5234581541470444430717237)
                  ·
                    refine ⟨490742019512854165379741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5234581541470444430717237 490742019512854165379741)
                    ·
                      rfl

theorem cell23_2867150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_2867150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867150 prefixEnd_2867150 := by exact prefixLift 2867150
  have htrace : WordTrace (prefixWord ++ tailWord_2867150) baseStart_2867150 baseEnd_2867150 := by
    simpa [prefixWord, tailWord_2867150, baseEnd_2867150] using wordTrace_append hprefix tailTrace_2867150
  have hstable : (prefixWord ++ tailWord_2867150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867150).length < 2 ^ (prefixWord ++ tailWord_2867150).sum := by decide
  have hdescent : baseEnd_2867150 < baseStart_2867150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867167 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 1, 5]
def baseStart_2867167 : Nat := 118140960795 + 2867167 * 2 ^ 59
def prefixEnd_2867167 : Nat := 4983230072969 + 3 ^ 40 * 2867167 * 2
def baseEnd_2867167 : Nat := 490744929236562976542215

theorem tailTrace_2867167 : CollatzResearch.WordTrace tailWord_2867167 prefixEnd_2867167 490744929236562976542215 := by
  unfold tailWord_2867167
  simp only [CollatzResearch.WordTrace]
  refine ⟨104574171603751106983839755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69716114402500737989226503 104574171603751106983839755)
  ·
    refine ⟨156861257405626660475759633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104574171603751106983839755 156861257405626660475759633)
    ·
      refine ⟨117645943054219995356819725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156861257405626660475759633 117645943054219995356819725)
      ·
        refine ⟨44117228645332498258807397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117645943054219995356819725 44117228645332498258807397)
        ·
          refine ⟨8271980370999843423526387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44117228645332498258807397 8271980370999843423526387)
          ·
            refine ⟨12407970556499765135289581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271980370999843423526387 12407970556499765135289581)
            ·
              refine ⟨4652988958687411925733593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12407970556499765135289581 4652988958687411925733593)
              ·
                refine ⟨3489741719015558944300195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652988958687411925733593 3489741719015558944300195)
                ·
                  refine ⟨5234612578523338416450293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489741719015558944300195 5234612578523338416450293)
                  ·
                    refine ⟨490744929236562976542215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5234612578523338416450293 490744929236562976542215)
                    ·
                      rfl

theorem cell23_2867167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_2867167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867167 prefixEnd_2867167 := by exact prefixLift 2867167
  have htrace : WordTrace (prefixWord ++ tailWord_2867167) baseStart_2867167 baseEnd_2867167 := by
    simpa [prefixWord, tailWord_2867167, baseEnd_2867167] using wordTrace_append hprefix tailTrace_2867167
  have hstable : (prefixWord ++ tailWord_2867167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867167).length < 2 ^ (prefixWord ++ tailWord_2867167).sum := by decide
  have hdescent : baseEnd_2867167 < baseStart_2867167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867180 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_2867180 : Nat := 118140960795 + 2867180 * 2 ^ 59
def prefixEnd_2867180 : Nat := 4983230072969 + 3 ^ 40 * 2867180 * 2
def baseEnd_2867180 : Nat := 490747154319399126254695

theorem tailTrace_2867180 : CollatzResearch.WordTrace tailWord_2867180 prefixEnd_2867180 490747154319399126254695 := by
  unfold tailWord_2867180
  simp only [CollatzResearch.WordTrace]
  refine ⟨52287322876352005102031497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69716430501802673469375329 52287322876352005102031497)
  ·
    refine ⟨39215492157264003826523623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52287322876352005102031497 39215492157264003826523623)
    ·
      refine ⟨58823238235896005739785435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39215492157264003826523623 58823238235896005739785435)
      ·
        refine ⟨88234857353844008609678153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58823238235896005739785435 88234857353844008609678153)
        ·
          refine ⟨66176143015383006457258615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88234857353844008609678153 66176143015383006457258615)
          ·
            refine ⟨99264214523074509685887923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66176143015383006457258615 99264214523074509685887923)
            ·
              refine ⟨148896321784611764528831885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99264214523074509685887923 148896321784611764528831885)
              ·
                refine ⟨55836120669229411698311957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148896321784611764528831885 55836120669229411698311957)
                ·
                  refine ⟨2617318156370128673358373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55836120669229411698311957 2617318156370128673358373)
                  ·
                    refine ⟨490747154319399126254695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2617318156370128673358373 490747154319399126254695)
                    ·
                      rfl

theorem cell23_2867180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_2867180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867180 prefixEnd_2867180 := by exact prefixLift 2867180
  have htrace : WordTrace (prefixWord ++ tailWord_2867180) baseStart_2867180 baseEnd_2867180 := by
    simpa [prefixWord, tailWord_2867180, baseEnd_2867180] using wordTrace_append hprefix tailTrace_2867180
  have hstable : (prefixWord ++ tailWord_2867180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867180).length < 2 ^ (prefixWord ++ tailWord_2867180).sum := by decide
  have hdescent : baseEnd_2867180 < baseStart_2867180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867193 : List Nat := [1, 2, 1, 3, 1, 15]
def baseStart_2867193 : Nat := 118140960795 + 2867193 * 2 ^ 59
def prefixEnd_2867193 : Nat := 4983230072969 + 3 ^ 40 * 2867193 * 2
def baseEnd_2867193 : Nat := 6058634313607842913175

theorem tailTrace_2867193 : CollatzResearch.WordTrace tailWord_2867193 prefixEnd_2867193 6058634313607842913175 := by
  unfold tailWord_2867193
  simp only [CollatzResearch.WordTrace]
  refine ⟨104575119901656913424286233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69716746601104608949524155 104575119901656913424286233)
  ·
    refine ⟨78431339926242685068214675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104575119901656913424286233 78431339926242685068214675)
    ·
      refine ⟨117647009889364027602322013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78431339926242685068214675 117647009889364027602322013)
      ·
        refine ⟨44117628708511510350870755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117647009889364027602322013 44117628708511510350870755)
        ·
          refine ⟨66176443062767265526306133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44117628708511510350870755 66176443062767265526306133)
          ·
            refine ⟨6058634313607842913175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 66176443062767265526306133 6058634313607842913175)
            ·
              rfl

theorem cell23_2867193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 15].length) (baseStart_2867193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867193 prefixEnd_2867193 := by exact prefixLift 2867193
  have htrace : WordTrace (prefixWord ++ tailWord_2867193) baseStart_2867193 baseEnd_2867193 := by
    simpa [prefixWord, tailWord_2867193, baseEnd_2867193] using wordTrace_append hprefix tailTrace_2867193
  have hstable : (prefixWord ++ tailWord_2867193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867193).length < 2 ^ (prefixWord ++ tailWord_2867193).sum := by decide
  have hdescent : baseEnd_2867193 < baseStart_2867193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867197 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2867197 : Nat := 118140960795 + 2867197 * 2 ^ 59
def prefixEnd_2867197 : Nat := 4983230072969 + 3 ^ 40 * 2867197 * 2
def baseEnd_2867197 : Nat := 490750064043107937417169

theorem tailTrace_2867197 : CollatzResearch.WordTrace tailWord_2867197 prefixEnd_2867197 490750064043107937417169 := by
  unfold tailWord_2867197
  simp only [CollatzResearch.WordTrace]
  refine ⟨104575265793642422107431845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69716843862428281404954563 104575265793642422107431845)
  ·
    refine ⟨19607862336307954145143471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104575265793642422107431845 19607862336307954145143471)
    ·
      refine ⟨29411793504461931217715207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19607862336307954145143471 29411793504461931217715207)
      ·
        refine ⟨44117690256692896826572811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411793504461931217715207 44117690256692896826572811)
        ·
          refine ⟨66176535385039345239859217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44117690256692896826572811 66176535385039345239859217)
          ·
            refine ⟨49632401538779508929894413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66176535385039345239859217 49632401538779508929894413)
            ·
              refine ⟨18612150577042315848710405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49632401538779508929894413 18612150577042315848710405)
              ·
                refine ⟨3489778233195434221633201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18612150577042315848710405 3489778233195434221633201)
                ·
                  refine ⟨2617333674896575666224901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489778233195434221633201 2617333674896575666224901)
                  ·
                    refine ⟨490750064043107937417169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2617333674896575666224901 490750064043107937417169)
                    ·
                      rfl

theorem cell23_2867197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2867197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867197 prefixEnd_2867197 := by exact prefixLift 2867197
  have htrace : WordTrace (prefixWord ++ tailWord_2867197) baseStart_2867197 baseEnd_2867197 := by
    simpa [prefixWord, tailWord_2867197, baseEnd_2867197] using wordTrace_append hprefix tailTrace_2867197
  have hstable : (prefixWord ++ tailWord_2867197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867197).length < 2 ^ (prefixWord ++ tailWord_2867197).sum := by decide
  have hdescent : baseEnd_2867197 < baseStart_2867197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867198 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2867198 : Nat := 118140960795 + 2867198 * 2 ^ 59
def prefixEnd_2867198 : Nat := 4983230072969 + 3 ^ 40 * 2867198 * 2
def baseEnd_2867198 : Nat := 1472250705609978308339003

theorem tailTrace_2867198 : CollatzResearch.WordTrace tailWord_2867198 prefixEnd_2867198 1472250705609978308339003 := by
  unfold tailWord_2867198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071912783329849909777281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69716868177759199518812165 13071912783329849909777281)
  ·
    refine ⟨9803934587497387432332961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13071912783329849909777281 9803934587497387432332961)
    ·
      refine ⟨7352950940623040574249721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9803934587497387432332961 7352950940623040574249721)
      ·
        refine ⟨5514713205467280430687291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7352950940623040574249721 5514713205467280430687291)
        ·
          refine ⟨8272069808200920646030937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514713205467280430687291 8272069808200920646030937)
          ·
            refine ⟨6204052356150690484523203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8272069808200920646030937 6204052356150690484523203)
            ·
              refine ⟨9306078534226035726784805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204052356150690484523203 9306078534226035726784805)
              ·
                refine ⟨1744889725167381698772151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9306078534226035726784805 1744889725167381698772151)
                ·
                  refine ⟨2617334587751072548158227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744889725167381698772151 2617334587751072548158227)
                  ·
                    refine ⟨3926001881626608822237341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617334587751072548158227 3926001881626608822237341)
                    ·
                      refine ⟨1472250705609978308339003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926001881626608822237341 1472250705609978308339003)
                      ·
                        rfl

theorem cell23_2867198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2867198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867198 prefixEnd_2867198 := by exact prefixLift 2867198
  have htrace : WordTrace (prefixWord ++ tailWord_2867198) baseStart_2867198 baseEnd_2867198 := by
    simpa [prefixWord, tailWord_2867198, baseEnd_2867198] using wordTrace_append hprefix tailTrace_2867198
  have hstable : (prefixWord ++ tailWord_2867198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867198).length < 2 ^ (prefixWord ++ tailWord_2867198).sum := by decide
  have hdescent : baseEnd_2867198 < baseStart_2867198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867207 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2867207 : Nat := 118140960795 + 2867207 * 2 ^ 59
def prefixEnd_2867207 : Nat := 4983230072969 + 3 ^ 40 * 2867207 * 2
def baseEnd_2867207 : Nat := 1472255326935868773126461

theorem tailTrace_2867207 : CollatzResearch.WordTrace tailWord_2867207 prefixEnd_2867207 1472255326935868773126461 := by
  unfold tailWord_2867207
  simp only [CollatzResearch.WordTrace]
  refine ⟨104575630523606193815295875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69717087015737462543530583 104575630523606193815295875)
  ·
    refine ⟨156863445785409290722943813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104575630523606193815295875 156863445785409290722943813)
    ·
      refine ⟨29411896084764242010551965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156863445785409290722943813 29411896084764242010551965)
      ·
        refine ⟨11029461031786590753956987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29411896084764242010551965 11029461031786590753956987)
        ·
          refine ⟨16544191547679886130935481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11029461031786590753956987 16544191547679886130935481)
          ·
            refine ⟨12408143660759914598201611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16544191547679886130935481 12408143660759914598201611)
            ·
              refine ⟨18612215491139871897302417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12408143660759914598201611 18612215491139871897302417)
              ·
                refine ⟨13959161618354903922976813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18612215491139871897302417 13959161618354903922976813)
                ·
                  refine ⟨5234685606883088971116305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13959161618354903922976813 5234685606883088971116305)
                  ·
                    refine ⟨3926014205162316728337229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234685606883088971116305 3926014205162316728337229)
                    ·
                      refine ⟨1472255326935868773126461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926014205162316728337229 1472255326935868773126461)
                      ·
                        rfl

theorem cell23_2867207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2867207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867207 prefixEnd_2867207 := by exact prefixLift 2867207
  have htrace : WordTrace (prefixWord ++ tailWord_2867207) baseStart_2867207 baseEnd_2867207 := by
    simpa [prefixWord, tailWord_2867207, baseEnd_2867207] using wordTrace_append hprefix tailTrace_2867207
  have hstable : (prefixWord ++ tailWord_2867207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867207).length < 2 ^ (prefixWord ++ tailWord_2867207).sum := by decide
  have hdescent : baseEnd_2867207 < baseStart_2867207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867221 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_2867221 : Nat := 118140960795 + 2867221 * 2 ^ 59
def prefixEnd_2867221 : Nat := 4983230072969 + 3 ^ 40 * 2867221 * 2
def baseEnd_2867221 : Nat := 1472262515665031718351397

theorem tailTrace_2867221 : CollatzResearch.WordTrace tailWord_2867221 prefixEnd_2867221 1472262515665031718351397 := by
  unfold tailWord_2867221
  simp only [CollatzResearch.WordTrace]
  refine ⟨104576141145555474206305517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69717427430370316137537011 104576141145555474206305517)
  ·
    refine ⟨39216052929583302827364569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104576141145555474206305517 39216052929583302827364569)
    ·
      refine ⟨29412039697187477120523427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39216052929583302827364569 29412039697187477120523427)
      ·
        refine ⟨44118059545781215680785141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29412039697187477120523427 44118059545781215680785141)
        ·
          refine ⟨4136068082416988970073607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44118059545781215680785141 4136068082416988970073607)
          ·
            refine ⟨6204102123625483455110411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136068082416988970073607 6204102123625483455110411)
            ·
              refine ⟨9306153185438225182665617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204102123625483455110411 9306153185438225182665617)
              ·
                refine ⟨6979614889078668886999213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9306153185438225182665617 6979614889078668886999213)
                ·
                  refine ⟨2617355583404500832624705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6979614889078668886999213 2617355583404500832624705)
                  ·
                    refine ⟨1963016687553375624468529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2617355583404500832624705 1963016687553375624468529)
                    ·
                      refine ⟨1472262515665031718351397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963016687553375624468529 1472262515665031718351397)
                      ·
                        rfl

theorem cell23_2867221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_2867221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867221 prefixEnd_2867221 := by exact prefixLift 2867221
  have htrace : WordTrace (prefixWord ++ tailWord_2867221) baseStart_2867221 baseEnd_2867221 := by
    simpa [prefixWord, tailWord_2867221, baseEnd_2867221] using wordTrace_append hprefix tailTrace_2867221
  have hstable : (prefixWord ++ tailWord_2867221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867221).length < 2 ^ (prefixWord ++ tailWord_2867221).sum := by decide
  have hdescent : baseEnd_2867221 < baseStart_2867221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867237 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2867237 : Nat := 118140960795 + 2867237 * 2 ^ 59
def prefixEnd_2867237 : Nat := 4983230072969 + 3 ^ 40 * 2867237 * 2
def baseEnd_2867237 : Nat := 1472270731355503655751323

theorem tailTrace_2867237 : CollatzResearch.WordTrace tailWord_2867237 prefixEnd_2867237 1472270731355503655751323 := by
  unfold tailWord_2867237
  simp only [CollatzResearch.WordTrace]
  refine ⟨104576724713497508938887965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69717816475665005959258643 104576724713497508938887965)
  ·
    refine ⟨39216271767561565852082987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104576724713497508938887965 39216271767561565852082987)
    ·
      refine ⟨58824407651342348778124481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39216271767561565852082987 58824407651342348778124481)
      ·
        refine ⟨44118305738506761583593361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58824407651342348778124481 44118305738506761583593361)
        ·
          refine ⟨33088729303880071187695021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44118305738506761583593361 33088729303880071187695021)
          ·
            refine ⟨12408273488955026695385633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33088729303880071187695021 12408273488955026695385633)
            ·
              refine ⟨9306205116716270021539225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12408273488955026695385633 9306205116716270021539225)
              ·
                refine ⟨6979653837537202516154419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9306205116716270021539225 6979653837537202516154419)
                ·
                  refine ⟨10469480756305803774231629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6979653837537202516154419 10469480756305803774231629)
                  ·
                    refine ⟨3926055283614676415336861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10469480756305803774231629 3926055283614676415336861)
                    ·
                      refine ⟨1472270731355503655751323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926055283614676415336861 1472270731355503655751323)
                      ·
                        rfl

theorem cell23_2867237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2867237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867237 prefixEnd_2867237 := by exact prefixLift 2867237
  have htrace : WordTrace (prefixWord ++ tailWord_2867237) baseStart_2867237 baseEnd_2867237 := by
    simpa [prefixWord, tailWord_2867237, baseEnd_2867237] using wordTrace_append hprefix tailTrace_2867237
  have hstable : (prefixWord ++ tailWord_2867237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867237).length < 2 ^ (prefixWord ++ tailWord_2867237).sum := by decide
  have hdescent : baseEnd_2867237 < baseStart_2867237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867247 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 5, 3, 2]
def baseStart_2867247 : Nat := 118140960795 + 2867247 * 2 ^ 59
def prefixEnd_2867247 : Nat := 4983230072969 + 3 ^ 40 * 2867247 * 2
def baseEnd_2867247 : Nat := 1472275866162048616626277

theorem tailTrace_2867247 : CollatzResearch.WordTrace tailWord_2867247 prefixEnd_2867247 1472275866162048616626277 := by
  unfold tailWord_2867247
  simp only [CollatzResearch.WordTrace]
  refine ⟨104577089443461280646751995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69718059628974187097834663 104577089443461280646751995)
  ·
    refine ⟨156865634165191920970127993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104577089443461280646751995 156865634165191920970127993)
    ·
      refine ⟨117649225623893940727595995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156865634165191920970127993 117649225623893940727595995)
      ·
        refine ⟨176473838435840911091393993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117649225623893940727595995 176473838435840911091393993)
        ·
          refine ⟨132355378826880683318545495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176473838435840911091393993 132355378826880683318545495)
          ·
            refine ⟨198533068240321024977818243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132355378826880683318545495 198533068240321024977818243)
            ·
              refine ⟨297799602360481537466727365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198533068240321024977818243 297799602360481537466727365)
              ·
                refine ⟨55837425442590288275011381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297799602360481537466727365 55837425442590288275011381)
                ·
                  refine ⟨5234758635242839525782317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55837425442590288275011381 5234758635242839525782317)
                  ·
                    refine ⟨1963034488216064822168369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5234758635242839525782317 1963034488216064822168369)
                    ·
                      refine ⟨1472275866162048616626277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963034488216064822168369 1472275866162048616626277)
                      ·
                        rfl

theorem cell23_2867247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3, 2].length) (baseStart_2867247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867247 prefixEnd_2867247 := by exact prefixLift 2867247
  have htrace : WordTrace (prefixWord ++ tailWord_2867247) baseStart_2867247 baseEnd_2867247 := by
    simpa [prefixWord, tailWord_2867247, baseEnd_2867247] using wordTrace_append hprefix tailTrace_2867247
  have hstable : (prefixWord ++ tailWord_2867247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867247).length < 2 ^ (prefixWord ++ tailWord_2867247).sum := by decide
  have hdescent : baseEnd_2867247 < baseStart_2867247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867271 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_2867271 : Nat := 118140960795 + 2867271 * 2 ^ 59
def prefixEnd_2867271 : Nat := 4983230072969 + 3 ^ 40 * 2867271 * 2
def baseEnd_2867271 : Nat := 1472288189697756522726167

theorem tailTrace_2867271 : CollatzResearch.WordTrace tailWord_2867271 prefixEnd_2867271 1472288189697756522726167 := by
  unfold tailWord_2867271
  simp only [CollatzResearch.WordTrace]
  refine ⟨104577964795374332745625667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69718643196916221830417111 104577964795374332745625667)
  ·
    refine ⟨156866947193061499118438501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104577964795374332745625667 156866947193061499118438501)
    ·
      refine ⟨29412552598699031084707219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156866947193061499118438501 29412552598699031084707219)
      ·
        refine ⟨44118828898048546627060829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29412552598699031084707219 44118828898048546627060829)
        ·
          refine ⟨16544560836768204985147811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44118828898048546627060829 16544560836768204985147811)
          ·
            refine ⟨24816841255152307477721717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16544560836768204985147811 24816841255152307477721717)
            ·
              refine ⟨2326578867670528826036411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24816841255152307477721717 2326578867670528826036411)
              ·
                refine ⟨3489868301505793239054617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326578867670528826036411 3489868301505793239054617)
                ·
                  refine ⟨2617401226129344929290963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489868301505793239054617 2617401226129344929290963)
                  ·
                    refine ⟨3926101839194017393936445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617401226129344929290963 3926101839194017393936445)
                    ·
                      refine ⟨1472288189697756522726167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926101839194017393936445 1472288189697756522726167)
                      ·
                        rfl

theorem cell23_2867271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_2867271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867271 prefixEnd_2867271 := by exact prefixLift 2867271
  have htrace : WordTrace (prefixWord ++ tailWord_2867271) baseStart_2867271 baseEnd_2867271 := by
    simpa [prefixWord, tailWord_2867271, baseEnd_2867271] using wordTrace_append hprefix tailTrace_2867271
  have hstable : (prefixWord ++ tailWord_2867271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867271).length < 2 ^ (prefixWord ++ tailWord_2867271).sum := by decide
  have hdescent : baseEnd_2867271 < baseStart_2867271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867300 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 9]
def baseStart_2867300 : Nat := 118140960795 + 2867300 * 2 ^ 59
def prefixEnd_2867300 : Nat := 4983230072969 + 3 ^ 40 * 2867300 * 2
def baseEnd_2867300 : Nat := 163589231181859656584837

theorem tailTrace_2867300 : CollatzResearch.WordTrace tailWord_2867300 prefixEnd_2867300 163589231181859656584837 := by
  unfold tailWord_2867300
  simp only [CollatzResearch.WordTrace]
  refine ⟨52289511256134635349215677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69719348341512847132287569 52289511256134635349215677)
  ·
    refine ⟨19608566721050488255955879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52289511256134635349215677 19608566721050488255955879)
    ·
      refine ⟨29412850081575732383933819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19608566721050488255955879 29412850081575732383933819)
      ·
        refine ⟨44119275122363598575900729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29412850081575732383933819 44119275122363598575900729)
        ·
          refine ⟨33089456341772698931925547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44119275122363598575900729 33089456341772698931925547)
          ·
            refine ⟨49634184512659048397888321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33089456341772698931925547 49634184512659048397888321)
            ·
              refine ⟨37225638384494286298416241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49634184512659048397888321 37225638384494286298416241)
              ·
                refine ⟨27919228788370714723812181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37225638384494286298416241 27919228788370714723812181)
                ·
                  refine ⟨163589231181859656584837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27919228788370714723812181 163589231181859656584837)
                  ·
                    rfl

theorem cell23_2867300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_2867300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867300 prefixEnd_2867300 := by exact prefixLift 2867300
  have htrace : WordTrace (prefixWord ++ tailWord_2867300) baseStart_2867300 baseEnd_2867300 := by
    simpa [prefixWord, tailWord_2867300, baseEnd_2867300] using wordTrace_append hprefix tailTrace_2867300
  have hstable : (prefixWord ++ tailWord_2867300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867300).length < 2 ^ (prefixWord ++ tailWord_2867300).sum := by decide
  have hdescent : baseEnd_2867300 < baseStart_2867300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867357 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2867357 : Nat := 118140960795 + 2867357 * 2 ^ 59
def prefixEnd_2867357 : Nat := 4983230072969 + 3 ^ 40 * 2867357 * 2
def baseEnd_2867357 : Nat := 1472332349034043186250771

theorem tailTrace_2867357 : CollatzResearch.WordTrace tailWord_2867357 prefixEnd_2867357 1472332349034043186250771 := by
  unfold tailWord_2867357
  simp only [CollatzResearch.WordTrace]
  refine ⟨104581101473062769433256325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69720734315375179622170883 104581101473062769433256325)
  ·
    refine ⟨19608956526199269268735561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104581101473062769433256325 19608956526199269268735561)
    ·
      refine ⟨14706717394649451951551671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19608956526199269268735561 14706717394649451951551671)
      ·
        refine ⟨22060076091974177927327507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14706717394649451951551671 22060076091974177927327507)
        ·
          refine ⟨33090114137961266890991261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22060076091974177927327507 33090114137961266890991261)
          ·
            refine ⟨12408792801735475084121723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33090114137961266890991261 12408792801735475084121723)
            ·
              refine ⟨18613189202603212626182585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12408792801735475084121723 18613189202603212626182585)
              ·
                refine ⟨13959891901952409469636939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18613189202603212626182585 13959891901952409469636939)
                ·
                  refine ⟨20939837852928614204455409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13959891901952409469636939 20939837852928614204455409)
                  ·
                    refine ⟨15704878389696460653341557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20939837852928614204455409 15704878389696460653341557)
                    ·
                      refine ⟨1472332349034043186250771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15704878389696460653341557 1472332349034043186250771)
                      ·
                        rfl

theorem cell23_2867357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2867357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867357 prefixEnd_2867357 := by exact prefixLift 2867357
  have htrace : WordTrace (prefixWord ++ tailWord_2867357) baseStart_2867357 baseEnd_2867357 := by
    simpa [prefixWord, tailWord_2867357, baseEnd_2867357] using wordTrace_append hprefix tailTrace_2867357
  have hstable : (prefixWord ++ tailWord_2867357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867357).length < 2 ^ (prefixWord ++ tailWord_2867357).sum := by decide
  have hdescent : baseEnd_2867357 < baseStart_2867357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867384 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_2867384 : Nat := 118140960795 + 2867384 * 2 ^ 59
def prefixEnd_2867384 : Nat := 4983230072969 + 3 ^ 40 * 2867384 * 2
def baseEnd_2867384 : Nat := 1472346213011714580613147

theorem tailTrace_2867384 : CollatzResearch.WordTrace tailWord_2867384 prefixEnd_2867384 1472346213011714580613147 := by
  unfold tailWord_2867384
  simp only [CollatzResearch.WordTrace]
  refine ⟨52291043121982476522244603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69721390829309968696326137 52291043121982476522244603)
  ·
    refine ⟨78436564682973714783366905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52291043121982476522244603 78436564682973714783366905)
    ·
      refine ⟨58827423512230286087525179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78436564682973714783366905 58827423512230286087525179)
      ·
        refine ⟨88241135268345429131287769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58827423512230286087525179 88241135268345429131287769)
        ·
          refine ⟨66180851451259071848465827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88241135268345429131287769 66180851451259071848465827)
          ·
            refine ⟨99271277176888607772698741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66180851451259071848465827 99271277176888607772698741)
            ·
              refine ⟨9306682235333306978690507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99271277176888607772698741 9306682235333306978690507)
              ·
                refine ⟨13960023352999960468035761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306682235333306978690507 13960023352999960468035761)
                ·
                  refine ⟨10470017514749970351026821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13960023352999960468035761 10470017514749970351026821)
                  ·
                    refine ⟨1963128284015619440817529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10470017514749970351026821 1963128284015619440817529)
                    ·
                      refine ⟨1472346213011714580613147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963128284015619440817529 1472346213011714580613147)
                      ·
                        rfl

theorem cell23_2867384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_2867384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867384 prefixEnd_2867384 := by exact prefixLift 2867384
  have htrace : WordTrace (prefixWord ++ tailWord_2867384) baseStart_2867384 baseEnd_2867384 := by
    simpa [prefixWord, tailWord_2867384, baseEnd_2867384] using wordTrace_append hprefix tailTrace_2867384
  have hstable : (prefixWord ++ tailWord_2867384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867384).length < 2 ^ (prefixWord ++ tailWord_2867384).sum := by decide
  have hdescent : baseEnd_2867384 < baseStart_2867384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867387 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3]
def baseStart_2867387 : Nat := 118140960795 + 2867387 * 2 ^ 59
def prefixEnd_2867387 : Nat := 4983230072969 + 3 ^ 40 * 2867387 * 2
def baseEnd_2867387 : Nat := 1472347753453678068875633

theorem tailTrace_2867387 : CollatzResearch.WordTrace tailWord_2867387 prefixEnd_2867387 1472347753453678068875633 := by
  unfold tailWord_2867387
  simp only [CollatzResearch.WordTrace]
  refine ⟨104582195662954084556848415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69721463775302723037898943 104582195662954084556848415)
  ·
    refine ⟨156873293494431126835272623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104582195662954084556848415 156873293494431126835272623)
    ·
      refine ⟨235309940241646690252908935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156873293494431126835272623 235309940241646690252908935)
      ·
        refine ⟨352964910362470035379363403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235309940241646690252908935 352964910362470035379363403)
        ·
          refine ⟨529447365543705053069045105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352964910362470035379363403 529447365543705053069045105)
          ·
            refine ⟨397085524157778789801783829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529447365543705053069045105 397085524157778789801783829)
            ·
              refine ⟨18613383944895880771958617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 397085524157778789801783829 18613383944895880771958617)
              ·
                refine ⟨13960037958671910578968963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18613383944895880771958617 13960037958671910578968963)
                ·
                  refine ⟨20940056938007865868453445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13960037958671910578968963 20940056938007865868453445)
                  ·
                    refine ⟨3926260675876474850335021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20940056938007865868453445 3926260675876474850335021)
                    ·
                      refine ⟨1472347753453678068875633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926260675876474850335021 1472347753453678068875633)
                      ·
                        rfl

theorem cell23_2867387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3].length) (baseStart_2867387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867387 prefixEnd_2867387 := by exact prefixLift 2867387
  have htrace : WordTrace (prefixWord ++ tailWord_2867387) baseStart_2867387 baseEnd_2867387 := by
    simpa [prefixWord, tailWord_2867387, baseEnd_2867387] using wordTrace_append hprefix tailTrace_2867387
  have hstable : (prefixWord ++ tailWord_2867387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867387).length < 2 ^ (prefixWord ++ tailWord_2867387).sum := by decide
  have hdescent : baseEnd_2867387 < baseStart_2867387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867467 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 3, 6]
def baseStart_2867467 : Nat := 118140960795 + 2867467 * 2 ^ 59
def prefixEnd_2867467 : Nat := 4983230072969 + 3 ^ 40 * 2867467 * 2
def baseEnd_2867467 : Nat := 490796277302012585291755

theorem tailTrace_2867467 : CollatzResearch.WordTrace tailWord_2867467 prefixEnd_2867467 490796277302012585291755 := by
  unfold tailWord_2867467
  simp only [CollatzResearch.WordTrace]
  refine ⟨104585113502664258219760655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69723409001776172146507103 104585113502664258219760655)
  ·
    refine ⟨156877670253996387329640983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104585113502664258219760655 156877670253996387329640983)
    ·
      refine ⟨235316505380994580994461475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156877670253996387329640983 235316505380994580994461475)
      ·
        refine ⟨352974758071491871491692213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235316505380994580994461475 352974758071491871491692213)
        ·
          refine ⟨33091383569202362952346145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352974758071491871491692213 33091383569202362952346145)
          ·
            refine ⟨24818537676901772214259609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33091383569202362952346145 24818537676901772214259609)
            ·
              refine ⟨18613903257676329160694707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24818537676901772214259609 18613903257676329160694707)
              ·
                refine ⟨27920854886514493741042061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18613903257676329160694707 27920854886514493741042061)
                ·
                  refine ⟨10470320582442935152890773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27920854886514493741042061 10470320582442935152890773)
                  ·
                    refine ⟨490796277302012585291755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10470320582442935152890773 490796277302012585291755)
                    ·
                      rfl

theorem cell23_2867467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_2867467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867467 prefixEnd_2867467 := by exact prefixLift 2867467
  have htrace : WordTrace (prefixWord ++ tailWord_2867467) baseStart_2867467 baseEnd_2867467 := by
    simpa [prefixWord, tailWord_2867467, baseEnd_2867467] using wordTrace_append hprefix tailTrace_2867467
  have hstable : (prefixWord ++ tailWord_2867467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867467).length < 2 ^ (prefixWord ++ tailWord_2867467).sum := by decide
  have hdescent : baseEnd_2867467 < baseStart_2867467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867485 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2867485 : Nat := 118140960795 + 2867485 * 2 ^ 59
def prefixEnd_2867485 : Nat := 4983230072969 + 3 ^ 40 * 2867485 * 2
def baseEnd_2867485 : Nat := 1472398074557818685450183

theorem tailTrace_2867485 : CollatzResearch.WordTrace tailWord_2867485 prefixEnd_2867485 1472398074557818685450183 := by
  unfold tailWord_2867485
  simp only [CollatzResearch.WordTrace]
  refine ⟨104585770016599047293915909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69723846677732698195943939 104585770016599047293915909)
  ·
    refine ⟨19609831878112321367609233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104585770016599047293915909 19609831878112321367609233)
    ·
      refine ⟨14707373908584241025706925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19609831878112321367609233 14707373908584241025706925)
      ·
        refine ⟨5515265215719090384640097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14707373908584241025706925 5515265215719090384640097)
        ·
          refine ⟨4136448911789317788480073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5515265215719090384640097 4136448911789317788480073)
          ·
            refine ⟨3102336683841988341360055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4136448911789317788480073 3102336683841988341360055)
            ·
              refine ⟨4653505025762982512040083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102336683841988341360055 4653505025762982512040083)
              ·
                refine ⟨6980257538644473768060125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653505025762982512040083 6980257538644473768060125)
                ·
                  refine ⟨2617596576991677663022547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6980257538644473768060125 2617596576991677663022547)
                  ·
                    refine ⟨3926394865487516494533821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617596576991677663022547 3926394865487516494533821)
                    ·
                      refine ⟨1472398074557818685450183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926394865487516494533821 1472398074557818685450183)
                      ·
                        rfl

theorem cell23_2867485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2867485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867485 prefixEnd_2867485 := by exact prefixLift 2867485
  have htrace : WordTrace (prefixWord ++ tailWord_2867485) baseStart_2867485 baseEnd_2867485 := by
    simpa [prefixWord, tailWord_2867485, baseEnd_2867485] using wordTrace_append hprefix tailTrace_2867485
  have hstable : (prefixWord ++ tailWord_2867485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867485).length < 2 ^ (prefixWord ++ tailWord_2867485).sum := by decide
  have hdescent : baseEnd_2867485 < baseStart_2867485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867508 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2867508 : Nat := 118140960795 + 2867508 * 2 ^ 59
def prefixEnd_2867508 : Nat := 4983230072969 + 3 ^ 40 * 2867508 * 2
def baseEnd_2867508 : Nat := 1472409884612872095462577

theorem tailTrace_2867508 : CollatzResearch.WordTrace tailWord_2867508 prefixEnd_2867508 1472409884612872095462577 := by
  unfold tailWord_2867508
  simp only [CollatzResearch.WordTrace]
  refine ⟨52293304447757861111001589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69724405930343814814668785 52293304447757861111001589)
  ·
    refine ⟨4902497291977299479156399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52293304447757861111001589 4902497291977299479156399)
    ·
      refine ⟨7353745937965949218734599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4902497291977299479156399 7353745937965949218734599)
      ·
        refine ⟨11030618906948923828101899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7353745937965949218734599 11030618906948923828101899)
        ·
          refine ⟨16545928360423385742152849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11030618906948923828101899 16545928360423385742152849)
          ·
            refine ⟨12409446270317539306614637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16545928360423385742152849 12409446270317539306614637)
            ·
              refine ⟨4653542351369077239980489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12409446270317539306614637 4653542351369077239980489)
              ·
                refine ⟨3490156763526807929985367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4653542351369077239980489 3490156763526807929985367)
                ·
                  refine ⟨5235235145290211894978051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490156763526807929985367 5235235145290211894978051)
                  ·
                    refine ⟨7852852717935317842467077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5235235145290211894978051 7852852717935317842467077)
                    ·
                      refine ⟨1472409884612872095462577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7852852717935317842467077 1472409884612872095462577)
                      ·
                        rfl

theorem cell23_2867508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2867508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867508 prefixEnd_2867508 := by exact prefixLift 2867508
  have htrace : WordTrace (prefixWord ++ tailWord_2867508) baseStart_2867508 baseEnd_2867508 := by
    simpa [prefixWord, tailWord_2867508, baseEnd_2867508] using wordTrace_append hprefix tailTrace_2867508
  have hstable : (prefixWord ++ tailWord_2867508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867508).length < 2 ^ (prefixWord ++ tailWord_2867508).sum := by decide
  have hdescent : baseEnd_2867508 < baseStart_2867508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867548 : List Nat := [2, 2, 4, 3, 1, 2, 1, 8]
def baseStart_2867548 : Nat := 118140960795 + 2867548 * 2 ^ 59
def prefixEnd_2867548 : Nat := 4983230072969 + 3 ^ 40 * 2867548 * 2
def baseEnd_2867548 : Nat := 54534460142187108850459

theorem tailTrace_2867548 : CollatzResearch.WordTrace tailWord_2867548 prefixEnd_2867548 54534460142187108850459 := by
  unfold tailWord_2867548
  simp only [CollatzResearch.WordTrace]
  refine ⟨52294033907685404526729649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69725378543580539368972865 52294033907685404526729649)
  ·
    refine ⟨39220525430764053395047237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52294033907685404526729649 39220525430764053395047237)
    ·
      refine ⟨7353848518268260011571357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39220525430764053395047237 7353848518268260011571357)
      ·
        refine ⟨2757693194350597504339259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7353848518268260011571357 2757693194350597504339259)
        ·
          refine ⟨4136539791525896256508889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757693194350597504339259 4136539791525896256508889)
          ·
            refine ⟨3102404843644422192381667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4136539791525896256508889 3102404843644422192381667)
            ·
              refine ⟨4653607265466633288572501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102404843644422192381667 4653607265466633288572501)
              ·
                refine ⟨54534460142187108850459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4653607265466633288572501 54534460142187108850459)
                ·
                  rfl

theorem cell23_2867548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 8].length) (baseStart_2867548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867548 prefixEnd_2867548 := by exact prefixLift 2867548
  have htrace : WordTrace (prefixWord ++ tailWord_2867548) baseStart_2867548 baseEnd_2867548 := by
    simpa [prefixWord, tailWord_2867548, baseEnd_2867548] using wordTrace_append hprefix tailTrace_2867548
  have hstable : (prefixWord ++ tailWord_2867548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867548).length < 2 ^ (prefixWord ++ tailWord_2867548).sum := by decide
  have hdescent : baseEnd_2867548 < baseStart_2867548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867551 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 3, 3, 2]
def baseStart_2867551 : Nat := 118140960795 + 2867551 * 2 ^ 59
def prefixEnd_2867551 : Nat := 4983230072969 + 3 ^ 40 * 2867551 * 2
def baseEnd_2867551 : Nat := 1472431964281015427224879

theorem tailTrace_2867551 : CollatzResearch.WordTrace tailWord_2867551 prefixEnd_2867551 1472431964281015427224879 := by
  unfold tailWord_2867551
  simp only [CollatzResearch.WordTrace]
  refine ⟨104588177234359940565818507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69725451489573293710545671 104588177234359940565818507)
  ·
    refine ⟨156882265851539910848727761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104588177234359940565818507 156882265851539910848727761)
    ·
      refine ⟨117661699388654933136545821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156882265851539910848727761 117661699388654933136545821)
      ·
        refine ⟨44123137270745599926204683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117661699388654933136545821 44123137270745599926204683)
        ·
          refine ⟨66184705906118399889307025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44123137270745599926204683 66184705906118399889307025)
          ·
            refine ⟨49638529429588799916980269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66184705906118399889307025 49638529429588799916980269)
            ·
              refine ⟨18614448536095799968867601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49638529429588799916980269 18614448536095799968867601)
              ·
                refine ⟨13960836402071849976650701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18614448536095799968867601 13960836402071849976650701)
                ·
                  refine ⟨5235313650776943741244013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13960836402071849976650701 5235313650776943741244013)
                  ·
                    refine ⟨1963242619041353902966505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5235313650776943741244013 1963242619041353902966505)
                    ·
                      refine ⟨1472431964281015427224879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963242619041353902966505 1472431964281015427224879)
                      ·
                        rfl

theorem cell23_2867551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_2867551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867551 prefixEnd_2867551 := by exact prefixLift 2867551
  have htrace : WordTrace (prefixWord ++ tailWord_2867551) baseStart_2867551 baseEnd_2867551 := by
    simpa [prefixWord, tailWord_2867551, baseEnd_2867551] using wordTrace_append hprefix tailTrace_2867551
  have hstable : (prefixWord ++ tailWord_2867551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867551).length < 2 ^ (prefixWord ++ tailWord_2867551).sum := by decide
  have hdescent : baseEnd_2867551 < baseStart_2867551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867585 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2867585 : Nat := 118140960795 + 2867585 * 2 ^ 59
def prefixEnd_2867585 : Nat := 4983230072969 + 3 ^ 40 * 2867585 * 2
def baseEnd_2867585 : Nat := 1472449422623268294199723

theorem tailTrace_2867585 : CollatzResearch.WordTrace tailWord_2867585 prefixEnd_2867585 1472449422623268294199723 := by
  unfold tailWord_2867585
  simp only [CollatzResearch.WordTrace]
  refine ⟨104589417316236764372556209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69726278210824509581704139 104589417316236764372556209)
  ·
    refine ⟨78442062987177573279417157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104589417316236764372556209 78442062987177573279417157)
    ·
      refine ⟨14707886810095794989890717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78442062987177573279417157 14707886810095794989890717)
      ·
        refine ⟨5515457553785923121209019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14707886810095794989890717 5515457553785923121209019)
        ·
          refine ⟨8273186330678884681813529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515457553785923121209019 8273186330678884681813529)
          ·
            refine ⟨6204889748009163511360147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8273186330678884681813529 6204889748009163511360147)
            ·
              refine ⟨9307334622013745267040221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204889748009163511360147 9307334622013745267040221)
              ·
                refine ⟨3490250483255154475140083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9307334622013745267040221 3490250483255154475140083)
                ·
                  refine ⟨5235375724882731712710125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490250483255154475140083 5235375724882731712710125)
                  ·
                    refine ⟨1963265896831024392266297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5235375724882731712710125 1963265896831024392266297)
                    ·
                      refine ⟨1472449422623268294199723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963265896831024392266297 1472449422623268294199723)
                      ·
                        rfl

theorem cell23_2867585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2867585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867585 prefixEnd_2867585 := by exact prefixLift 2867585
  have htrace : WordTrace (prefixWord ++ tailWord_2867585) baseStart_2867585 baseEnd_2867585 := by
    simpa [prefixWord, tailWord_2867585, baseEnd_2867585] using wordTrace_append hprefix tailTrace_2867585
  have hstable : (prefixWord ++ tailWord_2867585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867585).length < 2 ^ (prefixWord ++ tailWord_2867585).sum := by decide
  have hdescent : baseEnd_2867585 < baseStart_2867585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867634 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_2867634 : Nat := 118140960795 + 2867634 * 2 ^ 59
def prefixEnd_2867634 : Nat := 4983230072969 + 3 ^ 40 * 2867634 * 2
def baseEnd_2867634 : Nat := 490824861058446200828999

theorem tailTrace_2867634 : CollatzResearch.WordTrace tailWord_2867634 prefixEnd_2867634 490824861058446200828999 := by
  unfold tailWord_2867634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26147801123264811435272489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69727469662039497160726637 26147801123264811435272489)
  ·
    refine ⟨19610850842448608576454367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26147801123264811435272489 19610850842448608576454367)
    ·
      refine ⟨29416276263672912864681551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19610850842448608576454367 29416276263672912864681551)
      ·
        refine ⟨44124414395509369297022327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29416276263672912864681551 44124414395509369297022327)
        ·
          refine ⟨66186621593264053945533491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44124414395509369297022327 66186621593264053945533491)
          ·
            refine ⟨99279932389896080918300237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66186621593264053945533491 99279932389896080918300237)
            ·
              refine ⟨37229974646211030344362589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99279932389896080918300237 37229974646211030344362589)
              ·
                refine ⟨13961240492329136379135971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37229974646211030344362589 13961240492329136379135971)
                ·
                  refine ⟨20941860738493704568703957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13961240492329136379135971 20941860738493704568703957)
                  ·
                    refine ⟨490824861058446200828999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20941860738493704568703957 490824861058446200828999)
                    ·
                      rfl

theorem cell23_2867634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_2867634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867634 prefixEnd_2867634 := by exact prefixLift 2867634
  have htrace : WordTrace (prefixWord ++ tailWord_2867634) baseStart_2867634 baseEnd_2867634 := by
    simpa [prefixWord, tailWord_2867634, baseEnd_2867634] using wordTrace_append hprefix tailTrace_2867634
  have hstable : (prefixWord ++ tailWord_2867634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867634).length < 2 ^ (prefixWord ++ tailWord_2867634).sum := by decide
  have hdescent : baseEnd_2867634 < baseStart_2867634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867666 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2867666 : Nat := 118140960795 + 2867666 * 2 ^ 59
def prefixEnd_2867666 : Nat := 4983230072969 + 3 ^ 40 * 2867666 * 2
def baseEnd_2867666 : Nat := 1472491014556282477286851

theorem tailTrace_2867666 : CollatzResearch.WordTrace tailWord_2867666 prefixEnd_2867666 1472491014556282477286851 := by
  unfold tailWord_2867666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148092907235828801563713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69728247752628876804169901 26148092907235828801563713)
  ·
    refine ⟨19611069680426871601172785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26148092907235828801563713 19611069680426871601172785)
    ·
      refine ⟨14708302260320153700879589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19611069680426871601172785 14708302260320153700879589)
      ·
        refine ⟨2757806673810028818914923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14708302260320153700879589 2757806673810028818914923)
        ·
          refine ⟨4136710010715043228372385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757806673810028818914923 4136710010715043228372385)
          ·
            refine ⟨3102532508036282421279289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4136710010715043228372385 3102532508036282421279289)
            ·
              refine ⟨2326899381027211815959467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102532508036282421279289 2326899381027211815959467)
              ·
                refine ⟨3490349071540817723939201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326899381027211815959467 3490349071540817723939201)
                ·
                  refine ⟨2617761803655613292954401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3490349071540817723939201 2617761803655613292954401)
                  ·
                    refine ⟨1963321352741709969715801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2617761803655613292954401 1963321352741709969715801)
                    ·
                      refine ⟨1472491014556282477286851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963321352741709969715801 1472491014556282477286851)
                      ·
                        rfl

theorem cell23_2867666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2867666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867666 prefixEnd_2867666 := by exact prefixLift 2867666
  have htrace : WordTrace (prefixWord ++ tailWord_2867666) baseStart_2867666 baseEnd_2867666 := by
    simpa [prefixWord, tailWord_2867666, baseEnd_2867666] using wordTrace_append hprefix tailTrace_2867666
  have hstable : (prefixWord ++ tailWord_2867666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867666).length < 2 ^ (prefixWord ++ tailWord_2867666).sum := by decide
  have hdescent : baseEnd_2867666 < baseStart_2867666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867681 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2867681 : Nat := 118140960795 + 2867681 * 2 ^ 59
def prefixEnd_2867681 : Nat := 4983230072969 + 3 ^ 40 * 2867681 * 2
def baseEnd_2867681 : Nat := 490832905588699972866427

theorem tailTrace_2867681 : CollatzResearch.WordTrace tailWord_2867681 prefixEnd_2867681 490832905588699972866427 := by
  unfold tailWord_2867681
  simp only [CollatzResearch.WordTrace]
  refine ⟨104592918723888972768050897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69728612482592648512033931 104592918723888972768050897)
  ·
    refine ⟨78444689042916729576038173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104592918723888972768050897 78444689042916729576038173)
    ·
      refine ⟨29416758391093773591014315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78444689042916729576038173 29416758391093773591014315)
      ·
        refine ⟨44125137586640660386521473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29416758391093773591014315 44125137586640660386521473)
        ·
          refine ⟨33093853189980495289891105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44125137586640660386521473 33093853189980495289891105)
          ·
            refine ⟨24820389892485371467418329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33093853189980495289891105 24820389892485371467418329)
            ·
              refine ⟨18615292419364028600563747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24820389892485371467418329 18615292419364028600563747)
              ·
                refine ⟨27922938629046042900845621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18615292419364028600563747 27922938629046042900845621)
                ·
                  refine ⟨2617775496473066521954277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27922938629046042900845621 2617775496473066521954277)
                  ·
                    refine ⟨490832905588699972866427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2617775496473066521954277 490832905588699972866427)
                    ·
                      rfl

theorem cell23_2867681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2867681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867681 prefixEnd_2867681 := by exact prefixLift 2867681
  have htrace : WordTrace (prefixWord ++ tailWord_2867681) baseStart_2867681 baseEnd_2867681 := by
    simpa [prefixWord, tailWord_2867681, baseEnd_2867681] using wordTrace_append hprefix tailTrace_2867681
  have hstable : (prefixWord ++ tailWord_2867681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867681).length < 2 ^ (prefixWord ++ tailWord_2867681).sum := by decide
  have hdescent : baseEnd_2867681 < baseStart_2867681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867684 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2867684 : Nat := 118140960795 + 2867684 * 2 ^ 59
def prefixEnd_2867684 : Nat := 4983230072969 + 3 ^ 40 * 2867684 * 2
def baseEnd_2867684 : Nat := 1472500257208063406861767

theorem tailTrace_2867684 : CollatzResearch.WordTrace tailWord_2867684 prefixEnd_2867684 1472500257208063406861767 := by
  unfold tailWord_2867684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52296514071439052140205053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69728685428585402853606737 52296514071439052140205053)
  ·
    refine ⟨19611192776789644552576895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52296514071439052140205053 19611192776789644552576895)
    ·
      refine ⟨29416789165184466828865343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19611192776789644552576895 29416789165184466828865343)
      ·
        refine ⟨44125183747776700243298015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29416789165184466828865343 44125183747776700243298015)
        ·
          refine ⟨66187775621665050364947023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44125183747776700243298015 66187775621665050364947023)
          ·
            refine ⟨99281663432497575547420535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66187775621665050364947023 99281663432497575547420535)
            ·
              refine ⟨148922495148746363321130803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99281663432497575547420535 148922495148746363321130803)
              ·
                refine ⟨223383742723119544981696205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148922495148746363321130803 223383742723119544981696205)
                ·
                  refine ⟨83768903521169829368136077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223383742723119544981696205 83768903521169829368136077)
                  ·
                    refine ⟨31413338820438686013051029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83768903521169829368136077 31413338820438686013051029)
                    ·
                      refine ⟨1472500257208063406861767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31413338820438686013051029 1472500257208063406861767)
                      ·
                        rfl

theorem cell23_2867684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2867684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867684 prefixEnd_2867684 := by exact prefixLift 2867684
  have htrace : WordTrace (prefixWord ++ tailWord_2867684) baseStart_2867684 baseEnd_2867684 := by
    simpa [prefixWord, tailWord_2867684, baseEnd_2867684] using wordTrace_append hprefix tailTrace_2867684
  have hstable : (prefixWord ++ tailWord_2867684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867684).length < 2 ^ (prefixWord ++ tailWord_2867684).sum := by decide
  have hdescent : baseEnd_2867684 < baseStart_2867684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867688 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2867688 : Nat := 118140960795 + 2867688 * 2 ^ 59
def prefixEnd_2867688 : Nat := 4983230072969 + 3 ^ 40 * 2867688 * 2
def baseEnd_2867688 : Nat := 1472502311130681391211749

theorem tailTrace_2867688 : CollatzResearch.WordTrace tailWord_2867688 prefixEnd_2867688 1472502311130681391211749 := by
  unfold tailWord_2867688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52296587017431806481777859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69728782689909075309037145 52296587017431806481777859)
  ·
    refine ⟨78444880526147709722666789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52296587017431806481777859 78444880526147709722666789)
    ·
      refine ⟨14708415098652695573000023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78444880526147709722666789 14708415098652695573000023)
      ·
        refine ⟨22062622647979043359500035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14708415098652695573000023 22062622647979043359500035)
        ·
          refine ⟨33093933971968565039250053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22062622647979043359500035 33093933971968565039250053)
          ·
            refine ⟨6205112619744105944859385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33093933971968565039250053 6205112619744105944859385)
            ·
              refine ⟨4653834464808079458644539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6205112619744105944859385 4653834464808079458644539)
              ·
                refine ⟨6980751697212119187966809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653834464808079458644539 6980751697212119187966809)
                ·
                  refine ⟨5235563772909089390975107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6980751697212119187966809 5235563772909089390975107)
                  ·
                    refine ⟨7853345659363634086462661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5235563772909089390975107 7853345659363634086462661)
                    ·
                      refine ⟨1472502311130681391211749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7853345659363634086462661 1472502311130681391211749)
                      ·
                        rfl

theorem cell23_2867688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2867688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867688 prefixEnd_2867688 := by exact prefixLift 2867688
  have htrace : WordTrace (prefixWord ++ tailWord_2867688) baseStart_2867688 baseEnd_2867688 := by
    simpa [prefixWord, tailWord_2867688, baseEnd_2867688] using wordTrace_append hprefix tailTrace_2867688
  have hstable : (prefixWord ++ tailWord_2867688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867688).length < 2 ^ (prefixWord ++ tailWord_2867688).sum := by decide
  have hdescent : baseEnd_2867688 < baseStart_2867688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867711 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 6]
def baseStart_2867711 : Nat := 118140960795 + 2867711 * 2 ^ 59
def prefixEnd_2867711 : Nat := 4983230072969 + 3 ^ 40 * 2867711 * 2
def baseEnd_2867711 : Nat := 163612680131748311247127

theorem tailTrace_2867711 : CollatzResearch.WordTrace tailWord_2867711 prefixEnd_2867711 163612680131748311247127 := by
  unfold tailWord_2867711
  simp only [CollatzResearch.WordTrace]
  refine ⟨104594012913780287891642987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69729341942520191927761991 104594012913780287891642987)
  ·
    refine ⟨156891019370670431837464481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104594012913780287891642987 156891019370670431837464481)
    ·
      refine ⟨117668264528002823878098361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156891019370670431837464481 117668264528002823878098361)
      ·
        refine ⟨88251198396002117908573771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117668264528002823878098361 88251198396002117908573771)
        ·
          refine ⟨132376797594003176862860657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88251198396002117908573771 132376797594003176862860657)
          ·
            refine ⟨99282598195502382647145493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132376797594003176862860657 99282598195502382647145493)
            ·
              refine ⟨4653871790414174186584945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99282598195502382647145493 4653871790414174186584945)
              ·
                refine ⟨3490403842810630639938709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4653871790414174186584945 3490403842810630639938709)
                ·
                  refine ⟨163612680131748311247127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3490403842810630639938709 163612680131748311247127)
                  ·
                    rfl

theorem cell23_2867711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 6].length) (baseStart_2867711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867711 prefixEnd_2867711 := by exact prefixLift 2867711
  have htrace : WordTrace (prefixWord ++ tailWord_2867711) baseStart_2867711 baseEnd_2867711 := by
    simpa [prefixWord, tailWord_2867711, baseEnd_2867711] using wordTrace_append hprefix tailTrace_2867711
  have hstable : (prefixWord ++ tailWord_2867711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867711).length < 2 ^ (prefixWord ++ tailWord_2867711).sum := by decide
  have hdescent : baseEnd_2867711 < baseStart_2867711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867738 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_2867738 : Nat := 118140960795 + 2867738 * 2 ^ 59
def prefixEnd_2867738 : Nat := 4983230072969 + 3 ^ 40 * 2867738 * 2
def baseEnd_2867738 : Nat := 1472527985163406195586519

theorem tailTrace_2867738 : CollatzResearch.WordTrace tailWord_2867738 prefixEnd_2867738 1472527985163406195586519 := by
  unfold tailWord_2867738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148749421170617875718967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69729998456454981001917245 26148749421170617875718967)
  ·
    refine ⟨39223124131755926813578451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26148749421170617875718967 39223124131755926813578451)
    ·
      refine ⟨58834686197633890220367677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39223124131755926813578451 58834686197633890220367677)
      ·
        refine ⟨22063007324112708832637879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58834686197633890220367677 22063007324112708832637879)
        ·
          refine ⟨33094510986169063248956819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22063007324112708832637879 33094510986169063248956819)
          ·
            refine ⟨49641766479253594873435229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33094510986169063248956819 49641766479253594873435229)
            ·
              refine ⟨18615662429720098077538211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49641766479253594873435229 18615662429720098077538211)
              ·
                refine ⟨27923493644580147116307317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18615662429720098077538211 27923493644580147116307317)
                ·
                  refine ⟨2617827529179388792153811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27923493644580147116307317 2617827529179388792153811)
                  ·
                    refine ⟨3926741293769083188230717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617827529179388792153811 3926741293769083188230717)
                    ·
                      refine ⟨1472527985163406195586519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926741293769083188230717 1472527985163406195586519)
                      ·
                        rfl

theorem cell23_2867738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_2867738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867738 prefixEnd_2867738 := by exact prefixLift 2867738
  have htrace : WordTrace (prefixWord ++ tailWord_2867738) baseStart_2867738 baseEnd_2867738 := by
    simpa [prefixWord, tailWord_2867738, baseEnd_2867738] using wordTrace_append hprefix tailTrace_2867738
  have hstable : (prefixWord ++ tailWord_2867738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867738).length < 2 ^ (prefixWord ++ tailWord_2867738).sum := by decide
  have hdescent : baseEnd_2867738 < baseStart_2867738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867772 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_2867772 : Nat := 118140960795 + 2867772 * 2 ^ 59
def prefixEnd_2867772 : Nat := 4983230072969 + 3 ^ 40 * 2867772 * 2
def baseEnd_2867772 : Nat := 1472545443505659062561363

theorem tailTrace_2867772 : CollatzResearch.WordTrace tailWord_2867772 prefixEnd_2867772 1472545443505659062561363 := by
  unfold tailWord_2867772
  simp only [CollatzResearch.WordTrace]
  refine ⟨52298118883279647654806785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69730825177706196873075713 52298118883279647654806785)
  ·
    refine ⟨39223589162459735741105089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52298118883279647654806785 39223589162459735741105089)
    ·
      refine ⟨29417691871844801805828817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39223589162459735741105089 29417691871844801805828817)
      ·
        refine ⟨22063268903883601354371613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29417691871844801805828817 22063268903883601354371613)
        ·
          refine ⟨8273725838956350507889355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22063268903883601354371613 8273725838956350507889355)
          ·
            refine ⟨12410588758434525761834033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273725838956350507889355 12410588758434525761834033)
            ·
              refine ⟨9307941568825894321375525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12410588758434525761834033 9307941568825894321375525)
              ·
                refine ⟨1745239044154855185257911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9307941568825894321375525 1745239044154855185257911)
                ·
                  refine ⟨2617858566232282777886867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745239044154855185257911 2617858566232282777886867)
                  ·
                    refine ⟨3926787849348424166830301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2617858566232282777886867 3926787849348424166830301)
                    ·
                      refine ⟨1472545443505659062561363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3926787849348424166830301 1472545443505659062561363)
                      ·
                        rfl

theorem cell23_2867772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_2867772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867772 prefixEnd_2867772 := by exact prefixLift 2867772
  have htrace : WordTrace (prefixWord ++ tailWord_2867772) baseStart_2867772 baseEnd_2867772 := by
    simpa [prefixWord, tailWord_2867772, baseEnd_2867772] using wordTrace_append hprefix tailTrace_2867772
  have hstable : (prefixWord ++ tailWord_2867772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867772).length < 2 ^ (prefixWord ++ tailWord_2867772).sum := by decide
  have hdescent : baseEnd_2867772 < baseStart_2867772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867781 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2867781 : Nat := 118140960795 + 2867781 * 2 ^ 59
def prefixEnd_2867781 : Nat := 4983230072969 + 3 ^ 40 * 2867781 * 2
def baseEnd_2867781 : Nat := 1472550064831549527348821

theorem tailTrace_2867781 : CollatzResearch.WordTrace tailWord_2867781 prefixEnd_2867781 1472550064831549527348821 := by
  unfold tailWord_2867781
  simp only [CollatzResearch.WordTrace]
  refine ⟨104596566023526689846691197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69731044015684459897794131 104596566023526689846691197)
  ·
    refine ⟨39223712258822508692509199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104596566023526689846691197 39223712258822508692509199)
    ·
      refine ⟨58835568388233763038763799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39223712258822508692509199 58835568388233763038763799)
      ·
        refine ⟨88253352582350644558145699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58835568388233763038763799 88253352582350644558145699)
        ·
          refine ⟨132380028873525966837218549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88253352582350644558145699 132380028873525966837218549)
          ·
            refine ⟨12410627706893059390989239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132380028873525966837218549 12410627706893059390989239)
            ·
              refine ⟨18615941560339589086483859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12410627706893059390989239 18615941560339589086483859)
              ·
                refine ⟨27923912340509383629725789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18615941560339589086483859 27923912340509383629725789)
                ·
                  refine ⟨10471467127691018861147171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27923912340509383629725789 10471467127691018861147171)
                  ·
                    refine ⟨15707200691536528291720757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10471467127691018861147171 15707200691536528291720757)
                    ·
                      refine ⟨1472550064831549527348821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15707200691536528291720757 1472550064831549527348821)
                      ·
                        rfl

theorem cell23_2867781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2867781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867781 prefixEnd_2867781 := by exact prefixLift 2867781
  have htrace : WordTrace (prefixWord ++ tailWord_2867781) baseStart_2867781 baseEnd_2867781 := by
    simpa [prefixWord, tailWord_2867781, baseEnd_2867781] using wordTrace_append hprefix tailTrace_2867781
  have hstable : (prefixWord ++ tailWord_2867781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867781).length < 2 ^ (prefixWord ++ tailWord_2867781).sum := by decide
  have hdescent : baseEnd_2867781 < baseStart_2867781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867782 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2867782 : Nat := 118140960795 + 2867782 * 2 ^ 59
def prefixEnd_2867782 : Nat := 4983230072969 + 3 ^ 40 * 2867782 * 2
def baseEnd_2867782 : Nat := 1472550578312204023436317

theorem tailTrace_2867782 : CollatzResearch.WordTrace tailWord_2867782 prefixEnd_2867782 1472550578312204023436317 := by
  unfold tailWord_2867782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268643828016345844296175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69731068331015378011651733 3268643828016345844296175)
  ·
    refine ⟨4902965742024518766444263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3268643828016345844296175 4902965742024518766444263)
    ·
      refine ⟨7354448613036778149666395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4902965742024518766444263 7354448613036778149666395)
      ·
        refine ⟨11031672919555167224499593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7354448613036778149666395 11031672919555167224499593)
        ·
          refine ⟨8273754689666375418374695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11031672919555167224499593 8273754689666375418374695)
          ·
            refine ⟨12410632034499563127562043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273754689666375418374695 12410632034499563127562043)
            ·
              refine ⟨18615948051749344691343065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12410632034499563127562043 18615948051749344691343065)
              ·
                refine ⟨13961961038812008518507299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18615948051749344691343065 13961961038812008518507299)
                ·
                  refine ⟨20942941558218012777760949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13961961038812008518507299 20942941558218012777760949)
                  ·
                    refine ⟨1963400771082938697915089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20942941558218012777760949 1963400771082938697915089)
                    ·
                      refine ⟨1472550578312204023436317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963400771082938697915089 1472550578312204023436317)
                      ·
                        rfl

theorem cell23_2867782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2867782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867782 prefixEnd_2867782 := by exact prefixLift 2867782
  have htrace : WordTrace (prefixWord ++ tailWord_2867782) baseStart_2867782 baseEnd_2867782 := by
    simpa [prefixWord, tailWord_2867782, baseEnd_2867782] using wordTrace_append hprefix tailTrace_2867782
  have hstable : (prefixWord ++ tailWord_2867782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867782).length < 2 ^ (prefixWord ++ tailWord_2867782).sum := by decide
  have hdescent : baseEnd_2867782 < baseStart_2867782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867851 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_2867851 : Nat := 118140960795 + 2867851 * 2 ^ 59
def prefixEnd_2867851 : Nat := 4983230072969 + 3 ^ 40 * 2867851 * 2
def baseEnd_2867851 : Nat := 1472586008477364253473499

theorem tailTrace_2867851 : CollatzResearch.WordTrace tailWord_2867851 prefixEnd_2867851 1472586008477364253473499 := by
  unfold tailWord_2867851
  simp only [CollatzResearch.WordTrace]
  refine ⟨104599119133273091801739407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69732746088848727867826271 104599119133273091801739407)
  ·
    refine ⟨156898678699909637702609111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104599119133273091801739407 156898678699909637702609111)
    ·
      refine ⟨235348018049864456553913667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156898678699909637702609111 235348018049864456553913667)
      ·
        refine ⟨353022027074796684830870501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235348018049864456553913667 353022027074796684830870501)
        ·
          refine ⟨66191630076524378405788219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353022027074796684830870501 66191630076524378405788219)
          ·
            refine ⟨99287445114786567608682329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66191630076524378405788219 99287445114786567608682329)
            ·
              refine ⟨74465583836089925706511747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99287445114786567608682329 74465583836089925706511747)
              ·
                refine ⟨111698375754134888559767621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74465583836089925706511747 111698375754134888559767621)
                ·
                  refine ⟨20943445453900291604956429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111698375754134888559767621 20943445453900291604956429)
                  ·
                    refine ⟨7853792045212609351858661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20943445453900291604956429 7853792045212609351858661)
                    ·
                      refine ⟨1472586008477364253473499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7853792045212609351858661 1472586008477364253473499)
                      ·
                        rfl

theorem cell23_2867851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_2867851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867851 prefixEnd_2867851 := by exact prefixLift 2867851
  have htrace : WordTrace (prefixWord ++ tailWord_2867851) baseStart_2867851 baseEnd_2867851 := by
    simpa [prefixWord, tailWord_2867851, baseEnd_2867851] using wordTrace_append hprefix tailTrace_2867851
  have hstable : (prefixWord ++ tailWord_2867851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867851).length < 2 ^ (prefixWord ++ tailWord_2867851).sum := by decide
  have hdescent : baseEnd_2867851 < baseStart_2867851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867861 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2867861 : Nat := 118140960795 + 2867861 * 2 ^ 59
def prefixEnd_2867861 : Nat := 4983230072969 + 3 ^ 40 * 2867861 * 2
def baseEnd_2867861 : Nat := 490863714427969738116151

theorem tailTrace_2867861 : CollatzResearch.WordTrace tailWord_2867861 prefixEnd_2867861 490863714427969738116151 := by
  unfold tailWord_2867861
  simp only [CollatzResearch.WordTrace]
  refine ⟨104599483863236863509603437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69732989242157909006402291 104599483863236863509603437)
  ·
    refine ⟨39224806448713823816101289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104599483863236863509603437 39224806448713823816101289)
    ·
      refine ⟨29418604836535367862075967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39224806448713823816101289 29418604836535367862075967)
      ·
        refine ⟨44127907254803051793113951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29418604836535367862075967 44127907254803051793113951)
        ·
          refine ⟨66191860882204577689670927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44127907254803051793113951 66191860882204577689670927)
          ·
            refine ⟨99287791323306866534506391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66191860882204577689670927 99287791323306866534506391)
            ·
              refine ⟨148931686984960299801759587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99287791323306866534506391 148931686984960299801759587)
              ·
                refine ⟨223397530477440449702639381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148931686984960299801759587 223397530477440449702639381)
                ·
                  refine ⟨10471759241130021079811221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223397530477440449702639381 10471759241130021079811221)
                  ·
                    refine ⟨490863714427969738116151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10471759241130021079811221 490863714427969738116151)
                    ·
                      rfl

theorem cell23_2867861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2867861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867861 prefixEnd_2867861 := by exact prefixLift 2867861
  have htrace : WordTrace (prefixWord ++ tailWord_2867861) baseStart_2867861 baseEnd_2867861 := by
    simpa [prefixWord, tailWord_2867861, baseEnd_2867861] using wordTrace_append hprefix tailTrace_2867861
  have hstable : (prefixWord ++ tailWord_2867861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867861).length < 2 ^ (prefixWord ++ tailWord_2867861).sum := by decide
  have hdescent : baseEnd_2867861 < baseStart_2867861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867898 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_2867898 : Nat := 118140960795 + 2867898 * 2 ^ 59
def prefixEnd_2867898 : Nat := 4983230072969 + 3 ^ 40 * 2867898 * 2
def baseEnd_2867898 : Nat := 1472610142068125569585783

theorem tailTrace_2867898 : CollatzResearch.WordTrace tailWord_2867898 prefixEnd_2867898 1472610142068125569585783 := by
  unfold tailWord_2867898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26150208341025704707175087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69733888909401879219133565 26150208341025704707175087)
  ·
    refine ⟨39225312511538557060762631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26150208341025704707175087 39225312511538557060762631)
    ·
      refine ⟨58837968767307835591143947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39225312511538557060762631 58837968767307835591143947)
      ·
        refine ⟨88256953150961753386715921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58837968767307835591143947 88256953150961753386715921)
        ·
          refine ⟨66192714863221315040036941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88256953150961753386715921 66192714863221315040036941)
          ·
            refine ⟨24822268073707993140013853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66192714863221315040036941 24822268073707993140013853)
            ·
              refine ⟨9308350527640497427505195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24822268073707993140013853 9308350527640497427505195)
              ·
                refine ⟨13962525791460746141257793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308350527640497427505195 13962525791460746141257793)
                ·
                  refine ⟨10471894343595559605943345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13962525791460746141257793 10471894343595559605943345)
                  ·
                    refine ⟨7853920757696669704457509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10471894343595559605943345 7853920757696669704457509)
                    ·
                      refine ⟨1472610142068125569585783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7853920757696669704457509 1472610142068125569585783)
                      ·
                        rfl

theorem cell23_2867898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_2867898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867898 prefixEnd_2867898 := by exact prefixLift 2867898
  have htrace : WordTrace (prefixWord ++ tailWord_2867898) baseStart_2867898 baseEnd_2867898 := by
    simpa [prefixWord, tailWord_2867898, baseEnd_2867898] using wordTrace_append hprefix tailTrace_2867898
  have hstable : (prefixWord ++ tailWord_2867898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867898).length < 2 ^ (prefixWord ++ tailWord_2867898).sum := by decide
  have hdescent : baseEnd_2867898 < baseStart_2867898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867902 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_2867902 : Nat := 118140960795 + 2867902 * 2 ^ 59
def prefixEnd_2867902 : Nat := 4983230072969 + 3 ^ 40 * 2867902 * 2
def baseEnd_2867902 : Nat := 1472612195990743553935765

theorem tailTrace_2867902 : CollatzResearch.WordTrace tailWord_2867902 prefixEnd_2867902 1472612195990743553935765 := by
  unfold tailWord_2867902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075122407011040938980745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69733986170725551674563973 13075122407011040938980745)
  ·
    refine ⟨9806341805258280704235559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13075122407011040938980745 9806341805258280704235559)
    ·
      refine ⟨14709512707887421056353339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806341805258280704235559 14709512707887421056353339)
      ·
        refine ⟨22064269061831131584530009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14709512707887421056353339 22064269061831131584530009)
        ·
          refine ⟨16548201796373348688397507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22064269061831131584530009 16548201796373348688397507)
          ·
            refine ⟨24822302694560023032596261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16548201796373348688397507 24822302694560023032596261)
            ·
              refine ⟨4654181755230004318611799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24822302694560023032596261 4654181755230004318611799)
              ·
                refine ⟨6981272632845006477917699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654181755230004318611799 6981272632845006477917699)
                ·
                  refine ⟨10471908949267509716876549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981272632845006477917699 10471908949267509716876549)
                  ·
                    refine ⟨1963482927987658071914353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10471908949267509716876549 1963482927987658071914353)
                    ·
                      refine ⟨1472612195990743553935765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963482927987658071914353 1472612195990743553935765)
                      ·
                        rfl

theorem cell23_2867902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_2867902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867902 prefixEnd_2867902 := by exact prefixLift 2867902
  have htrace : WordTrace (prefixWord ++ tailWord_2867902) baseStart_2867902 baseEnd_2867902 := by
    simpa [prefixWord, tailWord_2867902, baseEnd_2867902] using wordTrace_append hprefix tailTrace_2867902
  have hstable : (prefixWord ++ tailWord_2867902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867902).length < 2 ^ (prefixWord ++ tailWord_2867902).sum := by decide
  have hdescent : baseEnd_2867902 < baseStart_2867902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867908 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 9]
def baseStart_2867908 : Nat := 118140960795 + 2867908 * 2 ^ 59
def prefixEnd_2867908 : Nat := 4983230072969 + 3 ^ 40 * 2867908 * 2
def baseEnd_2867908 : Nat := 163623919652741170051193

theorem tailTrace_2867908 : CollatzResearch.WordTrace tailWord_2867908 prefixEnd_2867908 163623919652741170051193 := by
  unfold tailWord_2867908
  simp only [CollatzResearch.WordTrace]
  refine ⟨52300599047033295268282189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69734132062711060357709585 52300599047033295268282189)
  ·
    refine ⟨19612724642637485725605821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52300599047033295268282189 19612724642637485725605821)
    ·
      refine ⟨7354771740989057147102183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19612724642637485725605821 7354771740989057147102183)
      ·
        refine ⟨11032157611483585720653275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7354771740989057147102183 11032157611483585720653275)
        ·
          refine ⟨16548236417225378580979913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032157611483585720653275 16548236417225378580979913)
          ·
            refine ⟨12411177312919033935734935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16548236417225378580979913 12411177312919033935734935)
            ·
              refine ⟨18616765969378550903602403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12411177312919033935734935 18616765969378550903602403)
              ·
                refine ⟨27925148954067826355403605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18616765969378550903602403 27925148954067826355403605)
                ·
                  refine ⟨163623919652741170051193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27925148954067826355403605 163623919652741170051193)
                  ·
                    rfl

theorem cell23_2867908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_2867908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867908 prefixEnd_2867908 := by exact prefixLift 2867908
  have htrace : WordTrace (prefixWord ++ tailWord_2867908) baseStart_2867908 baseEnd_2867908 := by
    simpa [prefixWord, tailWord_2867908, baseEnd_2867908] using wordTrace_append hprefix tailTrace_2867908
  have hstable : (prefixWord ++ tailWord_2867908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867908).length < 2 ^ (prefixWord ++ tailWord_2867908).sum := by decide
  have hdescent : baseEnd_2867908 < baseStart_2867908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_2867931 : Nat := 118140960795 + 2867931 * 2 ^ 59
def prefixEnd_2867931 : Nat := 4983230072969 + 3 ^ 40 * 2867931 * 2
def baseEnd_2867931 : Nat := 1472627086929723940473131

theorem tailTrace_2867931 : CollatzResearch.WordTrace tailWord_2867931 prefixEnd_2867931 1472627086929723940473131 := by
  unfold tailWord_2867931
  simp only [CollatzResearch.WordTrace]
  refine ⟨104602036972983265464651647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69734691315322176976434431 104602036972983265464651647)
  ·
    refine ⟨156903055459474898196977471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104602036972983265464651647 156903055459474898196977471)
    ·
      refine ⟨235354583189212347295466207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156903055459474898196977471 235354583189212347295466207)
      ·
        refine ⟨353031874783818520943199311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235354583189212347295466207 353031874783818520943199311)
        ·
          refine ⟨529547812175727781414798967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353031874783818520943199311 529547812175727781414798967)
          ·
            refine ⟨794321718263591672122198451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529547812175727781414798967 794321718263591672122198451)
            ·
              refine ⟨1191482577395387508183297677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794321718263591672122198451 1191482577395387508183297677)
              ·
                refine ⟨446805966523270315568736629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191482577395387508183297677 446805966523270315568736629)
                ·
                  refine ⟨41888059361556592084569059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 446805966523270315568736629 41888059361556592084569059)
                  ·
                    refine ⟨62832089042334888126853589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41888059361556592084569059 62832089042334888126853589)
                    ·
                      refine ⟨1472627086929723940473131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62832089042334888126853589 1472627086929723940473131)
                      ·
                        rfl

theorem cell23_2867931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_2867931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867931 prefixEnd_2867931 := by exact prefixLift 2867931
  have htrace : WordTrace (prefixWord ++ tailWord_2867931) baseStart_2867931 baseEnd_2867931 := by
    simpa [prefixWord, tailWord_2867931, baseEnd_2867931] using wordTrace_append hprefix tailTrace_2867931
  have hstable : (prefixWord ++ tailWord_2867931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867931).length < 2 ^ (prefixWord ++ tailWord_2867931).sum := by decide
  have hdescent : baseEnd_2867931 < baseStart_2867931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867975 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2867975 : Nat := 118140960795 + 2867975 * 2 ^ 59
def prefixEnd_2867975 : Nat := 4983230072969 + 3 ^ 40 * 2867975 * 2
def baseEnd_2867975 : Nat := 1472649680078521768322929

theorem tailTrace_2867975 : CollatzResearch.WordTrace tailWord_2867975 prefixEnd_2867975 1472649680078521768322929 := by
  unfold tailWord_2867975
  simp only [CollatzResearch.WordTrace]
  refine ⟨104603641784823860979253379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69735761189882573986168919 104603641784823860979253379)
  ·
    refine ⟨156905462677235791468880069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104603641784823860979253379 156905462677235791468880069)
    ·
      refine ⟨29419774251981710900415013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156905462677235791468880069 29419774251981710900415013)
      ·
        refine ⟨5516207672246570793827815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29419774251981710900415013 5516207672246570793827815)
        ·
          refine ⟨8274311508369856190741723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516207672246570793827815 8274311508369856190741723)
          ·
            refine ⟨12411467262554784286112585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274311508369856190741723 12411467262554784286112585)
            ·
              refine ⟨9308600446916088214584439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12411467262554784286112585 9308600446916088214584439)
              ·
                refine ⟨13962900670374132321876659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308600446916088214584439 13962900670374132321876659)
                ·
                  refine ⟨20944351005561198482814989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13962900670374132321876659 20944351005561198482814989)
                  ·
                    refine ⟨7854131627085449431055621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20944351005561198482814989 7854131627085449431055621)
                    ·
                      refine ⟨1472649680078521768322929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7854131627085449431055621 1472649680078521768322929)
                      ·
                        rfl

theorem cell23_2867975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2867975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2867975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2867975 prefixEnd_2867975 := by exact prefixLift 2867975
  have htrace : WordTrace (prefixWord ++ tailWord_2867975) baseStart_2867975 baseEnd_2867975 := by
    simpa [prefixWord, tailWord_2867975, baseEnd_2867975] using wordTrace_append hprefix tailTrace_2867975
  have hstable : (prefixWord ++ tailWord_2867975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867975).length < 2 ^ (prefixWord ++ tailWord_2867975).sum := by decide
  have hdescent : baseEnd_2867975 < baseStart_2867975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868002 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_2868002 : Nat := 118140960795 + 2868002 * 2 ^ 59
def prefixEnd_2868002 : Nat := 4983230072969 + 3 ^ 40 * 2868002 * 2
def baseEnd_2868002 : Nat := 490887848018731054228435

theorem tailTrace_2868002 : CollatzResearch.WordTrace tailWord_2868002 prefixEnd_2868002 490887848018731054228435 := by
  unfold tailWord_2868002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26151156638931511147621565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69736417703817363060324173 26151156638931511147621565)
  ·
    refine ⟨9806683739599316680358087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26151156638931511147621565 9806683739599316680358087)
    ·
      refine ⟨14710025609398975020537131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806683739599316680358087 14710025609398975020537131)
      ·
        refine ⟨22065038414098462530805697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14710025609398975020537131 22065038414098462530805697)
        ·
          refine ⟨16548778810573846898104273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22065038414098462530805697 16548778810573846898104273)
          ·
            refine ⟨12411584107930385173578205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16548778810573846898104273 12411584107930385173578205)
            ·
              refine ⟨4654344040473894440091827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12411584107930385173578205 4654344040473894440091827)
              ·
                refine ⟨6981516060710841660137741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654344040473894440091827 6981516060710841660137741)
                ·
                  refine ⟨2618068522766565622551653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6981516060710841660137741 2618068522766565622551653)
                  ·
                    refine ⟨490887848018731054228435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618068522766565622551653 490887848018731054228435)
                    ·
                      rfl

theorem cell23_2868002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_2868002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868002 prefixEnd_2868002 := by exact prefixLift 2868002
  have htrace : WordTrace (prefixWord ++ tailWord_2868002) baseStart_2868002 baseEnd_2868002 := by
    simpa [prefixWord, tailWord_2868002, baseEnd_2868002] using wordTrace_append hprefix tailTrace_2868002
  have hstable : (prefixWord ++ tailWord_2868002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868002).length < 2 ^ (prefixWord ++ tailWord_2868002).sum := by decide
  have hdescent : baseEnd_2868002 < baseStart_2868002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868029 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2868029 : Nat := 118140960795 + 2868029 * 2 ^ 59
def prefixEnd_2868029 : Nat := 4983230072969 + 3 ^ 40 * 2868029 * 2
def baseEnd_2868029 : Nat := 1472677408033864557047681

theorem tailTrace_2868029 : CollatzResearch.WordTrace tailWord_2868029 prefixEnd_2868029 1472677408033864557047681 := by
  unfold tailWord_2868029
  simp only [CollatzResearch.WordTrace]
  refine ⟨104605611326628228201719141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69737074217752152134479427 104605611326628228201719141)
  ·
    refine ⟨19613552123742792787822339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104605611326628228201719141 19613552123742792787822339)
    ·
      refine ⟨29420328185614189181733509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19613552123742792787822339 29420328185614189181733509)
      ·
        refine ⟨5516311534802660471575033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29420328185614189181733509 5516311534802660471575033)
        ·
          refine ⟨4137233651101995353681275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5516311534802660471575033 4137233651101995353681275)
          ·
            refine ⟨6205850476652993030521913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137233651101995353681275 6205850476652993030521913)
            ·
              refine ⟨4654387857489744772891435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6205850476652993030521913 4654387857489744772891435)
              ·
                refine ⟨6981581786234617159337153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654387857489744772891435 6981581786234617159337153)
                ·
                  refine ⟨5236186339675962869502865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981581786234617159337153 5236186339675962869502865)
                  ·
                    refine ⟨3927139754756972152127149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5236186339675962869502865 3927139754756972152127149)
                    ·
                      refine ⟨1472677408033864557047681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3927139754756972152127149 1472677408033864557047681)
                      ·
                        rfl

theorem cell23_2868029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2868029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868029 prefixEnd_2868029 := by exact prefixLift 2868029
  have htrace : WordTrace (prefixWord ++ tailWord_2868029) baseStart_2868029 baseEnd_2868029 := by
    simpa [prefixWord, tailWord_2868029, baseEnd_2868029] using wordTrace_append hprefix tailTrace_2868029
  have hstable : (prefixWord ++ tailWord_2868029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868029).length < 2 ^ (prefixWord ++ tailWord_2868029).sum := by decide
  have hdescent : baseEnd_2868029 < baseStart_2868029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868086 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2868086 : Nat := 118140960795 + 2868086 * 2 ^ 59
def prefixEnd_2868086 : Nat := 4983230072969 + 3 ^ 40 * 2868086 * 2
def baseEnd_2868086 : Nat := 1472706676431170834034919

theorem tailTrace_2868086 : CollatzResearch.WordTrace tailWord_2868086 prefixEnd_2868086 1472706676431170834034919 := by
  unfold tailWord_2868086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537980642963857933534007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69738460191614484624362741 6537980642963857933534007)
  ·
    refine ⟨9806970964445786900301011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6537980642963857933534007 9806970964445786900301011)
    ·
      refine ⟨14710456446668680350451517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806970964445786900301011 14710456446668680350451517)
      ·
        refine ⟨5516421167500755131419319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14710456446668680350451517 5516421167500755131419319)
        ·
          refine ⟨8274631751251132697128979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516421167500755131419319 8274631751251132697128979)
          ·
            refine ⟨12411947626876699045693469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274631751251132697128979 12411947626876699045693469)
            ·
              refine ⟨4654480360078762142135051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12411947626876699045693469 4654480360078762142135051)
              ·
                refine ⟨6981720540118143213202577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654480360078762142135051 6981720540118143213202577)
                ·
                  refine ⟨5236290405088607409901933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981720540118143213202577 5236290405088607409901933)
                  ·
                    refine ⟨1963608901908227778713225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5236290405088607409901933 1963608901908227778713225)
                    ·
                      refine ⟨1472706676431170834034919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963608901908227778713225 1472706676431170834034919)
                      ·
                        rfl

theorem cell23_2868086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2868086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868086 prefixEnd_2868086 := by exact prefixLift 2868086
  have htrace : WordTrace (prefixWord ++ tailWord_2868086) baseStart_2868086 baseEnd_2868086 := by
    simpa [prefixWord, tailWord_2868086, baseEnd_2868086] using wordTrace_append hprefix tailTrace_2868086
  have hstable : (prefixWord ++ tailWord_2868086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868086).length < 2 ^ (prefixWord ++ tailWord_2868086).sum := by decide
  have hdescent : baseEnd_2868086 < baseStart_2868086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868095 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_2868095 : Nat := 118140960795 + 2868095 * 2 ^ 59
def prefixEnd_2868095 : Nat := 4983230072969 + 3 ^ 40 * 2868095 * 2
def baseEnd_2868095 : Nat := 1472711297757061298822377

theorem tailTrace_2868095 : CollatzResearch.WordTrace tailWord_2868095 prefixEnd_2868095 1472711297757061298822377 := by
  unfold tailWord_2868095
  simp only [CollatzResearch.WordTrace]
  refine ⟨104608018544389121473621739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69738679029592747649081159 104608018544389121473621739)
  ·
    refine ⟨156912027816583682210432609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104608018544389121473621739 156912027816583682210432609)
    ·
      refine ⟨117684020862437761657824457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156912027816583682210432609 117684020862437761657824457)
      ·
        refine ⟨88263015646828321243368343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117684020862437761657824457 88263015646828321243368343)
        ·
          refine ⟨132394523470242481865052515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88263015646828321243368343 132394523470242481865052515)
          ·
            refine ⟨198591785205363722797578773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132394523470242481865052515 198591785205363722797578773)
            ·
              refine ⟨9308989931501424506136505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198591785205363722797578773 9308989931501424506136505)
              ·
                refine ⟨6981742448626068379602379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9308989931501424506136505 6981742448626068379602379)
                ·
                  refine ⟨10472613672939102569403569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981742448626068379602379 10472613672939102569403569)
                  ·
                    refine ⟨7854460254704326927052677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10472613672939102569403569 7854460254704326927052677)
                    ·
                      refine ⟨1472711297757061298822377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7854460254704326927052677 1472711297757061298822377)
                      ·
                        rfl

theorem cell23_2868095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_2868095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868095 prefixEnd_2868095 := by exact prefixLift 2868095
  have htrace : WordTrace (prefixWord ++ tailWord_2868095) baseStart_2868095 baseEnd_2868095 := by
    simpa [prefixWord, tailWord_2868095, baseEnd_2868095] using wordTrace_append hprefix tailTrace_2868095
  have hstable : (prefixWord ++ tailWord_2868095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868095).length < 2 ^ (prefixWord ++ tailWord_2868095).sum := by decide
  have hdescent : baseEnd_2868095 < baseStart_2868095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868116 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2868116 : Nat := 118140960795 + 2868116 * 2 ^ 59
def prefixEnd_2868116 : Nat := 4983230072969 + 3 ^ 40 * 2868116 * 2
def baseEnd_2868116 : Nat := 1472722080850805716659781

theorem tailTrace_2868116 : CollatzResearch.WordTrace tailWord_2868116 prefixEnd_2868116 1472722080850805716659781 := by
  unfold tailWord_2868116
  simp only [CollatzResearch.WordTrace]
  refine ⟨52304392238656521030068101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69739189651542028040090801 52304392238656521030068101)
  ·
    refine ⟨9807073544748097693137769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52304392238656521030068101 9807073544748097693137769)
    ·
      refine ⟨7355305158561073269853327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9807073544748097693137769 7355305158561073269853327)
      ·
        refine ⟨11032957737841609904779991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7355305158561073269853327 11032957737841609904779991)
        ·
          refine ⟨16549436606762414857169987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032957737841609904779991 16549436606762414857169987)
          ·
            refine ⟨24824154910143622285754981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16549436606762414857169987 24824154910143622285754981)
            ·
              refine ⟨4654529045651929178579059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24824154910143622285754981 4654529045651929178579059)
              ·
                refine ⟨6981793568477893767868589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654529045651929178579059 6981793568477893767868589)
                ·
                  refine ⟨2618172588179210162950721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6981793568477893767868589 2618172588179210162950721)
                  ·
                    refine ⟨1963629441134407622213041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2618172588179210162950721 1963629441134407622213041)
                    ·
                      refine ⟨1472722080850805716659781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963629441134407622213041 1472722080850805716659781)
                      ·
                        rfl

theorem cell23_2868116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2868116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868116 prefixEnd_2868116 := by exact prefixLift 2868116
  have htrace : WordTrace (prefixWord ++ tailWord_2868116) baseStart_2868116 baseEnd_2868116 := by
    simpa [prefixWord, tailWord_2868116, baseEnd_2868116] using wordTrace_append hprefix tailTrace_2868116
  have hstable : (prefixWord ++ tailWord_2868116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868116).length < 2 ^ (prefixWord ++ tailWord_2868116).sum := by decide
  have hdescent : baseEnd_2868116 < baseStart_2868116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868129 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2868129 : Nat := 118140960795 + 2868129 * 2 ^ 59
def prefixEnd_2868129 : Nat := 4983230072969 + 3 ^ 40 * 2868129 * 2
def baseEnd_2868129 : Nat := 1472728756099314165797221

theorem tailTrace_2868129 : CollatzResearch.WordTrace tailWord_2868129 prefixEnd_2868129 1472728756099314165797221 := by
  unfold tailWord_2868129
  simp only [CollatzResearch.WordTrace]
  refine ⟨104609258626265945280359441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69739505750843963520239627 104609258626265945280359441)
  ·
    refine ⟨78456943969699458960269581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104609258626265945280359441 78456943969699458960269581)
    ·
      refine ⟨29421353988637297110101093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78456943969699458960269581 29421353988637297110101093)
      ·
        refine ⟨5516503872869493208143955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29421353988637297110101093 5516503872869493208143955)
        ·
          refine ⟨8274755809304239812215933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516503872869493208143955 8274755809304239812215933)
          ·
            refine ⟨3103033428489089929580975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8274755809304239812215933 3103033428489089929580975)
            ·
              refine ⟨4654550142733634894371463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103033428489089929580975 4654550142733634894371463)
              ·
                refine ⟨6981825214100452341557195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654550142733634894371463 6981825214100452341557195)
                ·
                  refine ⟨10472737821150678512335793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981825214100452341557195 10472737821150678512335793)
                  ·
                    refine ⟨7854553365863008884251845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10472737821150678512335793 7854553365863008884251845)
                    ·
                      refine ⟨1472728756099314165797221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7854553365863008884251845 1472728756099314165797221)
                      ·
                        rfl

theorem cell23_2868129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2868129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868129 prefixEnd_2868129 := by exact prefixLift 2868129
  have htrace : WordTrace (prefixWord ++ tailWord_2868129) baseStart_2868129 baseEnd_2868129 := by
    simpa [prefixWord, tailWord_2868129, baseEnd_2868129] using wordTrace_append hprefix tailTrace_2868129
  have hstable : (prefixWord ++ tailWord_2868129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868129).length < 2 ^ (prefixWord ++ tailWord_2868129).sum := by decide
  have hdescent : baseEnd_2868129 < baseStart_2868129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868195 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 9]
def baseStart_2868195 : Nat := 118140960795 + 2868195 * 2 ^ 59
def prefixEnd_2868195 : Nat := 4983230072969 + 3 ^ 40 * 2868195 * 2
def baseEnd_2868195 : Nat := 163640293980278989730213

theorem tailTrace_2868195 : CollatzResearch.WordTrace tailWord_2868195 prefixEnd_2868195 163640293980278989730213 := by
  unfold tailWord_2868195
  simp only [CollatzResearch.WordTrace]
  refine ⟨104611665844026838552262039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69741110562684559034841359 104611665844026838552262039)
  ·
    refine ⟨156917498766040257828393059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104611665844026838552262039 156917498766040257828393059)
    ·
      refine ⟨235376248149060386742589589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156917498766040257828393059 235376248149060386742589589)
      ·
        refine ⟨11033261631987205628558887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235376248149060386742589589 11033261631987205628558887)
        ·
          refine ⟨16549892447980808442838331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11033261631987205628558887 16549892447980808442838331)
          ·
            refine ⟨24824838671971212664257497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16549892447980808442838331 24824838671971212664257497)
            ·
              refine ⟨18618629003978409498193123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24824838671971212664257497 18618629003978409498193123)
              ·
                refine ⟨27927943505967614247289685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18618629003978409498193123 27927943505967614247289685)
                ·
                  refine ⟨163640293980278989730213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27927943505967614247289685 163640293980278989730213)
                  ·
                    rfl

theorem cell23_2868195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 9].length) (baseStart_2868195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868195 prefixEnd_2868195 := by exact prefixLift 2868195
  have htrace : WordTrace (prefixWord ++ tailWord_2868195) baseStart_2868195 baseEnd_2868195 := by
    simpa [prefixWord, tailWord_2868195, baseEnd_2868195] using wordTrace_append hprefix tailTrace_2868195
  have hstable : (prefixWord ++ tailWord_2868195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868195).length < 2 ^ (prefixWord ++ tailWord_2868195).sum := by decide
  have hdescent : baseEnd_2868195 < baseStart_2868195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868206 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_2868206 : Nat := 118140960795 + 2868206 * 2 ^ 59
def prefixEnd_2868206 : Nat := 4983230072969 + 3 ^ 40 * 2868206 * 2
def baseEnd_2868206 : Nat := 1472768294109710364534367

theorem tailTrace_2868206 : CollatzResearch.WordTrace tailWord_2868206 prefixEnd_2868206 1472768294109710364534367 := by
  unfold tailWord_2868206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076508380873373428864059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69741378031324658287274981 13076508380873373428864059)
  ·
    refine ⟨19614762571310060143296089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13076508380873373428864059 19614762571310060143296089)
    ·
      refine ⟨14711071928482545107472067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19614762571310060143296089 14711071928482545107472067)
      ·
        refine ⟨22066607892723817661208101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14711071928482545107472067 22066607892723817661208101)
        ·
          refine ⟨4137488979885715811476519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22066607892723817661208101 4137488979885715811476519)
          ·
            refine ⟨6206233469828573717214779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137488979885715811476519 6206233469828573717214779)
            ·
              refine ⟨9309350204742860575822169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206233469828573717214779 9309350204742860575822169)
              ·
                refine ⟨6982012653557145431866627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9309350204742860575822169 6982012653557145431866627)
                ·
                  refine ⟨10473018980335718147799941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982012653557145431866627 10473018980335718147799941)
                  ·
                    refine ⟨1963691058812947152712489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10473018980335718147799941 1963691058812947152712489)
                    ·
                      refine ⟨1472768294109710364534367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963691058812947152712489 1472768294109710364534367)
                      ·
                        rfl

theorem cell23_2868206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_2868206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868206 prefixEnd_2868206 := by exact prefixLift 2868206
  have htrace : WordTrace (prefixWord ++ tailWord_2868206) baseStart_2868206 baseEnd_2868206 := by
    simpa [prefixWord, tailWord_2868206, baseEnd_2868206] using wordTrace_append hprefix tailTrace_2868206
  have hstable : (prefixWord ++ tailWord_2868206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868206).length < 2 ^ (prefixWord ++ tailWord_2868206).sum := by decide
  have hdescent : baseEnd_2868206 < baseStart_2868206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868210 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2868210 : Nat := 118140960795 + 2868210 * 2 ^ 59
def prefixEnd_2868210 : Nat := 4983230072969 + 3 ^ 40 * 2868210 * 2
def baseEnd_2868210 : Nat := 1472770348032328348884349

theorem tailTrace_2868210 : CollatzResearch.WordTrace tailWord_2868210 prefixEnd_2868210 1472770348032328348884349 := by
  unfold tailWord_2868210
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153053234743124028514521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69741475292648330742705389 26153053234743124028514521)
  ·
    refine ⟨19614789926057343021385891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26153053234743124028514521 19614789926057343021385891)
    ·
      refine ⟨29422184889086014532078837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19614789926057343021385891 29422184889086014532078837)
      ·
        refine ⟨2758329833351813862382391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29422184889086014532078837 2758329833351813862382391)
        ·
          refine ⟨4137494750027720793573587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758329833351813862382391 4137494750027720793573587)
          ·
            refine ⟨6206242125041581190360381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137494750027720793573587 6206242125041581190360381)
            ·
              refine ⟨2327340796890592946385143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6206242125041581190360381 2327340796890592946385143)
              ·
                refine ⟨3491011195335889419577715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327340796890592946385143 3491011195335889419577715)
                ·
                  refine ⟨5236516793003834129366573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491011195335889419577715 5236516793003834129366573)
                  ·
                    refine ⟨1963693797376437798512465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5236516793003834129366573 1963693797376437798512465)
                    ·
                      refine ⟨1472770348032328348884349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963693797376437798512465 1472770348032328348884349)
                      ·
                        rfl

theorem cell23_2868210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2868210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868210 prefixEnd_2868210 := by exact prefixLift 2868210
  have htrace : WordTrace (prefixWord ++ tailWord_2868210) baseStart_2868210 baseEnd_2868210 := by
    simpa [prefixWord, tailWord_2868210, baseEnd_2868210] using wordTrace_append hprefix tailTrace_2868210
  have hstable : (prefixWord ++ tailWord_2868210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868210).length < 2 ^ (prefixWord ++ tailWord_2868210).sum := by decide
  have hdescent : baseEnd_2868210 < baseStart_2868210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868259 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 2, 5]
def baseStart_2868259 : Nat := 118140960795 + 2868259 * 2 ^ 59
def prefixEnd_2868259 : Nat := 4983230072969 + 3 ^ 40 * 2868259 * 2
def baseEnd_2868259 : Nat := 490931836194799552390541

theorem tailTrace_2868259 : CollatzResearch.WordTrace tailWord_2868259 prefixEnd_2868259 490931836194799552390541 := by
  unfold tailWord_2868259
  simp only [CollatzResearch.WordTrace]
  refine ⟨104614000115794977482591831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69742666743863318321727887 104614000115794977482591831)
  ·
    refine ⟨156921000173692466223887747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104614000115794977482591831 156921000173692466223887747)
    ·
      refine ⟨235381500260538699335831621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156921000173692466223887747 235381500260538699335831621)
      ·
        refine ⟨44134031298851006125468429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235381500260538699335831621 44134031298851006125468429)
        ·
          refine ⟨16550261737069127297050661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44134031298851006125468429 16550261737069127297050661)
          ·
            refine ⟨3103174075700461368196999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16550261737069127297050661 3103174075700461368196999)
            ·
              refine ⟨4654761113550692052295499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103174075700461368196999 4654761113550692052295499)
              ·
                refine ⟨6982141670326038078443249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654761113550692052295499 6982141670326038078443249)
                ·
                  refine ⟨5236606252744528558832437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6982141670326038078443249 5236606252744528558832437)
                  ·
                    refine ⟨490931836194799552390541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5236606252744528558832437 490931836194799552390541)
                    ·
                      rfl

theorem cell23_2868259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 5].length) (baseStart_2868259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868259 prefixEnd_2868259 := by exact prefixLift 2868259
  have htrace : WordTrace (prefixWord ++ tailWord_2868259) baseStart_2868259 baseEnd_2868259 := by
    simpa [prefixWord, tailWord_2868259, baseEnd_2868259] using wordTrace_append hprefix tailTrace_2868259
  have hstable : (prefixWord ++ tailWord_2868259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868259).length < 2 ^ (prefixWord ++ tailWord_2868259).sum := by decide
  have hdescent : baseEnd_2868259 < baseStart_2868259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868272 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_2868272 : Nat := 118140960795 + 2868272 * 2 ^ 59
def prefixEnd_2868272 : Nat := 4983230072969 + 3 ^ 40 * 2868272 * 2
def baseEnd_2868272 : Nat := 490934061277635702103021

theorem tailTrace_2868272 : CollatzResearch.WordTrace tailWord_2868272 prefixEnd_2868272 490934061277635702103021 := by
  unfold tailWord_2868272
  simp only [CollatzResearch.WordTrace]
  refine ⟨52307237132373940351407535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69742982843165253801876713 52307237132373940351407535)
  ·
    refine ⟨78460855698560910527111303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52307237132373940351407535 78460855698560910527111303)
    ·
      refine ⟨117691283547841365790666955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78460855698560910527111303 117691283547841365790666955)
      ·
        refine ⟨176536925321762048686000433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117691283547841365790666955 176536925321762048686000433)
        ·
          refine ⟨132402693991321536514500325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176536925321762048686000433 132402693991321536514500325)
          ·
            refine ⟨24825505123372788096468811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132402693991321536514500325 24825505123372788096468811)
            ·
              refine ⟨37238257685059182144703217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24825505123372788096468811 37238257685059182144703217)
              ·
                refine ⟨27928693263794386608527413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37238257685059182144703217 27928693263794386608527413)
                ·
                  refine ⟨2618314993480723744549445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27928693263794386608527413 2618314993480723744549445)
                  ·
                    refine ⟨490934061277635702103021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618314993480723744549445 490934061277635702103021)
                    ·
                      rfl

theorem cell23_2868272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_2868272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868272 prefixEnd_2868272 := by exact prefixLift 2868272
  have htrace : WordTrace (prefixWord ++ tailWord_2868272) baseStart_2868272 baseEnd_2868272 := by
    simpa [prefixWord, tailWord_2868272, baseEnd_2868272] using wordTrace_append hprefix tailTrace_2868272
  have hstable : (prefixWord ++ tailWord_2868272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868272).length < 2 ^ (prefixWord ++ tailWord_2868272).sum := by decide
  have hdescent : baseEnd_2868272 < baseStart_2868272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868312 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_2868312 : Nat := 118140960795 + 2868312 * 2 ^ 59
def prefixEnd_2868312 : Nat := 4983230072969 + 3 ^ 40 * 2868312 * 2
def baseEnd_2868312 : Nat := 1472822723059086949808879

theorem tailTrace_2868312 : CollatzResearch.WordTrace tailWord_2868312 prefixEnd_2868312 1472822723059086949808879 := by
  unfold tailWord_2868312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52307966592301483767135595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69743955456401978356180793 52307966592301483767135595)
  ·
    refine ⟨78461949888452225650703393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52307966592301483767135595 78461949888452225650703393)
    ·
      refine ⟨58846462416339169238027545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78461949888452225650703393 58846462416339169238027545)
      ·
        refine ⟨44134846812254376928520659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58846462416339169238027545 44134846812254376928520659)
        ·
          refine ⟨66202270218381565392780989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44134846812254376928520659 66202270218381565392780989)
          ·
            refine ⟨24825851331893087022292871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66202270218381565392780989 24825851331893087022292871)
            ·
              refine ⟨37238776997839630533439307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24825851331893087022292871 37238776997839630533439307)
              ·
                refine ⟨55858165496759445800158961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37238776997839630533439307 55858165496759445800158961)
                ·
                  refine ⟨41893624122569584350119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55858165496759445800158961 41893624122569584350119221)
                  ·
                    refine ⟨3927527261490898532823677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41893624122569584350119221 3927527261490898532823677)
                    ·
                      refine ⟨1472822723059086949808879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3927527261490898532823677 1472822723059086949808879)
                      ·
                        rfl

theorem cell23_2868312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_2868312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868312 prefixEnd_2868312 := by exact prefixLift 2868312
  have htrace : WordTrace (prefixWord ++ tailWord_2868312) baseStart_2868312 baseEnd_2868312 := by
    simpa [prefixWord, tailWord_2868312, baseEnd_2868312] using wordTrace_append hprefix tailTrace_2868312
  have hstable : (prefixWord ++ tailWord_2868312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868312).length < 2 ^ (prefixWord ++ tailWord_2868312).sum := by decide
  have hdescent : baseEnd_2868312 < baseStart_2868312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868366 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_2868366 : Nat := 118140960795 + 2868366 * 2 ^ 59
def prefixEnd_2868366 : Nat := 4983230072969 + 3 ^ 40 * 2868366 * 2
def baseEnd_2868366 : Nat := 490950150338143246177877

theorem tailTrace_2868366 : CollatzResearch.WordTrace tailWord_2868366 prefixEnd_2868366 490950150338143246177877 := by
  unfold tailWord_2868366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13077237840800916844592119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69745268484271556504491301 13077237840800916844592119)
  ·
    refine ⟨19615856761201375266888179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13077237840800916844592119 19615856761201375266888179)
    ·
      refine ⟨29423785141802062900332269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19615856761201375266888179 29423785141802062900332269)
      ·
        refine ⟨11033919428175773587624601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29423785141802062900332269 11033919428175773587624601)
        ·
          refine ⟨8275439571131830190718451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11033919428175773587624601 8275439571131830190718451)
          ·
            refine ⟨12413159356697745286077677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275439571131830190718451 12413159356697745286077677)
            ·
              refine ⟨4654934758761654482279129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12413159356697745286077677 4654934758761654482279129)
              ·
                refine ⟨3491201069071240861709347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4654934758761654482279129 3491201069071240861709347)
                ·
                  refine ⟨5236801603606861292564021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491201069071240861709347 5236801603606861292564021)
                  ·
                    refine ⟨490950150338143246177877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5236801603606861292564021 490950150338143246177877)
                    ·
                      rfl

theorem cell23_2868366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_2868366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868366 prefixEnd_2868366 := by exact prefixLift 2868366
  have htrace : WordTrace (prefixWord ++ tailWord_2868366) baseStart_2868366 baseEnd_2868366 := by
    simpa [prefixWord, tailWord_2868366, baseEnd_2868366] using wordTrace_append hprefix tailTrace_2868366
  have hstable : (prefixWord ++ tailWord_2868366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868366).length < 2 ^ (prefixWord ++ tailWord_2868366).sum := by decide
  have hdescent : baseEnd_2868366 < baseStart_2868366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868383 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 1, 5]
def baseStart_2868383 : Nat := 118140960795 + 2868383 * 2 ^ 59
def prefixEnd_2868383 : Nat := 4983230072969 + 3 ^ 40 * 2868383 * 2
def baseEnd_2868383 : Nat := 490953060061852057340351

theorem tailTrace_2868383 : CollatzResearch.WordTrace tailWord_2868383 prefixEnd_2868383 490953060061852057340351 := by
  unfold tailWord_2868383
  simp only [CollatzResearch.WordTrace]
  refine ⟨104618522767345746660105803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69745681844897164440070535 104618522767345746660105803)
  ·
    refine ⟨156927784151018619990158705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104618522767345746660105803 156927784151018619990158705)
    ·
      refine ⟨117695838113263964992619029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156927784151018619990158705 117695838113263964992619029)
      ·
        refine ⟨5516992411559248359029017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117695838113263964992619029 5516992411559248359029017)
        ·
          refine ⟨4137744308669436269271763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5516992411559248359029017 4137744308669436269271763)
          ·
            refine ⟨6206616463004154403907645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137744308669436269271763 6206616463004154403907645)
            ·
              refine ⟨2327481173626557901465367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6206616463004154403907645 2327481173626557901465367)
              ·
                refine ⟨3491221760439836852198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327481173626557901465367 3491221760439836852198051)
                ·
                  refine ⟨5236832640659755278297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491221760439836852198051 5236832640659755278297077)
                  ·
                    refine ⟨490953060061852057340351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5236832640659755278297077 490953060061852057340351)
                    ·
                      rfl

theorem cell23_2868383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_2868383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868383 prefixEnd_2868383 := by exact prefixLift 2868383
  have htrace : WordTrace (prefixWord ++ tailWord_2868383) baseStart_2868383 baseEnd_2868383 := by
    simpa [prefixWord, tailWord_2868383, baseEnd_2868383] using wordTrace_append hprefix tailTrace_2868383
  have hstable : (prefixWord ++ tailWord_2868383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868383).length < 2 ^ (prefixWord ++ tailWord_2868383).sum := by decide
  have hdescent : baseEnd_2868383 < baseStart_2868383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868389 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2868389 : Nat := 118140960795 + 2868389 * 2 ^ 59
def prefixEnd_2868389 : Nat := 4983230072969 + 3 ^ 40 * 2868389 * 2
def baseEnd_2868389 : Nat := 1472862261069483148546025

theorem tailTrace_2868389 : CollatzResearch.WordTrace tailWord_2868389 prefixEnd_2868389 1472862261069483148546025 := by
  unfold tailWord_2868389
  simp only [CollatzResearch.WordTrace]
  refine ⟨104618741605324009684824221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69745827736882673123216147 104618741605324009684824221)
  ·
    refine ⟨39232028101996503631809083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104618741605324009684824221 39232028101996503631809083)
    ·
      refine ⟨58848042152994755447713625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39232028101996503631809083 58848042152994755447713625)
      ·
        refine ⟨44136031614746066585785219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58848042152994755447713625 44136031614746066585785219)
        ·
          refine ⟨66204047422119099878677829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44136031614746066585785219 66204047422119099878677829)
          ·
            refine ⟨12413258891647331227252093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66204047422119099878677829 12413258891647331227252093)
            ·
              refine ⟨4654972084367749210219535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12413258891647331227252093 4654972084367749210219535)
              ·
                refine ⟨6982458126551623815329303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654972084367749210219535 6982458126551623815329303)
                ·
                  refine ⟨10473687189827435722993955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982458126551623815329303 10473687189827435722993955)
                  ·
                    refine ⟨15710530784741153584490933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10473687189827435722993955 15710530784741153584490933)
                    ·
                      refine ⟨1472862261069483148546025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15710530784741153584490933 1472862261069483148546025)
                      ·
                        rfl

theorem cell23_2868389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2868389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868389 prefixEnd_2868389 := by exact prefixLift 2868389
  have htrace : WordTrace (prefixWord ++ tailWord_2868389) baseStart_2868389 baseEnd_2868389 := by
    simpa [prefixWord, tailWord_2868389, baseEnd_2868389] using wordTrace_append hprefix tailTrace_2868389
  have hstable : (prefixWord ++ tailWord_2868389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868389).length < 2 ^ (prefixWord ++ tailWord_2868389).sum := by decide
  have hdescent : baseEnd_2868389 < baseStart_2868389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868409 : List Nat := [1, 2, 1, 4, 1, 5, 1, 8]
def baseStart_2868409 : Nat := 118140960795 + 2868409 * 2 ^ 59
def prefixEnd_2868409 : Nat := 4983230072969 + 3 ^ 40 * 2868409 * 2
def baseEnd_2868409 : Nat := 54550834469724928529479

theorem tailTrace_2868409 : CollatzResearch.WordTrace tailWord_2868409 prefixEnd_2868409 54550834469724928529479 := by
  unfold tailWord_2868409
  simp only [CollatzResearch.WordTrace]
  refine ⟨104619471065251553100552281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69746314043501035400368187 104619471065251553100552281)
  ·
    refine ⟨78464603298938664825414211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104619471065251553100552281 78464603298938664825414211)
    ·
      refine ⟨117696904948407997238121317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78464603298938664825414211 117696904948407997238121317)
      ·
        refine ⟨22068169677826499482147747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117696904948407997238121317 22068169677826499482147747)
        ·
          refine ⟨33102254516739749223221621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22068169677826499482147747 33102254516739749223221621)
          ·
            refine ⟨3103336360944351489677027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33102254516739749223221621 3103336360944351489677027)
            ·
              refine ⟨4655004541416527234515541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103336360944351489677027 4655004541416527234515541)
              ·
                refine ⟨54550834469724928529479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4655004541416527234515541 54550834469724928529479)
                ·
                  rfl

theorem cell23_2868409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 8].length) (baseStart_2868409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868409 prefixEnd_2868409 := by exact prefixLift 2868409
  have htrace : WordTrace (prefixWord ++ tailWord_2868409) baseStart_2868409 baseEnd_2868409 := by
    simpa [prefixWord, tailWord_2868409, baseEnd_2868409] using wordTrace_append hprefix tailTrace_2868409
  have hstable : (prefixWord ++ tailWord_2868409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868409).length < 2 ^ (prefixWord ++ tailWord_2868409).sum := by decide
  have hdescent : baseEnd_2868409 < baseStart_2868409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868416 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_2868416 : Nat := 118140960795 + 2868416 * 2 ^ 59
def prefixEnd_2868416 : Nat := 4983230072969 + 3 ^ 40 * 2868416 * 2
def baseEnd_2868416 : Nat := 1472876125047154542908401

theorem tailTrace_2868416 : CollatzResearch.WordTrace tailWord_2868416 prefixEnd_2868416 1472876125047154542908401 := by
  unfold tailWord_2868416
  simp only [CollatzResearch.WordTrace]
  refine ⟨52309863188113096648028551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69746484250817462197371401 52309863188113096648028551)
  ·
    refine ⟨78464794782169644972042827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52309863188113096648028551 78464794782169644972042827)
    ·
      refine ⟨117697192173254467458064241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78464794782169644972042827 117697192173254467458064241)
      ·
        refine ⟨88272894129940850593548181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117697192173254467458064241 88272894129940850593548181)
        ·
          refine ⟨4137791912340977371572571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88272894129940850593548181 4137791912340977371572571)
          ·
            refine ⟨6206687868511466057358857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137791912340977371572571 6206687868511466057358857)
            ·
              refine ⟨4655015901383599543019143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6206687868511466057358857 4655015901383599543019143)
              ·
                refine ⟨6982523852075399314528715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655015901383599543019143 6982523852075399314528715)
                ·
                  refine ⟨10473785778113098971793073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982523852075399314528715 10473785778113098971793073)
                  ·
                    refine ⟨7855339333584824228844805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10473785778113098971793073 7855339333584824228844805)
                    ·
                      refine ⟨1472876125047154542908401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7855339333584824228844805 1472876125047154542908401)
                      ·
                        rfl

theorem cell23_2868416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_2868416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868416 prefixEnd_2868416 := by exact prefixLift 2868416
  have htrace : WordTrace (prefixWord ++ tailWord_2868416) baseStart_2868416 baseEnd_2868416 := by
    simpa [prefixWord, tailWord_2868416, baseEnd_2868416] using wordTrace_append hprefix tailTrace_2868416
  have hstable : (prefixWord ++ tailWord_2868416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868416).length < 2 ^ (prefixWord ++ tailWord_2868416).sum := by decide
  have hdescent : baseEnd_2868416 < baseStart_2868416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868420 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2868420 : Nat := 118140960795 + 2868420 * 2 ^ 59
def prefixEnd_2868420 : Nat := 4983230072969 + 3 ^ 40 * 2868420 * 2
def baseEnd_2868420 : Nat := 1472878178969772527258383

theorem tailTrace_2868420 : CollatzResearch.WordTrace tailWord_2868420 prefixEnd_2868420 1472878178969772527258383 := by
  unfold tailWord_2868420
  simp only [CollatzResearch.WordTrace]
  refine ⟨52309936134105850989601357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69746581512141134652801809 52309936134105850989601357)
  ·
    refine ⟨19616226050289694121100509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52309936134105850989601357 19616226050289694121100509)
    ·
      refine ⟨7356084768858635295412691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19616226050289694121100509 7356084768858635295412691)
      ·
        refine ⟨11034127153287952943119037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7356084768858635295412691 11034127153287952943119037)
        ·
          refine ⟨4137797682482982353669639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11034127153287952943119037 4137797682482982353669639)
          ·
            refine ⟨6206696523724473530504459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137797682482982353669639 6206696523724473530504459)
            ·
              refine ⟨9310044785586710295756689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206696523724473530504459 9310044785586710295756689)
              ·
                refine ⟨6982533589190032721817517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9310044785586710295756689 6982533589190032721817517)
                ·
                  refine ⟨2618450095946262270681569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6982533589190032721817517 2618450095946262270681569)
                  ·
                    refine ⟨1963837571959696703011177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2618450095946262270681569 1963837571959696703011177)
                    ·
                      refine ⟨1472878178969772527258383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963837571959696703011177 1472878178969772527258383)
                      ·
                        rfl

theorem cell23_2868420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2868420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868420 prefixEnd_2868420 := by exact prefixLift 2868420
  have htrace : WordTrace (prefixWord ++ tailWord_2868420) baseStart_2868420 baseEnd_2868420 := by
    simpa [prefixWord, tailWord_2868420, baseEnd_2868420] using wordTrace_append hprefix tailTrace_2868420
  have hstable : (prefixWord ++ tailWord_2868420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868420).length < 2 ^ (prefixWord ++ tailWord_2868420).sum := by decide
  have hdescent : baseEnd_2868420 < baseStart_2868420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868437 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2868437 : Nat := 118140960795 + 2868437 * 2 ^ 59
def prefixEnd_2868437 : Nat := 4983230072969 + 3 ^ 40 * 2868437 * 2
def baseEnd_2868437 : Nat := 1472886908140898960745805

theorem tailTrace_2868437 : CollatzResearch.WordTrace tailWord_2868437 prefixEnd_2868437 1472886908140898960745805 := by
  unfold tailWord_2868437
  simp only [CollatzResearch.WordTrace]
  refine ⟨104620492309150113882571565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69746994872766742588381043 104620492309150113882571565)
  ·
    refine ⟨39232684615931292705964337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104620492309150113882571565 39232684615931292705964337)
    ·
      refine ⟨29424513461948469529473253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39232684615931292705964337 29424513461948469529473253)
      ·
        refine ⟨5517096274115338036776235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29424513461948469529473253 5517096274115338036776235)
        ·
          refine ⟨8275644411173007055164353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517096274115338036776235 8275644411173007055164353)
          ·
            refine ⟨6206733308379755291373265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8275644411173007055164353 6206733308379755291373265)
            ·
              refine ⟨4655049981284816468529949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6206733308379755291373265 4655049981284816468529949)
              ·
                refine ⟨1745643742981806175698731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4655049981284816468529949 1745643742981806175698731)
                ·
                  refine ⟨2618465614472709263548097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745643742981806175698731 2618465614472709263548097)
                  ·
                    refine ⟨1963849210854531947661073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2618465614472709263548097 1963849210854531947661073)
                    ·
                      refine ⟨1472886908140898960745805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1963849210854531947661073 1472886908140898960745805)
                      ·
                        rfl

theorem cell23_2868437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2868437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868437 prefixEnd_2868437 := by exact prefixLift 2868437
  have htrace : WordTrace (prefixWord ++ tailWord_2868437) baseStart_2868437 baseEnd_2868437 := by
    simpa [prefixWord, tailWord_2868437, baseEnd_2868437] using wordTrace_append hprefix tailTrace_2868437
  have hstable : (prefixWord ++ tailWord_2868437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868437).length < 2 ^ (prefixWord ++ tailWord_2868437).sum := by decide
  have hdescent : baseEnd_2868437 < baseStart_2868437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868440 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_2868440 : Nat := 118140960795 + 2868440 * 2 ^ 59
def prefixEnd_2868440 : Nat := 4983230072969 + 3 ^ 40 * 2868440 * 2
def baseEnd_2868440 : Nat := 1472888448582862449008291

theorem tailTrace_2868440 : CollatzResearch.WordTrace tailWord_2868440 prefixEnd_2868440 1472888448582862449008291 := by
  unfold tailWord_2868440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52310300864069622697465387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69747067818759496929953849 52310300864069622697465387)
  ·
    refine ⟨78465451296104434046198081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52310300864069622697465387 78465451296104434046198081)
    ·
      refine ⟨58849088472078325534648561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78465451296104434046198081 58849088472078325534648561)
      ·
        refine ⟨44136816354058744150986421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58849088472078325534648561 44136816354058744150986421)
        ·
          refine ⟨4137826533193007264154977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44136816354058744150986421 4137826533193007264154977)
          ·
            refine ⟨3103369899894755448116233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4137826533193007264154977 3103369899894755448116233)
            ·
              refine ⟨2327527424921066586087175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3103369899894755448116233 2327527424921066586087175)
              ·
                refine ⟨3491291137381599879130763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327527424921066586087175 3491291137381599879130763)
                ·
                  refine ⟨5236936706072399818696145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491291137381599879130763 5236936706072399818696145)
                  ·
                    refine ⟨3927702529554299864022109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5236936706072399818696145 3927702529554299864022109)
                    ·
                      refine ⟨1472888448582862449008291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3927702529554299864022109 1472888448582862449008291)
                      ·
                        rfl

theorem cell23_2868440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_2868440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868440 prefixEnd_2868440 := by exact prefixLift 2868440
  have htrace : WordTrace (prefixWord ++ tailWord_2868440) baseStart_2868440 baseEnd_2868440 := by
    simpa [prefixWord, tailWord_2868440, baseEnd_2868440] using wordTrace_append hprefix tailTrace_2868440
  have hstable : (prefixWord ++ tailWord_2868440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868440).length < 2 ^ (prefixWord ++ tailWord_2868440).sum := by decide
  have hdescent : baseEnd_2868440 < baseStart_2868440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868453 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2868453 : Nat := 118140960795 + 2868453 * 2 ^ 59
def prefixEnd_2868453 : Nat := 4983230072969 + 3 ^ 40 * 2868453 * 2
def baseEnd_2868453 : Nat := 1472895123831370898145731

theorem tailTrace_2868453 : CollatzResearch.WordTrace tailWord_2868453 prefixEnd_2868453 1472895123831370898145731 := by
  unfold tailWord_2868453
  simp only [CollatzResearch.WordTrace]
  refine ⟨104621075877092148615154013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69747383918061432410102675 104621075877092148615154013)
  ·
    refine ⟨39232903453909555730682755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104621075877092148615154013 39232903453909555730682755)
    ·
      refine ⟨58849355180864333596024133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39232903453909555730682755 58849355180864333596024133)
      ·
        refine ⟨11034254096412062549254525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58849355180864333596024133 11034254096412062549254525)
        ·
          refine ⟨4137845286154523455970447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11034254096412062549254525 4137845286154523455970447)
          ·
            refine ⟨6206767929231785183955671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137845286154523455970447 6206767929231785183955671)
            ·
              refine ⟨9310151893847677775933507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206767929231785183955671 9310151893847677775933507)
              ·
                refine ⟨13965227840771516663900261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9310151893847677775933507 13965227840771516663900261)
                ·
                  refine ⟨2618480220144659374481299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13965227840771516663900261 2618480220144659374481299)
                  ·
                    refine ⟨3927720330216989061721949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618480220144659374481299 3927720330216989061721949)
                    ·
                      refine ⟨1472895123831370898145731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3927720330216989061721949 1472895123831370898145731)
                      ·
                        rfl

theorem cell23_2868453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2868453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868453 prefixEnd_2868453 := by exact prefixLift 2868453
  have htrace : WordTrace (prefixWord ++ tailWord_2868453) baseStart_2868453 baseEnd_2868453 := by
    simpa [prefixWord, tailWord_2868453, baseEnd_2868453] using wordTrace_append hprefix tailTrace_2868453
  have hstable : (prefixWord ++ tailWord_2868453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868453).length < 2 ^ (prefixWord ++ tailWord_2868453).sum := by decide
  have hdescent : baseEnd_2868453 < baseStart_2868453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868549 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2868549 : Nat := 118140960795 + 2868549 * 2 ^ 59
def prefixEnd_2868549 : Nat := 4983230072969 + 3 ^ 40 * 2868549 * 2
def baseEnd_2868549 : Nat := 1472944417974202522545289

theorem tailTrace_2868549 : CollatzResearch.WordTrace tailWord_2868549 prefixEnd_2868549 1472944417974202522545289 := by
  unfold tailWord_2868549
  simp only [CollatzResearch.WordTrace]
  refine ⟨104624577284744357010648701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69749718189829571340432467 104624577284744357010648701)
  ·
    refine ⟨39234216481779133878993263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104624577284744357010648701 39234216481779133878993263)
    ·
      refine ⟨58851324722668700818489895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39234216481779133878993263 58851324722668700818489895)
      ·
        refine ⟨88276987084003051227734843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58851324722668700818489895 88276987084003051227734843)
        ·
          refine ⟨132415480626004576841602265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88276987084003051227734843 132415480626004576841602265)
          ·
            refine ⟨99311610469503432631201699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132415480626004576841602265 99311610469503432631201699)
            ·
              refine ⟨148967415704255148946802549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99311610469503432631201699 148967415704255148946802549)
              ·
                refine ⟨13965695222273920213762739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148967415704255148946802549 13965695222273920213762739)
                ·
                  refine ⟨20948542833410880320644109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13965695222273920213762739 20948542833410880320644109)
                  ·
                    refine ⟨7855703562529080120241541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20948542833410880320644109 7855703562529080120241541)
                    ·
                      refine ⟨1472944417974202522545289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7855703562529080120241541 1472944417974202522545289)
                      ·
                        rfl

theorem cell23_2868549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2868549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868549 prefixEnd_2868549 := by exact prefixLift 2868549
  have htrace : WordTrace (prefixWord ++ tailWord_2868549) baseStart_2868549 baseEnd_2868549 := by
    simpa [prefixWord, tailWord_2868549, baseEnd_2868549] using wordTrace_append hprefix tailTrace_2868549
  have hstable : (prefixWord ++ tailWord_2868549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868549).length < 2 ^ (prefixWord ++ tailWord_2868549).sum := by decide
  have hdescent : baseEnd_2868549 < baseStart_2868549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868633 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 3]
def baseStart_2868633 : Nat := 118140960795 + 2868633 * 2 ^ 59
def prefixEnd_2868633 : Nat := 4983230072969 + 3 ^ 40 * 2868633 * 2
def baseEnd_2868633 : Nat := 1472987550349180193894903

theorem tailTrace_2868633 : CollatzResearch.WordTrace tailWord_2868633 prefixEnd_2868633 1472987550349180193894903 := by
  unfold tailWord_2868633
  simp only [CollatzResearch.WordTrace]
  refine ⟨104627641016440039356706553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69751760677626692904471035 104627641016440039356706553)
  ·
    refine ⟨78470730762330029517529915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104627641016440039356706553 78470730762330029517529915)
    ·
      refine ⟨117706096143495044276294873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78470730762330029517529915 117706096143495044276294873)
      ·
        refine ⟨88279572107621283207221155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117706096143495044276294873 88279572107621283207221155)
        ·
          refine ⟨132419358161431924810831733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88279572107621283207221155 132419358161431924810831733)
          ·
            refine ⟨12414314827634242951015475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132419358161431924810831733 12414314827634242951015475)
            ·
              refine ⟨18621472241451364426523213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12414314827634242951015475 18621472241451364426523213)
              ·
                refine ⟨6983052090544261659946205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18621472241451364426523213 6983052090544261659946205)
                ·
                  refine ⟨2618644533954098122479827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6983052090544261659946205 2618644533954098122479827)
                  ·
                    refine ⟨3927966800931147183719741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618644533954098122479827 3927966800931147183719741)
                    ·
                      refine ⟨1472987550349180193894903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3927966800931147183719741 1472987550349180193894903)
                      ·
                        rfl

theorem cell23_2868633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_2868633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868633 prefixEnd_2868633 := by exact prefixLift 2868633
  have htrace : WordTrace (prefixWord ++ tailWord_2868633) baseStart_2868633 baseEnd_2868633 := by
    simpa [prefixWord, tailWord_2868633, baseEnd_2868633] using wordTrace_append hprefix tailTrace_2868633
  have hstable : (prefixWord ++ tailWord_2868633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868633).length < 2 ^ (prefixWord ++ tailWord_2868633).sum := by decide
  have hdescent : baseEnd_2868633 < baseStart_2868633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868684 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 1, 1, 3]
def baseStart_2868684 : Nat := 118140960795 + 2868684 * 2 ^ 59
def prefixEnd_2868684 : Nat := 4983230072969 + 3 ^ 40 * 2868684 * 2
def baseEnd_2868684 : Nat := 1473013737862559494357169

theorem tailTrace_2868684 : CollatzResearch.WordTrace tailWord_2868684 prefixEnd_2868684 1473013737862559494357169 := by
  unfold tailWord_2868684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52314750569627637533406553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69753000759503516711208737 52314750569627637533406553)
  ·
    refine ⟨39236062927220728150054915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52314750569627637533406553 39236062927220728150054915)
    ·
      refine ⟨58854094390831092225082373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39236062927220728150054915 58854094390831092225082373)
      ·
        refine ⟨11035142698280829792202945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58854094390831092225082373 11035142698280829792202945)
        ·
          refine ⟨8276357023710622344152209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11035142698280829792202945 8276357023710622344152209)
          ·
            refine ⟨6207267767782966758114157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8276357023710622344152209 6207267767782966758114157)
            ·
              refine ⟨2327725412918612534292809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6207267767782966758114157 2327725412918612534292809)
              ·
                refine ⟨1745794059688959400719607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327725412918612534292809 1745794059688959400719607)
                ·
                  refine ⟨2618691089533439101079411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745794059688959400719607 2618691089533439101079411)
                  ·
                    refine ⟨3928036634300158651619117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618691089533439101079411 3928036634300158651619117)
                    ·
                      refine ⟨1473013737862559494357169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928036634300158651619117 1473013737862559494357169)
                      ·
                        rfl

theorem cell23_2868684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_2868684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868684 prefixEnd_2868684 := by exact prefixLift 2868684
  have htrace : WordTrace (prefixWord ++ tailWord_2868684) baseStart_2868684 baseEnd_2868684 := by
    simpa [prefixWord, tailWord_2868684, baseEnd_2868684] using wordTrace_append hprefix tailTrace_2868684
  have hstable : (prefixWord ++ tailWord_2868684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868684).length < 2 ^ (prefixWord ++ tailWord_2868684).sum := by decide
  have hdescent : baseEnd_2868684 < baseStart_2868684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868686 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2868686 : Nat := 118140960795 + 2868686 * 2 ^ 59
def prefixEnd_2868686 : Nat := 4983230072969 + 3 ^ 40 * 2868686 * 2
def baseEnd_2868686 : Nat := 1473014764823868486532159

theorem tailTrace_2868686 : CollatzResearch.WordTrace tailWord_2868686 prefixEnd_2868686 1473014764823868486532159 := by
  unfold tailWord_2868686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078696760656003676048239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69753049390165352938923941 13078696760656003676048239)
  ·
    refine ⟨19618045140984005514072359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13078696760656003676048239 19618045140984005514072359)
    ·
      refine ⟨29427067711476008271108539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19618045140984005514072359 29427067711476008271108539)
      ·
        refine ⟨44140601567214012406662809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29427067711476008271108539 44140601567214012406662809)
        ·
          refine ⟨33105451175410509304997107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44140601567214012406662809 33105451175410509304997107)
          ·
            refine ⟨49658176763115763957495661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33105451175410509304997107 49658176763115763957495661)
            ·
              refine ⟨18621816286168411484060873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49658176763115763957495661 18621816286168411484060873)
              ·
                refine ⟨13966362214626308613045655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18621816286168411484060873 13966362214626308613045655)
                ·
                  refine ⟨20949543321939462919568483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13966362214626308613045655 20949543321939462919568483)
                  ·
                    refine ⟨31424314982909194379352725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20949543321939462919568483 31424314982909194379352725)
                    ·
                      refine ⟨1473014764823868486532159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31424314982909194379352725 1473014764823868486532159)
                      ·
                        rfl

theorem cell23_2868686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2868686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868686 prefixEnd_2868686 := by exact prefixLift 2868686
  have htrace : WordTrace (prefixWord ++ tailWord_2868686) baseStart_2868686 baseEnd_2868686 := by
    simpa [prefixWord, tailWord_2868686, baseEnd_2868686] using wordTrace_append hprefix tailTrace_2868686
  have hstable : (prefixWord ++ tailWord_2868686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868686).length < 2 ^ (prefixWord ++ tailWord_2868686).sum := by decide
  have hdescent : baseEnd_2868686 < baseStart_2868686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868693 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2868693 : Nat := 118140960795 + 2868693 * 2 ^ 59
def prefixEnd_2868693 : Nat := 4983230072969 + 3 ^ 40 * 2868693 * 2
def baseEnd_2868693 : Nat := 1473018359188449959144627

theorem tailTrace_2868693 : CollatzResearch.WordTrace tailWord_2868693 prefixEnd_2868693 1473018359188449959144627 := by
  unfold tailWord_2868693
  simp only [CollatzResearch.WordTrace]
  refine ⟨104629829396222669603890733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69753219597481779735927155 104629829396222669603890733)
  ·
    refine ⟨39236186023583501101459025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104629829396222669603890733 39236186023583501101459025)
    ·
      refine ⟨29427139517687625826094269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39236186023583501101459025 29427139517687625826094269)
      ·
        refine ⟨11035177319132859684785351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29427139517687625826094269 11035177319132859684785351)
        ·
          refine ⟨16552765978699289527178027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11035177319132859684785351 16552765978699289527178027)
          ·
            refine ⟨24829148968048934290767041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16552765978699289527178027 24829148968048934290767041)
            ·
              refine ⟨18621861726036700718075281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24829148968048934290767041 18621861726036700718075281)
              ·
                refine ⟨13966396294527525538556461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18621861726036700718075281 13966396294527525538556461)
                ·
                  refine ⟨5237398610447822076958673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13966396294527525538556461 5237398610447822076958673)
                  ·
                    refine ⟨3928048957835866557719005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5237398610447822076958673 3928048957835866557719005)
                    ·
                      refine ⟨1473018359188449959144627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928048957835866557719005 1473018359188449959144627)
                      ·
                        rfl

theorem cell23_2868693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2868693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868693 prefixEnd_2868693 := by exact prefixLift 2868693
  have htrace : WordTrace (prefixWord ++ tailWord_2868693) baseStart_2868693 baseEnd_2868693 := by
    simpa [prefixWord, tailWord_2868693, baseEnd_2868693] using wordTrace_append hprefix tailTrace_2868693
  have hstable : (prefixWord ++ tailWord_2868693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868693).length < 2 ^ (prefixWord ++ tailWord_2868693).sum := by decide
  have hdescent : baseEnd_2868693 < baseStart_2868693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868723 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 3]
def baseStart_2868723 : Nat := 118140960795 + 2868723 * 2 ^ 59
def prefixEnd_2868723 : Nat := 4983230072969 + 3 ^ 40 * 2868723 * 2
def baseEnd_2868723 : Nat := 1473033763608084841769489

theorem tailTrace_2868723 : CollatzResearch.WordTrace tailWord_2868723 prefixEnd_2868723 1473033763608084841769489 := by
  unfold tailWord_2868723
  simp only [CollatzResearch.WordTrace]
  refine ⟨104630923586113984727482823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69753949057409323151655215 104630923586113984727482823)
  ·
    refine ⟨156946385379170977091224235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104630923586113984727482823 156946385379170977091224235)
    ·
      refine ⟨235419578068756465636836353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156946385379170977091224235 235419578068756465636836353)
      ·
        refine ⟨176564683551567349227627265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235419578068756465636836353 176564683551567349227627265)
        ·
          refine ⟨132423512663675511920720449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176564683551567349227627265 132423512663675511920720449)
          ·
            refine ⟨99317634497756633940540337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132423512663675511920720449 99317634497756633940540337)
            ·
              refine ⟨74488225873317475455405253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99317634497756633940540337 74488225873317475455405253)
              ·
                refine ⟨13966542351247026647888485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74488225873317475455405253 13966542351247026647888485)
                ·
                  refine ⟨2618726690858817496479091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13966542351247026647888485 2618726690858817496479091)
                  ·
                    refine ⟨3928090036288226244718637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618726690858817496479091 3928090036288226244718637)
                    ·
                      refine ⟨1473033763608084841769489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928090036288226244718637 1473033763608084841769489)
                      ·
                        rfl

theorem cell23_2868723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_2868723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868723 prefixEnd_2868723 := by exact prefixLift 2868723
  have htrace : WordTrace (prefixWord ++ tailWord_2868723) baseStart_2868723 baseEnd_2868723 := by
    simpa [prefixWord, tailWord_2868723, baseEnd_2868723] using wordTrace_append hprefix tailTrace_2868723
  have hstable : (prefixWord ++ tailWord_2868723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868723).length < 2 ^ (prefixWord ++ tailWord_2868723).sum := by decide
  have hdescent : baseEnd_2868723 < baseStart_2868723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868734 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2868734 : Nat := 118140960795 + 2868734 * 2 ^ 59
def prefixEnd_2868734 : Nat := 4983230072969 + 3 ^ 40 * 2868734 * 2
def baseEnd_2868734 : Nat := 491013137298428099577313

theorem tailTrace_2868734 : CollatzResearch.WordTrace tailWord_2868734 prefixEnd_2868734 491013137298428099577313 := by
  unfold tailWord_2868734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078915598634266700766657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69754216526049422404088837 13078915598634266700766657)
  ·
    refine ⟨9809186698975700025574993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13078915598634266700766657 9809186698975700025574993)
    ·
      refine ⟨7356890024231775019181245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9809186698975700025574993 7356890024231775019181245)
      ·
        refine ⟨2758833759086915632192967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7356890024231775019181245 2758833759086915632192967)
        ·
          refine ⟨4138250638630373448289451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758833759086915632192967 4138250638630373448289451)
          ·
            refine ⟨6207375957945560172434177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138250638630373448289451 6207375957945560172434177)
            ·
              refine ⟨4655531968459170129325633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6207375957945560172434177 4655531968459170129325633)
              ·
                refine ⟨3491648976344377596994225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655531968459170129325633 3491648976344377596994225)
                ·
                  refine ⟨2618736732258283197745669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3491648976344377596994225 2618736732258283197745669)
                  ·
                    refine ⟨491013137298428099577313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618736732258283197745669 491013137298428099577313)
                    ·
                      rfl

theorem cell23_2868734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2868734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868734 prefixEnd_2868734 := by exact prefixLift 2868734
  have htrace : WordTrace (prefixWord ++ tailWord_2868734) baseStart_2868734 baseEnd_2868734 := by
    simpa [prefixWord, tailWord_2868734, baseEnd_2868734] using wordTrace_append hprefix tailTrace_2868734
  have hstable : (prefixWord ++ tailWord_2868734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868734).length < 2 ^ (prefixWord ++ tailWord_2868734).sum := by decide
  have hdescent : baseEnd_2868734 < baseStart_2868734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868786 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_2868786 : Nat := 118140960795 + 2868786 * 2 ^ 59
def prefixEnd_2868786 : Nat := 4983230072969 + 3 ^ 40 * 2868786 * 2
def baseEnd_2868786 : Nat := 163674012543257566142411

theorem tailTrace_2868786 : CollatzResearch.WordTrace tailWord_2868786 prefixEnd_2868786 163674012543257566142411 := by
  unfold tailWord_2868786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158305346221436621756553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69755480923257164324684141 26158305346221436621756553)
  ·
    refine ⟨19618729009666077466317415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26158305346221436621756553 19618729009666077466317415)
    ·
      refine ⟨29428093514499116199476123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19618729009666077466317415 29428093514499116199476123)
      ·
        refine ⟨44142140271748674299214185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29428093514499116199476123 44142140271748674299214185)
        ·
          refine ⟨33106605203811505724410639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44142140271748674299214185 33106605203811505724410639)
          ·
            refine ⟨49659907805717258586615959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33106605203811505724410639 49659907805717258586615959)
            ·
              refine ⟨74489861708575887879923939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49659907805717258586615959 74489861708575887879923939)
              ·
                refine ⟨111734792562863831819885909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74489861708575887879923939 111734792562863831819885909)
                ·
                  refine ⟨163674012543257566142411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 111734792562863831819885909 163674012543257566142411)
                  ·
                    rfl

theorem cell23_2868786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_2868786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868786 prefixEnd_2868786 := by exact prefixLift 2868786
  have htrace : WordTrace (prefixWord ++ tailWord_2868786) baseStart_2868786 baseEnd_2868786 := by
    simpa [prefixWord, tailWord_2868786, baseEnd_2868786] using wordTrace_append hprefix tailTrace_2868786
  have hstable : (prefixWord ++ tailWord_2868786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868786).length < 2 ^ (prefixWord ++ tailWord_2868786).sum := by decide
  have hdescent : baseEnd_2868786 < baseStart_2868786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868793 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2868793 : Nat := 118140960795 + 2868793 * 2 ^ 59
def prefixEnd_2868793 : Nat := 4983230072969 + 3 ^ 40 * 2868793 * 2
def baseEnd_2868793 : Nat := 1473069707253899567894167

theorem tailTrace_2868793 : CollatzResearch.WordTrace tailWord_2868793 prefixEnd_2868793 1473069707253899567894167 := by
  unfold tailWord_2868793
  simp only [CollatzResearch.WordTrace]
  refine ⟨104633476695860386682531033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69755651130573591121687355 104633476695860386682531033)
  ·
    refine ⟨78475107521895290011898275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104633476695860386682531033 78475107521895290011898275)
    ·
      refine ⟨117712661282842935017847413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78475107521895290011898275 117712661282842935017847413)
      ·
        refine ⟨11035561995266525157923195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117712661282842935017847413 11035561995266525157923195)
        ·
          refine ⟨16553342992899787736884793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11035561995266525157923195 16553342992899787736884793)
          ·
            refine ⟨12415007244674840802663595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16553342992899787736884793 12415007244674840802663595)
            ·
              refine ⟨18622510867012261203995393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415007244674840802663595 18622510867012261203995393)
              ·
                refine ⟨13966883150259195902996545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18622510867012261203995393 13966883150259195902996545)
                ·
                  refine ⟨10475162362694396927247409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13966883150259195902996545 10475162362694396927247409)
                  ·
                    refine ⟨7856371772020797695435557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10475162362694396927247409 7856371772020797695435557)
                    ·
                      refine ⟨1473069707253899567894167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7856371772020797695435557 1473069707253899567894167)
                      ·
                        rfl

theorem cell23_2868793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2868793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868793 prefixEnd_2868793 := by exact prefixLift 2868793
  have htrace : WordTrace (prefixWord ++ tailWord_2868793) baseStart_2868793 baseEnd_2868793 := by
    simpa [prefixWord, tailWord_2868793, baseEnd_2868793] using wordTrace_append hprefix tailTrace_2868793
  have hstable : (prefixWord ++ tailWord_2868793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868793).length < 2 ^ (prefixWord ++ tailWord_2868793).sum := by decide
  have hdescent : baseEnd_2868793 < baseStart_2868793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868816 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_2868816 : Nat := 118140960795 + 2868816 * 2 ^ 59
def prefixEnd_2868816 : Nat := 4983230072969 + 3 ^ 40 * 2868816 * 2
def baseEnd_2868816 : Nat := 491027172436317659302187

theorem tailTrace_2868816 : CollatzResearch.WordTrace tailWord_2868816 prefixEnd_2868816 491027172436317659302187 := by
  unfold tailWord_2868816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52317157787388530805309151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69756210383184707740412201 52317157787388530805309151)
  ·
    refine ⟨78475736681082796207963727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52317157787388530805309151 78475736681082796207963727)
    ·
      refine ⟨117713605021624194311945591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78475736681082796207963727 117713605021624194311945591)
      ·
        refine ⟨176570407532436291467918387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117713605021624194311945591 176570407532436291467918387)
        ·
          refine ⟨264855611298654437201877581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176570407532436291467918387 264855611298654437201877581)
          ·
            refine ⟨99320854236995413950704093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264855611298654437201877581 99320854236995413950704093)
            ·
              refine ⟨37245320338873280231514035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99320854236995413950704093 37245320338873280231514035)
              ·
                refine ⟨55867980508309920347271053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37245320338873280231514035 55867980508309920347271053)
                ·
                  refine ⟨20950492690616220130226645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55867980508309920347271053 20950492690616220130226645)
                  ·
                    refine ⟨491027172436317659302187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20950492690616220130226645 491027172436317659302187)
                    ·
                      rfl

theorem cell23_2868816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_2868816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868816 prefixEnd_2868816 := by exact prefixLift 2868816
  have htrace : WordTrace (prefixWord ++ tailWord_2868816) baseStart_2868816 baseEnd_2868816 := by
    simpa [prefixWord, tailWord_2868816, baseEnd_2868816] using wordTrace_append hprefix tailTrace_2868816
  have hstable : (prefixWord ++ tailWord_2868816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868816).length < 2 ^ (prefixWord ++ tailWord_2868816).sum := by decide
  have hdescent : baseEnd_2868816 < baseStart_2868816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868833 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2868833 : Nat := 118140960795 + 2868833 * 2 ^ 59
def prefixEnd_2868833 : Nat := 4983230072969 + 3 ^ 40 * 2868833 * 2
def baseEnd_2868833 : Nat := 491030082160026470464661

theorem tailTrace_2868833 : CollatzResearch.WordTrace tailWord_2868833 prefixEnd_2868833 491030082160026470464661 := by
  unfold tailWord_2868833
  simp only [CollatzResearch.WordTrace]
  refine ⟨104634935615715473513987153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69756623743810315675991435 104634935615715473513987153)
  ·
    refine ⟨78476201711786605135490365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104634935615715473513987153 78476201711786605135490365)
    ·
      refine ⟨29428575641919976925808887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78476201711786605135490365 29428575641919976925808887)
      ·
        refine ⟨44142863462879965388713331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29428575641919976925808887 44142863462879965388713331)
        ·
          refine ⟨66214295194319948083069997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44142863462879965388713331 66214295194319948083069997)
          ·
            refine ⟨24830360697869980531151249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66214295194319948083069997 24830360697869980531151249)
            ·
              refine ⟨18622770523402485398363437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24830360697869980531151249 18622770523402485398363437)
              ·
                refine ⟨6983538946275932024386289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18622770523402485398363437 6983538946275932024386289)
                ·
                  refine ⟨5237654209706949018289717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6983538946275932024386289 5237654209706949018289717)
                  ·
                    refine ⟨491030082160026470464661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5237654209706949018289717 491030082160026470464661)
                    ·
                      rfl

theorem cell23_2868833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2868833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868833 prefixEnd_2868833 := by exact prefixLift 2868833
  have htrace : WordTrace (prefixWord ++ tailWord_2868833) baseStart_2868833 baseEnd_2868833 := by
    simpa [prefixWord, tailWord_2868833, baseEnd_2868833] using wordTrace_append hprefix tailTrace_2868833
  have hstable : (prefixWord ++ tailWord_2868833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868833).length < 2 ^ (prefixWord ++ tailWord_2868833).sum := by decide
  have hdescent : baseEnd_2868833 < baseStart_2868833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868837 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 5]
def baseStart_2868837 : Nat := 118140960795 + 2868837 * 2 ^ 59
def prefixEnd_2868837 : Nat := 4983230072969 + 3 ^ 40 * 2868837 * 2
def baseEnd_2868837 : Nat := 163676922266966377304885

theorem tailTrace_2868837 : CollatzResearch.WordTrace tailWord_2868837 prefixEnd_2868837 163676922266966377304885 := by
  unfold tailWord_2868837
  simp only [CollatzResearch.WordTrace]
  refine ⟨104635081507700982197132765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69756721005133988131421843 104635081507700982197132765)
  ·
    refine ⟨39238155565387868323924787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104635081507700982197132765 39238155565387868323924787)
    ·
      refine ⟨58857233348081802485887181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39238155565387868323924787 58857233348081802485887181)
      ·
        refine ⟨22071462505530675932207693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58857233348081802485887181 22071462505530675932207693)
        ·
          refine ⟨8276798439574003474577885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22071462505530675932207693 8276798439574003474577885)
          ·
            refine ⟨3103799414840251302966707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8276798439574003474577885 3103799414840251302966707)
            ·
              refine ⟨4655699122260376954450061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103799414840251302966707 4655699122260376954450061)
              ·
                refine ⟨1745887170847641357918773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4655699122260376954450061 1745887170847641357918773)
                ·
                  refine ⟨163676922266966377304885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1745887170847641357918773 163676922266966377304885)
                  ·
                    rfl

theorem cell23_2868837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_2868837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868837 prefixEnd_2868837 := by exact prefixLift 2868837
  have htrace : WordTrace (prefixWord ++ tailWord_2868837) baseStart_2868837 baseEnd_2868837 := by
    simpa [prefixWord, tailWord_2868837, baseEnd_2868837] using wordTrace_append hprefix tailTrace_2868837
  have hstable : (prefixWord ++ tailWord_2868837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868837).length < 2 ^ (prefixWord ++ tailWord_2868837).sum := by decide
  have hdescent : baseEnd_2868837 < baseStart_2868837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868850 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_2868850 : Nat := 118140960795 + 2868850 * 2 ^ 59
def prefixEnd_2868850 : Nat := 4983230072969 + 3 ^ 40 * 2868850 * 2
def baseEnd_2868850 : Nat := 491032991883735281627135

theorem tailTrace_2868850 : CollatzResearch.WordTrace tailWord_2868850 prefixEnd_2868850 491032991883735281627135 := by
  unfold tailWord_2868850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158888914163471354339001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69757037104435923611570669 26158888914163471354339001)
  ·
    refine ⟨19619166685622603515754251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26158888914163471354339001 19619166685622603515754251)
    ·
      refine ⟨29428750028433905273631377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19619166685622603515754251 29428750028433905273631377)
      ·
        refine ⟨22071562521325428955223533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29428750028433905273631377 22071562521325428955223533)
        ·
          refine ⟨8276835945497035858208825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22071562521325428955223533 8276835945497035858208825)
          ·
            refine ⟨6207626959122776893656619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8276835945497035858208825 6207626959122776893656619)
            ·
              refine ⟨9311440438684165340484929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6207626959122776893656619 9311440438684165340484929)
              ·
                refine ⟨6983580329013124005363697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9311440438684165340484929 6983580329013124005363697)
                ·
                  refine ⟨5237685246759843004022773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6983580329013124005363697 5237685246759843004022773)
                  ·
                    refine ⟨491032991883735281627135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5237685246759843004022773 491032991883735281627135)
                    ·
                      rfl

theorem cell23_2868850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_2868850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868850 prefixEnd_2868850 := by exact prefixLift 2868850
  have htrace : WordTrace (prefixWord ++ tailWord_2868850) baseStart_2868850 baseEnd_2868850 := by
    simpa [prefixWord, tailWord_2868850, baseEnd_2868850] using wordTrace_append hprefix tailTrace_2868850
  have hstable : (prefixWord ++ tailWord_2868850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868850).length < 2 ^ (prefixWord ++ tailWord_2868850).sum := by decide
  have hdescent : baseEnd_2868850 < baseStart_2868850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868854 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2868854 : Nat := 118140960795 + 2868854 * 2 ^ 59
def prefixEnd_2868854 : Nat := 4983230072969 + 3 ^ 40 * 2868854 * 2
def baseEnd_2868854 : Nat := 163677892174869314359043

theorem tailTrace_2868854 : CollatzResearch.WordTrace tailWord_2868854 prefixEnd_2868854 163677892174869314359043 := by
  unfold tailWord_2868854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6539731346789962131281351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69757134365759596067001077 6539731346789962131281351)
  ·
    refine ⟨9809597020184943196922027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6539731346789962131281351 9809597020184943196922027)
    ·
      refine ⟨14714395530277414795383041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9809597020184943196922027 14714395530277414795383041)
      ·
        refine ⟨11035796647708061096537281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14714395530277414795383041 11035796647708061096537281)
        ·
          refine ⟨8276847485781045822402961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11035796647708061096537281 8276847485781045822402961)
          ·
            refine ⟨6207635614335784366802221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8276847485781045822402961 6207635614335784366802221)
            ·
              refine ⟨2327863355375919137550833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6207635614335784366802221 2327863355375919137550833)
              ·
                refine ⟨1745897516531939353163125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327863355375919137550833 1745897516531939353163125)
                ·
                  refine ⟨163677892174869314359043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1745897516531939353163125 163677892174869314359043)
                  ·
                    rfl

theorem cell23_2868854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2868854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868854 prefixEnd_2868854 := by exact prefixLift 2868854
  have htrace : WordTrace (prefixWord ++ tailWord_2868854) baseStart_2868854 baseEnd_2868854 := by
    simpa [prefixWord, tailWord_2868854, baseEnd_2868854] using wordTrace_append hprefix tailTrace_2868854
  have hstable : (prefixWord ++ tailWord_2868854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868854).length < 2 ^ (prefixWord ++ tailWord_2868854).sum := by decide
  have hdescent : baseEnd_2868854 < baseStart_2868854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868873 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_2868873 : Nat := 118140960795 + 2868873 * 2 ^ 59
def prefixEnd_2868873 : Nat := 4983230072969 + 3 ^ 40 * 2868873 * 2
def baseEnd_2868873 : Nat := 1473110785706259254893799

theorem tailTrace_2868873 : CollatzResearch.WordTrace tailWord_2868873 prefixEnd_2868873 1473110785706259254893799 := by
  unfold tailWord_2868873
  simp only [CollatzResearch.WordTrace]
  refine ⟨104636394535570560345443273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69757596357047040230295515 104636394535570560345443273)
  ·
    refine ⟨78477295901677920259082455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104636394535570560345443273 78477295901677920259082455)
    ·
      refine ⟨117715943852516880388623683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78477295901677920259082455 117715943852516880388623683)
      ·
        refine ⟨176573915778775320582935525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117715943852516880388623683 176573915778775320582935525)
        ·
          refine ⟨33107609208520372609300411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176573915778775320582935525 33107609208520372609300411)
          ·
            refine ⟨49661413812780558913950617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33107609208520372609300411 49661413812780558913950617)
            ·
              refine ⟨37246060359585419185462963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49661413812780558913950617 37246060359585419185462963)
              ·
                refine ⟨55869090539378128778194445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37246060359585419185462963 55869090539378128778194445)
                ·
                  refine ⟨20950908952266798291822917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55869090539378128778194445 20950908952266798291822917)
                  ·
                    refine ⟨3928295428550024679716797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20950908952266798291822917 3928295428550024679716797)
                    ·
                      refine ⟨1473110785706259254893799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928295428550024679716797 1473110785706259254893799)
                      ·
                        rfl

theorem cell23_2868873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_2868873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868873 prefixEnd_2868873 := by exact prefixLift 2868873
  have htrace : WordTrace (prefixWord ++ tailWord_2868873) baseStart_2868873 baseEnd_2868873 := by
    simpa [prefixWord, tailWord_2868873, baseEnd_2868873] using wordTrace_append hprefix tailTrace_2868873
  have hstable : (prefixWord ++ tailWord_2868873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868873).length < 2 ^ (prefixWord ++ tailWord_2868873).sum := by decide
  have hdescent : baseEnd_2868873 < baseStart_2868873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868914 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_2868914 : Nat := 118140960795 + 2868914 * 2 ^ 59
def prefixEnd_2868914 : Nat := 4983230072969 + 3 ^ 40 * 2868914 * 2
def baseEnd_2868914 : Nat := 491043946137697864827037

theorem tailTrace_2868914 : CollatzResearch.WordTrace tailWord_2868914 prefixEnd_2868914 491043946137697864827037 := by
  unfold tailWord_2868914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26159472482105506086921449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69758593285614682898457197 26159472482105506086921449)
  ·
    refine ⟨19619604361579129565191087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26159472482105506086921449 19619604361579129565191087)
    ·
      refine ⟨29429406542368694347786631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19619604361579129565191087 29429406542368694347786631)
      ·
        refine ⟨44144109813553041521679947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29429406542368694347786631 44144109813553041521679947)
        ·
          refine ⟨66216164720329562282519921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44144109813553041521679947 66216164720329562282519921)
          ·
            refine ⟨49662123540247171711889941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66216164720329562282519921 49662123540247171711889941)
            ·
              refine ⟨2327912040949086173994841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49662123540247171711889941 2327912040949086173994841)
              ·
                refine ⟨1745934030711814630496131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327912040949086173994841 1745934030711814630496131)
                ·
                  refine ⟨2618901046067721945744197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745934030711814630496131 2618901046067721945744197)
                  ·
                    refine ⟨491043946137697864827037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2618901046067721945744197 491043946137697864827037)
                    ·
                      rfl

theorem cell23_2868914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_2868914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868914 prefixEnd_2868914 := by exact prefixLift 2868914
  have htrace : WordTrace (prefixWord ++ tailWord_2868914) baseStart_2868914 baseEnd_2868914 := by
    simpa [prefixWord, tailWord_2868914, baseEnd_2868914] using wordTrace_append hprefix tailTrace_2868914
  have hstable : (prefixWord ++ tailWord_2868914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868914).length < 2 ^ (prefixWord ++ tailWord_2868914).sum := by decide
  have hdescent : baseEnd_2868914 < baseStart_2868914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868920 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_2868920 : Nat := 118140960795 + 2868920 * 2 ^ 59
def prefixEnd_2868920 : Nat := 4983230072969 + 3 ^ 40 * 2868920 * 2
def baseEnd_2868920 : Nat := 1473134919297020571006083

theorem tailTrace_2868920 : CollatzResearch.WordTrace tailWord_2868920 prefixEnd_2868920 1473134919297020571006083 := by
  unfold tailWord_2868920
  simp only [CollatzResearch.WordTrace]
  refine ⟨52319054383200143686202107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69758739177600191581602809 52319054383200143686202107)
  ·
    refine ⟨78478581574800215529303161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52319054383200143686202107 78478581574800215529303161)
    ·
      refine ⟨58858936181100161646977371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78478581574800215529303161 58858936181100161646977371)
      ·
        refine ⟨88288404271650242470466057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58858936181100161646977371 88288404271650242470466057)
        ·
          refine ⟨66216303203737681852849543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88288404271650242470466057 66216303203737681852849543)
          ·
            refine ⟨99324454805606522779274315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66216303203737681852849543 99324454805606522779274315)
            ·
              refine ⟨148986682208409784168911473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99324454805606522779274315 148986682208409784168911473)
              ·
                refine ⟨111740011656307338126683605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148986682208409784168911473 111740011656307338126683605)
                ·
                  refine ⟨2618906523194703237344147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 111740011656307338126683605 2618906523194703237344147)
                  ·
                    refine ⟨3928359784792054856016221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618906523194703237344147 3928359784792054856016221)
                    ·
                      refine ⟨1473134919297020571006083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928359784792054856016221 1473134919297020571006083)
                      ·
                        rfl

theorem cell23_2868920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_2868920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868920 prefixEnd_2868920 := by exact prefixLift 2868920
  have htrace : WordTrace (prefixWord ++ tailWord_2868920) baseStart_2868920 baseEnd_2868920 := by
    simpa [prefixWord, tailWord_2868920, baseEnd_2868920] using wordTrace_append hprefix tailTrace_2868920
  have hstable : (prefixWord ++ tailWord_2868920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868920).length < 2 ^ (prefixWord ++ tailWord_2868920).sum := by decide
  have hdescent : baseEnd_2868920 < baseStart_2868920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868941 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2868941 : Nat := 118140960795 + 2868941 * 2 ^ 59
def prefixEnd_2868941 : Nat := 4983230072969 + 3 ^ 40 * 2868941 * 2
def baseEnd_2868941 : Nat := 1473145702390764988843487

theorem tailTrace_2868941 : CollatzResearch.WordTrace tailWord_2868941 prefixEnd_2868941 1473145702390764988843487 := by
  unfold tailWord_2868941
  simp only [CollatzResearch.WordTrace]
  refine ⟨104638874699324207958918677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69759249799549471972612451 104638874699324207958918677)
  ·
    refine ⟨4904947251530822248074313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104638874699324207958918677 4904947251530822248074313)
    ·
      refine ⟨3678710438648116686055735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4904947251530822248074313 3678710438648116686055735)
      ·
        refine ⟨5518065657972175029083603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678710438648116686055735 5518065657972175029083603)
        ·
          refine ⟨8277098486958262543625405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518065657972175029083603 8277098486958262543625405)
          ·
            refine ⟨3103911932609348453859527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8277098486958262543625405 3103911932609348453859527)
            ·
              refine ⟨4655867898914022680789291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103911932609348453859527 4655867898914022680789291)
              ·
                refine ⟨6983801848371034021183937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655867898914022680789291 6983801848371034021183937)
                ·
                  refine ⟨5237851386278275515887953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6983801848371034021183937 5237851386278275515887953)
                  ·
                    refine ⟨3928388539708706636915965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5237851386278275515887953 3928388539708706636915965)
                    ·
                      refine ⟨1473145702390764988843487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928388539708706636915965 1473145702390764988843487)
                      ·
                        rfl

theorem cell23_2868941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2868941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868941 prefixEnd_2868941 := by exact prefixLift 2868941
  have htrace : WordTrace (prefixWord ++ tailWord_2868941) baseStart_2868941 baseEnd_2868941 := by
    simpa [prefixWord, tailWord_2868941, baseEnd_2868941] using wordTrace_append hprefix tailTrace_2868941
  have hstable : (prefixWord ++ tailWord_2868941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868941).length < 2 ^ (prefixWord ++ tailWord_2868941).sum := by decide
  have hdescent : baseEnd_2868941 < baseStart_2868941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868954 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3]
def baseStart_2868954 : Nat := 118140960795 + 2868954 * 2 ^ 59
def prefixEnd_2868954 : Nat := 4983230072969 + 3 ^ 40 * 2868954 * 2
def baseEnd_2868954 : Nat := 1473152377639273437980927

theorem tailTrace_2868954 : CollatzResearch.WordTrace tailWord_2868954 prefixEnd_2868954 1473152377639273437980927 := by
  unfold tailWord_2868954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26159837212069277794785479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69759565898851407452761277 26159837212069277794785479)
  ·
    refine ⟨39239755818103916692178219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26159837212069277794785479 39239755818103916692178219)
    ·
      refine ⟨58859633727155875038267329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39239755818103916692178219 58859633727155875038267329)
      ·
        refine ⟨44144725295366906278700497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58859633727155875038267329 44144725295366906278700497)
        ·
          refine ⟨33108543971525179709025373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44144725295366906278700497 33108543971525179709025373)
          ·
            refine ⟨12415703989321942390884515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33108543971525179709025373 12415703989321942390884515)
            ·
              refine ⟨18623555983982913586326773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415703989321942390884515 18623555983982913586326773)
              ·
                refine ⟨1745958373498398148718135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18623555983982913586326773 1745958373498398148718135)
                ·
                  refine ⟨2618937560247597223077203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745958373498398148718135 2618937560247597223077203)
                  ·
                    refine ⟨3928406340371395834615805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618937560247597223077203 3928406340371395834615805)
                    ·
                      refine ⟨1473152377639273437980927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928406340371395834615805 1473152377639273437980927)
                      ·
                        rfl

theorem cell23_2868954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_2868954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868954 prefixEnd_2868954 := by exact prefixLift 2868954
  have htrace : WordTrace (prefixWord ++ tailWord_2868954) baseStart_2868954 baseEnd_2868954 := by
    simpa [prefixWord, tailWord_2868954, baseEnd_2868954] using wordTrace_append hprefix tailTrace_2868954
  have hstable : (prefixWord ++ tailWord_2868954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868954).length < 2 ^ (prefixWord ++ tailWord_2868954).sum := by decide
  have hdescent : baseEnd_2868954 < baseStart_2868954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868994 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2868994 : Nat := 118140960795 + 2868994 * 2 ^ 59
def prefixEnd_2868994 : Nat := 4983230072969 + 3 ^ 40 * 2868994 * 2
def baseEnd_2868994 : Nat := 1473172916865453281480743

theorem tailTrace_2868994 : CollatzResearch.WordTrace tailWord_2868994 prefixEnd_2868994 1473172916865453281480743 := by
  unfold tailWord_2868994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26160201942033049502649509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69760538512088132007065357 26160201942033049502649509)
  ·
    refine ⟨4905037864131196781746783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26160201942033049502649509 4905037864131196781746783)
    ·
      refine ⟨7357556796196795172620175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4905037864131196781746783 7357556796196795172620175)
      ·
        refine ⟨11036335194295192758930263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7357556796196795172620175 11036335194295192758930263)
        ·
          refine ⟨16554502791442789138395395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11036335194295192758930263 16554502791442789138395395)
          ·
            refine ⟨24831754187164183707593093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16554502791442789138395395 24831754187164183707593093)
            ·
              refine ⟨4655953910093284445173705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24831754187164183707593093 4655953910093284445173705)
              ·
                refine ⟨3491965432569963333880279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655953910093284445173705 3491965432569963333880279)
                ·
                  refine ⟨5237948148854945000820419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491965432569963333880279 5237948148854945000820419)
                  ·
                    refine ⟨7856922223282417501230629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237948148854945000820419 7856922223282417501230629)
                    ·
                      refine ⟨1473172916865453281480743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7856922223282417501230629 1473172916865453281480743)
                      ·
                        rfl

theorem cell23_2868994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2868994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2868994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2868994 prefixEnd_2868994 := by exact prefixLift 2868994
  have htrace : WordTrace (prefixWord ++ tailWord_2868994) baseStart_2868994 baseEnd_2868994 := by
    simpa [prefixWord, tailWord_2868994, baseEnd_2868994] using wordTrace_append hprefix tailTrace_2868994
  have hstable : (prefixWord ++ tailWord_2868994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868994).length < 2 ^ (prefixWord ++ tailWord_2868994).sum := by decide
  have hdescent : baseEnd_2868994 < baseStart_2868994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869022 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2869022 : Nat := 118140960795 + 2869022 * 2 ^ 59
def prefixEnd_2869022 : Nat := 4983230072969 + 3 ^ 40 * 2869022 * 2
def baseEnd_2869022 : Nat := 1473187294323779171930615

theorem tailTrace_2869022 : CollatzResearch.WordTrace tailWord_2869022 prefixEnd_2869022 1473187294323779171930615 := by
  unfold tailWord_2869022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13080228626503844849077165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69761219341353839195078213 13080228626503844849077165)
  ·
    refine ⟨4905085734938941818403937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13080228626503844849077165 4905085734938941818403937)
    ·
      refine ⟨3678814301204206363802953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4905085734938941818403937 3678814301204206363802953)
      ·
        refine ⟨2759110725903154772852215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3678814301204206363802953 2759110725903154772852215)
        ·
          refine ⟨4138666088854732159278323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759110725903154772852215 4138666088854732159278323)
          ·
            refine ⟨6207999133282098238917485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138666088854732159278323 6207999133282098238917485)
            ·
              refine ⟨2327999674980786839594057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6207999133282098238917485 2327999674980786839594057)
              ·
                refine ⟨1745999756235590129695543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327999674980786839594057 1745999756235590129695543)
                ·
                  refine ⟨2618999634353385194543315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745999756235590129695543 2618999634353385194543315)
                  ·
                    refine ⟨3928499451530077791814973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2618999634353385194543315 3928499451530077791814973)
                    ·
                      refine ⟨1473187294323779171930615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928499451530077791814973 1473187294323779171930615)
                      ·
                        rfl

theorem cell23_2869022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2869022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869022 prefixEnd_2869022 := by exact prefixLift 2869022
  have htrace : WordTrace (prefixWord ++ tailWord_2869022) baseStart_2869022 baseEnd_2869022 := by
    simpa [prefixWord, tailWord_2869022, baseEnd_2869022] using wordTrace_append hprefix tailTrace_2869022
  have hstable : (prefixWord ++ tailWord_2869022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869022).length < 2 ^ (prefixWord ++ tailWord_2869022).sum := by decide
  have hdescent : baseEnd_2869022 < baseStart_2869022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869027 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 3]
def baseStart_2869027 : Nat := 118140960795 + 2869027 * 2 ^ 59
def prefixEnd_2869027 : Nat := 4983230072969 + 3 ^ 40 * 2869027 * 2
def baseEnd_2869027 : Nat := 1473189861727051652368091

theorem tailTrace_2869027 : CollatzResearch.WordTrace tailWord_2869027 prefixEnd_2869027 1473189861727051652368091 := by
  unfold tailWord_2869027
  simp only [CollatzResearch.WordTrace]
  refine ⟨104642011377012644646549335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69761340918008429764366223 104642011377012644646549335)
  ·
    refine ⟨156963017065518966969824003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104642011377012644646549335 156963017065518966969824003)
    ·
      refine ⟨235444525598278450454736005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156963017065518966969824003 235444525598278450454736005)
      ·
        refine ⟨44145848549677209460263001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235444525598278450454736005 44145848549677209460263001)
        ·
          refine ⟨33109386412257907095197251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44145848549677209460263001 33109386412257907095197251)
          ·
            refine ⟨49664079618386860642795877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33109386412257907095197251 49664079618386860642795877)
            ·
              refine ⟨9312014928447536370524227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49664079618386860642795877 9312014928447536370524227)
              ·
                refine ⟨13968022392671304555786341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9312014928447536370524227 13968022392671304555786341)
                ·
                  refine ⟨2619004198625869604209939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13968022392671304555786341 2619004198625869604209939)
                  ·
                    refine ⟨3928506297938804406314909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2619004198625869604209939 3928506297938804406314909)
                    ·
                      refine ⟨1473189861727051652368091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928506297938804406314909 1473189861727051652368091)
                      ·
                        rfl

theorem cell23_2869027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_2869027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869027 prefixEnd_2869027 := by exact prefixLift 2869027
  have htrace : WordTrace (prefixWord ++ tailWord_2869027) baseStart_2869027 baseEnd_2869027 := by
    simpa [prefixWord, tailWord_2869027, baseEnd_2869027] using wordTrace_append hprefix tailTrace_2869027
  have hstable : (prefixWord ++ tailWord_2869027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869027).length < 2 ^ (prefixWord ++ tailWord_2869027).sum := by decide
  have hdescent : baseEnd_2869027 < baseStart_2869027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869038 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2869038 : Nat := 118140960795 + 2869038 * 2 ^ 59
def prefixEnd_2869038 : Nat := 4983230072969 + 3 ^ 40 * 2869038 * 2
def baseEnd_2869038 : Nat := 491065170004750369776847

theorem tailTrace_2869038 : CollatzResearch.WordTrace tailWord_2869038 prefixEnd_2869038 491065170004750369776847 := by
  unfold tailWord_2869038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13080301572496599190649971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69761608386648529016799845 13080301572496599190649971)
  ·
    refine ⟨19620452358744898785974957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13080301572496599190649971 19620452358744898785974957)
    ·
      refine ⟨7357669634529337044740609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19620452358744898785974957 7357669634529337044740609)
      ·
        refine ⟨5518252225897002783555457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7357669634529337044740609 5518252225897002783555457)
        ·
          refine ⟨4138689169422752087666593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5518252225897002783555457 4138689169422752087666593)
          ·
            refine ⟨3104016877067064065749945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4138689169422752087666593 3104016877067064065749945)
            ·
              refine ⟨2328012657800298049312459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104016877067064065749945 2328012657800298049312459)
              ·
                refine ⟨3492018986700447073968689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328012657800298049312459 3492018986700447073968689)
                ·
                  refine ⟨2619014240025335305476517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492018986700447073968689 2619014240025335305476517)
                  ·
                    refine ⟨491065170004750369776847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619014240025335305476517 491065170004750369776847)
                    ·
                      rfl

theorem cell23_2869038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2869038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869038 prefixEnd_2869038 := by exact prefixLift 2869038
  have htrace : WordTrace (prefixWord ++ tailWord_2869038) baseStart_2869038 baseEnd_2869038 := by
    simpa [prefixWord, tailWord_2869038, baseEnd_2869038] using wordTrace_append hprefix tailTrace_2869038
  have hstable : (prefixWord ++ tailWord_2869038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869038).length < 2 ^ (prefixWord ++ tailWord_2869038).sum := by decide
  have hdescent : baseEnd_2869038 < baseStart_2869038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869101 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_2869101 : Nat := 118140960795 + 2869101 * 2 ^ 59
def prefixEnd_2869101 : Nat := 4983230072969 + 3 ^ 40 * 2869101 * 2
def baseEnd_2869101 : Nat := 1473227859295484362842751

theorem tailTrace_2869101 : CollatzResearch.WordTrace tailWord_2869101 prefixEnd_2869101 1473227859295484362842751 := by
  unfold tailWord_2869101
  simp only [CollatzResearch.WordTrace]
  refine ⟨104644710378744555284743157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69763140252496370189828771 104644710378744555284743157)
  ·
    refine ⟨9810441598007302057944671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104644710378744555284743157 9810441598007302057944671)
    ·
      refine ⟨14715662397010953086917007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9810441598007302057944671 14715662397010953086917007)
      ·
        refine ⟨22073493595516429630375511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14715662397010953086917007 22073493595516429630375511)
        ·
          refine ⟨33110240393274644445563267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22073493595516429630375511 33110240393274644445563267)
          ·
            refine ⟨49665360589911966668344901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33110240393274644445563267 49665360589911966668344901)
            ·
              refine ⟨9312255110608493750314669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49665360589911966668344901 9312255110608493750314669)
              ·
                refine ⟨3492095666478185156368001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9312255110608493750314669 3492095666478185156368001)
                ·
                  refine ⟨2619071749858638867276001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492095666478185156368001 2619071749858638867276001)
                  ·
                    refine ⟨1964303812393979150457001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2619071749858638867276001 1964303812393979150457001)
                    ·
                      refine ⟨1473227859295484362842751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1964303812393979150457001 1473227859295484362842751)
                      ·
                        rfl

theorem cell23_2869101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_2869101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869101 prefixEnd_2869101 := by exact prefixLift 2869101
  have htrace : WordTrace (prefixWord ++ tailWord_2869101) baseStart_2869101 baseEnd_2869101 := by
    simpa [prefixWord, tailWord_2869101, baseEnd_2869101] using wordTrace_append hprefix tailTrace_2869101
  have hstable : (prefixWord ++ tailWord_2869101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869101).length < 2 ^ (prefixWord ++ tailWord_2869101).sum := by decide
  have hdescent : baseEnd_2869101 < baseStart_2869101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869120 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_2869120 : Nat := 118140960795 + 2869120 * 2 ^ 59
def prefixEnd_2869120 : Nat := 4983230072969 + 3 ^ 40 * 2869120 * 2
def baseEnd_2869120 : Nat := 491079205142639929501721

theorem tailTrace_2869120 : CollatzResearch.WordTrace tailWord_2869120 prefixEnd_2869120 491079205142639929501721 := by
  unfold tailWord_2869120
  simp only [CollatzResearch.WordTrace]
  refine ⟨52322701682837860764842407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69763602243783814353123209 52322701682837860764842407)
  ·
    refine ⟨78484052524256791147263611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52322701682837860764842407 78484052524256791147263611)
    ·
      refine ⟨117726078786385186720895417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78484052524256791147263611 117726078786385186720895417)
      ·
        refine ⟨88294559089788890040671563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117726078786385186720895417 88294559089788890040671563)
        ·
          refine ⟨132441838634683335061007345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88294559089788890040671563 132441838634683335061007345)
          ·
            refine ⟨99331378976012501295755509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132441838634683335061007345 99331378976012501295755509)
            ·
              refine ⟨9312316779001171996477079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99331378976012501295755509 9312316779001171996477079)
              ·
                refine ⟨13968475168501757994715619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9312316779001171996477079 13968475168501757994715619)
                ·
                  refine ⟨20952712752752636992073429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13968475168501757994715619 20952712752752636992073429)
                  ·
                    refine ⟨491079205142639929501721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20952712752752636992073429 491079205142639929501721)
                    ·
                      rfl

theorem cell23_2869120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_2869120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869120 prefixEnd_2869120 := by exact prefixLift 2869120
  have htrace : WordTrace (prefixWord ++ tailWord_2869120) baseStart_2869120 baseEnd_2869120 := by
    simpa [prefixWord, tailWord_2869120, baseEnd_2869120] using wordTrace_append hprefix tailTrace_2869120
  have hstable : (prefixWord ++ tailWord_2869120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869120).length < 2 ^ (prefixWord ++ tailWord_2869120).sum := by decide
  have hdescent : baseEnd_2869120 < baseStart_2869120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869167 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 3, 4]
def baseStart_2869167 : Nat := 118140960795 + 2869167 * 2 ^ 59
def prefixEnd_2869167 : Nat := 4983230072969 + 3 ^ 40 * 2869167 * 2
def baseEnd_2869167 : Nat := 491087249672893701539149

theorem tailTrace_2869167 : CollatzResearch.WordTrace tailWord_2869167 prefixEnd_2869167 491087249672893701539149 := by
  unfold tailWord_2869167
  simp only [CollatzResearch.WordTrace]
  refine ⟨104647117596505448556645755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69764745064336965704430503 104647117596505448556645755)
  ·
    refine ⟨156970676394758172834968633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104647117596505448556645755 156970676394758172834968633)
    ·
      refine ⟨117728007296068629626226475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156970676394758172834968633 117728007296068629626226475)
      ·
        refine ⟨176592010944102944439339713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117728007296068629626226475 176592010944102944439339713)
        ·
          refine ⟨132444008208077208329504785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176592010944102944439339713 132444008208077208329504785)
          ·
            refine ⟨99333006156057906247128589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132444008208077208329504785 99333006156057906247128589)
            ·
              refine ⟨37249877308521714842673221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99333006156057906247128589 37249877308521714842673221)
              ·
                refine ⟨6984351995347821533001229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37249877308521714842673221 6984351995347821533001229)
                ·
                  refine ⟨2619131998255433074875461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6984351995347821533001229 2619131998255433074875461)
                  ·
                    refine ⟨491087249672893701539149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2619131998255433074875461 491087249672893701539149)
                    ·
                      rfl

theorem cell23_2869167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_2869167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869167 prefixEnd_2869167 := by exact prefixLift 2869167
  have htrace : WordTrace (prefixWord ++ tailWord_2869167) baseStart_2869167 baseEnd_2869167 := by
    simpa [prefixWord, tailWord_2869167, baseEnd_2869167] using wordTrace_append hprefix tailTrace_2869167
  have hstable : (prefixWord ++ tailWord_2869167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869167).length < 2 ^ (prefixWord ++ tailWord_2869167).sum := by decide
  have hdescent : baseEnd_2869167 < baseStart_2869167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869177 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2869177 : Nat := 118140960795 + 2869177 * 2 ^ 59
def prefixEnd_2869177 : Nat := 4983230072969 + 3 ^ 40 * 2869177 * 2
def baseEnd_2869177 : Nat := 1473266883825226065492401

theorem tailTrace_2869177 : CollatzResearch.WordTrace tailWord_2869177 prefixEnd_2869177 1473266883825226065492401 := by
  unfold tailWord_2869177
  simp only [CollatzResearch.WordTrace]
  refine ⟨104647482326469220264509785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69764988217646146843006523 104647482326469220264509785)
  ·
    refine ⟨78485611744851915198382339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104647482326469220264509785 78485611744851915198382339)
    ·
      refine ⟨117728417617277872797573509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78485611744851915198382339 117728417617277872797573509)
      ·
        refine ⟨22074078303239601149545033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117728417617277872797573509 22074078303239601149545033)
        ·
          refine ⟨16555558727429700862158775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22074078303239601149545033 16555558727429700862158775)
          ·
            refine ⟨24833338091144551293238163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16555558727429700862158775 24833338091144551293238163)
            ·
              refine ⟨37250007136716826939857245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24833338091144551293238163 37250007136716826939857245)
              ·
                refine ⟨13968752676268810102446467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37250007136716826939857245 13968752676268810102446467)
                ·
                  refine ⟨20953129014403215153669701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13968752676268810102446467 20953129014403215153669701)
                  ·
                    refine ⟨3928711690200602841313069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20953129014403215153669701 3928711690200602841313069)
                    ·
                      refine ⟨1473266883825226065492401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3928711690200602841313069 1473266883825226065492401)
                      ·
                        rfl

theorem cell23_2869177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2869177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869177 prefixEnd_2869177 := by exact prefixLift 2869177
  have htrace : WordTrace (prefixWord ++ tailWord_2869177) baseStart_2869177 baseEnd_2869177 := by
    simpa [prefixWord, tailWord_2869177, baseEnd_2869177] using wordTrace_append hprefix tailTrace_2869177
  have hstable : (prefixWord ++ tailWord_2869177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869177).length < 2 ^ (prefixWord ++ tailWord_2869177).sum := by decide
  have hdescent : baseEnd_2869177 < baseStart_2869177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869200 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_2869200 : Nat := 118140960795 + 2869200 * 2 ^ 59
def prefixEnd_2869200 : Nat := 4983230072969 + 3 ^ 40 * 2869200 * 2
def baseEnd_2869200 : Nat := 1473278693880279475504795

theorem tailTrace_2869200 : CollatzResearch.WordTrace tailWord_2869200 prefixEnd_2869200 1473278693880279475504795 := by
  unfold tailWord_2869200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52324160602692947596298527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69765547470257263461731369 52324160602692947596298527)
  ·
    refine ⟨78486240904039421394447791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52324160602692947596298527 78486240904039421394447791)
    ·
      refine ⟨117729361356059132091671687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78486240904039421394447791 117729361356059132091671687)
      ·
        refine ⟨176594042034088698137507531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117729361356059132091671687 176594042034088698137507531)
        ·
          refine ⟨264891063051133047206261297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176594042034088698137507531 264891063051133047206261297)
          ·
            refine ⟨198668297288349785404695973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264891063051133047206261297 198668297288349785404695973)
            ·
              refine ⟨37250305741565584763380495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198668297288349785404695973 37250305741565584763380495)
              ·
                refine ⟨55875458612348377145070743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37250305741565584763380495 55875458612348377145070743)
                ·
                  refine ⟨83813187918522565717606115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55875458612348377145070743 83813187918522565717606115)
                  ·
                    refine ⟨125719781877783848576409173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83813187918522565717606115 125719781877783848576409173)
                    ·
                      refine ⟨1473278693880279475504795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 125719781877783848576409173 1473278693880279475504795)
                      ·
                        rfl

theorem cell23_2869200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_2869200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2869200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2869200 prefixEnd_2869200 := by exact prefixLift 2869200
  have htrace : WordTrace (prefixWord ++ tailWord_2869200) baseStart_2869200 baseEnd_2869200 := by
    simpa [prefixWord, tailWord_2869200, baseEnd_2869200] using wordTrace_append hprefix tailTrace_2869200
  have hstable : (prefixWord ++ tailWord_2869200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869200).length < 2 ^ (prefixWord ++ tailWord_2869200).sum := by decide
  have hdescent : baseEnd_2869200 < baseStart_2869200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
