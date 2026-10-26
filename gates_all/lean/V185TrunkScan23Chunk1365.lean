import V185TrunkScan23Chunk1364

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8084620 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_8084620 : Nat := 118140960795 + 8084620 * 2 ^ 59
def prefixEnd_8084620 : Nat := 4983230072969 + 3 ^ 40 * 8084620 * 2
def baseEnd_8084620 : Nat := 1383765322984088040256505

theorem tailTrace_8084620 : CollatzResearch.WordTrace tailWord_8084620 prefixEnd_8084620 1383765322984088040256505 := by
  unfold tailWord_8084620
  simp only [CollatzResearch.WordTrace]
  refine ⟨147435157985404979007265657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196580210647206638676354209 147435157985404979007265657)
  ·
    refine ⟨110576368489053734255449243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147435157985404979007265657 110576368489053734255449243)
    ·
      refine ⟨165864552733580601383173865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110576368489053734255449243 165864552733580601383173865)
      ·
        refine ⟨124398414550185451037380399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165864552733580601383173865 124398414550185451037380399)
        ·
          refine ⟨186597621825278176556070599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124398414550185451037380399 186597621825278176556070599)
          ·
            refine ⟨279896432737917264834105899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186597621825278176556070599 279896432737917264834105899)
            ·
              refine ⟨419844649106875897251158849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279896432737917264834105899 419844649106875897251158849)
              ·
                refine ⟨314883486830156922938369137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419844649106875897251158849 314883486830156922938369137)
                ·
                  refine ⟨236162615122617692203776853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314883486830156922938369137 236162615122617692203776853)
                  ·
                    refine ⟨1383765322984088040256505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236162615122617692203776853 1383765322984088040256505)
                    ·
                      rfl

theorem cell23_8084620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_8084620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084620 prefixEnd_8084620 := by exact prefixLift 8084620
  have htrace : WordTrace (prefixWord ++ tailWord_8084620) baseStart_8084620 baseEnd_8084620 := by
    simpa [prefixWord, tailWord_8084620, baseEnd_8084620] using wordTrace_append hprefix tailTrace_8084620
  have hstable : (prefixWord ++ tailWord_8084620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084620).length < 2 ^ (prefixWord ++ tailWord_8084620).sum := by decide
  have hdescent : baseEnd_8084620 < baseStart_8084620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084667 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 6, 4]
def baseStart_8084667 : Nat := 118140960795 + 8084667 * 2 ^ 59
def prefixEnd_8084667 : Nat := 4983230072969 + 3 ^ 40 * 8084667 * 2
def baseEnd_8084667 : Nat := 1383773367514341812293933

theorem tailTrace_8084667 : CollatzResearch.WordTrace tailWord_8084667 prefixEnd_8084667 1383773367514341812293933 := by
  unfold tailWord_8084667
  simp only [CollatzResearch.WordTrace]
  refine ⟨294872030201639685041492255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196581353467759790027661503 294872030201639685041492255)
  ·
    refine ⟨442308045302459527562238383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294872030201639685041492255 442308045302459527562238383)
    ·
      refine ⟨663462067953689291343357575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442308045302459527562238383 663462067953689291343357575)
      ·
        refine ⟨995193101930533937015036363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663462067953689291343357575 995193101930533937015036363)
        ·
          refine ⟨1492789652895800905522554545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995193101930533937015036363 1492789652895800905522554545)
          ·
            refine ⟨1119592239671850679141915909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492789652895800905522554545 1119592239671850679141915909)
            ·
              refine ⟨209923544938472002339109233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1119592239671850679141915909 209923544938472002339109233)
              ·
                refine ⟨157442658703854001754331925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209923544938472002339109233 157442658703854001754331925)
                ·
                  refine ⟨7380124626743156332234309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157442658703854001754331925 7380124626743156332234309)
                  ·
                    refine ⟨1383773367514341812293933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7380124626743156332234309 1383773367514341812293933)
                    ·
                      rfl

theorem cell23_8084667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 4].length) (baseStart_8084667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084667 prefixEnd_8084667 := by exact prefixLift 8084667
  have htrace : WordTrace (prefixWord ++ tailWord_8084667) baseStart_8084667 baseEnd_8084667 := by
    simpa [prefixWord, tailWord_8084667, baseEnd_8084667] using wordTrace_append hprefix tailTrace_8084667
  have hstable : (prefixWord ++ tailWord_8084667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084667).length < 2 ^ (prefixWord ++ tailWord_8084667).sum := by decide
  have hdescent : baseEnd_8084667 < baseStart_8084667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084714 : List Nat := [3, 1, 3, 1, 1, 5, 1, 8]
def baseStart_8084714 : Nat := 118140960795 + 8084714 * 2 ^ 59
def prefixEnd_8084714 : Nat := 4983230072969 + 3 ^ 40 * 8084714 * 2
def baseEnd_8084714 : Nat := 153753490227177287147929

theorem tailTrace_8084714 : CollatzResearch.WordTrace tailWord_8084714 prefixEnd_8084714 153753490227177287147929 := by
  unfold tailWord_8084714
  simp only [CollatzResearch.WordTrace]
  refine ⟨73718436108117353017113299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196582496288312941378968797 73718436108117353017113299)
  ·
    refine ⟨110577654162176029525669949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73718436108117353017113299 110577654162176029525669949)
    ·
      refine ⟨41466620310816011072126231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110577654162176029525669949 41466620310816011072126231)
      ·
        refine ⟨62199930466224016608189347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41466620310816011072126231 62199930466224016608189347)
        ·
          refine ⟨93299895699336024912284021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62199930466224016608189347 93299895699336024912284021)
          ·
            refine ⟨8746865221812752335526627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93299895699336024912284021 8746865221812752335526627)
            ·
              refine ⟨13120297832719128503289941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746865221812752335526627 13120297832719128503289941)
              ·
                refine ⟨153753490227177287147929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13120297832719128503289941 153753490227177287147929)
                ·
                  rfl

theorem cell23_8084714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_8084714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084714 prefixEnd_8084714 := by exact prefixLift 8084714
  have htrace : WordTrace (prefixWord ++ tailWord_8084714) baseStart_8084714 baseEnd_8084714 := by
    simpa [prefixWord, tailWord_8084714, baseEnd_8084714] using wordTrace_append hprefix tailTrace_8084714
  have hstable : (prefixWord ++ tailWord_8084714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084714).length < 2 ^ (prefixWord ++ tailWord_8084714).sum := by decide
  have hdescent : baseEnd_8084714 < baseStart_8084714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084777 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_8084777 : Nat := 118140960795 + 8084777 * 2 ^ 59
def prefixEnd_8084777 : Nat := 4983230072969 + 3 ^ 40 * 8084777 * 2
def baseEnd_8084777 : Nat := 4151376585415020006506293

theorem tailTrace_8084777 : CollatzResearch.WordTrace tailWord_8084777 prefixEnd_8084777 4151376585415020006506293 := by
  unfold tailWord_8084777
  simp only [CollatzResearch.WordTrace]
  refine ⟨294876042231241173827996585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196584028154160782551997723 294876042231241173827996585)
  ·
    refine ⟨221157031673430880370997439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294876042231241173827996585 221157031673430880370997439)
    ·
      refine ⟨331735547510146320556496159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221157031673430880370997439 331735547510146320556496159)
      ·
        refine ⟨497603321265219480834744239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331735547510146320556496159 497603321265219480834744239)
        ·
          refine ⟨746404981897829221252116359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497603321265219480834744239 746404981897829221252116359)
          ·
            refine ⟨1119607472846743831878174539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746404981897829221252116359 1119607472846743831878174539)
            ·
              refine ⟨1679411209270115747817261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119607472846743831878174539 1679411209270115747817261809)
              ·
                refine ⟨1259558406952586810862946357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679411209270115747817261809 1259558406952586810862946357)
                ·
                  refine ⟨118083600651805013518401221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259558406952586810862946357 118083600651805013518401221)
                  ·
                    refine ⟨22140675122213440034700229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118083600651805013518401221 22140675122213440034700229)
                    ·
                      refine ⟨4151376585415020006506293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22140675122213440034700229 4151376585415020006506293)
                      ·
                        rfl

theorem cell23_8084777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_8084777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084777 prefixEnd_8084777 := by exact prefixLift 8084777
  have htrace : WordTrace (prefixWord ++ tailWord_8084777) baseStart_8084777 baseEnd_8084777 := by
    simpa [prefixWord, tailWord_8084777, baseEnd_8084777] using wordTrace_append hprefix tailTrace_8084777
  have hstable : (prefixWord ++ tailWord_8084777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084777).length < 2 ^ (prefixWord ++ tailWord_8084777).sum := by decide
  have hdescent : baseEnd_8084777 < baseStart_8084777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084798 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_8084798 : Nat := 118140960795 + 8084798 * 2 ^ 59
def prefixEnd_8084798 : Nat := 4983230072969 + 3 ^ 40 * 8084798 * 2
def baseEnd_8084798 : Nat := 4151387368508764424343697

theorem tailTrace_8084798 : CollatzResearch.WordTrace tailWord_8084798 prefixEnd_8084798 4151387368508764424343697 := by
  unfold tailWord_8084798
  simp only [CollatzResearch.WordTrace]
  refine ⟨36859601020520636801813881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196584538776110062943007365 36859601020520636801813881)
  ·
    refine ⟨27644700765390477601360411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36859601020520636801813881 27644700765390477601360411)
    ·
      refine ⟨41467051148085716402040617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27644700765390477601360411 41467051148085716402040617)
      ·
        refine ⟨31100288361064287301530463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41467051148085716402040617 31100288361064287301530463)
        ·
          refine ⟨46650432541596430952295695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31100288361064287301530463 46650432541596430952295695)
          ·
            refine ⟨69975648812394646428443543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46650432541596430952295695 69975648812394646428443543)
            ·
              refine ⟨104963473218591969642665315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69975648812394646428443543 104963473218591969642665315)
              ·
                refine ⟨157445209827887954463997973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104963473218591969642665315 157445209827887954463997973)
                ·
                  refine ⟨7380244210682247865499905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157445209827887954463997973 7380244210682247865499905)
                  ·
                    refine ⟨5535183158011685899124929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7380244210682247865499905 5535183158011685899124929)
                    ·
                      refine ⟨4151387368508764424343697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535183158011685899124929 4151387368508764424343697)
                      ·
                        rfl

theorem cell23_8084798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_8084798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084798 prefixEnd_8084798 := by exact prefixLift 8084798
  have htrace : WordTrace (prefixWord ++ tailWord_8084798) baseStart_8084798 baseEnd_8084798 := by
    simpa [prefixWord, tailWord_8084798, baseEnd_8084798] using wordTrace_append hprefix tailTrace_8084798
  have hstable : (prefixWord ++ tailWord_8084798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084798).length < 2 ^ (prefixWord ++ tailWord_8084798).sum := by decide
  have hdescent : baseEnd_8084798 < baseStart_8084798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084801 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8084801 : Nat := 118140960795 + 8084801 * 2 ^ 59
def prefixEnd_8084801 : Nat := 4983230072969 + 3 ^ 40 * 8084801 * 2
def baseEnd_8084801 : Nat := 4151388908950727912606183

theorem tailTrace_8084801 : CollatzResearch.WordTrace tailWord_8084801 prefixEnd_8084801 4151388908950727912606183 := by
  unfold tailWord_8084801
  simp only [CollatzResearch.WordTrace]
  refine ⟨294876917583154225926870257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196584611722102817284580171 294876917583154225926870257)
  ·
    refine ⟨221157688187365669445152693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294876917583154225926870257 221157688187365669445152693)
    ·
      refine ⟨20733533267565531510483065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221157688187365669445152693 20733533267565531510483065)
      ·
        refine ⟨15550149950674148632862299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20733533267565531510483065 15550149950674148632862299)
        ·
          refine ⟨23325224926011222949293449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550149950674148632862299 23325224926011222949293449)
          ·
            refine ⟨17493918694508417211970087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23325224926011222949293449 17493918694508417211970087)
            ·
              refine ⟨26240878041762625817955131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17493918694508417211970087 26240878041762625817955131)
              ·
                refine ⟨39361317062643938726932697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26240878041762625817955131 39361317062643938726932697)
                ·
                  refine ⟨29520987796982954045199523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39361317062643938726932697 29520987796982954045199523)
                  ·
                    refine ⟨44281481695474431067799285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29520987796982954045199523 44281481695474431067799285)
                    ·
                      refine ⟨4151388908950727912606183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44281481695474431067799285 4151388908950727912606183)
                      ·
                        rfl

theorem cell23_8084801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8084801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084801 prefixEnd_8084801 := by exact prefixLift 8084801
  have htrace : WordTrace (prefixWord ++ tailWord_8084801) baseStart_8084801 baseEnd_8084801 := by
    simpa [prefixWord, tailWord_8084801, baseEnd_8084801] using wordTrace_append hprefix tailTrace_8084801
  have hstable : (prefixWord ++ tailWord_8084801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084801).length < 2 ^ (prefixWord ++ tailWord_8084801).sum := by decide
  have hdescent : baseEnd_8084801 < baseStart_8084801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084821 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 7]
def baseStart_8084821 : Nat := 118140960795 + 8084821 * 2 ^ 59
def prefixEnd_8084821 : Nat := 4983230072969 + 3 ^ 40 * 8084821 * 2
def baseEnd_8084821 : Nat := 461266575395979759372899

theorem tailTrace_8084821 : CollatzResearch.WordTrace tailWord_8084821 prefixEnd_8084821 461266575395979759372899 := by
  unfold tailWord_8084821
  simp only [CollatzResearch.WordTrace]
  refine ⟨294877647043081769342598317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196585098028721179561732211 294877647043081769342598317)
  ·
    refine ⟨110579117641155663503474369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294877647043081769342598317 110579117641155663503474369)
    ·
      refine ⟨82934338230866747627605777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110579117641155663503474369 82934338230866747627605777)
      ·
        refine ⟨62200753673150060720704333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82934338230866747627605777 62200753673150060720704333)
        ·
          refine ⟨23325282627431272770264125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62200753673150060720704333 23325282627431272770264125)
          ·
            refine ⟨8746980985286727288849047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23325282627431272770264125 8746980985286727288849047)
            ·
              refine ⟨13120471477930090933273571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746980985286727288849047 13120471477930090933273571)
              ·
                refine ⟨19680707216895136399910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120471477930090933273571 19680707216895136399910357)
                ·
                  refine ⟨461266575395979759372899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19680707216895136399910357 461266575395979759372899)
                  ·
                    rfl

theorem cell23_8084821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_8084821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084821 prefixEnd_8084821 := by exact prefixLift 8084821
  have htrace : WordTrace (prefixWord ++ tailWord_8084821) baseStart_8084821 baseEnd_8084821 := by
    simpa [prefixWord, tailWord_8084821, baseEnd_8084821] using wordTrace_append hprefix tailTrace_8084821
  have hstable : (prefixWord ++ tailWord_8084821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084821).length < 2 ^ (prefixWord ++ tailWord_8084821).sum := by decide
  have hdescent : baseEnd_8084821 < baseStart_8084821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084832 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2]
def baseStart_8084832 : Nat := 118140960795 + 8084832 * 2 ^ 59
def prefixEnd_8084832 : Nat := 4983230072969 + 3 ^ 40 * 8084832 * 2
def baseEnd_8084832 : Nat := 4151404826851017291318541

theorem tailTrace_8084832 : CollatzResearch.WordTrace tailWord_8084832 prefixEnd_8084832 4151404826851017291318541 := by
  unfold tailWord_8084832
  simp only [CollatzResearch.WordTrace]
  refine ⟨147439024123020959110624375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196585365497361278814165833 147439024123020959110624375)
  ·
    refine ⟨221158536184531438665936563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147439024123020959110624375 221158536184531438665936563)
    ·
      refine ⟨331737804276797157998904845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221158536184531438665936563 331737804276797157998904845)
      ·
        refine ⟨124401676603798934249589317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331737804276797157998904845 124401676603798934249589317)
        ·
          refine ⟨23325314363212300171797997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124401676603798934249589317 23325314363212300171797997)
          ·
            refine ⟨8746992886204612564424249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23325314363212300171797997 8746992886204612564424249)
            ·
              refine ⟨6560244664653459423318187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8746992886204612564424249 6560244664653459423318187)
              ·
                refine ⟨9840366996980189134977281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560244664653459423318187 9840366996980189134977281)
                ·
                  refine ⟨7380275247735141851232961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9840366996980189134977281 7380275247735141851232961)
                  ·
                    refine ⟨5535206435801356388424721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7380275247735141851232961 5535206435801356388424721)
                    ·
                      refine ⟨4151404826851017291318541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535206435801356388424721 4151404826851017291318541)
                      ·
                        rfl

theorem cell23_8084832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_8084832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084832 prefixEnd_8084832 := by exact prefixLift 8084832
  have htrace : WordTrace (prefixWord ++ tailWord_8084832) baseStart_8084832 baseEnd_8084832 := by
    simpa [prefixWord, tailWord_8084832, baseEnd_8084832] using wordTrace_append hprefix tailTrace_8084832
  have hstable : (prefixWord ++ tailWord_8084832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084832).length < 2 ^ (prefixWord ++ tailWord_8084832).sum := by decide
  have hdescent : baseEnd_8084832 < baseStart_8084832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084871 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_8084871 : Nat := 118140960795 + 8084871 * 2 ^ 59
def prefixEnd_8084871 : Nat := 4983230072969 + 3 ^ 40 * 8084871 * 2
def baseEnd_8084871 : Nat := 4151424852596542638730861

theorem tailTrace_8084871 : CollatzResearch.WordTrace tailWord_8084871 prefixEnd_8084871 4151424852596542638730861 := by
  unfold tailWord_8084871
  simp only [CollatzResearch.WordTrace]
  refine ⟨294879470692900627881918467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196586313795267085254612311 294879470692900627881918467)
  ·
    refine ⟨442319206039350941822877701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294879470692900627881918467 442319206039350941822877701)
    ·
      refine ⟨82934851132378301591789569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442319206039350941822877701 82934851132378301591789569)
      ·
        refine ⟨62201138349283726193842177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82934851132378301591789569 62201138349283726193842177)
        ·
          refine ⟨46650853761962794645381633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62201138349283726193842177 46650853761962794645381633)
          ·
            refine ⟨34988140321472095984036225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46650853761962794645381633 34988140321472095984036225)
            ·
              refine ⟨26241105241104071988027169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34988140321472095984036225 26241105241104071988027169)
              ·
                refine ⟨19680828930828053991020377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26241105241104071988027169 19680828930828053991020377)
                ·
                  refine ⟨14760621698121040493265283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19680828930828053991020377 14760621698121040493265283)
                  ·
                    refine ⟨22140932547181560739897925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14760621698121040493265283 22140932547181560739897925)
                    ·
                      refine ⟨4151424852596542638730861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22140932547181560739897925 4151424852596542638730861)
                      ·
                        rfl

theorem cell23_8084871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_8084871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084871 prefixEnd_8084871 := by exact prefixLift 8084871
  have htrace : WordTrace (prefixWord ++ tailWord_8084871) baseStart_8084871 baseEnd_8084871 := by
    simpa [prefixWord, tailWord_8084871, baseEnd_8084871] using wordTrace_append hprefix tailTrace_8084871
  have hstable : (prefixWord ++ tailWord_8084871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084871).length < 2 ^ (prefixWord ++ tailWord_8084871).sum := by decide
  have hdescent : baseEnd_8084871 < baseStart_8084871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084898 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_8084898 : Nat := 118140960795 + 8084898 * 2 ^ 59
def prefixEnd_8084898 : Nat := 4983230072969 + 3 ^ 40 * 8084898 * 2
def baseEnd_8084898 : Nat := 1383812905524738011031079

theorem tailTrace_8084898 : CollatzResearch.WordTrace tailWord_8084898 prefixEnd_8084898 1383812905524738011031079 := by
  unfold tailWord_8084898
  simp only [CollatzResearch.WordTrace]
  refine ⟨73720113865950702873287837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196586970309201874328767565 73720113865950702873287837)
  ·
    refine ⟨27645042699731513577482939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73720113865950702873287837 27645042699731513577482939)
    ·
      refine ⟨41467564049597270366224409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27645042699731513577482939 41467564049597270366224409)
      ·
        refine ⟨31100673037197952774668307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41467564049597270366224409 31100673037197952774668307)
        ·
          refine ⟨46651009555796929162002461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31100673037197952774668307 46651009555796929162002461)
          ·
            refine ⟨17494128583423848435750923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46651009555796929162002461 17494128583423848435750923)
            ·
              refine ⟨26241192875135772653626385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17494128583423848435750923 26241192875135772653626385)
              ·
                refine ⟨19680894656351829490219789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26241192875135772653626385 19680894656351829490219789)
                ·
                  refine ⟨7380335496131936058832421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19680894656351829490219789 7380335496131936058832421)
                  ·
                    refine ⟨1383812905524738011031079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7380335496131936058832421 1383812905524738011031079)
                    ·
                      rfl

theorem cell23_8084898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_8084898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084898 prefixEnd_8084898 := by exact prefixLift 8084898
  have htrace : WordTrace (prefixWord ++ tailWord_8084898) baseStart_8084898 baseEnd_8084898 := by
    simpa [prefixWord, tailWord_8084898, baseEnd_8084898] using wordTrace_append hprefix tailTrace_8084898
  have hstable : (prefixWord ++ tailWord_8084898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084898).length < 2 ^ (prefixWord ++ tailWord_8084898).sum := by decide
  have hdescent : baseEnd_8084898 < baseStart_8084898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084938 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_8084938 : Nat := 118140960795 + 8084938 * 2 ^ 59
def prefixEnd_8084938 : Nat := 4983230072969 + 3 ^ 40 * 8084938 * 2
def baseEnd_8084938 : Nat := 4151459255800393876593053

theorem tailTrace_8084938 : CollatzResearch.WordTrace tailWord_8084938 prefixEnd_8084938 4151459255800393876593053 := by
  unfold tailWord_8084938
  simp only [CollatzResearch.WordTrace]
  refine ⟨73720478595914474581151867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196587942922438598883071645 73720478595914474581151867)
  ·
    refine ⟨110580717893871711871727801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73720478595914474581151867 110580717893871711871727801)
    ·
      refine ⟨82935538420403783903795851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110580717893871711871727801 82935538420403783903795851)
      ·
        refine ⟨124403307630605675855693777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82935538420403783903795851 124403307630605675855693777)
        ·
          refine ⟨93302480722954256891770333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124403307630605675855693777 93302480722954256891770333)
          ·
            refine ⟨34988430271107846334413875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93302480722954256891770333 34988430271107846334413875)
            ·
              refine ⟨52482645406661769501620813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34988430271107846334413875 52482645406661769501620813)
              ·
                refine ⟨19680992027498163563107805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52482645406661769501620813 19680992027498163563107805)
                ·
                  refine ⟨7380372010311811336165427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19680992027498163563107805 7380372010311811336165427)
                  ·
                    refine ⟨11070558015467717004248141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7380372010311811336165427 11070558015467717004248141)
                    ·
                      refine ⟨4151459255800393876593053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11070558015467717004248141 4151459255800393876593053)
                      ·
                        rfl

theorem cell23_8084938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_8084938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084938 prefixEnd_8084938 := by exact prefixLift 8084938
  have htrace : WordTrace (prefixWord ++ tailWord_8084938) baseStart_8084938 baseEnd_8084938 := by
    simpa [prefixWord, tailWord_8084938, baseEnd_8084938] using wordTrace_append hprefix tailTrace_8084938
  have hstable : (prefixWord ++ tailWord_8084938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084938).length < 2 ^ (prefixWord ++ tailWord_8084938).sum := by decide
  have hdescent : baseEnd_8084938 < baseStart_8084938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084984 : List Nat := [2, 1, 2, 1, 1, 5, 11]
def baseStart_8084984 : Nat := 118140960795 + 8084984 * 2 ^ 59
def prefixEnd_8084984 : Nat := 4983230072969 + 3 ^ 40 * 8084984 * 2
def baseEnd_8084984 : Nat := 51252875011240749340961

theorem tailTrace_8084984 : CollatzResearch.WordTrace tailWord_8084984 prefixEnd_8084984 51252875011240749340961 := by
  unfold tailWord_8084984
  simp only [CollatzResearch.WordTrace]
  refine ⟨147441796070745624090391003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196589061427660832120521337 147441796070745624090391003)
  ·
    refine ⟨221162694106118436135586505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147441796070745624090391003 221162694106118436135586505)
    ·
      refine ⟨165872020579588827101689879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221162694106118436135586505 165872020579588827101689879)
      ·
        refine ⟨248808030869383240652534819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165872020579588827101689879 248808030869383240652534819)
        ·
          refine ⟨373212046304074860978802229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248808030869383240652534819 373212046304074860978802229)
          ·
            refine ⟨34988629341007018216762709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373212046304074860978802229 34988629341007018216762709)
            ·
              refine ⟨51252875011240749340961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34988629341007018216762709 51252875011240749340961)
              ·
                rfl

theorem cell23_8084984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 11].length) (baseStart_8084984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084984 prefixEnd_8084984 := by exact prefixLift 8084984
  have htrace : WordTrace (prefixWord ++ tailWord_8084984) baseStart_8084984 baseEnd_8084984 := by
    simpa [prefixWord, tailWord_8084984, baseEnd_8084984] using wordTrace_append hprefix tailTrace_8084984
  have hstable : (prefixWord ++ tailWord_8084984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084984).length < 2 ^ (prefixWord ++ tailWord_8084984).sum := by decide
  have hdescent : baseEnd_8084984 < baseStart_8084984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085032 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_8085032 : Nat := 118140960795 + 8085032 * 2 ^ 59
def prefixEnd_8085032 : Nat := 4983230072969 + 3 ^ 40 * 8085032 * 2
def baseEnd_8085032 : Nat := 4151507522981916508817621

theorem tailTrace_8085032 : CollatzResearch.WordTrace tailWord_8085032 prefixEnd_8085032 4151507522981916508817621 := by
  unfold tailWord_8085032
  simp only [CollatzResearch.WordTrace]
  refine ⟨147442671422658676189264675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196590228563544901585686233 147442671422658676189264675)
  ·
    refine ⟨221164007133988014283897013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147442671422658676189264675 221164007133988014283897013)
    ·
      refine ⟨20734125668811376339115345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221164007133988014283897013 20734125668811376339115345)
      ·
        refine ⟨15550594251608532254336509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20734125668811376339115345 15550594251608532254336509)
        ·
          refine ⟨5831472844353199595376191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15550594251608532254336509 5831472844353199595376191)
          ·
            refine ⟨8747209266529799393064287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831472844353199595376191 8747209266529799393064287)
            ·
              refine ⟨13120813899794699089596431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747209266529799393064287 13120813899794699089596431)
              ·
                refine ⟨19681220849692048634394647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120813899794699089596431 19681220849692048634394647)
                ·
                  refine ⟨29521831274538072951591971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19681220849692048634394647 29521831274538072951591971)
                  ·
                    refine ⟨44282746911807109427387957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29521831274538072951591971 44282746911807109427387957)
                    ·
                      refine ⟨4151507522981916508817621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44282746911807109427387957 4151507522981916508817621)
                      ·
                        rfl

theorem cell23_8085032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_8085032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085032 prefixEnd_8085032 := by exact prefixLift 8085032
  have htrace : WordTrace (prefixWord ++ tailWord_8085032) baseStart_8085032 baseEnd_8085032 := by
    simpa [prefixWord, tailWord_8085032, baseEnd_8085032] using wordTrace_append hprefix tailTrace_8085032
  have hstable : (prefixWord ++ tailWord_8085032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085032).length < 2 ^ (prefixWord ++ tailWord_8085032).sum := by decide
  have hdescent : baseEnd_8085032 < baseStart_8085032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085045 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_8085045 : Nat := 118140960795 + 8085045 * 2 ^ 59
def prefixEnd_8085045 : Nat := 4983230072969 + 3 ^ 40 * 8085045 * 2
def baseEnd_8085045 : Nat := 4151514198230424957955061

theorem tailTrace_8085045 : CollatzResearch.WordTrace tailWord_8085045 prefixEnd_8085045 4151514198230424957955061 := by
  unfold tailWord_8085045
  simp only [CollatzResearch.WordTrace]
  refine ⟨294885816994270255598752589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196590544662846837065835059 294885816994270255598752589)
  ·
    refine ⟨110582181372851345849532221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294885816994270255598752589 110582181372851345849532221)
    ·
      refine ⟨41468318014819254693574583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110582181372851345849532221 41468318014819254693574583)
      ·
        refine ⟨62202477022228882040361875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41468318014819254693574583 62202477022228882040361875)
        ·
          refine ⟨93303715533343323060542813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62202477022228882040361875 93303715533343323060542813)
          ·
            refine ⟨34988893325003746147703555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93303715533343323060542813 34988893325003746147703555)
            ·
              refine ⟨52483339987505619221555333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34988893325003746147703555 52483339987505619221555333)
              ·
                refine ⟨9840626247657303604041625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52483339987505619221555333 9840626247657303604041625)
                ·
                  refine ⟨7380469685742977703031219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9840626247657303604041625 7380469685742977703031219)
                  ·
                    refine ⟨11070704528614466554546829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7380469685742977703031219 11070704528614466554546829)
                    ·
                      refine ⟨4151514198230424957955061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11070704528614466554546829 4151514198230424957955061)
                      ·
                        rfl

theorem cell23_8085045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_8085045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085045 prefixEnd_8085045 := by exact prefixLift 8085045
  have htrace : WordTrace (prefixWord ++ tailWord_8085045) baseStart_8085045 baseEnd_8085045 := by
    simpa [prefixWord, tailWord_8085045, baseEnd_8085045] using wordTrace_append hprefix tailTrace_8085045
  have hstable : (prefixWord ++ tailWord_8085045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085045).length < 2 ^ (prefixWord ++ tailWord_8085045).sum := by decide
  have hdescent : baseEnd_8085045 < baseStart_8085045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085046 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_8085046 : Nat := 118140960795 + 8085046 * 2 ^ 59
def prefixEnd_8085046 : Nat := 4983230072969 + 3 ^ 40 * 8085046 * 2
def baseEnd_8085046 : Nat := 4151514711711079454042557

theorem tailTrace_8085046 : CollatzResearch.WordTrace tailWord_8085046 prefixEnd_8085046 4151514711711079454042557 := by
  unfold tailWord_8085046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18430365841704164548096187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196590568978177755179692661 18430365841704164548096187)
  ·
    refine ⟨27645548762556246822144281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18430365841704164548096187 27645548762556246822144281)
    ·
      refine ⟨20734161571917185116608211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27645548762556246822144281 20734161571917185116608211)
      ·
        refine ⟨31101242357875777674912317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20734161571917185116608211 31101242357875777674912317)
        ·
          refine ⟨11662965884203416628092119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31101242357875777674912317 11662965884203416628092119)
          ·
            refine ⟨17494448826305124942138179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11662965884203416628092119 17494448826305124942138179)
            ·
              refine ⟨26241673239457687413207269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17494448826305124942138179 26241673239457687413207269)
              ·
                refine ⟨4920313732398316389976363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26241673239457687413207269 4920313732398316389976363)
                ·
                  refine ⟨7380470598597474584964545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920313732398316389976363 7380470598597474584964545)
                  ·
                    refine ⟨5535352948948105938723409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7380470598597474584964545 5535352948948105938723409)
                    ·
                      refine ⟨4151514711711079454042557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535352948948105938723409 4151514711711079454042557)
                      ·
                        rfl

theorem cell23_8085046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_8085046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085046 prefixEnd_8085046 := by exact prefixLift 8085046
  have htrace : WordTrace (prefixWord ++ tailWord_8085046) baseStart_8085046 baseEnd_8085046 := by
    simpa [prefixWord, tailWord_8085046, baseEnd_8085046] using wordTrace_append hprefix tailTrace_8085046
  have hstable : (prefixWord ++ tailWord_8085046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085046).length < 2 ^ (prefixWord ++ tailWord_8085046).sum := by decide
  have hdescent : baseEnd_8085046 < baseStart_8085046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085061 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_8085061 : Nat := 118140960795 + 8085061 * 2 ^ 59
def prefixEnd_8085061 : Nat := 4983230072969 + 3 ^ 40 * 8085061 * 2
def baseEnd_8085061 : Nat := 1383840804640298965118329

theorem tailTrace_8085061 : CollatzResearch.WordTrace tailWord_8085061 prefixEnd_8085061 1383840804640298965118329 := by
  unfold tailWord_8085061
  simp only [CollatzResearch.WordTrace]
  refine ⟨294886400562212290331335037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196590933708141526887556691 294886400562212290331335037)
  ·
    refine ⟨110582400210829608874250639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294886400562212290331335037 110582400210829608874250639)
    ·
      refine ⟨165873600316244413311375959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110582400210829608874250639 165873600316244413311375959)
      ·
        refine ⟨248810400474366619967063939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165873600316244413311375959 248810400474366619967063939)
        ·
          refine ⟨373215600711549929950595909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248810400474366619967063939 373215600711549929950595909)
          ·
            refine ⟨69977925133415611865736733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373215600711549929950595909 69977925133415611865736733)
            ·
              refine ⟨26241721925030854449651275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69977925133415611865736733 26241721925030854449651275)
              ·
                refine ⟨39362582887546281674476913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26241721925030854449651275 39362582887546281674476913)
                ·
                  refine ⟨29521937165659711255857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39362582887546281674476913 29521937165659711255857685)
                  ·
                    refine ⟨1383840804640298965118329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29521937165659711255857685 1383840804640298965118329)
                    ·
                      rfl

theorem cell23_8085061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_8085061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085061 prefixEnd_8085061 := by exact prefixLift 8085061
  have htrace : WordTrace (prefixWord ++ tailWord_8085061) baseStart_8085061 baseEnd_8085061 := by
    simpa [prefixWord, tailWord_8085061, baseEnd_8085061] using wordTrace_append hprefix tailTrace_8085061
  have hstable : (prefixWord ++ tailWord_8085061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085061).length < 2 ^ (prefixWord ++ tailWord_8085061).sum := by decide
  have hdescent : baseEnd_8085061 < baseStart_8085061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085071 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_8085071 : Nat := 118140960795 + 8085071 * 2 ^ 59
def prefixEnd_8085071 : Nat := 4983230072969 + 3 ^ 40 * 8085071 * 2
def baseEnd_8085071 : Nat := 4151527548727441856229941

theorem tailTrace_8085071 : CollatzResearch.WordTrace tailWord_8085071 prefixEnd_8085071 4151527548727441856229941 := by
  unfold tailWord_8085071
  simp only [CollatzResearch.WordTrace]
  refine ⟨294886765292176062039199067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196591176861450708026132711 294886765292176062039199067)
  ·
    refine ⟨442330147938264093058798601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294886765292176062039199067 442330147938264093058798601)
    ·
      refine ⟨331747610953698069794098951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442330147938264093058798601 331747610953698069794098951)
      ·
        refine ⟨497621416430547104691148427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331747610953698069794098951 497621416430547104691148427)
        ·
          refine ⟨746432124645820657036722641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497621416430547104691148427 746432124645820657036722641)
          ·
            refine ⟨559824093484365492777541981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746432124645820657036722641 559824093484365492777541981)
            ·
              refine ⟨209934035056637059791578243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559824093484365492777541981 209934035056637059791578243)
              ·
                refine ⟨314901052584955589687367365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209934035056637059791578243 314901052584955589687367365)
                ·
                  refine ⟨59043947359679173066381381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314901052584955589687367365 59043947359679173066381381)
                  ·
                    refine ⟨11070740129939844949946509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59043947359679173066381381 11070740129939844949946509)
                    ·
                      refine ⟨4151527548727441856229941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11070740129939844949946509 4151527548727441856229941)
                      ·
                        rfl

theorem cell23_8085071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_8085071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085071 prefixEnd_8085071 := by exact prefixLift 8085071
  have htrace : WordTrace (prefixWord ++ tailWord_8085071) baseStart_8085071 baseEnd_8085071 := by
    simpa [prefixWord, tailWord_8085071, baseEnd_8085071] using wordTrace_append hprefix tailTrace_8085071
  have hstable : (prefixWord ++ tailWord_8085071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085071).length < 2 ^ (prefixWord ++ tailWord_8085071).sum := by decide
  have hdescent : baseEnd_8085071 < baseStart_8085071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085098 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_8085098 : Nat := 118140960795 + 8085098 * 2 ^ 59
def prefixEnd_8085098 : Nat := 4983230072969 + 3 ^ 40 * 8085098 * 2
def baseEnd_8085098 : Nat := 4151541412705113250592317

theorem tailTrace_8085098 : CollatzResearch.WordTrace tailWord_8085098 prefixEnd_8085098 4151541412705113250592317 := by
  unfold tailWord_8085098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73721937515769561412607987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196591833375385497100287965 73721937515769561412607987)
  ·
    refine ⟨110582906273654342118911981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73721937515769561412607987 110582906273654342118911981)
    ·
      refine ⟨41468589852620378294591993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110582906273654342118911981 41468589852620378294591993)
      ·
        refine ⟨31101442389465283720943995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41468589852620378294591993 31101442389465283720943995)
        ·
          refine ⟨46652163584197925581415993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31101442389465283720943995 46652163584197925581415993)
          ·
            refine ⟨34989122688148444186061995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46652163584197925581415993 34989122688148444186061995)
            ·
              refine ⟨52483684032222666279092993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34989122688148444186061995 52483684032222666279092993)
              ·
                refine ⟨39362763024166999709319745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52483684032222666279092993 39362763024166999709319745)
                ·
                  refine ⟨29522072268125249781989809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39362763024166999709319745 29522072268125249781989809)
                  ·
                    refine ⟨22141554201093937336492357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29522072268125249781989809 22141554201093937336492357)
                    ·
                      refine ⟨4151541412705113250592317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22141554201093937336492357 4151541412705113250592317)
                      ·
                        rfl

theorem cell23_8085098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_8085098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085098 prefixEnd_8085098 := by exact prefixLift 8085098
  have htrace : WordTrace (prefixWord ++ tailWord_8085098) baseStart_8085098 baseEnd_8085098 := by
    simpa [prefixWord, tailWord_8085098, baseEnd_8085098] using wordTrace_append hprefix tailTrace_8085098
  have hstable : (prefixWord ++ tailWord_8085098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085098).length < 2 ^ (prefixWord ++ tailWord_8085098).sum := by decide
  have hdescent : baseEnd_8085098 < baseStart_8085098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085219 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 1, 4]
def baseStart_8085219 : Nat := 118140960795 + 8085219 * 2 ^ 59
def prefixEnd_8085219 : Nat := 4983230072969 + 3 ^ 40 * 8085219 * 2
def baseEnd_8085219 : Nat := 1383867847954769092393087

theorem tailTrace_8085219 : CollatzResearch.WordTrace tailWord_8085219 prefixEnd_8085219 1383867847954769092393087 := by
  unfold tailWord_8085219
  simp only [CollatzResearch.WordTrace]
  refine ⟨294892163295639883315586711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196594775530426588877057807 294892163295639883315586711)
  ·
    refine ⟨442338244943459824973380067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294892163295639883315586711 442338244943459824973380067)
    ·
      refine ⟨663507367415189737460070101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442338244943459824973380067 663507367415189737460070101)
      ·
        refine ⟨15550953923793509471720393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 663507367415189737460070101 15550953923793509471720393)
        ·
          refine ⟨11663215442845132103790295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15550953923793509471720393 11663215442845132103790295)
          ·
            refine ⟨17494823164267698155685443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663215442845132103790295 17494823164267698155685443)
            ·
              refine ⟨26242234746401547233528165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17494823164267698155685443 26242234746401547233528165)
              ·
                refine ⟨4920419014950290106286531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26242234746401547233528165 4920419014950290106286531)
                ·
                  refine ⟨7380628522425435159429797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920419014950290106286531 7380628522425435159429797)
                  ·
                    refine ⟨1383867847954769092393087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7380628522425435159429797 1383867847954769092393087)
                    ·
                      rfl

theorem cell23_8085219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 4].length) (baseStart_8085219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085219 prefixEnd_8085219 := by exact prefixLift 8085219
  have htrace : WordTrace (prefixWord ++ tailWord_8085219) baseStart_8085219 baseEnd_8085219 := by
    simpa [prefixWord, tailWord_8085219, baseEnd_8085219] using wordTrace_append hprefix tailTrace_8085219
  have hstable : (prefixWord ++ tailWord_8085219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085219).length < 2 ^ (prefixWord ++ tailWord_8085219).sum := by decide
  have hdescent : baseEnd_8085219 < baseStart_8085219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085225 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 3]
def baseStart_8085225 : Nat := 118140960795 + 8085225 * 2 ^ 59
def prefixEnd_8085225 : Nat := 4983230072969 + 3 ^ 40 * 8085225 * 2
def baseEnd_8085225 : Nat := 4151606624748234253704233

theorem tailTrace_8085225 : CollatzResearch.WordTrace tailWord_8085225 prefixEnd_8085225 4151606624748234253704233 := by
  unfold tailWord_8085225
  simp only [CollatzResearch.WordTrace]
  refine ⟨294892382133618146340305129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196594921422412097560203419 294892382133618146340305129)
  ·
    refine ⟨221169286600213609755228847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294892382133618146340305129 221169286600213609755228847)
    ·
      refine ⟨331753929900320414632843271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221169286600213609755228847 331753929900320414632843271)
      ·
        refine ⟨497630894850480621949264907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331753929900320414632843271 497630894850480621949264907)
        ·
          refine ⟨746446342275720932923897361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497630894850480621949264907 746446342275720932923897361)
          ·
            refine ⟨559834756706790699692923021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746446342275720932923897361 559834756706790699692923021)
            ·
              refine ⟨209938033765046512384846133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559834756706790699692923021 209938033765046512384846133)
              ·
                refine ⟨19681690665473110536079325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209938033765046512384846133 19681690665473110536079325)
                ·
                  refine ⟨7380633999552416451029747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19681690665473110536079325 7380633999552416451029747)
                  ·
                    refine ⟨11070950999328624676544621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7380633999552416451029747 11070950999328624676544621)
                    ·
                      refine ⟨4151606624748234253704233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11070950999328624676544621 4151606624748234253704233)
                      ·
                        rfl

theorem cell23_8085225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_8085225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085225 prefixEnd_8085225 := by exact prefixLift 8085225
  have htrace : WordTrace (prefixWord ++ tailWord_8085225) baseStart_8085225 baseEnd_8085225 := by
    simpa [prefixWord, tailWord_8085225, baseEnd_8085225] using wordTrace_append hprefix tailTrace_8085225
  have hstable : (prefixWord ++ tailWord_8085225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085225).length < 2 ^ (prefixWord ++ tailWord_8085225).sum := by decide
  have hdescent : baseEnd_8085225 < baseStart_8085225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085228 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_8085228 : Nat := 118140960795 + 8085228 * 2 ^ 59
def prefixEnd_8085228 : Nat := 4983230072969 + 3 ^ 40 * 8085228 * 2
def baseEnd_8085228 : Nat := 1383869388396732580655573

theorem tailTrace_8085228 : CollatzResearch.WordTrace tailWord_8085228 prefixEnd_8085228 1383869388396732580655573 := by
  unfold tailWord_8085228
  simp only [CollatzResearch.WordTrace]
  refine ⟨147446245776303638926332169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196594994368404851901776225 147446245776303638926332169)
  ·
    refine ⟨110584684332227729194749127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147446245776303638926332169 110584684332227729194749127)
    ·
      refine ⟨165877026498341593792123691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110584684332227729194749127 165877026498341593792123691)
      ·
        refine ⟨248815539747512390688185537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165877026498341593792123691 248815539747512390688185537)
        ·
          refine ⟨186611654810634293016139153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248815539747512390688185537 186611654810634293016139153)
          ·
            refine ⟨139958741107975719762104365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186611654810634293016139153 139958741107975719762104365)
            ·
              refine ⟨52484527915490894910789137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139958741107975719762104365 52484527915490894910789137)
              ·
                refine ⟨39363395936618171183091853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52484527915490894910789137 39363395936618171183091853)
                ·
                  refine ⟨14761273476231814193659445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39363395936618171183091853 14761273476231814193659445)
                  ·
                    refine ⟨1383869388396732580655573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14761273476231814193659445 1383869388396732580655573)
                    ·
                      rfl

theorem cell23_8085228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_8085228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085228 prefixEnd_8085228 := by exact prefixLift 8085228
  have htrace : WordTrace (prefixWord ++ tailWord_8085228) baseStart_8085228 baseEnd_8085228 := by
    simpa [prefixWord, tailWord_8085228, baseEnd_8085228] using wordTrace_append hprefix tailTrace_8085228
  have hstable : (prefixWord ++ tailWord_8085228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085228).length < 2 ^ (prefixWord ++ tailWord_8085228).sum := by decide
  have hdescent : baseEnd_8085228 < baseStart_8085228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085235 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 4, 3, 2]
def baseStart_8085235 : Nat := 118140960795 + 8085235 * 2 ^ 59
def prefixEnd_8085235 : Nat := 4983230072969 + 3 ^ 40 * 8085235 * 2
def baseEnd_8085235 : Nat := 4151611759554779214579187

theorem tailTrace_8085235 : CollatzResearch.WordTrace tailWord_8085235 prefixEnd_8085235 4151611759554779214579187 := by
  unfold tailWord_8085235
  simp only [CollatzResearch.WordTrace]
  refine ⟨294892746863581918048169159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196595164575721278698779439 294892746863581918048169159)
  ·
    refine ⟨442339120295372877072253739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294892746863581918048169159 442339120295372877072253739)
    ·
      refine ⟨663508680443059315608380609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442339120295372877072253739 663508680443059315608380609)
      ·
        refine ⟨497631510332294486706285457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663508680443059315608380609 497631510332294486706285457)
        ·
          refine ⟨373223632749220865029714093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497631510332294486706285457 373223632749220865029714093)
          ·
            refine ⟨139958862280957824386142785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373223632749220865029714093 139958862280957824386142785)
            ·
              refine ⟨104969146710718368289607089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139958862280957824386142785 104969146710718368289607089)
              ·
                refine ⟨78726860033038776217205317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104969146710718368289607089 78726860033038776217205317)
                ·
                  refine ⟨14761286256194770540725997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78726860033038776217205317 14761286256194770540725997)
                  ·
                    refine ⟨5535482346073038952772249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14761286256194770540725997 5535482346073038952772249)
                    ·
                      refine ⟨4151611759554779214579187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535482346073038952772249 4151611759554779214579187)
                      ·
                        rfl

theorem cell23_8085235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3, 2].length) (baseStart_8085235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085235 prefixEnd_8085235 := by exact prefixLift 8085235
  have htrace : WordTrace (prefixWord ++ tailWord_8085235) baseStart_8085235 baseEnd_8085235 := by
    simpa [prefixWord, tailWord_8085235, baseEnd_8085235] using wordTrace_append hprefix tailTrace_8085235
  have hstable : (prefixWord ++ tailWord_8085235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085235).length < 2 ^ (prefixWord ++ tailWord_8085235).sum := by decide
  have hdescent : baseEnd_8085235 < baseStart_8085235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085246 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_8085246 : Nat := 118140960795 + 8085246 * 2 ^ 59
def prefixEnd_8085246 : Nat := 4983230072969 + 3 ^ 40 * 8085246 * 2
def baseEnd_8085246 : Nat := 4151617407841978671541637

theorem tailTrace_8085246 : CollatzResearch.WordTrace tailWord_8085246 prefixEnd_8085246 4151617407841978671541637 := by
  unfold tailWord_8085246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36861643508317758365852449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196595432044361377951213061 36861643508317758365852449)
  ·
    refine ⟨27646232631238318774389337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36861643508317758365852449 27646232631238318774389337)
    ·
      refine ⟨20734674473428739080792003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27646232631238318774389337 20734674473428739080792003)
      ·
        refine ⟨31102011710143108621188005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20734674473428739080792003 31102011710143108621188005)
        ·
          refine ⟨5831627195651832866472751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31102011710143108621188005 5831627195651832866472751)
          ·
            refine ⟨8747440793477749299709127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831627195651832866472751 8747440793477749299709127)
            ·
              refine ⟨13121161190216623949563691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747440793477749299709127 13121161190216623949563691)
              ·
                refine ⟨19681741785324935924345537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121161190216623949563691 19681741785324935924345537)
                ·
                  refine ⟨14761306338993701943259153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19681741785324935924345537 14761306338993701943259153)
                  ·
                    refine ⟨11070979754245276457444365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14761306338993701943259153 11070979754245276457444365)
                    ·
                      refine ⟨4151617407841978671541637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11070979754245276457444365 4151617407841978671541637)
                      ·
                        rfl

theorem cell23_8085246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_8085246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085246 prefixEnd_8085246 := by exact prefixLift 8085246
  have htrace : WordTrace (prefixWord ++ tailWord_8085246) baseStart_8085246 baseEnd_8085246 := by
    simpa [prefixWord, tailWord_8085246, baseEnd_8085246] using wordTrace_append hprefix tailTrace_8085246
  have hstable : (prefixWord ++ tailWord_8085246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085246).length < 2 ^ (prefixWord ++ tailWord_8085246).sum := by decide
  have hdescent : baseEnd_8085246 < baseStart_8085246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085252 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_8085252 : Nat := 118140960795 + 8085252 * 2 ^ 59
def prefixEnd_8085252 : Nat := 4983230072969 + 3 ^ 40 * 8085252 * 2
def baseEnd_8085252 : Nat := 4151620488725905648066609

theorem tailTrace_8085252 : CollatzResearch.WordTrace tailWord_8085252 prefixEnd_8085252 4151620488725905648066609 := by
  unfold tailWord_8085252
  simp only [CollatzResearch.WordTrace]
  refine ⟨147446683452260164975769005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196595577936346886634358673 147446683452260164975769005)
  ·
    refine ⟨55292506294597561865913377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147446683452260164975769005 55292506294597561865913377)
    ·
      refine ⟨41469379720948171399435033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55292506294597561865913377 41469379720948171399435033)
      ·
        refine ⟨31102034790711128549576275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41469379720948171399435033 31102034790711128549576275)
        ·
          refine ⟨46653052186066692824364413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31102034790711128549576275 46653052186066692824364413)
          ·
            refine ⟨17494894569775009809136655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46653052186066692824364413 17494894569775009809136655)
            ·
              refine ⟨26242341854662514713704983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17494894569775009809136655 26242341854662514713704983)
              ·
                refine ⟨39363512781993772070557475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26242341854662514713704983 39363512781993772070557475)
                ·
                  refine ⟨59045269172990658105836213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39363512781993772070557475 59045269172990658105836213)
                  ·
                    refine ⟨5535493984967874197422145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59045269172990658105836213 5535493984967874197422145)
                    ·
                      refine ⟨4151620488725905648066609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535493984967874197422145 4151620488725905648066609)
                      ·
                        rfl

theorem cell23_8085252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_8085252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085252 prefixEnd_8085252 := by exact prefixLift 8085252
  have htrace : WordTrace (prefixWord ++ tailWord_8085252) baseStart_8085252 baseEnd_8085252 := by
    simpa [prefixWord, tailWord_8085252, baseEnd_8085252] using wordTrace_append hprefix tailTrace_8085252
  have hstable : (prefixWord ++ tailWord_8085252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085252).length < 2 ^ (prefixWord ++ tailWord_8085252).sum := by decide
  have hdescent : baseEnd_8085252 < baseStart_8085252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085262 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_8085262 : Nat := 118140960795 + 8085262 * 2 ^ 59
def prefixEnd_8085262 : Nat := 4983230072969 + 3 ^ 40 * 8085262 * 2
def baseEnd_8085262 : Nat := 1383875207844150202980521

theorem tailTrace_8085262 : CollatzResearch.WordTrace tailWord_8085262 prefixEnd_8085262 1383875207844150202980521 := by
  unfold tailWord_8085262
  simp only [CollatzResearch.WordTrace]
  refine ⟨36861716454310512707425255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196595821089656067772934693 36861716454310512707425255)
  ·
    refine ⟨55292574681465769061137883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36861716454310512707425255 55292574681465769061137883)
    ·
      refine ⟨82938862022198653591706825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55292574681465769061137883 82938862022198653591706825)
      ·
        refine ⟨62204146516648990193780119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82938862022198653591706825 62204146516648990193780119)
        ·
          refine ⟨93306219774973485290670179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62204146516648990193780119 93306219774973485290670179)
          ·
            refine ⟨139959329662460227936005269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93306219774973485290670179 139959329662460227936005269)
            ·
              refine ⟨6560593577927823184500247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139959329662460227936005269 6560593577927823184500247)
              ·
                refine ⟨9840890366891734776750371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560593577927823184500247 9840890366891734776750371)
                ·
                  refine ⟨14761335550337602165125557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9840890366891734776750371 14761335550337602165125557)
                  ·
                    refine ⟨1383875207844150202980521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14761335550337602165125557 1383875207844150202980521)
                    ·
                      rfl

theorem cell23_8085262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_8085262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085262 prefixEnd_8085262 := by exact prefixLift 8085262
  have htrace : WordTrace (prefixWord ++ tailWord_8085262) baseStart_8085262 baseEnd_8085262 := by
    simpa [prefixWord, tailWord_8085262, baseEnd_8085262] using wordTrace_append hprefix tailTrace_8085262
  have hstable : (prefixWord ++ tailWord_8085262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085262).length < 2 ^ (prefixWord ++ tailWord_8085262).sum := by decide
  have hdescent : baseEnd_8085262 < baseStart_8085262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085285 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_8085285 : Nat := 118140960795 + 8085285 * 2 ^ 59
def prefixEnd_8085285 : Nat := 4983230072969 + 3 ^ 40 * 8085285 * 2
def baseEnd_8085285 : Nat := 4151637433587504018953957

theorem tailTrace_8085285 : CollatzResearch.WordTrace tailWord_8085285 prefixEnd_8085285 4151637433587504018953957 := by
  unfold tailWord_8085285
  simp only [CollatzResearch.WordTrace]
  refine ⟨294894570513400776587489309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196596380342267184391659539 294894570513400776587489309)
  ·
    refine ⟨110585463942525291220308491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294894570513400776587489309 110585463942525291220308491)
    ·
      refine ⟨165878195913787936830462737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110585463942525291220308491 165878195913787936830462737)
      ·
        refine ⟨124408646935340952622847053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165878195913787936830462737 124408646935340952622847053)
        ·
          refine ⟨46653242600752857233567645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124408646935340952622847053 46653242600752857233567645)
          ·
            refine ⟨17494965975282321462587867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46653242600752857233567645 17494965975282321462587867)
            ·
              refine ⟨26242448962923482193881801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17494965975282321462587867 26242448962923482193881801)
              ·
                refine ⟨19681836722192611645411351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26242448962923482193881801 19681836722192611645411351)
                ·
                  refine ⟨29522755083288917468117027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19681836722192611645411351 29522755083288917468117027)
                  ·
                    refine ⟨44284132624933376202175541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29522755083288917468117027 44284132624933376202175541)
                    ·
                      refine ⟨4151637433587504018953957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44284132624933376202175541 4151637433587504018953957)
                      ·
                        rfl

theorem cell23_8085285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_8085285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085285 prefixEnd_8085285 := by exact prefixLift 8085285
  have htrace : WordTrace (prefixWord ++ tailWord_8085285) baseStart_8085285 baseEnd_8085285 := by
    simpa [prefixWord, tailWord_8085285, baseEnd_8085285] using wordTrace_append hprefix tailTrace_8085285
  have hstable : (prefixWord ++ tailWord_8085285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085285).length < 2 ^ (prefixWord ++ tailWord_8085285).sum := by decide
  have hdescent : baseEnd_8085285 < baseStart_8085285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085328 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_8085328 : Nat := 118140960795 + 8085328 * 2 ^ 59
def prefixEnd_8085328 : Nat := 4983230072969 + 3 ^ 40 * 8085328 * 2
def baseEnd_8085328 : Nat := 4151659513255647350716259

theorem tailTrace_8085328 : CollatzResearch.WordTrace tailWord_8085328 prefixEnd_8085328 4151659513255647350716259 := by
  unfold tailWord_8085328
  simp only [CollatzResearch.WordTrace]
  refine ⟨147448069426122497465652319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196597425901496663287536425 147448069426122497465652319)
  ·
    refine ⟨221172104139183746198478479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147448069426122497465652319 221172104139183746198478479)
    ·
      refine ⟨331758156208775619297717719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221172104139183746198478479 331758156208775619297717719)
      ·
        refine ⟨497637234313163428946576579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331758156208775619297717719 497637234313163428946576579)
        ·
          refine ⟨746455851469745143419864869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497637234313163428946576579 746455851469745143419864869)
          ·
            refine ⟨139960472150577214391224663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 746455851469745143419864869 139960472150577214391224663)
            ·
              refine ⟨209940708225865821586836995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139960472150577214391224663 209940708225865821586836995)
              ·
                refine ⟨314911062338798732380255493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209940708225865821586836995 314911062338798732380255493)
                ·
                  refine ⟨59045824188524762321297905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314911062338798732380255493 59045824188524762321297905)
                  ·
                    refine ⟨44284368141393571740973429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59045824188524762321297905 44284368141393571740973429)
                    ·
                      refine ⟨4151659513255647350716259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44284368141393571740973429 4151659513255647350716259)
                      ·
                        rfl

theorem cell23_8085328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_8085328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085328 prefixEnd_8085328 := by exact prefixLift 8085328
  have htrace : WordTrace (prefixWord ++ tailWord_8085328) baseStart_8085328 baseEnd_8085328 := by
    simpa [prefixWord, tailWord_8085328, baseEnd_8085328] using wordTrace_append hprefix tailTrace_8085328
  have hstable : (prefixWord ++ tailWord_8085328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085328).length < 2 ^ (prefixWord ++ tailWord_8085328).sum := by decide
  have hdescent : baseEnd_8085328 < baseStart_8085328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085333 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 1, 2, 2]
def baseStart_8085333 : Nat := 118140960795 + 8085333 * 2 ^ 59
def prefixEnd_8085333 : Nat := 4983230072969 + 3 ^ 40 * 8085333 * 2
def baseEnd_8085333 : Nat := 4151662080658919831153737

theorem tailTrace_8085333 : CollatzResearch.WordTrace tailWord_8085333 prefixEnd_8085333 4151662080658919831153737 := by
  unfold tailWord_8085333
  simp only [CollatzResearch.WordTrace]
  refine ⟨294896321217226880785236653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196597547478151253856824435 294896321217226880785236653)
  ·
    refine ⟨110586120456460080294463745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294896321217226880785236653 110586120456460080294463745)
    ·
      refine ⟨82939590342345060220847809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110586120456460080294463745 82939590342345060220847809)
      ·
        refine ⟨62204692756758795165635857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82939590342345060220847809 62204692756758795165635857)
        ·
          refine ⟨46653519567569096374226893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62204692756758795165635857 46653519567569096374226893)
          ·
            refine ⟨17495069837838411140335085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46653519567569096374226893 17495069837838411140335085)
            ·
              refine ⟨6560651189189404177625657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17495069837838411140335085 6560651189189404177625657)
              ·
                refine ⟨4920488391892053133219243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560651189189404177625657 4920488391892053133219243)
                ·
                  refine ⟨7380732587838079699828865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920488391892053133219243 7380732587838079699828865)
                  ·
                    refine ⟨5535549440878559774871649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7380732587838079699828865 5535549440878559774871649)
                    ·
                      refine ⟨4151662080658919831153737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535549440878559774871649 4151662080658919831153737)
                      ·
                        rfl

theorem cell23_8085333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_8085333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085333 prefixEnd_8085333 := by exact prefixLift 8085333
  have htrace : WordTrace (prefixWord ++ tailWord_8085333) baseStart_8085333 baseEnd_8085333 := by
    simpa [prefixWord, tailWord_8085333, baseEnd_8085333] using wordTrace_append hprefix tailTrace_8085333
  have hstable : (prefixWord ++ tailWord_8085333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085333).length < 2 ^ (prefixWord ++ tailWord_8085333).sum := by decide
  have hdescent : baseEnd_8085333 < baseStart_8085333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085368 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_8085368 : Nat := 118140960795 + 8085368 * 2 ^ 59
def prefixEnd_8085368 : Nat := 4983230072969 + 3 ^ 40 * 8085368 * 2
def baseEnd_8085368 : Nat := 4151680052481827194216075

theorem tailTrace_8085368 : CollatzResearch.WordTrace tailWord_8085368 prefixEnd_8085368 4151680052481827194216075 := by
  unfold tailWord_8085368
  simp only [CollatzResearch.WordTrace]
  refine ⟨147448798886050040881380379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196598398514733387841840505 147448798886050040881380379)
  ·
    refine ⟨221173198329075061322070569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147448798886050040881380379 221173198329075061322070569)
    ·
      refine ⟨165879898746806295991552927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221173198329075061322070569 165879898746806295991552927)
      ·
        refine ⟨248819848120209443987329391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165879898746806295991552927 248819848120209443987329391)
        ·
          refine ⟨373229772180314165980994087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248819848120209443987329391 373229772180314165980994087)
          ·
            refine ⟨559844658270471248971491131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373229772180314165980994087 559844658270471248971491131)
            ·
              refine ⟨839766987405706873457236697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559844658270471248971491131 839766987405706873457236697)
              ·
                refine ⟨629825240554280155092927523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839766987405706873457236697 629825240554280155092927523)
                ·
                  refine ⟨944737860831420232639391285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629825240554280155092927523 944737860831420232639391285)
                  ·
                    refine ⟨88569174452945646809942933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 944737860831420232639391285 88569174452945646809942933)
                    ·
                      refine ⟨4151680052481827194216075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88569174452945646809942933 4151680052481827194216075)
                      ·
                        rfl

theorem cell23_8085368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_8085368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085368 prefixEnd_8085368 := by exact prefixLift 8085368
  have htrace : WordTrace (prefixWord ++ tailWord_8085368) baseStart_8085368 baseEnd_8085368 := by
    simpa [prefixWord, tailWord_8085368, baseEnd_8085368] using wordTrace_append hprefix tailTrace_8085368
  have hstable : (prefixWord ++ tailWord_8085368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085368).length < 2 ^ (prefixWord ++ tailWord_8085368).sum := by decide
  have hdescent : baseEnd_8085368 < baseStart_8085368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085385 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_8085385 : Nat := 118140960795 + 8085385 * 2 ^ 59
def prefixEnd_8085385 : Nat := 4983230072969 + 3 ^ 40 * 8085385 * 2
def baseEnd_8085385 : Nat := 4151688781652953627703497

theorem tailTrace_8085385 : CollatzResearch.WordTrace tailWord_8085385 prefixEnd_8085385 4151688781652953627703497 := by
  unfold tailWord_8085385
  simp only [CollatzResearch.WordTrace]
  refine ⟨294898217813038493666129609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196598811875358995777419739 294898217813038493666129609)
  ·
    refine ⟨221173663359778870249597207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294898217813038493666129609 221173663359778870249597207)
    ·
      refine ⟨331760495039668305374395811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221173663359778870249597207 331760495039668305374395811)
      ·
        refine ⟨497640742559502458061593717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331760495039668305374395811 497640742559502458061593717)
        ·
          refine ⟨46653819614953355443274411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497640742559502458061593717 46653819614953355443274411)
          ·
            refine ⟨69980729422430033164911617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46653819614953355443274411 69980729422430033164911617)
            ·
              refine ⟨52485547066822524873683713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69980729422430033164911617 52485547066822524873683713)
              ·
                refine ⟨39364160300116893655262785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52485547066822524873683713 39364160300116893655262785)
                ·
                  refine ⟨29523120225087670241447089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39364160300116893655262785 29523120225087670241447089)
                  ·
                    refine ⟨22142340168815752681085317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29523120225087670241447089 22142340168815752681085317)
                    ·
                      refine ⟨4151688781652953627703497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22142340168815752681085317 4151688781652953627703497)
                      ·
                        rfl

theorem cell23_8085385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_8085385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085385 prefixEnd_8085385 := by exact prefixLift 8085385
  have htrace : WordTrace (prefixWord ++ tailWord_8085385) baseStart_8085385 baseEnd_8085385 := by
    simpa [prefixWord, tailWord_8085385, baseEnd_8085385] using wordTrace_append hprefix tailTrace_8085385
  have hstable : (prefixWord ++ tailWord_8085385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085385).length < 2 ^ (prefixWord ++ tailWord_8085385).sum := by decide
  have hdescent : baseEnd_8085385 < baseStart_8085385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085402 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_8085402 : Nat := 118140960795 + 8085402 * 2 ^ 59
def prefixEnd_8085402 : Nat := 4983230072969 + 3 ^ 40 * 8085402 * 2
def baseEnd_8085402 : Nat := 4151697510824080061190919

theorem tailTrace_8085402 : CollatzResearch.WordTrace tailWord_8085402 prefixEnd_8085402 4151697510824080061190919 := by
  unfold tailWord_8085402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73724709463494226392374615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196599225235984603712998973 73724709463494226392374615)
  ·
    refine ⟨110587064195241339588561923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73724709463494226392374615 110587064195241339588561923)
    ·
      refine ⟨165880596292862009382842885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110587064195241339588561923 165880596292862009382842885)
      ·
        refine ⟨31102611804911626759283041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165880596292862009382842885 31102611804911626759283041)
        ·
          refine ⟨23326958853683720069462281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31102611804911626759283041 23326958853683720069462281)
          ·
            refine ⟨17495219140262790052096711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23326958853683720069462281 17495219140262790052096711)
            ·
              refine ⟨26242828710394185078145067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495219140262790052096711 26242828710394185078145067)
              ·
                refine ⟨39364243065591277617217601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26242828710394185078145067 39364243065591277617217601)
                ·
                  refine ⟨29523182299193458212913201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39364243065591277617217601 29523182299193458212913201)
                  ·
                    refine ⟨22142386724395093659684901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29523182299193458212913201 22142386724395093659684901)
                    ·
                      refine ⟨4151697510824080061190919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22142386724395093659684901 4151697510824080061190919)
                      ·
                        rfl

theorem cell23_8085402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_8085402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085402 prefixEnd_8085402 := by exact prefixLift 8085402
  have htrace : WordTrace (prefixWord ++ tailWord_8085402) baseStart_8085402 baseEnd_8085402 := by
    simpa [prefixWord, tailWord_8085402, baseEnd_8085402] using wordTrace_append hprefix tailTrace_8085402
  have hstable : (prefixWord ++ tailWord_8085402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085402).length < 2 ^ (prefixWord ++ tailWord_8085402).sum := by decide
  have hdescent : baseEnd_8085402 < baseStart_8085402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085429 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 5]
def baseStart_8085429 : Nat := 118140960795 + 8085429 * 2 ^ 59
def prefixEnd_8085429 : Nat := 4983230072969 + 3 ^ 40 * 8085429 * 2
def baseEnd_8085429 : Nat := 461301263866861272839255

theorem tailTrace_8085429 : CollatzResearch.WordTrace tailWord_8085429 prefixEnd_8085429 461301263866861272839255 := by
  unfold tailWord_8085429
  simp only [CollatzResearch.WordTrace]
  refine ⟨294899822624879089180731341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196599881749919392787154227 294899822624879089180731341)
  ·
    refine ⟨110587433484329658442774253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294899822624879089180731341 110587433484329658442774253)
    ·
      refine ⟨41470287556623621916040345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110587433484329658442774253 41470287556623621916040345)
      ·
        refine ⟨31102715667467716437030259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41470287556623621916040345 31102715667467716437030259)
        ·
          refine ⟨46654073501201574655545389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31102715667467716437030259 46654073501201574655545389)
          ·
            refine ⟨17495277562950590495829521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46654073501201574655545389 17495277562950590495829521)
            ·
              refine ⟨13121458172212942871872141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17495277562950590495829521 13121458172212942871872141)
              ·
                refine ⟨4920546814579853576952053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13121458172212942871872141 4920546814579853576952053)
                ·
                  refine ⟨461301263866861272839255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920546814579853576952053 461301263866861272839255)
                  ·
                    rfl

theorem cell23_8085429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_8085429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085429 prefixEnd_8085429 := by exact prefixLift 8085429
  have htrace : WordTrace (prefixWord ++ tailWord_8085429) baseStart_8085429 baseEnd_8085429 := by
    simpa [prefixWord, tailWord_8085429, baseEnd_8085429] using wordTrace_append hprefix tailTrace_8085429
  have hstable : (prefixWord ++ tailWord_8085429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085429).length < 2 ^ (prefixWord ++ tailWord_8085429).sum := by decide
  have hdescent : baseEnd_8085429 < baseStart_8085429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085482 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_8085482 : Nat := 118140960795 + 8085482 * 2 ^ 59
def prefixEnd_8085482 : Nat := 4983230072969 + 3 ^ 40 * 8085482 * 2
def baseEnd_8085482 : Nat := 4151738589276439748190551

theorem tailTrace_8085482 : CollatzResearch.WordTrace tailWord_8085482 prefixEnd_8085482 4151738589276439748190551 := by
  unfold tailWord_8085482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73725438923421769808102675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196601170462458052821607133 73725438923421769808102675)
  ·
    refine ⟨110588158385132654712154013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73725438923421769808102675 110588158385132654712154013)
    ·
      refine ⟨41470559394424745517057755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110588158385132654712154013 41470559394424745517057755)
      ·
        refine ⟨62205839091637118275586633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41470559394424745517057755 62205839091637118275586633)
        ·
          refine ⟨46654379318727838706689975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62205839091637118275586633 46654379318727838706689975)
          ·
            refine ⟨69981568978091758060034963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46654379318727838706689975 69981568978091758060034963)
            ·
              refine ⟨104972353467137637090052445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69981568978091758060034963 104972353467137637090052445)
              ·
                refine ⟨39364632550176613908769667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104972353467137637090052445 39364632550176613908769667)
                ·
                  refine ⟨59046948825264920863154501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39364632550176613908769667 59046948825264920863154501)
                  ·
                    refine ⟨11071302904737172661841469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59046948825264920863154501 11071302904737172661841469)
                    ·
                      refine ⟨4151738589276439748190551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11071302904737172661841469 4151738589276439748190551)
                      ·
                        rfl

theorem cell23_8085482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_8085482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085482 prefixEnd_8085482 := by exact prefixLift 8085482
  have htrace : WordTrace (prefixWord ++ tailWord_8085482) baseStart_8085482 baseEnd_8085482 := by
    simpa [prefixWord, tailWord_8085482, baseEnd_8085482] using wordTrace_append hprefix tailTrace_8085482
  have hstable : (prefixWord ++ tailWord_8085482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085482).length < 2 ^ (prefixWord ++ tailWord_8085482).sum := by decide
  have hdescent : baseEnd_8085482 < baseStart_8085482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085569 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_8085569 : Nat := 118140960795 + 8085569 * 2 ^ 59
def prefixEnd_8085569 : Nat := 4983230072969 + 3 ^ 40 * 8085569 * 2
def baseEnd_8085569 : Nat := 4151783262093380907802651

theorem tailTrace_8085569 : CollatzResearch.WordTrace tailWord_8085569 prefixEnd_8085569 4151783262093380907802651 := by
  unfold tailWord_8085569
  simp only [CollatzResearch.WordTrace]
  refine ⟨294904928844371893090827761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196603285896247928727218507 294904928844371893090827761)
  ·
    refine ⟨221178696633278919818120821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294904928844371893090827761 221178696633278919818120821)
    ·
      refine ⟨20735502809369898732948827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221178696633278919818120821 20735502809369898732948827)
      ·
        refine ⟨31103254214054848099423241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20735502809369898732948827 31103254214054848099423241)
        ·
          refine ⟨23327440660541136074567431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31103254214054848099423241 23327440660541136074567431)
          ·
            refine ⟨34991160990811704111851147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23327440660541136074567431 34991160990811704111851147)
            ·
              refine ⟨52486741486217556167776721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34991160990811704111851147 52486741486217556167776721)
              ·
                refine ⟨39365056114663167125832541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52486741486217556167776721 39365056114663167125832541)
                ·
                  refine ⟨14761896042998687672187203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39365056114663167125832541 14761896042998687672187203)
                  ·
                    refine ⟨22142844064498031508280805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14761896042998687672187203 22142844064498031508280805)
                    ·
                      refine ⟨4151783262093380907802651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22142844064498031508280805 4151783262093380907802651)
                      ·
                        rfl

theorem cell23_8085569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_8085569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085569 prefixEnd_8085569 := by exact prefixLift 8085569
  have htrace : WordTrace (prefixWord ++ tailWord_8085569) baseStart_8085569 baseEnd_8085569 := by
    simpa [prefixWord, tailWord_8085569, baseEnd_8085569] using wordTrace_append hprefix tailTrace_8085569
  have hstable : (prefixWord ++ tailWord_8085569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085569).length < 2 ^ (prefixWord ++ tailWord_8085569).sum := by decide
  have hdescent : baseEnd_8085569 < baseStart_8085569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085589 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_8085589 : Nat := 118140960795 + 8085589 * 2 ^ 59
def prefixEnd_8085589 : Nat := 4983230072969 + 3 ^ 40 * 8085589 * 2
def baseEnd_8085589 : Nat := 4151793531706470829552559

theorem tailTrace_8085589 : CollatzResearch.WordTrace tailWord_8085589 prefixEnd_8085589 4151793531706470829552559 := by
  unfold tailWord_8085589
  simp only [CollatzResearch.WordTrace]
  refine ⟨294905658304299436506555821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196603772202866291004370547 294905658304299436506555821)
  ·
    refine ⟨110589621864112288689958433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294905658304299436506555821 110589621864112288689958433)
    ·
      refine ⟨82942216398084216517468825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110589621864112288689958433 82942216398084216517468825)
      ·
        refine ⟨62206662298563162388101619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82942216398084216517468825 62206662298563162388101619)
        ·
          refine ⟨93309993447844743582152429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62206662298563162388101619 93309993447844743582152429)
          ·
            refine ⟨34991247542941778843307161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93309993447844743582152429 34991247542941778843307161)
            ·
              refine ⟨26243435657206334132480371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34991247542941778843307161 26243435657206334132480371)
              ·
                refine ⟨39365153485809501198720557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26243435657206334132480371 39365153485809501198720557)
                ·
                  refine ⟨14761932557178562949520209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39365153485809501198720557 14761932557178562949520209)
                  ·
                    refine ⟨11071449417883922212140157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14761932557178562949520209 11071449417883922212140157)
                    ·
                      refine ⟨4151793531706470829552559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11071449417883922212140157 4151793531706470829552559)
                      ·
                        rfl

theorem cell23_8085589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_8085589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085589 prefixEnd_8085589 := by exact prefixLift 8085589
  have htrace : WordTrace (prefixWord ++ tailWord_8085589) baseStart_8085589 baseEnd_8085589 := by
    simpa [prefixWord, tailWord_8085589, baseEnd_8085589] using wordTrace_append hprefix tailTrace_8085589
  have hstable : (prefixWord ++ tailWord_8085589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085589).length < 2 ^ (prefixWord ++ tailWord_8085589).sum := by decide
  have hdescent : baseEnd_8085589 < baseStart_8085589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085590 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_8085590 : Nat := 118140960795 + 8085590 * 2 ^ 59
def prefixEnd_8085590 : Nat := 4983230072969 + 3 ^ 40 * 8085590 * 2
def baseEnd_8085590 : Nat := 4151794045187125325640055

theorem tailTrace_8085590 : CollatzResearch.WordTrace tailWord_8085590 prefixEnd_8085590 4151794045187125325640055 := by
  unfold tailWord_8085590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18431605923580988354833889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196603796518197209118228149 18431605923580988354833889)
  ·
    refine ⟨13823704442685741266125417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18431605923580988354833889 13823704442685741266125417)
    ·
      refine ⟨10367778332014305949594063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13823704442685741266125417 10367778332014305949594063)
      ·
        refine ⟨15551667498021458924391095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367778332014305949594063 15551667498021458924391095)
        ·
          refine ⟨23327501247032188386586643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15551667498021458924391095 23327501247032188386586643)
          ·
            refine ⟨34991251870548282579879965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23327501247032188386586643 34991251870548282579879965)
            ·
              refine ⟨13121719451455605967454987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34991251870548282579879965 13121719451455605967454987)
              ·
                refine ⟨19682579177183408951182481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121719451455605967454987 19682579177183408951182481)
                ·
                  refine ⟨14761934382887556713386861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19682579177183408951182481 14761934382887556713386861)
                  ·
                    refine ⟨5535725393582833767520073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14761934382887556713386861 5535725393582833767520073)
                    ·
                      refine ⟨4151794045187125325640055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535725393582833767520073 4151794045187125325640055)
                      ·
                        rfl

theorem cell23_8085590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_8085590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085590 prefixEnd_8085590 := by exact prefixLift 8085590
  have htrace : WordTrace (prefixWord ++ tailWord_8085590) baseStart_8085590 baseEnd_8085590 := by
    simpa [prefixWord, tailWord_8085590, baseEnd_8085590] using wordTrace_append hprefix tailTrace_8085590
  have hstable : (prefixWord ++ tailWord_8085590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085590).length < 2 ^ (prefixWord ++ tailWord_8085590).sum := by decide
  have hdescent : baseEnd_8085590 < baseStart_8085590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085603 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 1, 2, 2]
def baseStart_8085603 : Nat := 118140960795 + 8085603 * 2 ^ 59
def prefixEnd_8085603 : Nat := 4983230072969 + 3 ^ 40 * 8085603 * 2
def baseEnd_8085603 : Nat := 4151800720435633774777495

theorem tailTrace_8085603 : CollatzResearch.WordTrace tailWord_8085603 prefixEnd_8085603 4151800720435633774777495 := by
  unfold tailWord_8085603
  simp only [CollatzResearch.WordTrace]
  refine ⟨294906168926248716897565463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196604112617499144598376975 294906168926248716897565463)
  ·
    refine ⟨442359253389373075346348195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294906168926248716897565463 442359253389373075346348195)
    ·
      refine ⟨663538880084059613019522293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442359253389373075346348195 663538880084059613019522293)
      ·
        refine ⟨62206770007880588720580215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 663538880084059613019522293 62206770007880588720580215)
        ·
          refine ⟨93310155011820883080870323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62206770007880588720580215 93310155011820883080870323)
          ·
            refine ⟨139965232517731324621305485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93310155011820883080870323 139965232517731324621305485)
            ·
              refine ⟨52486962194149246732989557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139965232517731324621305485 52486962194149246732989557)
              ·
                refine ⟨4920652705701491881217771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52486962194149246732989557 4920652705701491881217771)
                ·
                  refine ⟨7380979058552237821826657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920652705701491881217771 7380979058552237821826657)
                  ·
                    refine ⟨5535734293914178366369993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7380979058552237821826657 5535734293914178366369993)
                    ·
                      refine ⟨4151800720435633774777495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535734293914178366369993 4151800720435633774777495)
                      ·
                        rfl

theorem cell23_8085603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_8085603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085603 prefixEnd_8085603 := by exact prefixLift 8085603
  have htrace : WordTrace (prefixWord ++ tailWord_8085603) baseStart_8085603 baseEnd_8085603 := by
    simpa [prefixWord, tailWord_8085603, baseEnd_8085603] using wordTrace_append hprefix tailTrace_8085603
  have hstable : (prefixWord ++ tailWord_8085603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085603).length < 2 ^ (prefixWord ++ tailWord_8085603).sum := by decide
  have hdescent : baseEnd_8085603 < baseStart_8085603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085633 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_8085633 : Nat := 118140960795 + 8085633 * 2 ^ 59
def prefixEnd_8085633 : Nat := 4983230072969 + 3 ^ 40 * 8085633 * 2
def baseEnd_8085633 : Nat := 4151816124855268657402357

theorem tailTrace_8085633 : CollatzResearch.WordTrace tailWord_8085633 prefixEnd_8085633 4151816124855268657402357 := by
  unfold tailWord_8085633
  simp only [CollatzResearch.WordTrace]
  refine ⟨294907263116140032021157553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196604842077426688014105035 294907263116140032021157553)
  ·
    refine ⟨221180447337105024015868165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294907263116140032021157553 221180447337105024015868165)
    ·
      refine ⟨41471333875707192002975281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221180447337105024015868165 41471333875707192002975281)
      ·
        refine ⟨31103500406780394002231461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41471333875707192002975281 31103500406780394002231461)
        ·
          refine ⟨5831906326271323875418399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31103500406780394002231461 5831906326271323875418399)
          ·
            refine ⟨8747859489406985813127599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831906326271323875418399 8747859489406985813127599)
            ·
              refine ⟨13121789234110478719691399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747859489406985813127599 13121789234110478719691399)
              ·
                refine ⟨19682683851165718079537099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13121789234110478719691399 19682683851165718079537099)
                ·
                  refine ⟨29524025776748577119305649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19682683851165718079537099 29524025776748577119305649)
                  ·
                    refine ⟨22143019332561432839479237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29524025776748577119305649 22143019332561432839479237)
                    ·
                      refine ⟨4151816124855268657402357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22143019332561432839479237 4151816124855268657402357)
                      ·
                        rfl

theorem cell23_8085633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_8085633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085633 prefixEnd_8085633 := by exact prefixLift 8085633
  have htrace : WordTrace (prefixWord ++ tailWord_8085633) baseStart_8085633 baseEnd_8085633 := by
    simpa [prefixWord, tailWord_8085633, baseEnd_8085633] using wordTrace_append hprefix tailTrace_8085633
  have hstable : (prefixWord ++ tailWord_8085633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085633).length < 2 ^ (prefixWord ++ tailWord_8085633).sum := by decide
  have hdescent : baseEnd_8085633 < baseStart_8085633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085663 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 1, 3, 2]
def baseStart_8085663 : Nat := 118140960795 + 8085663 * 2 ^ 59
def prefixEnd_8085663 : Nat := 4983230072969 + 3 ^ 40 * 8085663 * 2
def baseEnd_8085663 : Nat := 4151831529274903540027219

theorem tailTrace_8085663 : CollatzResearch.WordTrace tailWord_8085663 prefixEnd_8085663 4151831529274903540027219 := by
  unfold tailWord_8085663
  simp only [CollatzResearch.WordTrace]
  refine ⟨294908357306031347144749643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196605571537354231429833095 294908357306031347144749643)
  ·
    refine ⟨442362535959047020717124465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294908357306031347144749643 442362535959047020717124465)
    ·
      refine ⟨331771901969285265537843349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442362535959047020717124465 331771901969285265537843349)
      ·
        refine ⟨15551807904810246822086407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331771901969285265537843349 15551807904810246822086407)
        ·
          refine ⟨23327711857215370233129611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15551807904810246822086407 23327711857215370233129611)
          ·
            refine ⟨34991567785823055349694417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23327711857215370233129611 34991567785823055349694417)
            ·
              refine ⟨26243675839367291512270813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34991567785823055349694417 26243675839367291512270813)
              ·
                refine ⟨9841378439762734317101555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26243675839367291512270813 9841378439762734317101555)
                ·
                  refine ⟨14762067659644101475652333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9841378439762734317101555 14762067659644101475652333)
                  ·
                    refine ⟨5535775372366538053369625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14762067659644101475652333 5535775372366538053369625)
                    ·
                      refine ⟨4151831529274903540027219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535775372366538053369625 4151831529274903540027219)
                      ·
                        rfl

theorem cell23_8085663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_8085663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085663 prefixEnd_8085663 := by exact prefixLift 8085663
  have htrace : WordTrace (prefixWord ++ tailWord_8085663) baseStart_8085663 baseEnd_8085663 := by
    simpa [prefixWord, tailWord_8085663, baseEnd_8085663] using wordTrace_append hprefix tailTrace_8085663
  have hstable : (prefixWord ++ tailWord_8085663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085663).length < 2 ^ (prefixWord ++ tailWord_8085663).sum := by decide
  have hdescent : baseEnd_8085663 < baseStart_8085663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085697 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_8085697 : Nat := 118140960795 + 8085697 * 2 ^ 59
def prefixEnd_8085697 : Nat := 4983230072969 + 3 ^ 40 * 8085697 * 2
def baseEnd_8085697 : Nat := 4151848987617156407002063

theorem tailTrace_8085697 : CollatzResearch.WordTrace tailWord_8085697 prefixEnd_8085697 4151848987617156407002063 := by
  unfold tailWord_8085697
  simp only [CollatzResearch.WordTrace]
  refine ⟨294909597387908170951487345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196606398258605447300991563 294909597387908170951487345)
  ·
    refine ⟨221182198040931128213615509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294909597387908170951487345 221182198040931128213615509)
    ·
      refine ⟨10367915533168646635013227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221182198040931128213615509 10367915533168646635013227)
      ·
        refine ⟨15551873299752969952519841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367915533168646635013227 15551873299752969952519841)
        ·
          refine ⟨11663904974814727464389881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15551873299752969952519841 11663904974814727464389881)
          ·
            refine ⟨8747928731111045598292411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11663904974814727464389881 8747928731111045598292411)
            ·
              refine ⟨13121893096666568397438617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747928731111045598292411 13121893096666568397438617)
              ·
                refine ⟨9841419822499926298078963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13121893096666568397438617 9841419822499926298078963)
                ·
                  refine ⟨14762129733749889447118445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9841419822499926298078963 14762129733749889447118445)
                  ·
                    refine ⟨5535798650156208542669417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14762129733749889447118445 5535798650156208542669417)
                    ·
                      refine ⟨4151848987617156407002063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535798650156208542669417 4151848987617156407002063)
                      ·
                        rfl

theorem cell23_8085697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_8085697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085697 prefixEnd_8085697 := by exact prefixLift 8085697
  have htrace : WordTrace (prefixWord ++ tailWord_8085697) baseStart_8085697 baseEnd_8085697 := by
    simpa [prefixWord, tailWord_8085697, baseEnd_8085697] using wordTrace_append hprefix tailTrace_8085697
  have hstable : (prefixWord ++ tailWord_8085697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085697).length < 2 ^ (prefixWord ++ tailWord_8085697).sum := by decide
  have hdescent : baseEnd_8085697 < baseStart_8085697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085729 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_8085729 : Nat := 118140960795 + 8085729 * 2 ^ 59
def prefixEnd_8085729 : Nat := 4983230072969 + 3 ^ 40 * 8085729 * 2
def baseEnd_8085729 : Nat := 1383955139666033427267305

theorem tailTrace_8085729 : CollatzResearch.WordTrace tailWord_8085729 prefixEnd_8085729 1383955139666033427267305 := by
  unfold tailWord_8085729
  simp only [CollatzResearch.WordTrace]
  refine ⟨294910764523792240416652241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196607176349194826944434827 294910764523792240416652241)
  ·
    refine ⟨221183073392844180312489181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294910764523792240416652241 221183073392844180312489181)
    ·
      refine ⟨82943652522316567617183443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221183073392844180312489181 82943652522316567617183443)
      ·
        refine ⟨124415478783474851425775165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82943652522316567617183443 124415478783474851425775165)
        ·
          refine ⟨46655804543803069284665687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124415478783474851425775165 46655804543803069284665687)
          ·
            refine ⟨69983706815704603926998531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46655804543803069284665687 69983706815704603926998531)
            ·
              refine ⟨104975560223556905890497797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69983706815704603926998531 104975560223556905890497797)
              ·
                refine ⟨19682917541916919854468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104975560223556905890497797 19682917541916919854468337)
                ·
                  refine ⟨14762188156437689890851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19682917541916919854468337 14762188156437689890851253)
                  ·
                    refine ⟨1383955139666033427267305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14762188156437689890851253 1383955139666033427267305)
                    ·
                      rfl

theorem cell23_8085729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_8085729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085729 prefixEnd_8085729 := by exact prefixLift 8085729
  have htrace : WordTrace (prefixWord ++ tailWord_8085729) baseStart_8085729 baseEnd_8085729 := by
    simpa [prefixWord, tailWord_8085729, baseEnd_8085729] using wordTrace_append hprefix tailTrace_8085729
  have hstable : (prefixWord ++ tailWord_8085729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085729).length < 2 ^ (prefixWord ++ tailWord_8085729).sum := by decide
  have hdescent : baseEnd_8085729 < baseStart_8085729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085733 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 5]
def baseStart_8085733 : Nat := 118140960795 + 8085733 * 2 ^ 59
def prefixEnd_8085733 : Nat := 4983230072969 + 3 ^ 40 * 8085733 * 2
def baseEnd_8085733 : Nat := 461318608102302029572433

theorem tailTrace_8085733 : CollatzResearch.WordTrace tailWord_8085733 prefixEnd_8085733 461318608102302029572433 := by
  unfold tailWord_8085733
  simp only [CollatzResearch.WordTrace]
  refine ⟨294910910415777749099797853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196607273610518499399865235 294910910415777749099797853)
  ·
    refine ⟨110591591405916655912424195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294910910415777749099797853 110591591405916655912424195)
    ·
      refine ⟨165887387108874983868636293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110591591405916655912424195 165887387108874983868636293)
      ·
        refine ⟨31103885082914059475369305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165887387108874983868636293 31103885082914059475369305)
        ·
          refine ⟨23327913812185544606526979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31103885082914059475369305 23327913812185544606526979)
          ·
            refine ⟨34991870718278316909790469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23327913812185544606526979 34991870718278316909790469)
            ·
              refine ⟨6560975759677184420585713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34991870718278316909790469 6560975759677184420585713)
              ·
                refine ⟨4920731819757888315439285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560975759677184420585713 4920731819757888315439285)
                ·
                  refine ⟨461318608102302029572433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920731819757888315439285 461318608102302029572433)
                  ·
                    rfl

theorem cell23_8085733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_8085733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085733 prefixEnd_8085733 := by exact prefixLift 8085733
  have htrace : WordTrace (prefixWord ++ tailWord_8085733) baseStart_8085733 baseEnd_8085733 := by
    simpa [prefixWord, tailWord_8085733, baseEnd_8085733] using wordTrace_append hprefix tailTrace_8085733
  have hstable : (prefixWord ++ tailWord_8085733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085733).length < 2 ^ (prefixWord ++ tailWord_8085733).sum := by decide
  have hdescent : baseEnd_8085733 < baseStart_8085733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085736 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_8085736 : Nat := 118140960795 + 8085736 * 2 ^ 59
def prefixEnd_8085736 : Nat := 4983230072969 + 3 ^ 40 * 8085736 * 2
def baseEnd_8085736 : Nat := 4151869013362681754414383

theorem tailTrace_8085736 : CollatzResearch.WordTrace tailWord_8085736 prefixEnd_8085736 4151869013362681754414383 := by
  unfold tailWord_8085736
  simp only [CollatzResearch.WordTrace]
  refine ⟨147455509917383440306078531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196607346556511253741438041 147455509917383440306078531)
  ·
    refine ⟨221183264876075160459117797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147455509917383440306078531 221183264876075160459117797)
    ·
      refine ⟨41471862164264092586084587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221183264876075160459117797 41471862164264092586084587)
      ·
        refine ⟨62207793246396138879126881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41471862164264092586084587 62207793246396138879126881)
        ·
          refine ⟨46655844934797104159345161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62207793246396138879126881 46655844934797104159345161)
          ·
            refine ⟨34991883701097828119508871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46655844934797104159345161 34991883701097828119508871)
            ·
              refine ⟨52487825551646742179263307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34991883701097828119508871 52487825551646742179263307)
              ·
                refine ⟨78731738327470113268894961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52487825551646742179263307 78731738327470113268894961)
                ·
                  refine ⟨59048803745602584951671221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78731738327470113268894961 59048803745602584951671221)
                  ·
                    refine ⟨5535825351150242339219177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59048803745602584951671221 5535825351150242339219177)
                    ·
                      refine ⟨4151869013362681754414383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535825351150242339219177 4151869013362681754414383)
                      ·
                        rfl

theorem cell23_8085736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_8085736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085736 prefixEnd_8085736 := by exact prefixLift 8085736
  have htrace : WordTrace (prefixWord ++ tailWord_8085736) baseStart_8085736 baseEnd_8085736 := by
    simpa [prefixWord, tailWord_8085736, baseEnd_8085736] using wordTrace_append hprefix tailTrace_8085736
  have hstable : (prefixWord ++ tailWord_8085736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085736).length < 2 ^ (prefixWord ++ tailWord_8085736).sum := by decide
  have hdescent : baseEnd_8085736 < baseStart_8085736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085793 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 1, 4]
def baseStart_8085793 : Nat := 118140960795 + 8085793 * 2 ^ 59
def prefixEnd_8085793 : Nat := 4983230072969 + 3 ^ 40 * 8085793 * 2
def baseEnd_8085793 : Nat := 1383966093919996010467207

theorem tailTrace_8085793 : CollatzResearch.WordTrace tailWord_8085793 prefixEnd_8085793 1383966093919996010467207 := by
  unfold tailWord_8085793
  simp only [CollatzResearch.WordTrace]
  refine ⟨294913098795560379346982033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196608732530373586231321355 294913098795560379346982033)
  ·
    refine ⟨221184824096670284510236525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294913098795560379346982033 221184824096670284510236525)
    ·
      refine ⟨82944309036251356691338697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221184824096670284510236525 82944309036251356691338697)
      ·
        refine ⟨62208231777188517518504023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82944309036251356691338697 62208231777188517518504023)
        ·
          refine ⟨93312347665782776277756035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62208231777188517518504023 93312347665782776277756035)
          ·
            refine ⟨139968521498674164416634053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93312347665782776277756035 139968521498674164416634053)
            ·
              refine ⟨26244097781001405828118885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139968521498674164416634053 26244097781001405828118885)
              ·
                refine ⟨4920768333937763592772291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26244097781001405828118885 4920768333937763592772291)
                ·
                  refine ⟨7381152500906645389158437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920768333937763592772291 7381152500906645389158437)
                  ·
                    refine ⟨1383966093919996010467207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7381152500906645389158437 1383966093919996010467207)
                    ·
                      rfl

theorem cell23_8085793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_8085793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085793 prefixEnd_8085793 := by exact prefixLift 8085793
  have htrace : WordTrace (prefixWord ++ tailWord_8085793) baseStart_8085793 baseEnd_8085793 := by
    simpa [prefixWord, tailWord_8085793, baseEnd_8085793] using wordTrace_append hprefix tailTrace_8085793
  have hstable : (prefixWord ++ tailWord_8085793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085793).length < 2 ^ (prefixWord ++ tailWord_8085793).sum := by decide
  have hdescent : baseEnd_8085793 < baseStart_8085793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085836 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_8085836 : Nat := 118140960795 + 8085836 * 2 ^ 59
def prefixEnd_8085836 : Nat := 4983230072969 + 3 ^ 40 * 8085836 * 2
def baseEnd_8085836 : Nat := 1383973453809377121054641

theorem tailTrace_8085836 : CollatzResearch.WordTrace tailWord_8085836 prefixEnd_8085836 1383973453809377121054641 := by
  unfold tailWord_8085836
  simp only [CollatzResearch.WordTrace]
  refine ⟨147457333567202298845398681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196609778089603065127198241 147457333567202298845398681)
  ·
    refine ⟨110593000175401724134049011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147457333567202298845398681 110593000175401724134049011)
    ·
      refine ⟨165889500263102586201073517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110593000175401724134049011 165889500263102586201073517)
      ·
        refine ⟨62208562598663469825402569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165889500263102586201073517 62208562598663469825402569)
        ·
          refine ⟨46656421948997602369051927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62208562598663469825402569 46656421948997602369051927)
          ·
            refine ⟨69984632923496403553577891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46656421948997602369051927 69984632923496403553577891)
            ·
              refine ⟨104976949385244605330366837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69984632923496403553577891 104976949385244605330366837)
              ·
                refine ⟨9841589004866681749721891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104976949385244605330366837 9841589004866681749721891)
                ·
                  refine ⟨14762383507300022624582837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9841589004866681749721891 14762383507300022624582837)
                  ·
                    refine ⟨1383973453809377121054641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14762383507300022624582837 1383973453809377121054641)
                    ·
                      rfl

theorem cell23_8085836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_8085836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085836 prefixEnd_8085836 := by exact prefixLift 8085836
  have htrace : WordTrace (prefixWord ++ tailWord_8085836) baseStart_8085836 baseEnd_8085836 := by
    simpa [prefixWord, tailWord_8085836, baseEnd_8085836] using wordTrace_append hprefix tailTrace_8085836
  have hstable : (prefixWord ++ tailWord_8085836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085836).length < 2 ^ (prefixWord ++ tailWord_8085836).sum := by decide
  have hdescent : baseEnd_8085836 < baseStart_8085836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085873 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_8085873 : Nat := 118140960795 + 8085873 * 2 ^ 59
def prefixEnd_8085873 : Nat := 4983230072969 + 3 ^ 40 * 8085873 * 2
def baseEnd_8085873 : Nat := 4151939360212347718401253

theorem tailTrace_8085873 : CollatzResearch.WordTrace tailWord_8085873 prefixEnd_8085873 4151939360212347718401253 := by
  unfold tailWord_8085873
  simp only [CollatzResearch.WordTrace]
  refine ⟨294916016635270553009894273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196610677756847035339929515 294916016635270553009894273)
  ·
    refine ⟨221187012476452914757420705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294916016635270553009894273 221187012476452914757420705)
    ·
      refine ⟨165890259357339686068065529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221187012476452914757420705 165890259357339686068065529)
      ·
        refine ⟨124417694518004764551049147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165890259357339686068065529 124417694518004764551049147)
        ·
          refine ⟨186626541777007146826573721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124417694518004764551049147 186626541777007146826573721)
          ·
            refine ⟨139969906332755360119930291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186626541777007146826573721 139969906332755360119930291)
            ·
              refine ⟨209954859499133040179895437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139969906332755360119930291 209954859499133040179895437)
              ·
                refine ⟨78733072312174890067460789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209954859499133040179895437 78733072312174890067460789)
                ·
                  refine ⟨7381225529266395943824449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78733072312174890067460789 7381225529266395943824449)
                  ·
                    refine ⟨5535919146949796957868337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381225529266395943824449 5535919146949796957868337)
                    ·
                      refine ⟨4151939360212347718401253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535919146949796957868337 4151939360212347718401253)
                      ·
                        rfl

theorem cell23_8085873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_8085873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085873 prefixEnd_8085873 := by exact prefixLift 8085873
  have htrace : WordTrace (prefixWord ++ tailWord_8085873) baseStart_8085873 baseEnd_8085873 := by
    simpa [prefixWord, tailWord_8085873, baseEnd_8085873] using wordTrace_append hprefix tailTrace_8085873
  have hstable : (prefixWord ++ tailWord_8085873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085873).length < 2 ^ (prefixWord ++ tailWord_8085873).sum := by decide
  have hdescent : baseEnd_8085873 < baseStart_8085873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085923 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3]
def baseStart_8085923 : Nat := 118140960795 + 8085923 * 2 ^ 59
def prefixEnd_8085923 : Nat := 4983230072969 + 3 ^ 40 * 8085923 * 2
def baseEnd_8085923 : Nat := 4151965034245072522776023

theorem tailTrace_8085923 : CollatzResearch.WordTrace tailWord_8085923 prefixEnd_8085923 4151965034245072522776023 := by
  unfold tailWord_8085923
  simp only [CollatzResearch.WordTrace]
  refine ⟨294917840285089411549214423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196611893523392941032809615 294917840285089411549214423)
  ·
    refine ⟨442376760427634117323821635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294917840285089411549214423 442376760427634117323821635)
    ·
      refine ⟨663565140641451175985732453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442376760427634117323821635 663565140641451175985732453)
      ·
        refine ⟨124418463870272095497324835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 663565140641451175985732453 124418463870272095497324835)
        ·
          refine ⟨186627695805408143245987253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124418463870272095497324835 186627695805408143245987253)
          ·
            refine ⟨17496346481757013429311305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186627695805408143245987253 17496346481757013429311305)
            ·
              refine ⟨13122259861317760071983479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17496346481757013429311305 13122259861317760071983479)
              ·
                refine ⟨19683389791976640107975219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13122259861317760071983479 19683389791976640107975219)
                ·
                  refine ⟨29525084687964960161962829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19683389791976640107975219 29525084687964960161962829)
                  ·
                    refine ⟨11071906757986860060736061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29525084687964960161962829 11071906757986860060736061)
                    ·
                      refine ⟨4151965034245072522776023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11071906757986860060736061 4151965034245072522776023)
                      ·
                        rfl

theorem cell23_8085923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_8085923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085923 prefixEnd_8085923 := by exact prefixLift 8085923
  have htrace : WordTrace (prefixWord ++ tailWord_8085923) baseStart_8085923 baseEnd_8085923 := by
    simpa [prefixWord, tailWord_8085923, baseEnd_8085923] using wordTrace_append hprefix tailTrace_8085923
  have hstable : (prefixWord ++ tailWord_8085923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085923).length < 2 ^ (prefixWord ++ tailWord_8085923).sum := by decide
  have hdescent : baseEnd_8085923 < baseStart_8085923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085966 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_8085966 : Nat := 118140960795 + 8085966 * 2 ^ 59
def prefixEnd_8085966 : Nat := 4983230072969 + 3 ^ 40 * 8085966 * 2
def baseEnd_8085966 : Nat := 4151987113913215854538325

theorem tailTrace_8085966 : CollatzResearch.WordTrace tailWord_8085966 prefixEnd_8085966 4151987113913215854538325 := by
  unfold tailWord_8085966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36864926077991703736628719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196612939082622419928686501 36864926077991703736628719)
  ·
    refine ⟨55297389116987555604943079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36864926077991703736628719 55297389116987555604943079)
    ·
      refine ⟨82946083675481333407414619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55297389116987555604943079 82946083675481333407414619)
      ·
        refine ⟨124419125513222000111121929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82946083675481333407414619 124419125513222000111121929)
        ·
          refine ⟨93314344134916500083341447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124419125513222000111121929 93314344134916500083341447)
          ·
            refine ⟨139971516202374750125012171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93314344134916500083341447 139971516202374750125012171)
            ·
              refine ⟨209957274303562125187518257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139971516202374750125012171 209957274303562125187518257)
              ·
                refine ⟨157467955727671593890638693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209957274303562125187518257 157467955727671593890638693)
                ·
                  refine ⟨29525241698938423854494755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157467955727671593890638693 29525241698938423854494755)
                  ·
                    refine ⟨44287862548407635781742133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29525241698938423854494755 44287862548407635781742133)
                    ·
                      refine ⟨4151987113913215854538325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44287862548407635781742133 4151987113913215854538325)
                      ·
                        rfl

theorem cell23_8085966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_8085966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085966 prefixEnd_8085966 := by exact prefixLift 8085966
  have htrace : WordTrace (prefixWord ++ tailWord_8085966) baseStart_8085966 baseEnd_8085966 := by
    simpa [prefixWord, tailWord_8085966, baseEnd_8085966] using wordTrace_append hprefix tailTrace_8085966
  have hstable : (prefixWord ++ tailWord_8085966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085966).length < 2 ^ (prefixWord ++ tailWord_8085966).sum := by decide
  have hdescent : baseEnd_8085966 < baseStart_8085966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085974 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_8085974 : Nat := 118140960795 + 8085974 * 2 ^ 59
def prefixEnd_8085974 : Nat := 4983230072969 + 3 ^ 40 * 8085974 * 2
def baseEnd_8085974 : Nat := 4151991221758451823238289

theorem tailTrace_8085974 : CollatzResearch.WordTrace tailWord_8085974 prefixEnd_8085974 4151991221758451823238289 := by
  unfold tailWord_8085974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18432481275494040453707561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196613133605269764839547317 18432481275494040453707561)
  ·
    refine ⟨13824360956620530340280671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18432481275494040453707561 13824360956620530340280671)
    ·
      refine ⟨20736541434930795510421007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13824360956620530340280671 20736541434930795510421007)
      ·
        refine ⟨31104812152396193265631511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20736541434930795510421007 31104812152396193265631511)
        ·
          refine ⟨46657218228594289898447267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31104812152396193265631511 46657218228594289898447267)
          ·
            refine ⟨69985827342891434847670901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46657218228594289898447267 69985827342891434847670901)
            ·
              refine ⟨6561171313396072016969147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69985827342891434847670901 6561171313396072016969147)
              ·
                refine ⟨9841756970094108025453721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6561171313396072016969147 9841756970094108025453721)
                ·
                  refine ⟨7381317727570581019090291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9841756970094108025453721 7381317727570581019090291)
                  ·
                    refine ⟨11071976591355871528635437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7381317727570581019090291 11071976591355871528635437)
                    ·
                      refine ⟨4151991221758451823238289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11071976591355871528635437 4151991221758451823238289)
                      ·
                        rfl

theorem cell23_8085974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_8085974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085974 prefixEnd_8085974 := by exact prefixLift 8085974
  have htrace : WordTrace (prefixWord ++ tailWord_8085974) baseStart_8085974 baseEnd_8085974 := by
    simpa [prefixWord, tailWord_8085974, baseEnd_8085974] using wordTrace_append hprefix tailTrace_8085974
  have hstable : (prefixWord ++ tailWord_8085974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085974).length < 2 ^ (prefixWord ++ tailWord_8085974).sum := by decide
  have hdescent : baseEnd_8085974 < baseStart_8085974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8085997 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_8085997 : Nat := 118140960795 + 8085997 * 2 ^ 59
def prefixEnd_8085997 : Nat := 4983230072969 + 3 ^ 40 * 8085997 * 2
def baseEnd_8085997 : Nat := 4152003031813505233250683

theorem tailTrace_8085997 : CollatzResearch.WordTrace tailWord_8085997 prefixEnd_8085997 4152003031813505233250683 := by
  unfold tailWord_8085997
  simp only [CollatzResearch.WordTrace]
  refine ⟨294920539286821322187408245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196613692857880881458272163 294920539286821322187408245)
  ·
    refine ⟨27648800558139498955069523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294920539286821322187408245 27648800558139498955069523)
    ·
      refine ⟨41473200837209248432604285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27648800558139498955069523 41473200837209248432604285)
      ·
        refine ⟨15552450313953468162226607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41473200837209248432604285 15552450313953468162226607)
        ·
          refine ⟨23328675470930202243339911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552450313953468162226607 23328675470930202243339911)
          ·
            refine ⟨34993013206395303365009867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23328675470930202243339911 34993013206395303365009867)
            ·
              refine ⟨52489519809592955047514801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34993013206395303365009867 52489519809592955047514801)
              ·
                refine ⟨39367139857194716285636101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52489519809592955047514801 39367139857194716285636101)
                ·
                  refine ⟨7381338723224009303556769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39367139857194716285636101 7381338723224009303556769)
                  ·
                    refine ⟨5536004042418006977667577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381338723224009303556769 5536004042418006977667577)
                    ·
                      refine ⟨4152003031813505233250683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536004042418006977667577 4152003031813505233250683)
                      ·
                        rfl

theorem cell23_8085997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_8085997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8085997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8085997 prefixEnd_8085997 := by exact prefixLift 8085997
  have htrace : WordTrace (prefixWord ++ tailWord_8085997) baseStart_8085997 baseEnd_8085997 := by
    simpa [prefixWord, tailWord_8085997, baseEnd_8085997] using wordTrace_append hprefix tailTrace_8085997
  have hstable : (prefixWord ++ tailWord_8085997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8085997).length < 2 ^ (prefixWord ++ tailWord_8085997).sum := by decide
  have hdescent : baseEnd_8085997 < baseStart_8085997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8085997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086020 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 7]
def baseStart_8086020 : Nat := 118140960795 + 8086020 * 2 ^ 59
def prefixEnd_8086020 : Nat := 4983230072969 + 3 ^ 40 * 8086020 * 2
def baseEnd_8086020 : Nat := 461334982429839849251453

theorem tailTrace_8086020 : CollatzResearch.WordTrace tailWord_8086020 prefixEnd_8086020 461334982429839849251453 := by
  unfold tailWord_8086020
  simp only [CollatzResearch.WordTrace]
  refine ⟨147460689082868998557747757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196614252110491998076997009 147460689082868998557747757)
  ·
    refine ⟨55297758406075874459155409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147460689082868998557747757 55297758406075874459155409)
    ·
      refine ⟨41473318804556905844366557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55297758406075874459155409 41473318804556905844366557)
      ·
        refine ⟨15552494551708839691637459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41473318804556905844366557 15552494551708839691637459)
        ·
          refine ⟨23328741827563259537456189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552494551708839691637459 23328741827563259537456189)
          ·
            refine ⟨8748278185336222326546071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23328741827563259537456189 8748278185336222326546071)
            ·
              refine ⟨13122417278004333489819107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748278185336222326546071 13122417278004333489819107)
              ·
                refine ⟨19683625917006500234728661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13122417278004333489819107 19683625917006500234728661)
                ·
                  refine ⟨461334982429839849251453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19683625917006500234728661 461334982429839849251453)
                  ·
                    rfl

theorem cell23_8086020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_8086020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086020 prefixEnd_8086020 := by exact prefixLift 8086020
  have htrace : WordTrace (prefixWord ++ tailWord_8086020) baseStart_8086020 baseEnd_8086020 := by
    simpa [prefixWord, tailWord_8086020, baseEnd_8086020] using wordTrace_append hprefix tailTrace_8086020
  have hstable : (prefixWord ++ tailWord_8086020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086020).length < 2 ^ (prefixWord ++ tailWord_8086020).sum := by decide
  have hdescent : baseEnd_8086020 < baseStart_8086020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086053 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_8086053 : Nat := 118140960795 + 8086053 * 2 ^ 59
def prefixEnd_8086053 : Nat := 4983230072969 + 3 ^ 40 * 8086053 * 2
def baseEnd_8086053 : Nat := 4152031786730157014150425

theorem tailTrace_8086053 : CollatzResearch.WordTrace tailWord_8086053 prefixEnd_8086053 4152031786730157014150425 := by
  unfold tailWord_8086053
  simp only [CollatzResearch.WordTrace]
  refine ⟨294922581774618443751446813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196615054516412295834297875 294922581774618443751446813)
  ·
    refine ⟨110595968165481916406792555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294922581774618443751446813 110595968165481916406792555)
    ·
      refine ⟨165893952248222874610188833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110595968165481916406792555 165893952248222874610188833)
      ·
        refine ⟨124420464186167155957641625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165893952248222874610188833 124420464186167155957641625)
        ·
          refine ⟨93315348139625366968231219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124420464186167155957641625 93315348139625366968231219)
          ·
            refine ⟨139973022209438050452346829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93315348139625366968231219 139973022209438050452346829)
            ·
              refine ⟨52489883328539268919630061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139973022209438050452346829 52489883328539268919630061)
              ·
                refine ⟨19683706248202225844861273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52489883328539268919630061 19683706248202225844861273)
                ·
                  refine ⟨14762779686151669383645955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19683706248202225844861273 14762779686151669383645955)
                  ·
                    refine ⟨22144169529227504075468933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14762779686151669383645955 22144169529227504075468933)
                    ·
                      refine ⟨4152031786730157014150425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22144169529227504075468933 4152031786730157014150425)
                      ·
                        rfl

theorem cell23_8086053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_8086053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086053 prefixEnd_8086053 := by exact prefixLift 8086053
  have htrace : WordTrace (prefixWord ++ tailWord_8086053) baseStart_8086053 baseEnd_8086053 := by
    simpa [prefixWord, tailWord_8086053, baseEnd_8086053] using wordTrace_append hprefix tailTrace_8086053
  have hstable : (prefixWord ++ tailWord_8086053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086053).length < 2 ^ (prefixWord ++ tailWord_8086053).sum := by decide
  have hdescent : baseEnd_8086053 < baseStart_8086053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086096 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_8086096 : Nat := 118140960795 + 8086096 * 2 ^ 59
def prefixEnd_8086096 : Nat := 4983230072969 + 3 ^ 40 * 8086096 * 2
def baseEnd_8086096 : Nat := 4152053866398300345912727

theorem tailTrace_8086096 : CollatzResearch.WordTrace tailWord_8086096 prefixEnd_8086096 4152053866398300345912727 := by
  unfold tailWord_8086096
  simp only [CollatzResearch.WordTrace]
  refine ⟨147462075056731331047631071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196616100075641774730174761 147462075056731331047631071)
  ·
    refine ⟨221193112585096996571446607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147462075056731331047631071 221193112585096996571446607)
    ·
      refine ⟨331789668877645494857169911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221193112585096996571446607 331789668877645494857169911)
      ·
        refine ⟨497684503316468242285754867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331789668877645494857169911 497684503316468242285754867)
        ·
          refine ⟨746526754974702363428632301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497684503316468242285754867 746526754974702363428632301)
          ·
            refine ⟨279947533115513386285737113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746526754974702363428632301 279947533115513386285737113)
            ·
              refine ⟨209960649836635039714302835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279947533115513386285737113 209960649836635039714302835)
              ·
                refine ⟨314940974754952559571454253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209960649836635039714302835 314940974754952559571454253)
                ·
                  refine ⟨118102865533107209839295345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314940974754952559571454253 118102865533107209839295345)
                  ·
                    refine ⟨88577149149830407379471509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118102865533107209839295345 88577149149830407379471509)
                    ·
                      refine ⟨4152053866398300345912727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88577149149830407379471509 4152053866398300345912727)
                      ·
                        rfl

theorem cell23_8086096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_8086096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086096 prefixEnd_8086096 := by exact prefixLift 8086096
  have htrace : WordTrace (prefixWord ++ tailWord_8086096) baseStart_8086096 baseEnd_8086096 := by
    simpa [prefixWord, tailWord_8086096, baseEnd_8086096] using wordTrace_append hprefix tailTrace_8086096
  have hstable : (prefixWord ++ tailWord_8086096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086096).length < 2 ^ (prefixWord ++ tailWord_8086096).sum := by decide
  have hdescent : baseEnd_8086096 < baseStart_8086096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086137 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 3]
def baseStart_8086137 : Nat := 118140960795 + 8086137 * 2 ^ 59
def prefixEnd_8086137 : Nat := 4983230072969 + 3 ^ 40 * 8086137 * 2
def baseEnd_8086137 : Nat := 4152074919105134685500039

theorem tailTrace_8086137 : CollatzResearch.WordTrace tailWord_8086137 prefixEnd_8086137 4152074919105134685500039 := by
  unfold tailWord_8086137
  simp only [CollatzResearch.WordTrace]
  refine ⟨294925645506314126097504665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196617097004209417398336443 294925645506314126097504665)
  ·
    refine ⟨221194234129735594573128499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294925645506314126097504665 221194234129735594573128499)
    ·
      refine ⟨331791351194603391859692749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221194234129735594573128499 331791351194603391859692749)
      ·
        refine ⟨124421756697976271947384781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331791351194603391859692749 124421756697976271947384781)
        ·
          refine ⟨46658158761741101980269293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124421756697976271947384781 46658158761741101980269293)
          ·
            refine ⟨17496809535652913242600985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46658158761741101980269293 17496809535652913242600985)
            ·
              refine ⟨13122607151739684931950739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17496809535652913242600985 13122607151739684931950739)
              ·
                refine ⟨19683910727609527397926109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13122607151739684931950739 19683910727609527397926109)
                ·
                  refine ⟨7381466522853572774222291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19683910727609527397926109 7381466522853572774222291)
                  ·
                    refine ⟨11072199784280359161333437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7381466522853572774222291 11072199784280359161333437)
                    ·
                      refine ⟨4152074919105134685500039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11072199784280359161333437 4152074919105134685500039)
                      ·
                        rfl

theorem cell23_8086137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_8086137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086137 prefixEnd_8086137 := by exact prefixLift 8086137
  have htrace : WordTrace (prefixWord ++ tailWord_8086137) baseStart_8086137 baseEnd_8086137 := by
    simpa [prefixWord, tailWord_8086137, baseEnd_8086137] using wordTrace_append hprefix tailTrace_8086137
  have hstable : (prefixWord ++ tailWord_8086137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086137).length < 2 ^ (prefixWord ++ tailWord_8086137).sum := by decide
  have hdescent : baseEnd_8086137 < baseStart_8086137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086143 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_8086143 : Nat := 118140960795 + 8086143 * 2 ^ 59
def prefixEnd_8086143 : Nat := 4983230072969 + 3 ^ 40 * 8086143 * 2
def baseEnd_8086143 : Nat := 4152077999989061662025011

theorem tailTrace_8086143 : CollatzResearch.WordTrace tailWord_8086143 prefixEnd_8086143 4152077999989061662025011 := by
  unfold tailWord_8086143
  simp only [CollatzResearch.WordTrace]
  refine ⟨294925864344292389122223083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196617242896194926081482055 294925864344292389122223083)
  ·
    refine ⟨442388796516438583683334625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294925864344292389122223083 442388796516438583683334625)
    ·
      refine ⟨331791597387328937762500969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442388796516438583683334625 331791597387328937762500969)
      ·
        refine ⟨248843698040496703321875727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331791597387328937762500969 248843698040496703321875727)
        ·
          refine ⟨373265547060745054982813591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248843698040496703321875727 373265547060745054982813591)
          ·
            refine ⟨559898320591117582474220387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373265547060745054982813591 559898320591117582474220387)
            ·
              refine ⟨839847480886676373711330581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559898320591117582474220387 839847480886676373711330581)
              ·
                refine ⟨39367850666562955017718621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 839847480886676373711330581 39367850666562955017718621)
                ·
                  refine ⟨14762943999961108131644483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39367850666562955017718621 14762943999961108131644483)
                  ·
                    refine ⟨22144415999941662197466725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14762943999961108131644483 22144415999941662197466725)
                    ·
                      refine ⟨4152077999989061662025011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22144415999941662197466725 4152077999989061662025011)
                      ·
                        rfl

theorem cell23_8086143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_8086143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086143 prefixEnd_8086143 := by exact prefixLift 8086143
  have htrace : WordTrace (prefixWord ++ tailWord_8086143) baseStart_8086143 baseEnd_8086143 := by
    simpa [prefixWord, tailWord_8086143, baseEnd_8086143] using wordTrace_append hprefix tailTrace_8086143
  have hstable : (prefixWord ++ tailWord_8086143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086143).length < 2 ^ (prefixWord ++ tailWord_8086143).sum := by decide
  have hdescent : baseEnd_8086143 < baseStart_8086143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086180 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_8086180 : Nat := 118140960795 + 8086180 * 2 ^ 59
def prefixEnd_8086180 : Nat := 4983230072969 + 3 ^ 40 * 8086180 * 2
def baseEnd_8086180 : Nat := 4152096998773278017262341

theorem tailTrace_8086180 : CollatzResearch.WordTrace tailWord_8086180 prefixEnd_8086180 4152096998773278017262341 := by
  unfold tailWord_8086180
  simp only [CollatzResearch.WordTrace]
  refine ⟨147463606922579172220659997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196618142563438896294213329 147463606922579172220659997)
  ·
    refine ⟨55298852595967189582747499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147463606922579172220659997 55298852595967189582747499)
    ·
      refine ⟨82948278893950784374121249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55298852595967189582747499 82948278893950784374121249)
      ·
        refine ⟨62211209170463088280590937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82948278893950784374121249 62211209170463088280590937)
        ·
          refine ⟨46658406877847316210443203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62211209170463088280590937 46658406877847316210443203)
          ·
            refine ⟨69987610316770974315664805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46658406877847316210443203 69987610316770974315664805)
            ·
              refine ⟨13122676934394557684187151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69987610316770974315664805 13122676934394557684187151)
              ·
                refine ⟨19684015401591836526280727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13122676934394557684187151 19684015401591836526280727)
                ·
                  refine ⟨29526023102387754789421091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19684015401591836526280727 29526023102387754789421091)
                  ·
                    refine ⟨44289034653581632184131637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29526023102387754789421091 44289034653581632184131637)
                    ·
                      refine ⟨4152096998773278017262341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44289034653581632184131637 4152096998773278017262341)
                      ·
                        rfl

theorem cell23_8086180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_8086180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086180 prefixEnd_8086180 := by exact prefixLift 8086180
  have htrace : WordTrace (prefixWord ++ tailWord_8086180) baseStart_8086180 baseEnd_8086180 := by
    simpa [prefixWord, tailWord_8086180, baseEnd_8086180] using wordTrace_append hprefix tailTrace_8086180
  have hstable : (prefixWord ++ tailWord_8086180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086180).length < 2 ^ (prefixWord ++ tailWord_8086180).sum := by decide
  have hdescent : baseEnd_8086180 < baseStart_8086180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086244 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_8086244 : Nat := 118140960795 + 8086244 * 2 ^ 59
def prefixEnd_8086244 : Nat := 4983230072969 + 3 ^ 40 * 8086244 * 2
def baseEnd_8086244 : Nat := 4152129861535165766862047

theorem tailTrace_8086244 : CollatzResearch.WordTrace tailWord_8086244 prefixEnd_8086244 4152129861535165766862047 := by
  unfold tailWord_8086244
  simp only [CollatzResearch.WordTrace]
  refine ⟨147464774058463241685824893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196619698744617655581099857 147464774058463241685824893)
  ·
    refine ⟨55299290271923715632184335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147464774058463241685824893 55299290271923715632184335)
    ·
      refine ⟨82948935407885573448276503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55299290271923715632184335 82948935407885573448276503)
      ·
        refine ⟨124423403111828360172414755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82948935407885573448276503 124423403111828360172414755)
        ·
          refine ⟨186635104667742540258622133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124423403111828360172414755 186635104667742540258622133)
          ·
            refine ⟨17497041062600863149245825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186635104667742540258622133 17497041062600863149245825)
            ·
              refine ⟨13122780796950647361934369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17497041062600863149245825 13122780796950647361934369)
              ·
                refine ⟨9842085597712985521450777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13122780796950647361934369 9842085597712985521450777)
                ·
                  refine ⟨7381564198284739141088083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9842085597712985521450777 7381564198284739141088083)
                  ·
                    refine ⟨11072346297427108711632125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7381564198284739141088083 11072346297427108711632125)
                    ·
                      refine ⟨4152129861535165766862047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11072346297427108711632125 4152129861535165766862047)
                      ·
                        rfl

theorem cell23_8086244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_8086244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086244 prefixEnd_8086244 := by exact prefixLift 8086244
  have htrace : WordTrace (prefixWord ++ tailWord_8086244) baseStart_8086244 baseEnd_8086244 := by
    simpa [prefixWord, tailWord_8086244, baseEnd_8086244] using wordTrace_append hprefix tailTrace_8086244
  have hstable : (prefixWord ++ tailWord_8086244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086244).length < 2 ^ (prefixWord ++ tailWord_8086244).sum := by decide
  have hdescent : baseEnd_8086244 < baseStart_8086244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086283 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_8086283 : Nat := 118140960795 + 8086283 * 2 ^ 59
def prefixEnd_8086283 : Nat := 4983230072969 + 3 ^ 40 * 8086283 * 2
def baseEnd_8086283 : Nat := 4152149887280691114274367

theorem tailTrace_8086283 : CollatzResearch.WordTrace tailWord_8086283 prefixEnd_8086283 4152149887280691114274367 := by
  unfold tailWord_8086283
  simp only [CollatzResearch.WordTrace]
  refine ⟨294930970563785193032319503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196620647042523462021546335 294930970563785193032319503)
  ·
    refine ⟨442396455845677789548479255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294930970563785193032319503 442396455845677789548479255)
    ·
      refine ⟨663594683768516684322718883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442396455845677789548479255 663594683768516684322718883)
      ·
        refine ⟨995392025652775026484078325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663594683768516684322718883 995392025652775026484078325)
        ·
          refine ⟨93318002404947658732882343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 995392025652775026484078325 93318002404947658732882343)
          ·
            refine ⟨139977003607421488099323515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93318002404947658732882343 139977003607421488099323515)
            ·
              refine ⟨209965505411132232148985273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139977003607421488099323515 209965505411132232148985273)
              ·
                refine ⟨157474129058349174111738955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209965505411132232148985273 157474129058349174111738955)
                ·
                  refine ⟨236211193587523761167608433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157474129058349174111738955 236211193587523761167608433)
                  ·
                    refine ⟨177158395190642820875706325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236211193587523761167608433 177158395190642820875706325)
                    ·
                      refine ⟨4152149887280691114274367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177158395190642820875706325 4152149887280691114274367)
                      ·
                        rfl

theorem cell23_8086283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_8086283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086283 prefixEnd_8086283 := by exact prefixLift 8086283
  have htrace : WordTrace (prefixWord ++ tailWord_8086283) baseStart_8086283 baseEnd_8086283 := by
    simpa [prefixWord, tailWord_8086283, baseEnd_8086283] using wordTrace_append hprefix tailTrace_8086283
  have hstable : (prefixWord ++ tailWord_8086283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086283).length < 2 ^ (prefixWord ++ tailWord_8086283).sum := by decide
  have hdescent : baseEnd_8086283 < baseStart_8086283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086357 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_8086357 : Nat := 118140960795 + 8086357 * 2 ^ 59
def prefixEnd_8086357 : Nat := 4983230072969 + 3 ^ 40 * 8086357 * 2
def baseEnd_8086357 : Nat := 4152187884849123824749027

theorem tailTrace_8086357 : CollatzResearch.WordTrace tailWord_8086357 prefixEnd_8086357 4152187884849123824749027 := by
  unfold tailWord_8086357
  simp only [CollatzResearch.WordTrace]
  refine ⟨294933669565517103670513325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196622446377011402447008883 294933669565517103670513325)
  ·
    refine ⟨110600126087068913876442497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294933669565517103670513325 110600126087068913876442497)
    ·
      refine ⟨82950094565301685407331873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110600126087068913876442497 82950094565301685407331873)
      ·
        refine ⟨62212570923976264055498905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82950094565301685407331873 62212570923976264055498905)
        ·
          refine ⟨46659428192982198041624179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62212570923976264055498905 46659428192982198041624179)
          ·
            refine ⟨69989142289473297062436269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46659428192982198041624179 69989142289473297062436269)
            ·
              refine ⟨26245928358552486398413601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69989142289473297062436269 26245928358552486398413601)
              ·
                refine ⟨19684446268914364798810201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26245928358552486398413601 19684446268914364798810201)
                ·
                  refine ⟨14763334701685773599107651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19684446268914364798810201 14763334701685773599107651)
                  ·
                    refine ⟨22145002052528660398661477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14763334701685773599107651 22145002052528660398661477)
                    ·
                      refine ⟨4152187884849123824749027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22145002052528660398661477 4152187884849123824749027)
                      ·
                        rfl

theorem cell23_8086357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_8086357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086357 prefixEnd_8086357 := by exact prefixLift 8086357
  have htrace : WordTrace (prefixWord ++ tailWord_8086357) baseStart_8086357 baseEnd_8086357 := by
    simpa [prefixWord, tailWord_8086357, baseEnd_8086357] using wordTrace_append hprefix tailTrace_8086357
  have hstable : (prefixWord ++ tailWord_8086357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086357).length < 2 ^ (prefixWord ++ tailWord_8086357).sum := by decide
  have hdescent : baseEnd_8086357 < baseStart_8086357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086417 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_8086417 : Nat := 118140960795 + 8086417 * 2 ^ 59
def prefixEnd_8086417 : Nat := 4983230072969 + 3 ^ 40 * 8086417 * 2
def baseEnd_8086417 : Nat := 4152218693688393589998751

theorem tailTrace_8086417 : CollatzResearch.WordTrace tailWord_8086417 prefixEnd_8086417 4152218693688393589998751 := by
  unfold tailWord_8086417
  simp only [CollatzResearch.WordTrace]
  refine ⟨294935857945299733917697505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196623905296866489278465003 294935857945299733917697505)
  ·
    refine ⟨221201893458974800438273129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294935857945299733917697505 221201893458974800438273129)
    ·
      refine ⟨165901420094231100328704847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221201893458974800438273129 165901420094231100328704847)
      ·
        refine ⟨248852130141346650493057271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165901420094231100328704847 248852130141346650493057271)
        ·
          refine ⟨373278195212019975739585907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248852130141346650493057271 373278195212019975739585907)
          ·
            refine ⟨559917292818029963609378861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373278195212019975739585907 559917292818029963609378861)
            ·
              refine ⟨209968984806761236353517073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559917292818029963609378861 209968984806761236353517073)
              ·
                refine ⟨157476738605070927265137805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209968984806761236353517073 157476738605070927265137805)
                ·
                  refine ⟨59053776976901597724426677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157476738605070927265137805 59053776976901597724426677)
                  ·
                    refine ⟨5536291591584524786665001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59053776976901597724426677 5536291591584524786665001)
                    ·
                      refine ⟨4152218693688393589998751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536291591584524786665001 4152218693688393589998751)
                      ·
                        rfl

theorem cell23_8086417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_8086417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086417 prefixEnd_8086417 := by exact prefixLift 8086417
  have htrace : WordTrace (prefixWord ++ tailWord_8086417) baseStart_8086417 baseEnd_8086417 := by
    simpa [prefixWord, tailWord_8086417, baseEnd_8086417] using wordTrace_append hprefix tailTrace_8086417
  have hstable : (prefixWord ++ tailWord_8086417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086417).length < 2 ^ (prefixWord ++ tailWord_8086417).sum := by decide
  have hdescent : baseEnd_8086417 < baseStart_8086417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086418 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_8086418 : Nat := 118140960795 + 8086418 * 2 ^ 59
def prefixEnd_8086418 : Nat := 4983230072969 + 3 ^ 40 * 8086418 * 2
def baseEnd_8086418 : Nat := 1384073069056349362028749

theorem tailTrace_8086418 : CollatzResearch.WordTrace tailWord_8086418 prefixEnd_8086418 1384073069056349362028749 := by
  unfold tailWord_8086418
  simp only [CollatzResearch.WordTrace]
  refine ⟨73733973604574027772120977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196623929612197407392322605 73733973604574027772120977)
  ·
    refine ⟨55300480203430520829090733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73733973604574027772120977 55300480203430520829090733)
    ·
      refine ⟨20737680076286445310909025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55300480203430520829090733 20737680076286445310909025)
      ·
        refine ⟨15553260057214833983181769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20737680076286445310909025 15553260057214833983181769)
        ·
          refine ⟨11664945042911125487386327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15553260057214833983181769 11664945042911125487386327)
          ·
            refine ⟨17497417564366688231079491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11664945042911125487386327 17497417564366688231079491)
            ·
              refine ⟨26246126346550032346619237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17497417564366688231079491 26246126346550032346619237)
              ·
                refine ⟨4921148689978131064991107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26246126346550032346619237 4921148689978131064991107)
                ·
                  refine ⟨7381723034967196597486661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921148689978131064991107 7381723034967196597486661)
                  ·
                    refine ⟨1384073069056349362028749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7381723034967196597486661 1384073069056349362028749)
                    ·
                      rfl

theorem cell23_8086418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_8086418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086418 prefixEnd_8086418 := by exact prefixLift 8086418
  have htrace : WordTrace (prefixWord ++ tailWord_8086418) baseStart_8086418 baseEnd_8086418 := by
    simpa [prefixWord, tailWord_8086418, baseEnd_8086418] using wordTrace_append hprefix tailTrace_8086418
  have hstable : (prefixWord ++ tailWord_8086418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086418).length < 2 ^ (prefixWord ++ tailWord_8086418).sum := by decide
  have hdescent : baseEnd_8086418 < baseStart_8086418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086445 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_8086445 : Nat := 118140960795 + 8086445 * 2 ^ 59
def prefixEnd_8086445 : Nat := 4983230072969 + 3 ^ 40 * 8086445 * 2
def baseEnd_8086445 : Nat := 4152233071146719480448623

theorem tailTrace_8086445 : CollatzResearch.WordTrace tailWord_8086445 prefixEnd_8086445 4152233071146719480448623 := by
  unfold tailWord_8086445
  simp only [CollatzResearch.WordTrace]
  refine ⟨294936879189198294699716789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196624586126132196466477859 294936879189198294699716789)
  ·
    refine ⟨27650332423987340128098449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294936879189198294699716789 27650332423987340128098449)
    ·
      refine ⟨20737749317990505096073837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27650332423987340128098449 20737749317990505096073837)
      ·
        refine ⟨7776655994246439411027689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20737749317990505096073837 7776655994246439411027689)
        ·
          refine ⟨5832491995684829558270767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7776655994246439411027689 5832491995684829558270767)
          ·
            refine ⟨8748737993527244337406151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832491995684829558270767 8748737993527244337406151)
            ·
              refine ⟨13123106990290866506109227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748737993527244337406151 13123106990290866506109227)
              ·
                refine ⟨19684660485436299759163841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13123106990290866506109227 19684660485436299759163841)
                ·
                  refine ⟨14763495364077224819372881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19684660485436299759163841 14763495364077224819372881)
                  ·
                    refine ⟨11072621523057918614529661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14763495364077224819372881 11072621523057918614529661)
                    ·
                      refine ⟨4152233071146719480448623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11072621523057918614529661 4152233071146719480448623)
                      ·
                        rfl

theorem cell23_8086445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_8086445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086445 prefixEnd_8086445 := by exact prefixLift 8086445
  have htrace : WordTrace (prefixWord ++ tailWord_8086445) baseStart_8086445 baseEnd_8086445 := by
    simpa [prefixWord, tailWord_8086445, baseEnd_8086445] using wordTrace_append hprefix tailTrace_8086445
  have hstable : (prefixWord ++ tailWord_8086445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086445).length < 2 ^ (prefixWord ++ tailWord_8086445).sum := by decide
  have hdescent : baseEnd_8086445 < baseStart_8086445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086447 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 8, 2]
def baseStart_8086447 : Nat := 118140960795 + 8086447 * 2 ^ 59
def prefixEnd_8086447 : Nat := 4983230072969 + 3 ^ 40 * 8086447 * 2
def baseEnd_8086447 : Nat := 4152234098108028472623613

theorem tailTrace_8086447 : CollatzResearch.WordTrace tailWord_8086447 prefixEnd_8086447 4152234098108028472623613 := by
  unfold tailWord_8086447
  simp only [CollatzResearch.WordTrace]
  refine ⟨294936952135191049041289595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196624634756794032694193063 294936952135191049041289595)
  ·
    refine ⟨442405428202786573561934393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294936952135191049041289595 442405428202786573561934393)
    ·
      refine ⟨331804071152089930171450795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442405428202786573561934393 331804071152089930171450795)
      ·
        refine ⟨497706106728134895257176193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331804071152089930171450795 497706106728134895257176193)
        ·
          refine ⟨373279580046101171442882145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497706106728134895257176193 373279580046101171442882145)
          ·
            refine ⟨279959685034575878582161609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373279580046101171442882145 279959685034575878582161609)
            ·
              refine ⟨209969763775931908936621207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279959685034575878582161609 209969763775931908936621207)
              ·
                refine ⟨314954645663897863404931811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209969763775931908936621207 314954645663897863404931811)
                ·
                  refine ⟨472431968495846795107397717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314954645663897863404931811 472431968495846795107397717)
                  ·
                    refine ⟨5536312130810704630164817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 472431968495846795107397717 5536312130810704630164817)
                    ·
                      refine ⟨4152234098108028472623613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536312130810704630164817 4152234098108028472623613)
                      ·
                        rfl

theorem cell23_8086447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8, 2].length) (baseStart_8086447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086447 prefixEnd_8086447 := by exact prefixLift 8086447
  have htrace : WordTrace (prefixWord ++ tailWord_8086447) baseStart_8086447 baseEnd_8086447 := by
    simpa [prefixWord, tailWord_8086447, baseEnd_8086447] using wordTrace_append hprefix tailTrace_8086447
  have hstable : (prefixWord ++ tailWord_8086447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086447).length < 2 ^ (prefixWord ++ tailWord_8086447).sum := by decide
  have hdescent : baseEnd_8086447 < baseStart_8086447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086457 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_8086457 : Nat := 118140960795 + 8086457 * 2 ^ 59
def prefixEnd_8086457 : Nat := 4983230072969 + 3 ^ 40 * 8086457 * 2
def baseEnd_8086457 : Nat := 1384079744304857811166189

theorem tailTrace_8086457 : CollatzResearch.WordTrace tailWord_8086457 prefixEnd_8086457 1384079744304857811166189 := by
  unfold tailWord_8086457
  simp only [CollatzResearch.WordTrace]
  refine ⟨294937316865154820749153625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196624877910103213832769083 294937316865154820749153625)
  ·
    refine ⟨221202987648866115561865219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294937316865154820749153625 221202987648866115561865219)
    ·
      refine ⟨331804481473299173342797829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221202987648866115561865219 331804481473299173342797829)
      ·
        refine ⟨62213340276243595001774593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331804481473299173342797829 62213340276243595001774593)
        ·
          refine ⟨46660005207182696251330945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62213340276243595001774593 46660005207182696251330945)
          ·
            refine ⟨34995003905387022188498209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46660005207182696251330945 34995003905387022188498209)
            ·
              refine ⟨26246252929040266641373657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34995003905387022188498209 26246252929040266641373657)
              ·
                refine ⟨19684689696780199981030243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26246252929040266641373657 19684689696780199981030243)
                ·
                  refine ⟨29527034545170299971545365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19684689696780199981030243 29527034545170299971545365)
                  ·
                    refine ⟨1384079744304857811166189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29527034545170299971545365 1384079744304857811166189)
                    ·
                      rfl

theorem cell23_8086457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_8086457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086457 prefixEnd_8086457 := by exact prefixLift 8086457
  have htrace : WordTrace (prefixWord ++ tailWord_8086457) baseStart_8086457 baseEnd_8086457 := by
    simpa [prefixWord, tailWord_8086457, baseEnd_8086457] using wordTrace_append hprefix tailTrace_8086457
  have hstable : (prefixWord ++ tailWord_8086457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086457).length < 2 ^ (prefixWord ++ tailWord_8086457).sum := by decide
  have hdescent : baseEnd_8086457 < baseStart_8086457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086464 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_8086464 : Nat := 118140960795 + 8086464 * 2 ^ 59
def prefixEnd_8086464 : Nat := 4983230072969 + 3 ^ 40 * 8086464 * 2
def baseEnd_8086464 : Nat := 4152242827279154906111035

theorem tailTrace_8086464 : CollatzResearch.WordTrace tailWord_8086464 prefixEnd_8086464 4152242827279154906111035 := by
  unfold tailWord_8086464
  simp only [CollatzResearch.WordTrace]
  refine ⟨147468786088064730472329223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196625048117419640629772297 147468786088064730472329223)
  ·
    refine ⟨221203179132097095708493835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147468786088064730472329223 221203179132097095708493835)
    ·
      refine ⟨331804768698145643562740753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221203179132097095708493835 331804768698145643562740753)
      ·
        refine ⟨248853576523609232672055565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331804768698145643562740753 248853576523609232672055565)
        ·
          refine ⟨93320091196353462252020837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248853576523609232672055565 93320091196353462252020837)
          ·
            refine ⟨17497517099316274172253907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93320091196353462252020837 17497517099316274172253907)
            ·
              refine ⟨26246275648974411258380861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17497517099316274172253907 26246275648974411258380861)
              ·
                refine ⟨9842353368365404221892823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26246275648974411258380861 9842353368365404221892823)
                ·
                  refine ⟨14763530052548106332839235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842353368365404221892823 14763530052548106332839235)
                  ·
                    refine ⟨22145295078822159499258853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14763530052548106332839235 22145295078822159499258853)
                    ·
                      refine ⟨4152242827279154906111035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22145295078822159499258853 4152242827279154906111035)
                      ·
                        rfl

theorem cell23_8086464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_8086464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086464 prefixEnd_8086464 := by exact prefixLift 8086464
  have htrace : WordTrace (prefixWord ++ tailWord_8086464) baseStart_8086464 baseEnd_8086464 := by
    simpa [prefixWord, tailWord_8086464, baseEnd_8086464] using wordTrace_append hprefix tailTrace_8086464
  have hstable : (prefixWord ++ tailWord_8086464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086464).length < 2 ^ (prefixWord ++ tailWord_8086464).sum := by decide
  have hdescent : baseEnd_8086464 < baseStart_8086464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086480 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_8086480 : Nat := 118140960795 + 8086480 * 2 ^ 59
def prefixEnd_8086480 : Nat := 4983230072969 + 3 ^ 40 * 8086480 * 2
def baseEnd_8086480 : Nat := 4152251042969626843510961

theorem tailTrace_8086480 : CollatzResearch.WordTrace tailWord_8086480 prefixEnd_8086480 4152251042969626843510961 := by
  unfold tailWord_8086480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147469077872035747838620447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196625437162714330451493929 147469077872035747838620447)
  ·
    refine ⟨221203616808053621757930671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147469077872035747838620447 221203616808053621757930671)
    ·
      refine ⟨331805425212080432636896007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221203616808053621757930671 331805425212080432636896007)
      ·
        refine ⟨497708137818120648955344011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331805425212080432636896007 497708137818120648955344011)
        ·
          refine ⟨746562206727180973433016017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497708137818120648955344011 746562206727180973433016017)
          ·
            refine ⟨559921655045385730074762013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746562206727180973433016017 559921655045385730074762013)
            ·
              refine ⟨209970620642019648778035755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559921655045385730074762013 209970620642019648778035755)
              ·
                refine ⟨314955930963029473167053633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209970620642019648778035755 314955930963029473167053633)
                ·
                  refine ⟨236216948222272104875290225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314955930963029473167053633 236216948222272104875290225)
                  ·
                    refine ⟨177162711166704078656467669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236216948222272104875290225 177162711166704078656467669)
                    ·
                      refine ⟨4152251042969626843510961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177162711166704078656467669 4152251042969626843510961)
                      ·
                        rfl

theorem cell23_8086480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_8086480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086480 prefixEnd_8086480 := by exact prefixLift 8086480
  have htrace : WordTrace (prefixWord ++ tailWord_8086480) baseStart_8086480 baseEnd_8086480 := by
    simpa [prefixWord, tailWord_8086480, baseEnd_8086480] using wordTrace_append hprefix tailTrace_8086480
  have hstable : (prefixWord ++ tailWord_8086480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086480).length < 2 ^ (prefixWord ++ tailWord_8086480).sum := by decide
  have hdescent : baseEnd_8086480 < baseStart_8086480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086481 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_8086481 : Nat := 118140960795 + 8086481 * 2 ^ 59
def prefixEnd_8086481 : Nat := 4983230072969 + 3 ^ 40 * 8086481 * 2
def baseEnd_8086481 : Nat := 4152251556450281339598457

theorem tailTrace_8086481 : CollatzResearch.WordTrace tailWord_8086481 prefixEnd_8086481 4152251556450281339598457 := by
  unfold tailWord_8086481
  simp only [CollatzResearch.WordTrace]
  refine ⟨294938192217067872848027297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196625461478045248565351531 294938192217067872848027297)
  ·
    refine ⟨221203644162800904636020473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294938192217067872848027297 221203644162800904636020473)
    ·
      refine ⟨165902733122100678477015355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221203644162800904636020473 165902733122100678477015355)
      ·
        refine ⟨248854099683151017715523033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165902733122100678477015355 248854099683151017715523033)
        ·
          refine ⟨186640574762363263286642275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248854099683151017715523033 186640574762363263286642275)
          ·
            refine ⟨279960862143544894929963413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186640574762363263286642275 279960862143544894929963413)
            ·
              refine ⟨13123165412978666949842035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279960862143544894929963413 13123165412978666949842035)
              ·
                refine ⟨19684748119468000424763053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13123165412978666949842035 19684748119468000424763053)
                ·
                  refine ⟨7381780544800500159286145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19684748119468000424763053 7381780544800500159286145)
                  ·
                    refine ⟨5536335408600375119464609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381780544800500159286145 5536335408600375119464609)
                    ·
                      refine ⟨4152251556450281339598457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536335408600375119464609 4152251556450281339598457)
                      ·
                        rfl

theorem cell23_8086481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_8086481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086481 prefixEnd_8086481 := by exact prefixLift 8086481
  have htrace : WordTrace (prefixWord ++ tailWord_8086481) baseStart_8086481 baseEnd_8086481 := by
    simpa [prefixWord, tailWord_8086481, baseEnd_8086481] using wordTrace_append hprefix tailTrace_8086481
  have hstable : (prefixWord ++ tailWord_8086481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086481).length < 2 ^ (prefixWord ++ tailWord_8086481).sum := by decide
  have hdescent : baseEnd_8086481 < baseStart_8086481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086484 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_8086484 : Nat := 118140960795 + 8086484 * 2 ^ 59
def prefixEnd_8086484 : Nat := 4983230072969 + 3 ^ 40 * 8086484 * 2
def baseEnd_8086484 : Nat := 4152253096892244827860943

theorem tailTrace_8086484 : CollatzResearch.WordTrace tailWord_8086484 prefixEnd_8086484 4152253096892244827860943 := by
  unfold tailWord_8086484
  simp only [CollatzResearch.WordTrace]
  refine ⟨147469150818028502180193253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196625534424038002906924337 147469150818028502180193253)
  ·
    refine ⟨27650465778380344158786235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147469150818028502180193253 27650465778380344158786235)
    ·
      refine ⟨41475698667570516238179353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27650465778380344158786235 41475698667570516238179353)
      ·
        refine ⟨31106774000677887178634515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41475698667570516238179353 31106774000677887178634515)
        ·
          refine ⟨46660161001016830767951773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31106774000677887178634515 46660161001016830767951773)
          ·
            refine ⟨17497560375381311537981915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46660161001016830767951773 17497560375381311537981915)
            ·
              refine ⟨26246340563071967306972873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17497560375381311537981915 26246340563071967306972873)
              ·
                refine ⟨19684755422303975480229655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26246340563071967306972873 19684755422303975480229655)
                ·
                  refine ⟨29527133133455963220344483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19684755422303975480229655 29527133133455963220344483)
                  ·
                    refine ⟨44290699700183944830516725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29527133133455963220344483 44290699700183944830516725)
                    ·
                      refine ⟨4152253096892244827860943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44290699700183944830516725 4152253096892244827860943)
                      ·
                        rfl

theorem cell23_8086484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_8086484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086484 prefixEnd_8086484 := by exact prefixLift 8086484
  have htrace : WordTrace (prefixWord ++ tailWord_8086484) baseStart_8086484 baseEnd_8086484 := by
    simpa [prefixWord, tailWord_8086484, baseEnd_8086484] using wordTrace_append hprefix tailTrace_8086484
  have hstable : (prefixWord ++ tailWord_8086484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086484).length < 2 ^ (prefixWord ++ tailWord_8086484).sum := by decide
  have hdescent : baseEnd_8086484 < baseStart_8086484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086498 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_8086498 : Nat := 118140960795 + 8086498 * 2 ^ 59
def prefixEnd_8086498 : Nat := 4983230072969 + 3 ^ 40 * 8086498 * 2
def baseEnd_8086498 : Nat := 4152260285621407773085879

theorem tailTrace_8086498 : CollatzResearch.WordTrace tailWord_8086498 prefixEnd_8086498 4152260285621407773085879 := by
  unfold tailWord_8086498
  simp only [CollatzResearch.WordTrace]
  refine ⟨73734703064501571187849037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196625874838670856500930765 73734703064501571187849037)
  ·
    refine ⟨27650513649188089195443389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73734703064501571187849037 27650513649188089195443389)
    ·
      refine ⟨10368942618445533448291271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27650513649188089195443389 10368942618445533448291271)
      ·
        refine ⟨15553413927668300172436907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368942618445533448291271 15553413927668300172436907)
        ·
          refine ⟨23330120891502450258655361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553413927668300172436907 23330120891502450258655361)
          ·
            refine ⟨17497590668626837693991521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23330120891502450258655361 17497590668626837693991521)
            ·
              refine ⟨13123193001470128270493641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17497590668626837693991521 13123193001470128270493641)
              ·
                refine ⟨9842394751102596202870231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13123193001470128270493641 9842394751102596202870231)
                ·
                  refine ⟨14763592126653894304305347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842394751102596202870231 14763592126653894304305347)
                  ·
                    refine ⟨22145388189980841456458021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14763592126653894304305347 22145388189980841456458021)
                    ·
                      refine ⟨4152260285621407773085879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22145388189980841456458021 4152260285621407773085879)
                      ·
                        rfl

theorem cell23_8086498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_8086498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086498 prefixEnd_8086498 := by exact prefixLift 8086498
  have htrace : WordTrace (prefixWord ++ tailWord_8086498) baseStart_8086498 baseEnd_8086498 := by
    simpa [prefixWord, tailWord_8086498, baseEnd_8086498] using wordTrace_append hprefix tailTrace_8086498
  have hstable : (prefixWord ++ tailWord_8086498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086498).length < 2 ^ (prefixWord ++ tailWord_8086498).sum := by decide
  have hdescent : baseEnd_8086498 < baseStart_8086498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086574 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_8086574 : Nat := 118140960795 + 8086574 * 2 ^ 59
def prefixEnd_8086574 : Nat := 4983230072969 + 3 ^ 40 * 8086574 * 2
def baseEnd_8086574 : Nat := 4152299310151149475735529

theorem tailTrace_8086574 : CollatzResearch.WordTrace tailWord_8086574 prefixEnd_8086574 4152299310151149475735529 := by
  unfold tailWord_8086574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36867698025716368716395347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196627722803820633154108517 36867698025716368716395347)
  ·
    refine ⟨55301547038574553074593021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36867698025716368716395347 55301547038574553074593021)
    ·
      refine ⟨20738080139465457402972383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55301547038574553074593021 20738080139465457402972383)
      ·
        refine ⟨31107120209198186104458575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20738080139465457402972383 31107120209198186104458575)
        ·
          refine ⟨46660680313797279156687863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31107120209198186104458575 46660680313797279156687863)
          ·
            refine ⟨69991020470695918735031795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46660680313797279156687863 69991020470695918735031795)
            ·
              refine ⟨104986530706043878102547693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69991020470695918735031795 104986530706043878102547693)
              ·
                refine ⟨39369949014766454288455385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104986530706043878102547693 39369949014766454288455385)
                ·
                  refine ⟨29527461761074840716341539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39369949014766454288455385 29527461761074840716341539)
                  ·
                    refine ⟨44291192641612261074512309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29527461761074840716341539 44291192641612261074512309)
                    ·
                      refine ⟨4152299310151149475735529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44291192641612261074512309 4152299310151149475735529)
                      ·
                        rfl

theorem cell23_8086574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_8086574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086574 prefixEnd_8086574 := by exact prefixLift 8086574
  have htrace : WordTrace (prefixWord ++ tailWord_8086574) baseStart_8086574 baseEnd_8086574 := by
    simpa [prefixWord, tailWord_8086574, baseEnd_8086574] using wordTrace_append hprefix tailTrace_8086574
  have hstable : (prefixWord ++ tailWord_8086574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086574).length < 2 ^ (prefixWord ++ tailWord_8086574).sum := by decide
  have hdescent : baseEnd_8086574 < baseStart_8086574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086588 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_8086588 : Nat := 118140960795 + 8086588 * 2 ^ 59
def prefixEnd_8086588 : Nat := 4983230072969 + 3 ^ 40 * 8086588 * 2
def baseEnd_8086588 : Nat := 4152306498880312420960465

theorem tailTrace_8086588 : CollatzResearch.WordTrace tailWord_8086588 prefixEnd_8086588 4152306498880312420960465 := by
  unfold tailWord_8086588
  simp only [CollatzResearch.WordTrace]
  refine ⟨147471047413840115061086209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196628063218453486748114945 147471047413840115061086209)
  ·
    refine ⟨110603285560380086295814657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147471047413840115061086209 110603285560380086295814657)
    ·
      refine ⟨82952464170285064721860993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110603285560380086295814657 82952464170285064721860993)
      ·
        refine ⟨62214348127713798541395745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82952464170285064721860993 62214348127713798541395745)
        ·
          refine ⟨46660761095785348906046809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62214348127713798541395745 46660761095785348906046809)
          ·
            refine ⟨34995570821839011679535107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46660761095785348906046809 34995570821839011679535107)
            ·
              refine ⟨52493356232758517519302661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34995570821839011679535107 52493356232758517519302661)
              ·
                refine ⟨9842504293642222034869249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52493356232758517519302661 9842504293642222034869249)
                ·
                  refine ⟨7381878220231666526151937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9842504293642222034869249 7381878220231666526151937)
                  ·
                    refine ⟨5536408665173749894613953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381878220231666526151937 5536408665173749894613953)
                    ·
                      refine ⟨4152306498880312420960465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536408665173749894613953 4152306498880312420960465)
                      ·
                        rfl

theorem cell23_8086588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_8086588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086588 prefixEnd_8086588 := by exact prefixLift 8086588
  have htrace : WordTrace (prefixWord ++ tailWord_8086588) baseStart_8086588 baseEnd_8086588 := by
    simpa [prefixWord, tailWord_8086588, baseEnd_8086588] using wordTrace_append hprefix tailTrace_8086588
  have hstable : (prefixWord ++ tailWord_8086588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086588).length < 2 ^ (prefixWord ++ tailWord_8086588).sum := by decide
  have hdescent : baseEnd_8086588 < baseStart_8086588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086605 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_8086605 : Nat := 118140960795 + 8086605 * 2 ^ 59
def prefixEnd_8086605 : Nat := 4983230072969 + 3 ^ 40 * 8086605 * 2
def baseEnd_8086605 : Nat := 4152315228051438854447887

theorem tailTrace_8086605 : CollatzResearch.WordTrace tailWord_8086605 prefixEnd_8086605 4152315228051438854447887 := by
  unfold tailWord_8086605
  simp only [CollatzResearch.WordTrace]
  refine ⟨294942714868618642025541269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196628476579079094683694179 294942714868618642025541269)
  ·
    refine ⟨13825439759466498844947247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 294942714868618642025541269 13825439759466498844947247)
    ·
      refine ⟨20738159639199748267420871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13825439759466498844947247 20738159639199748267420871)
      ·
        refine ⟨31107239458799622401131307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20738159639199748267420871 31107239458799622401131307)
        ·
          refine ⟨46660859188199433601696961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31107239458799622401131307 46660859188199433601696961)
          ·
            refine ⟨34995644391149575201272721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46660859188199433601696961 34995644391149575201272721)
            ·
              refine ⟨26246733293362181400954541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34995644391149575201272721 26246733293362181400954541)
              ·
                refine ⟨9842524985010818025357953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26246733293362181400954541 9842524985010818025357953)
                ·
                  refine ⟨7381893738758113519018465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9842524985010818025357953 7381893738758113519018465)
                  ·
                    refine ⟨5536420304068585139263849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381893738758113519018465 5536420304068585139263849)
                    ·
                      refine ⟨4152315228051438854447887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536420304068585139263849 4152315228051438854447887)
                      ·
                        rfl

theorem cell23_8086605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_8086605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086605 prefixEnd_8086605 := by exact prefixLift 8086605
  have htrace : WordTrace (prefixWord ++ tailWord_8086605) baseStart_8086605 baseEnd_8086605 := by
    simpa [prefixWord, tailWord_8086605, baseEnd_8086605] using wordTrace_append hprefix tailTrace_8086605
  have hstable : (prefixWord ++ tailWord_8086605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086605).length < 2 ^ (prefixWord ++ tailWord_8086605).sum := by decide
  have hdescent : baseEnd_8086605 < baseStart_8086605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086617 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_8086617 : Nat := 118140960795 + 8086617 * 2 ^ 59
def prefixEnd_8086617 : Nat := 4983230072969 + 3 ^ 40 * 8086617 * 2
def baseEnd_8086617 : Nat := 4152321389819292807497831

theorem tailTrace_8086617 : CollatzResearch.WordTrace tailWord_8086617 prefixEnd_8086617 4152321389819292807497831 := by
  unfold tailWord_8086617
  simp only [CollatzResearch.WordTrace]
  refine ⟨294943152544575168074978105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196628768363050112049985403 294943152544575168074978105)
  ·
    refine ⟨221207364408431376056233579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294943152544575168074978105 221207364408431376056233579)
    ·
      refine ⟨331811046612647064084350369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221207364408431376056233579 331811046612647064084350369)
      ·
        refine ⟨248858284959485298063262777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331811046612647064084350369 248858284959485298063262777)
        ·
          refine ⟨186643713719613973547447083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248858284959485298063262777 186643713719613973547447083)
          ·
            refine ⟨279965570579420960321170625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186643713719613973547447083 279965570579420960321170625)
            ·
              refine ⟨209974177934565720240877969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279965570579420960321170625 209974177934565720240877969)
              ·
                refine ⟨157480633450924290180658477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209974177934565720240877969 157480633450924290180658477)
                ·
                  refine ⟨59055237544096608817746929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157480633450924290180658477 59055237544096608817746929)
                  ·
                    refine ⟨44291428158072456613310197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59055237544096608817746929 44291428158072456613310197)
                    ·
                      refine ⟨4152321389819292807497831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44291428158072456613310197 4152321389819292807497831)
                      ·
                        rfl

theorem cell23_8086617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_8086617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086617 prefixEnd_8086617 := by exact prefixLift 8086617
  have htrace : WordTrace (prefixWord ++ tailWord_8086617) baseStart_8086617 baseEnd_8086617 := by
    simpa [prefixWord, tailWord_8086617, baseEnd_8086617] using wordTrace_append hprefix tailTrace_8086617
  have hstable : (prefixWord ++ tailWord_8086617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086617).length < 2 ^ (prefixWord ++ tailWord_8086617).sum := by decide
  have hdescent : baseEnd_8086617 < baseStart_8086617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086684 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 8]
def baseStart_8086684 : Nat := 118140960795 + 8086684 * 2 ^ 59
def prefixEnd_8086684 : Nat := 4983230072969 + 3 ^ 40 * 8086684 * 2
def baseEnd_8086684 : Nat := 461372865891460449484447

theorem tailTrace_8086684 : CollatzResearch.WordTrace tailWord_8086684 prefixEnd_8086684 461372865891460449484447 := by
  unfold tailWord_8086684
  simp only [CollatzResearch.WordTrace]
  refine ⟨147472798117666219258833553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196630397490221625678444737 147472798117666219258833553)
  ·
    refine ⟨110604598588249664444125165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147472798117666219258833553 110604598588249664444125165)
    ·
      refine ⟨41476724470593624166546937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110604598588249664444125165 41476724470593624166546937)
      ·
        refine ⟨31107543352945218124910203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41476724470593624166546937 31107543352945218124910203)
        ·
          refine ⟨46661315029417827187365305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31107543352945218124910203 46661315029417827187365305)
          ·
            refine ⟨34995986272063370390523979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46661315029417827187365305 34995986272063370390523979)
            ·
              refine ⟨52493979408095055585785969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34995986272063370390523979 52493979408095055585785969)
              ·
                refine ⟨39370484556071291689339477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52493979408095055585785969 39370484556071291689339477)
                ·
                  refine ⟨461372865891460449484447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39370484556071291689339477 461372865891460449484447)
                  ·
                    rfl

theorem cell23_8086684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_8086684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086684 prefixEnd_8086684 := by exact prefixLift 8086684
  have htrace : WordTrace (prefixWord ++ tailWord_8086684) baseStart_8086684 baseEnd_8086684 := by
    simpa [prefixWord, tailWord_8086684, baseEnd_8086684] using wordTrace_append hprefix tailTrace_8086684
  have hstable : (prefixWord ++ tailWord_8086684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086684).length < 2 ^ (prefixWord ++ tailWord_8086684).sum := by decide
  have hdescent : baseEnd_8086684 < baseStart_8086684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086698 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_8086698 : Nat := 118140960795 + 8086698 * 2 ^ 59
def prefixEnd_8086698 : Nat := 4983230072969 + 3 ^ 40 * 8086698 * 2
def baseEnd_8086698 : Nat := 4152362981752306990584959

theorem tailTrace_8086698 : CollatzResearch.WordTrace tailWord_8086698 prefixEnd_8086698 4152362981752306990584959 := by
  unfold tailWord_8086698
  simp only [CollatzResearch.WordTrace]
  refine ⟨73736526714320429727169187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196630737904854479272451165 73736526714320429727169187)
  ·
    refine ⟨110604790071480644590753781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73736526714320429727169187 110604790071480644590753781)
    ·
      refine ⟨10369199069201310430383167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110604790071480644590753781 10369199069201310430383167)
      ·
        refine ⟨15553798603801965645574751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10369199069201310430383167 15553798603801965645574751)
        ·
          refine ⟨23330697905702948468362127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553798603801965645574751 23330697905702948468362127)
          ·
            refine ⟨34996046858554422702543191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23330697905702948468362127 34996046858554422702543191)
            ·
              refine ⟨52494070287831634053814787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34996046858554422702543191 52494070287831634053814787)
              ·
                refine ⟨78741105431747451080722181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52494070287831634053814787 78741105431747451080722181)
                ·
                  refine ⟨14763957268452647077635409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78741105431747451080722181 14763957268452647077635409)
                  ·
                    refine ⟨11072967951339485308226557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14763957268452647077635409 11072967951339485308226557)
                    ·
                      refine ⟨4152362981752306990584959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11072967951339485308226557 4152362981752306990584959)
                      ·
                        rfl

theorem cell23_8086698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_8086698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086698 prefixEnd_8086698 := by exact prefixLift 8086698
  have htrace : WordTrace (prefixWord ++ tailWord_8086698) baseStart_8086698 baseEnd_8086698 := by
    simpa [prefixWord, tailWord_8086698, baseEnd_8086698] using wordTrace_append hprefix tailTrace_8086698
  have hstable : (prefixWord ++ tailWord_8086698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086698).length < 2 ^ (prefixWord ++ tailWord_8086698).sum := by decide
  have hdescent : baseEnd_8086698 < baseStart_8086698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086714 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_8086714 : Nat := 118140960795 + 8086714 * 2 ^ 59
def prefixEnd_8086714 : Nat := 4983230072969 + 3 ^ 40 * 8086714 * 2
def baseEnd_8086714 : Nat := 1384123732480926309328295

theorem tailTrace_8086714 : CollatzResearch.WordTrace tailWord_8086714 prefixEnd_8086714 1384123732480926309328295 := by
  unfold tailWord_8086714
  simp only [CollatzResearch.WordTrace]
  refine ⟨73736672606305938410314799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196631126950149169094172797 73736672606305938410314799)
  ·
    refine ⟨110605008909458907615472199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73736672606305938410314799 110605008909458907615472199)
    ·
      refine ⟨165907513364188361423208299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110605008909458907615472199 165907513364188361423208299)
      ·
        refine ⟨248861270046282542134812449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165907513364188361423208299 248861270046282542134812449)
        ·
          refine ⟨186645952534711906601109337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248861270046282542134812449 186645952534711906601109337)
          ·
            refine ⟨139984464401033929950832003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186645952534711906601109337 139984464401033929950832003)
            ·
              refine ⟨209976696601550894926248005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139984464401033929950832003 209976696601550894926248005)
              ·
                refine ⟨39370630612790792798671501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209976696601550894926248005 39370630612790792798671501)
                ·
                  refine ⟨14763986479796547299501813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39370630612790792798671501 14763986479796547299501813)
                  ·
                    refine ⟨1384123732480926309328295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14763986479796547299501813 1384123732480926309328295)
                    ·
                      rfl

theorem cell23_8086714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_8086714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086714 prefixEnd_8086714 := by exact prefixLift 8086714
  have htrace : WordTrace (prefixWord ++ tailWord_8086714) baseStart_8086714 baseEnd_8086714 := by
    simpa [prefixWord, tailWord_8086714, baseEnd_8086714] using wordTrace_append hprefix tailTrace_8086714
  have hstable : (prefixWord ++ tailWord_8086714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086714).length < 2 ^ (prefixWord ++ tailWord_8086714).sum := by decide
  have hdescent : baseEnd_8086714 < baseStart_8086714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086718 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_8086718 : Nat := 118140960795 + 8086718 * 2 ^ 59
def prefixEnd_8086718 : Nat := 4983230072969 + 3 ^ 40 * 8086718 * 2
def baseEnd_8086718 : Nat := 461374805707266323592763

theorem tailTrace_8086718 : CollatzResearch.WordTrace tailWord_8086718 prefixEnd_8086718 461374805707266323592763 := by
  unfold tailWord_8086718
  simp only [CollatzResearch.WordTrace]
  refine ⟨36868354539651157790550601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196631224211472841549603205 36868354539651157790550601)
  ·
    refine ⟨27651265904738368342912951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36868354539651157790550601 27651265904738368342912951)
    ·
      refine ⟨41476898857107552514369427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27651265904738368342912951 41476898857107552514369427)
      ·
        refine ⟨62215348285661328771554141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41476898857107552514369427 62215348285661328771554141)
        ·
          refine ⟨23330755607122998289332803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62215348285661328771554141 23330755607122998289332803)
          ·
            refine ⟨34996133410684497433999205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23330755607122998289332803 34996133410684497433999205)
            ·
              refine ⟨6561775014503343268874851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34996133410684497433999205 6561775014503343268874851)
              ·
                refine ⟨9842662521755014903312277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6561775014503343268874851 9842662521755014903312277)
                ·
                  refine ⟨461374805707266323592763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9842662521755014903312277 461374805707266323592763)
                  ·
                    rfl

theorem cell23_8086718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_8086718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086718 prefixEnd_8086718 := by exact prefixLift 8086718
  have htrace : WordTrace (prefixWord ++ tailWord_8086718) baseStart_8086718 baseEnd_8086718 := by
    simpa [prefixWord, tailWord_8086718, baseEnd_8086718] using wordTrace_append hprefix tailTrace_8086718
  have hstable : (prefixWord ++ tailWord_8086718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086718).length < 2 ^ (prefixWord ++ tailWord_8086718).sum := by decide
  have hdescent : baseEnd_8086718 < baseStart_8086718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086751 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_8086751 : Nat := 118140960795 + 8086751 * 2 ^ 59
def prefixEnd_8086751 : Nat := 4983230072969 + 3 ^ 40 * 8086751 * 2
def baseEnd_8086751 : Nat := 4152390196226995283222215

theorem tailTrace_8086751 : CollatzResearch.WordTrace tailWord_8086751 prefixEnd_8086751 4152390196226995283222215 := by
  unfold tailWord_8086751
  simp only [CollatzResearch.WordTrace]
  refine ⟨294948039926089708960356107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196632026617393139306904071 294948039926089708960356107)
  ·
    refine ⟨442422059889134563440534161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294948039926089708960356107 442422059889134563440534161)
    ·
      refine ⟨331816544916850922580400621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442422059889134563440534161 331816544916850922580400621)
      ·
        refine ⟨124431204343819095967650233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331816544916850922580400621 124431204343819095967650233)
        ·
          refine ⟨93323403257864321975737675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124431204343819095967650233 93323403257864321975737675)
          ·
            refine ⟨139985104886796482963606513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93323403257864321975737675 139985104886796482963606513)
            ·
              refine ⟨104988828665097362222704885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139985104886796482963606513 104988828665097362222704885)
              ·
                refine ⟨9842702687352877708378583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104988828665097362222704885 9842702687352877708378583)
                ·
                  refine ⟨14764054031029316562567875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842702687352877708378583 14764054031029316562567875)
                  ·
                    refine ⟨22146081046543974843851813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14764054031029316562567875 22146081046543974843851813)
                    ·
                      refine ⟨4152390196226995283222215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22146081046543974843851813 4152390196226995283222215)
                      ·
                        rfl

theorem cell23_8086751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_8086751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086751 prefixEnd_8086751 := by exact prefixLift 8086751
  have htrace : WordTrace (prefixWord ++ tailWord_8086751) baseStart_8086751 baseEnd_8086751 := by
    simpa [prefixWord, tailWord_8086751, baseEnd_8086751] using wordTrace_append hprefix tailTrace_8086751
  have hstable : (prefixWord ++ tailWord_8086751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086751).length < 2 ^ (prefixWord ++ tailWord_8086751).sum := by decide
  have hdescent : baseEnd_8086751 < baseStart_8086751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086762 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_8086762 : Nat := 118140960795 + 8086762 * 2 ^ 59
def prefixEnd_8086762 : Nat := 4983230072969 + 3 ^ 40 * 8086762 * 2
def baseEnd_8086762 : Nat := 4152395844514194740184665

theorem tailTrace_8086762 : CollatzResearch.WordTrace tailWord_8086762 prefixEnd_8086762 4152395844514194740184665 := by
  unfold tailWord_8086762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737110282262464459751635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196632294086033238559337693 73737110282262464459751635)
  ·
    refine ⟨110605665423393696689627453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73737110282262464459751635 110605665423393696689627453)
    ·
      refine ⟨41477124533772636258610295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110605665423393696689627453 41477124533772636258610295)
      ·
        refine ⟨62215686800658954387915443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41477124533772636258610295 62215686800658954387915443)
        ·
          refine ⟨93323530200988431581873165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62215686800658954387915443 93323530200988431581873165)
          ·
            refine ⟨34996323825370661843202437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93323530200988431581873165 34996323825370661843202437)
            ·
              refine ⟨6561810717256999095600457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34996323825370661843202437 6561810717256999095600457)
              ·
                refine ⟨4921358037942749321700343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561810717256999095600457 4921358037942749321700343)
                ·
                  refine ⟨7382037056914123982550515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921358037942749321700343 7382037056914123982550515)
                  ·
                    refine ⟨11073055585371185973825773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382037056914123982550515 11073055585371185973825773)
                    ·
                      refine ⟨4152395844514194740184665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073055585371185973825773 4152395844514194740184665)
                      ·
                        rfl

theorem cell23_8086762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_8086762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086762 prefixEnd_8086762 := by exact prefixLift 8086762
  have htrace : WordTrace (prefixWord ++ tailWord_8086762) baseStart_8086762 baseEnd_8086762 := by
    simpa [prefixWord, tailWord_8086762, baseEnd_8086762] using wordTrace_append hprefix tailTrace_8086762
  have hstable : (prefixWord ++ tailWord_8086762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086762).length < 2 ^ (prefixWord ++ tailWord_8086762).sum := by decide
  have hdescent : baseEnd_8086762 < baseStart_8086762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086771 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3]
def baseStart_8086771 : Nat := 118140960795 + 8086771 * 2 ^ 59
def prefixEnd_8086771 : Nat := 4983230072969 + 3 ^ 40 * 8086771 * 2
def baseEnd_8086771 : Nat := 4152400465840085204972123

theorem tailTrace_8086771 : CollatzResearch.WordTrace tailWord_8086771 prefixEnd_8086771 4152400465840085204972123 := by
  unfold tailWord_8086771
  simp only [CollatzResearch.WordTrace]
  refine ⟨294948769386017252376084167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196632512924011501584056111 294948769386017252376084167)
  ·
    refine ⟨442423154079025878564126251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294948769386017252376084167 442423154079025878564126251)
    ·
      refine ⟨663634731118538817846189377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442423154079025878564126251 663634731118538817846189377)
      ·
        refine ⟨497726048338904113384642033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663634731118538817846189377 497726048338904113384642033)
        ·
          refine ⟨373294536254178085038481525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497726048338904113384642033 373294536254178085038481525)
          ·
            refine ⟨34996362773829195472357643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373294536254178085038481525 34996362773829195472357643)
            ·
              refine ⟨52494544160743793208536465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34996362773829195472357643 52494544160743793208536465)
              ·
                refine ⟨39370908120557844906402349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52494544160743793208536465 39370908120557844906402349)
                ·
                  refine ⟨14764090545209191839900881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39370908120557844906402349 14764090545209191839900881)
                  ·
                    refine ⟨11073067908906893879925661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14764090545209191839900881 11073067908906893879925661)
                    ·
                      refine ⟨4152400465840085204972123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073067908906893879925661 4152400465840085204972123)
                      ·
                        rfl

theorem cell23_8086771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_8086771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086771 prefixEnd_8086771 := by exact prefixLift 8086771
  have htrace : WordTrace (prefixWord ++ tailWord_8086771) baseStart_8086771 baseEnd_8086771 := by
    simpa [prefixWord, tailWord_8086771, baseEnd_8086771] using wordTrace_append hprefix tailTrace_8086771
  have hstable : (prefixWord ++ tailWord_8086771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086771).length < 2 ^ (prefixWord ++ tailWord_8086771).sum := by decide
  have hdescent : baseEnd_8086771 < baseStart_8086771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086785 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_8086785 : Nat := 118140960795 + 8086785 * 2 ^ 59
def prefixEnd_8086785 : Nat := 4983230072969 + 3 ^ 40 * 8086785 * 2
def baseEnd_8086785 : Nat := 4152407654569248150197059

theorem tailTrace_8086785 : CollatzResearch.WordTrace tailWord_8086785 prefixEnd_8086785 4152407654569248150197059 := by
  unfold tailWord_8086785
  simp only [CollatzResearch.WordTrace]
  refine ⟨294949280007966532767093809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196632853338644355178062539 294949280007966532767093809)
  ·
    refine ⟨221211960005974899575320357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294949280007966532767093809 221211960005974899575320357)
    ·
      refine ⟨41477242501120293670372567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221211960005974899575320357 41477242501120293670372567)
      ·
        refine ⟨62215863751680440505558851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41477242501120293670372567 62215863751680440505558851)
        ·
          refine ⟨93323795627520660758338277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62215863751680440505558851 93323795627520660758338277)
          ·
            refine ⟨17498211680160123892188427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93323795627520660758338277 17498211680160123892188427)
            ·
              refine ⟨26247317520240185838282641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498211680160123892188427 26247317520240185838282641)
              ·
                refine ⟨19685488140180139378711981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26247317520240185838282641 19685488140180139378711981)
                ·
                  refine ⟨7382058052567552267016993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19685488140180139378711981 7382058052567552267016993)
                  ·
                    refine ⟨5536543539425664200262745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382058052567552267016993 5536543539425664200262745)
                    ·
                      refine ⟨4152407654569248150197059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536543539425664200262745 4152407654569248150197059)
                      ·
                        rfl

theorem cell23_8086785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_8086785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086785 prefixEnd_8086785 := by exact prefixLift 8086785
  have htrace : WordTrace (prefixWord ++ tailWord_8086785) baseStart_8086785 baseEnd_8086785 := by
    simpa [prefixWord, tailWord_8086785, baseEnd_8086785] using wordTrace_append hprefix tailTrace_8086785
  have hstable : (prefixWord ++ tailWord_8086785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086785).length < 2 ^ (prefixWord ++ tailWord_8086785).sum := by decide
  have hdescent : baseEnd_8086785 < baseStart_8086785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086788 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_8086788 : Nat := 118140960795 + 8086788 * 2 ^ 59
def prefixEnd_8086788 : Nat := 4983230072969 + 3 ^ 40 * 8086788 * 2
def baseEnd_8086788 : Nat := 4152409195011211638459545

theorem tailTrace_8086788 : CollatzResearch.WordTrace tailWord_8086788 prefixEnd_8086788 4152409195011211638459545 := by
  unfold tailWord_8086788
  simp only [CollatzResearch.WordTrace]
  refine ⟨147474694713477832139726509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196632926284637109519635345 147474694713477832139726509)
  ·
    refine ⟨55303010517554187052397441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147474694713477832139726509 55303010517554187052397441)
    ·
      refine ⟨41477257888165640289298081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55303010517554187052397441 41477257888165640289298081)
      ·
        refine ⟨31107943416124230216973561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41477257888165640289298081 31107943416124230216973561)
        ·
          refine ⟨23330957562093172662730171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31107943416124230216973561 23330957562093172662730171)
          ·
            refine ⟨34996436343139758994095257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23330957562093172662730171 34996436343139758994095257)
            ·
              refine ⟨26247327257354819245571443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34996436343139758994095257 26247327257354819245571443)
              ·
                refine ⟨39370990886032228868357165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26247327257354819245571443 39370990886032228868357165)
                ·
                  refine ⟨14764121582262085825633937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39370990886032228868357165 14764121582262085825633937)
                  ·
                    refine ⟨11073091186696564369225453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14764121582262085825633937 11073091186696564369225453)
                    ·
                      refine ⟨4152409195011211638459545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073091186696564369225453 4152409195011211638459545)
                      ·
                        rfl

theorem cell23_8086788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_8086788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086788 prefixEnd_8086788 := by exact prefixLift 8086788
  have htrace : WordTrace (prefixWord ++ tailWord_8086788) baseStart_8086788 baseEnd_8086788 := by
    simpa [prefixWord, tailWord_8086788, baseEnd_8086788] using wordTrace_append hprefix tailTrace_8086788
  have hstable : (prefixWord ++ tailWord_8086788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086788).length < 2 ^ (prefixWord ++ tailWord_8086788).sum := by decide
  have hdescent : baseEnd_8086788 < baseStart_8086788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086801 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_8086801 : Nat := 118140960795 + 8086801 * 2 ^ 59
def prefixEnd_8086801 : Nat := 4983230072969 + 3 ^ 40 * 8086801 * 2
def baseEnd_8086801 : Nat := 4152415870259720087596985

theorem tailTrace_8086801 : CollatzResearch.WordTrace tailWord_8086801 prefixEnd_8086801 4152415870259720087596985 := by
  unfold tailWord_8086801
  simp only [CollatzResearch.WordTrace]
  refine ⟨294949863575908567499676257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196633242383939044999784171 294949863575908567499676257)
  ·
    refine ⟨221212397681931425624757193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294949863575908567499676257 221212397681931425624757193)
    ·
      refine ⟨165909298261448569218567895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221212397681931425624757193 165909298261448569218567895)
      ·
        refine ⟨248863947392172853827851843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165909298261448569218567895 248863947392172853827851843)
        ·
          refine ⟨373295921088259280741777765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248863947392172853827851843 373295921088259280741777765)
          ·
            refine ⟨69992985204048615139083331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373295921088259280741777765 69992985204048615139083331)
            ·
              refine ⟨104989477806072922708624997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69992985204048615139083331 104989477806072922708624997)
              ·
                refine ⟨19685527088638673007867187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104989477806072922708624997 19685527088638673007867187)
                ·
                  refine ⟨29528290632958009511800781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19685527088638673007867187 29528290632958009511800781)
                  ·
                    refine ⟨11073108987359253566925293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29528290632958009511800781 11073108987359253566925293)
                    ·
                      refine ⟨4152415870259720087596985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073108987359253566925293 4152415870259720087596985)
                      ·
                        rfl

theorem cell23_8086801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_8086801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086801 prefixEnd_8086801 := by exact prefixLift 8086801
  have htrace : WordTrace (prefixWord ++ tailWord_8086801) baseStart_8086801 baseEnd_8086801 := by
    simpa [prefixWord, tailWord_8086801, baseEnd_8086801] using wordTrace_append hprefix tailTrace_8086801
  have hstable : (prefixWord ++ tailWord_8086801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086801).length < 2 ^ (prefixWord ++ tailWord_8086801).sum := by decide
  have hdescent : baseEnd_8086801 < baseStart_8086801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086802 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_8086802 : Nat := 118140960795 + 8086802 * 2 ^ 59
def prefixEnd_8086802 : Nat := 4983230072969 + 3 ^ 40 * 8086802 * 2
def baseEnd_8086802 : Nat := 4152416383740374583684481

theorem tailTrace_8086802 : CollatzResearch.WordTrace tailWord_8086802 prefixEnd_8086802 4152416383740374583684481 := by
  unfold tailWord_8086802
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737475012226236167615665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196633266699269963113641773 73737475012226236167615665)
  ·
    refine ⟨55303106259169677125711749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73737475012226236167615665 55303106259169677125711749)
    ·
      refine ⟨10369332423594314461070953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55303106259169677125711749 10369332423594314461070953)
      ·
        refine ⟨7776999317695735845803215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10369332423594314461070953 7776999317695735845803215)
        ·
          refine ⟨11665498976543603768704823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776999317695735845803215 11665498976543603768704823)
          ·
            refine ⟨17498248464815405653057235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11665498976543603768704823 17498248464815405653057235)
            ·
              refine ⟨26247372697223108479585853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498248464815405653057235 26247372697223108479585853)
              ·
                refine ⟨9842764761458665679844695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26247372697223108479585853 9842764761458665679844695)
                ·
                  refine ⟨14764147142187998519767043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9842764761458665679844695 14764147142187998519767043)
                  ·
                    refine ⟨22146220713281997779650565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14764147142187998519767043 22146220713281997779650565)
                    ·
                      refine ⟨4152416383740374583684481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22146220713281997779650565 4152416383740374583684481)
                      ·
                        rfl

theorem cell23_8086802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_8086802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086802 prefixEnd_8086802 := by exact prefixLift 8086802
  have htrace : WordTrace (prefixWord ++ tailWord_8086802) baseStart_8086802 baseEnd_8086802 := by
    simpa [prefixWord, tailWord_8086802, baseEnd_8086802] using wordTrace_append hprefix tailTrace_8086802
  have hstable : (prefixWord ++ tailWord_8086802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086802).length < 2 ^ (prefixWord ++ tailWord_8086802).sum := by decide
  have hdescent : baseEnd_8086802 < baseStart_8086802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086858 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_8086858 : Nat := 118140960795 + 8086858 * 2 ^ 59
def prefixEnd_8086858 : Nat := 4983230072969 + 3 ^ 40 * 8086858 * 2
def baseEnd_8086858 : Nat := 4152445138657026364584223

theorem tailTrace_8086858 : CollatzResearch.WordTrace tailWord_8086858 prefixEnd_8086858 4152445138657026364584223 := by
  unfold tailWord_8086858
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737985634175516558625307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196634628357801377489667485 73737985634175516558625307)
  ·
    refine ⟨110606978451263274837937961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73737985634175516558625307 110606978451263274837937961)
    ·
      refine ⟨82955233838447456128453471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110606978451263274837937961 82955233838447456128453471)
      ·
        refine ⟨124432850757671184192680207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82955233838447456128453471 124432850757671184192680207)
        ·
          refine ⟨186649276136506776289020311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124432850757671184192680207 186649276136506776289020311)
          ·
            refine ⟨279973914204760164433530467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186649276136506776289020311 279973914204760164433530467)
            ·
              refine ⟨419960871307140246650295701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279973914204760164433530467 419960871307140246650295701)
              ·
                refine ⟨19685665842522199061732611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 419960871307140246650295701 19685665842522199061732611)
                ·
                  refine ⟨29528498763783298592598917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19685665842522199061732611 29528498763783298592598917)
                  ·
                    refine ⟨5536593518209368486112297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29528498763783298592598917 5536593518209368486112297)
                    ·
                      refine ⟨4152445138657026364584223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536593518209368486112297 4152445138657026364584223)
                      ·
                        rfl

theorem cell23_8086858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_8086858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086858 prefixEnd_8086858 := by exact prefixLift 8086858
  have htrace : WordTrace (prefixWord ++ tailWord_8086858) baseStart_8086858 baseEnd_8086858 := by
    simpa [prefixWord, tailWord_8086858, baseEnd_8086858] using wordTrace_append hprefix tailTrace_8086858
  have hstable : (prefixWord ++ tailWord_8086858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086858).length < 2 ^ (prefixWord ++ tailWord_8086858).sum := by decide
  have hdescent : baseEnd_8086858 < baseStart_8086858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086870 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8086870 : Nat := 118140960795 + 8086870 * 2 ^ 59
def prefixEnd_8086870 : Nat := 4983230072969 + 3 ^ 40 * 8086870 * 2
def baseEnd_8086870 : Nat := 4152451300424880317634169

theorem tailTrace_8086870 : CollatzResearch.WordTrace tailWord_8086870 prefixEnd_8086870 4152451300424880317634169 := by
  unfold tailWord_8086870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434523763291162017746129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196634920141772394855958709 18434523763291162017746129)
  ·
    refine ⟨13825892822468371513309597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18434523763291162017746129 13825892822468371513309597)
    ·
      refine ⟨5184709808425639317491099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13825892822468371513309597 5184709808425639317491099)
      ·
        refine ⟨7777064712638458976236649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184709808425639317491099 7777064712638458976236649)
        ·
          refine ⟨5832798534478844232177487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7777064712638458976236649 5832798534478844232177487)
          ·
            refine ⟨8749197801718266348266231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832798534478844232177487 8749197801718266348266231)
            ·
              refine ⟨13123796702577399522399347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749197801718266348266231 13123796702577399522399347)
              ·
                refine ⟨19685695053866099283599021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13123796702577399522399347 19685695053866099283599021)
                ·
                  refine ⟨7382135645199787231349633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19685695053866099283599021 7382135645199787231349633)
                  ·
                    refine ⟨5536601733899840423512225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382135645199787231349633 5536601733899840423512225)
                    ·
                      refine ⟨4152451300424880317634169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536601733899840423512225 4152451300424880317634169)
                      ·
                        rfl

theorem cell23_8086870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8086870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086870 prefixEnd_8086870 := by exact prefixLift 8086870
  have htrace : WordTrace (prefixWord ++ tailWord_8086870) baseStart_8086870 baseEnd_8086870 := by
    simpa [prefixWord, tailWord_8086870, baseEnd_8086870] using wordTrace_append hprefix tailTrace_8086870
  have hstable : (prefixWord ++ tailWord_8086870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086870).length < 2 ^ (prefixWord ++ tailWord_8086870).sum := by decide
  have hdescent : baseEnd_8086870 < baseStart_8086870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086892 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_8086892 : Nat := 118140960795 + 8086892 * 2 ^ 59
def prefixEnd_8086892 : Nat := 4983230072969 + 3 ^ 40 * 8086892 * 2
def baseEnd_8086892 : Nat := 4152462596999279231559067

theorem tailTrace_8086892 : CollatzResearch.WordTrace tailWord_8086892 prefixEnd_8086892 4152462596999279231559067 := by
  unfold tailWord_8086892
  simp only [CollatzResearch.WordTrace]
  refine ⟨147476591309289445020619465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196635455079052593360825953 147476591309289445020619465)
  ·
    refine ⟨110607443481967083765464599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147476591309289445020619465 110607443481967083765464599)
    ·
      refine ⟨165911165222950625648196899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110607443481967083765464599 165911165222950625648196899)
      ·
        refine ⟨248866747834425938472295349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165911165222950625648196899 248866747834425938472295349)
        ·
          refine ⟨23331257609477431731777689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248866747834425938472295349 23331257609477431731777689)
          ·
            refine ⟨17498443207108073798833267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23331257609477431731777689 17498443207108073798833267)
            ·
              refine ⟨26247664810662110698249901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498443207108073798833267 26247664810662110698249901)
              ·
                refine ⟨9842874303998291511843713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26247664810662110698249901 9842874303998291511843713)
                ·
                  refine ⟨7382155727998718633882785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9842874303998291511843713 7382155727998718633882785)
                  ·
                    refine ⟨5536616795999038975412089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382155727998718633882785 5536616795999038975412089)
                    ·
                      refine ⟨4152462596999279231559067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536616795999038975412089 4152462596999279231559067)
                      ·
                        rfl

theorem cell23_8086892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_8086892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086892 prefixEnd_8086892 := by exact prefixLift 8086892
  have htrace : WordTrace (prefixWord ++ tailWord_8086892) baseStart_8086892 baseEnd_8086892 := by
    simpa [prefixWord, tailWord_8086892, baseEnd_8086892] using wordTrace_append hprefix tailTrace_8086892
  have hstable : (prefixWord ++ tailWord_8086892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086892).length < 2 ^ (prefixWord ++ tailWord_8086892).sum := by decide
  have hdescent : baseEnd_8086892 < baseStart_8086892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086932 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 5]
def baseStart_8086932 : Nat := 118140960795 + 8086932 * 2 ^ 59
def prefixEnd_8086932 : Nat := 4983230072969 + 3 ^ 40 * 8086932 * 2
def baseEnd_8086932 : Nat := 461387015136162119450987

theorem tailTrace_8086932 : CollatzResearch.WordTrace tailWord_8086932 prefixEnd_8086932 461387015136162119450987 := by
  unfold tailWord_8086932
  simp only [CollatzResearch.WordTrace]
  refine ⟨147477320769216988436347525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196636427692289317915130033 147477320769216988436347525)
  ·
    refine ⟨27651997644228185331815161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147477320769216988436347525 27651997644228185331815161)
    ·
      refine ⟨20738998233171138998861371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27651997644228185331815161 20738998233171138998861371)
      ·
        refine ⟨31108497349756708498292057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20738998233171138998861371 31108497349756708498292057)
        ·
          refine ⟨23331373012317531373719043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31108497349756708498292057 23331373012317531373719043)
          ·
            refine ⟨34997059518476297060578565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23331373012317531373719043 34997059518476297060578565)
            ·
              refine ⟨6561948659714305698858481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34997059518476297060578565 6561948659714305698858481)
              ·
                refine ⟨4921461494785729274143861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561948659714305698858481 4921461494785729274143861)
                ·
                  refine ⟨461387015136162119450987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4921461494785729274143861 461387015136162119450987)
                  ·
                    rfl

theorem cell23_8086932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_8086932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086932 prefixEnd_8086932 := by exact prefixLift 8086932
  have htrace : WordTrace (prefixWord ++ tailWord_8086932) baseStart_8086932 baseEnd_8086932 := by
    simpa [prefixWord, tailWord_8086932, baseEnd_8086932] using wordTrace_append hprefix tailTrace_8086932
  have hstable : (prefixWord ++ tailWord_8086932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086932).length < 2 ^ (prefixWord ++ tailWord_8086932).sum := by decide
  have hdescent : baseEnd_8086932 < baseStart_8086932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086942 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_8086942 : Nat := 118140960795 + 8086942 * 2 ^ 59
def prefixEnd_8086942 : Nat := 4983230072969 + 3 ^ 40 * 8086942 * 2
def baseEnd_8086942 : Nat := 4152488271032004035933837

theorem tailTrace_8086942 : CollatzResearch.WordTrace tailWord_8086942 prefixEnd_8086942 4152488271032004035933837 := by
  unfold tailWord_8086942
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869375783549718572569885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196636670845598499053706053 36869375783549718572569885)
  ·
    refine ⟨13826015918831144464713707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36869375783549718572569885 13826015918831144464713707)
    ·
      refine ⟨20739023878246716697070561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13826015918831144464713707 20739023878246716697070561)
      ·
        refine ⟨15554267908685037522802921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20739023878246716697070561 15554267908685037522802921)
        ·
          refine ⟨11665700931513778142102191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15554267908685037522802921 11665700931513778142102191)
          ·
            refine ⟨17498551397270667213153287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11665700931513778142102191 17498551397270667213153287)
            ·
              refine ⟨26247827095906000819729931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498551397270667213153287 26247827095906000819729931)
              ·
                refine ⟨39371740643859001229594897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26247827095906000819729931 39371740643859001229594897)
                ·
                  refine ⟨29528805482894250922196173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39371740643859001229594897 29528805482894250922196173)
                  ·
                    refine ⟨11073302056085344095823565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29528805482894250922196173 11073302056085344095823565)
                    ·
                      refine ⟨4152488271032004035933837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073302056085344095823565 4152488271032004035933837)
                      ·
                        rfl

theorem cell23_8086942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_8086942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086942 prefixEnd_8086942 := by exact prefixLift 8086942
  have htrace : WordTrace (prefixWord ++ tailWord_8086942) baseStart_8086942 baseEnd_8086942 := by
    simpa [prefixWord, tailWord_8086942, baseEnd_8086942] using wordTrace_append hprefix tailTrace_8086942
  have hstable : (prefixWord ++ tailWord_8086942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086942).length < 2 ^ (prefixWord ++ tailWord_8086942).sum := by decide
  have hdescent : baseEnd_8086942 < baseStart_8086942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086965 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_8086965 : Nat := 118140960795 + 8086965 * 2 ^ 59
def prefixEnd_8086965 : Nat := 4983230072969 + 3 ^ 40 * 8086965 * 2
def baseEnd_8086965 : Nat := 4152500081087057445946231

theorem tailTrace_8086965 : CollatzResearch.WordTrace tailWord_8086965 prefixEnd_8086965 4152500081087057445946231 := by
  unfold tailWord_8086965
  simp only [CollatzResearch.WordTrace]
  refine ⟨294955845147314423508646349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196637230098209615672430899 294955845147314423508646349)
  ·
    refine ⟨110608441930242908815742381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294955845147314423508646349 110608441930242908815742381)
    ·
      refine ⟨41478165723841090805903393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110608441930242908815742381 41478165723841090805903393)
      ·
        refine ⟨31108624292880818104427545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41478165723841090805903393 31108624292880818104427545)
        ·
          refine ⟨23331468219660613578320659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31108624292880818104427545 23331468219660613578320659)
          ·
            refine ⟨34997202329490920367480989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23331468219660613578320659 34997202329490920367480989)
            ·
              refine ⟨13123950873559095137805371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34997202329490920367480989 13123950873559095137805371)
              ·
                refine ⟨19685926310338642706708057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13123950873559095137805371 19685926310338642706708057)
                ·
                  refine ⟨14764444732753982030031043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19685926310338642706708057 14764444732753982030031043)
                  ·
                    refine ⟨22146667099130973045046565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14764444732753982030031043 22146667099130973045046565)
                    ·
                      refine ⟨4152500081087057445946231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22146667099130973045046565 4152500081087057445946231)
                      ·
                        rfl

theorem cell23_8086965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_8086965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086965 prefixEnd_8086965 := by exact prefixLift 8086965
  have htrace : WordTrace (prefixWord ++ tailWord_8086965) baseStart_8086965 baseEnd_8086965 := by
    simpa [prefixWord, tailWord_8086965, baseEnd_8086965] using wordTrace_append hprefix tailTrace_8086965
  have hstable : (prefixWord ++ tailWord_8086965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086965).length < 2 ^ (prefixWord ++ tailWord_8086965).sum := by decide
  have hdescent : baseEnd_8086965 < baseStart_8086965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086988 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 8]
def baseStart_8086988 : Nat := 118140960795 + 8086988 * 2 ^ 59
def prefixEnd_8086988 : Nat := 4983230072969 + 3 ^ 40 * 8086988 * 2
def baseEnd_8086988 : Nat := 461390210126901206217625

theorem tailTrace_8086988 : CollatzResearch.WordTrace tailWord_8086988 prefixEnd_8086988 461390210126901206217625 := by
  unfold tailWord_8086988
  simp only [CollatzResearch.WordTrace]
  refine ⟨147478342013115549218366809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196637789350820732291155745 147478342013115549218366809)
  ·
    refine ⟨110608756509836661913775107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147478342013115549218366809 110608756509836661913775107)
    ·
      refine ⟨165913134764754992870662661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110608756509836661913775107 165913134764754992870662661)
      ·
        refine ⟨31108712768391561163249249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165913134764754992870662661 31108712768391561163249249)
        ·
          refine ⟨23331534576293670872436937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31108712768391561163249249 23331534576293670872436937)
          ·
            refine ⟨17498650932220253154327703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23331534576293670872436937 17498650932220253154327703)
            ·
              refine ⟨26247976398330379731491555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498650932220253154327703 26247976398330379731491555)
              ·
                refine ⟨39371964597495569597237333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26247976398330379731491555 39371964597495569597237333)
                ·
                  refine ⟨461390210126901206217625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39371964597495569597237333 461390210126901206217625)
                  ·
                    rfl

theorem cell23_8086988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_8086988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086988 prefixEnd_8086988 := by exact prefixLift 8086988
  have htrace : WordTrace (prefixWord ++ tailWord_8086988) baseStart_8086988 baseEnd_8086988 := by
    simpa [prefixWord, tailWord_8086988, baseEnd_8086988] using wordTrace_append hprefix tailTrace_8086988
  have hstable : (prefixWord ++ tailWord_8086988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086988).length < 2 ^ (prefixWord ++ tailWord_8086988).sum := by decide
  have hdescent : baseEnd_8086988 < baseStart_8086988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8086991 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_8086991 : Nat := 118140960795 + 8086991 * 2 ^ 59
def prefixEnd_8086991 : Nat := 4983230072969 + 3 ^ 40 * 8086991 * 2
def baseEnd_8086991 : Nat := 4152513431584074344221111

theorem tailTrace_8086991 : CollatzResearch.WordTrace tailWord_8086991 prefixEnd_8086991 4152513431584074344221111 := by
  unfold tailWord_8086991
  simp only [CollatzResearch.WordTrace]
  refine ⟨294956793445220229949092827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196637862296813486632728551 294956793445220229949092827)
  ·
    refine ⟨442435190167830344923639241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294956793445220229949092827 442435190167830344923639241)
    ·
      refine ⟨331826392625872758692729431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442435190167830344923639241 331826392625872758692729431)
      ·
        refine ⟨497739588938809138039094147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331826392625872758692729431 497739588938809138039094147)
        ·
          refine ⟨746609383408213707058641221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497739588938809138039094147 746609383408213707058641221)
          ·
            refine ⟨139989259389040070073495229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 746609383408213707058641221 139989259389040070073495229)
            ·
              refine ⟨52495972270890026277560711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139989259389040070073495229 52495972270890026277560711)
              ·
                refine ⟨78743958406335039416341067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52495972270890026277560711 78743958406335039416341067)
                ·
                  refine ⟨118115937609502559124511601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78743958406335039416341067 118115937609502559124511601)
                  ·
                    refine ⟨88586953207126919343383701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118115937609502559124511601 88586953207126919343383701)
                    ·
                      refine ⟨4152513431584074344221111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88586953207126919343383701 4152513431584074344221111)
                      ·
                        rfl

theorem cell23_8086991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_8086991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8086991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8086991 prefixEnd_8086991 := by exact prefixLift 8086991
  have htrace : WordTrace (prefixWord ++ tailWord_8086991) baseStart_8086991 baseEnd_8086991 := by
    simpa [prefixWord, tailWord_8086991, baseEnd_8086991] using wordTrace_append hprefix tailTrace_8086991
  have hstable : (prefixWord ++ tailWord_8086991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8086991).length < 2 ^ (prefixWord ++ tailWord_8086991).sum := by decide
  have hdescent : baseEnd_8086991 < baseStart_8086991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8086991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087025 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_8087025 : Nat := 118140960795 + 8087025 * 2 ^ 59
def prefixEnd_8087025 : Nat := 4983230072969 + 3 ^ 40 * 8087025 * 2
def baseEnd_8087025 : Nat := 4152530889926327211195955

theorem tailTrace_8087025 : CollatzResearch.WordTrace tailWord_8087025 prefixEnd_8087025 4152530889926327211195955 := by
  unfold tailWord_8087025
  simp only [CollatzResearch.WordTrace]
  refine ⟨294958033527097053755830529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196638689018064702503887019 294958033527097053755830529)
  ·
    refine ⟨221218525145322790316872897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294958033527097053755830529 221218525145322790316872897)
    ·
      refine ⟨165913893858992092737654673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221218525145322790316872897 165913893858992092737654673)
      ·
        refine ⟨124435420394244069553241005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165913893858992092737654673 124435420394244069553241005)
        ·
          refine ⟨46663282647841526082465377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124435420394244069553241005 46663282647841526082465377)
          ·
            refine ⟨34997461985881144561849033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46663282647841526082465377 34997461985881144561849033)
            ·
              refine ⟨26248096489410858421386775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34997461985881144561849033 26248096489410858421386775)
              ·
                refine ⟨39372144734116287632080163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26248096489410858421386775 39372144734116287632080163)
                ·
                  refine ⟨59058217101174431448120245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39372144734116287632080163 59058217101174431448120245)
                  ·
                    refine ⟨5536707853235102948261273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59058217101174431448120245 5536707853235102948261273)
                    ·
                      refine ⟨4152530889926327211195955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536707853235102948261273 4152530889926327211195955)
                      ·
                        rfl

theorem cell23_8087025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_8087025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087025 prefixEnd_8087025 := by exact prefixLift 8087025
  have htrace : WordTrace (prefixWord ++ tailWord_8087025) baseStart_8087025 baseEnd_8087025 := by
    simpa [prefixWord, tailWord_8087025, baseEnd_8087025] using wordTrace_append hprefix tailTrace_8087025
  have hstable : (prefixWord ++ tailWord_8087025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087025).length < 2 ^ (prefixWord ++ tailWord_8087025).sum := by decide
  have hdescent : baseEnd_8087025 < baseStart_8087025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087049 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 1, 1, 3]
def baseStart_8087049 : Nat := 118140960795 + 8087049 * 2 ^ 59
def prefixEnd_8087049 : Nat := 4983230072969 + 3 ^ 40 * 8087049 * 2
def baseEnd_8087049 : Nat := 4152543213462035117295845

theorem tailTrace_8087049 : CollatzResearch.WordTrace tailWord_8087049 prefixEnd_8087049 4152543213462035117295845 := by
  unfold tailWord_8087049
  simp only [CollatzResearch.WordTrace]
  refine ⟨294958908879010105854704201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196639272586006737236469467 294958908879010105854704201)
  ·
    refine ⟨221219181659257579391028151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294958908879010105854704201 221219181659257579391028151)
    ·
      refine ⟨331828772488886369086542227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221219181659257579391028151 331828772488886369086542227)
      ·
        refine ⟨497743158733329553629813341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331828772488886369086542227 497743158733329553629813341)
        ·
          refine ⟨186653684524998582611180003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497743158733329553629813341 186653684524998582611180003)
          ·
            refine ⟨279980526787497873916770005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186653684524998582611180003 279980526787497873916770005)
            ·
              refine ⟨6562043596581981419924297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 279980526787497873916770005 6562043596581981419924297)
              ·
                refine ⟨4921532697436486064943223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562043596581981419924297 4921532697436486064943223)
                ·
                  refine ⟨7382299046154729097414835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921532697436486064943223 7382299046154729097414835)
                  ·
                    refine ⟨11073448569232093646122253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382299046154729097414835 11073448569232093646122253)
                    ·
                      refine ⟨4152543213462035117295845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073448569232093646122253 4152543213462035117295845)
                      ·
                        rfl

theorem cell23_8087049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 1, 3].length) (baseStart_8087049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087049 prefixEnd_8087049 := by exact prefixLift 8087049
  have htrace : WordTrace (prefixWord ++ tailWord_8087049) baseStart_8087049 baseEnd_8087049 := by
    simpa [prefixWord, tailWord_8087049, baseEnd_8087049] using wordTrace_append hprefix tailTrace_8087049
  have hstable : (prefixWord ++ tailWord_8087049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087049).length < 2 ^ (prefixWord ++ tailWord_8087049).sum := by decide
  have hdescent : baseEnd_8087049 < baseStart_8087049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087068 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_8087068 : Nat := 118140960795 + 8087068 * 2 ^ 59
def prefixEnd_8087068 : Nat := 4983230072969 + 3 ^ 40 * 8087068 * 2
def baseEnd_8087068 : Nat := 4152552969594470542958257

theorem tailTrace_8087068 : CollatzResearch.WordTrace tailWord_8087068 prefixEnd_8087068 4152552969594470542958257 := by
  unfold tailWord_8087068
  simp only [CollatzResearch.WordTrace]
  refine ⟨147479800932970636049822929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196639734577294181399763905 147479800932970636049822929)
  ·
    refine ⟨110609850699727977037367197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147479800932970636049822929 110609850699727977037367197)
    ·
      refine ⟨41478694012397991389012699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110609850699727977037367197 41478694012397991389012699)
      ·
        refine ⟨62218041018596987083519049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41478694012397991389012699 62218041018596987083519049)
        ·
          refine ⟨46663530763947740312639287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62218041018596987083519049 46663530763947740312639287)
          ·
            refine ⟨69995296145921610468958931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46663530763947740312639287 69995296145921610468958931)
            ·
              refine ⟨104992944218882415703438397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69995296145921610468958931 104992944218882415703438397)
              ·
                refine ⟨39372354082080905888789399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104992944218882415703438397 39372354082080905888789399)
                ·
                  refine ⟨59058531123121358833184099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39372354082080905888789399 59058531123121358833184099)
                  ·
                    refine ⟨88587796684682038249776149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59058531123121358833184099 88587796684682038249776149)
                    ·
                      refine ⟨4152552969594470542958257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88587796684682038249776149 4152552969594470542958257)
                      ·
                        rfl

theorem cell23_8087068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_8087068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087068 prefixEnd_8087068 := by exact prefixLift 8087068
  have htrace : WordTrace (prefixWord ++ tailWord_8087068) baseStart_8087068 baseEnd_8087068 := by
    simpa [prefixWord, tailWord_8087068, baseEnd_8087068] using wordTrace_append hprefix tailTrace_8087068
  have hstable : (prefixWord ++ tailWord_8087068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087068).length < 2 ^ (prefixWord ++ tailWord_8087068).sum := by decide
  have hdescent : baseEnd_8087068 < baseStart_8087068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087072 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8087072 : Nat := 118140960795 + 8087072 * 2 ^ 59
def prefixEnd_8087072 : Nat := 4983230072969 + 3 ^ 40 * 8087072 * 2
def baseEnd_8087072 : Nat := 4152555023517088527308239

theorem tailTrace_8087072 : CollatzResearch.WordTrace tailWord_8087072 prefixEnd_8087072 4152555023517088527308239 := by
  unfold tailWord_8087072
  simp only [CollatzResearch.WordTrace]
  refine ⟨147479873878963390391395735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196639831838617853855194313 147479873878963390391395735)
  ·
    refine ⟨221219810818445085587093603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147479873878963390391395735 221219810818445085587093603)
    ·
      refine ⟨331829716227667628380640405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221219810818445085587093603 331829716227667628380640405)
      ·
        refine ⟨15554517948171920080342519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331829716227667628380640405 15554517948171920080342519)
        ·
          refine ⟨23331776922257880120513779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15554517948171920080342519 23331776922257880120513779)
          ·
            refine ⟨34997665383386820180770669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23331776922257880120513779 34997665383386820180770669)
            ·
              refine ⟨13124124518770057567789001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34997665383386820180770669 13124124518770057567789001)
              ·
                refine ⟨9843093389077543175841751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13124124518770057567789001 9843093389077543175841751)
                ·
                  refine ⟨14764640083616314763762627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9843093389077543175841751 14764640083616314763762627)
                  ·
                    refine ⟨22146960125424472145643941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14764640083616314763762627 22146960125424472145643941)
                    ·
                      refine ⟨4152555023517088527308239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22146960125424472145643941 4152555023517088527308239)
                      ·
                        rfl

theorem cell23_8087072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8087072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087072 prefixEnd_8087072 := by exact prefixLift 8087072
  have htrace : WordTrace (prefixWord ++ tailWord_8087072) baseStart_8087072 baseEnd_8087072 := by
    simpa [prefixWord, tailWord_8087072, baseEnd_8087072] using wordTrace_append hprefix tailTrace_8087072
  have hstable : (prefixWord ++ tailWord_8087072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087072).length < 2 ^ (prefixWord ++ tailWord_8087072).sum := by decide
  have hdescent : baseEnd_8087072 < baseStart_8087072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087089 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 1, 2, 2]
def baseStart_8087089 : Nat := 118140960795 + 8087089 * 2 ^ 59
def prefixEnd_8087089 : Nat := 4983230072969 + 3 ^ 40 * 8087089 * 2
def baseEnd_8087089 : Nat := 4152563752688214960795661

theorem tailTrace_8087089 : CollatzResearch.WordTrace tailWord_8087089 prefixEnd_8087089 4152563752688214960795661 := by
  unfold tailWord_8087089
  simp only [CollatzResearch.WordTrace]
  refine ⟨294960367798865192686160321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196640245199243461790773547 294960367798865192686160321)
  ·
    refine ⟨221220275849148894514620241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294960367798865192686160321 221220275849148894514620241)
    ·
      refine ⟨165915206886861670885965181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221220275849148894514620241 165915206886861670885965181)
      ·
        refine ⟨62218202582573126582236943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165915206886861670885965181 62218202582573126582236943)
        ·
          refine ⟨93327303873859689873355415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62218202582573126582236943 93327303873859689873355415)
          ·
            refine ⟨139990955810789534810033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93327303873859689873355415 139990955810789534810033123)
            ·
              refine ⟨209986433716184302215049685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139990955810789534810033123 209986433716184302215049685)
              ·
                refine ⟨4921557040223069583165227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209986433716184302215049685 4921557040223069583165227)
                ·
                  refine ⟨7382335560334604374747841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921557040223069583165227 7382335560334604374747841)
                  ·
                    refine ⟨5536751670250953281060881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382335560334604374747841 5536751670250953281060881)
                    ·
                      refine ⟨4152563752688214960795661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5536751670250953281060881 4152563752688214960795661)
                      ·
                        rfl

theorem cell23_8087089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_8087089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087089 prefixEnd_8087089 := by exact prefixLift 8087089
  have htrace : WordTrace (prefixWord ++ tailWord_8087089) baseStart_8087089 baseEnd_8087089 := by
    simpa [prefixWord, tailWord_8087089, baseEnd_8087089] using wordTrace_append hprefix tailTrace_8087089
  have hstable : (prefixWord ++ tailWord_8087089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087089).length < 2 ^ (prefixWord ++ tailWord_8087089).sum := by decide
  have hdescent : baseEnd_8087089 < baseStart_8087089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087105 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_8087105 : Nat := 118140960795 + 8087105 * 2 ^ 59
def prefixEnd_8087105 : Nat := 4983230072969 + 3 ^ 40 * 8087105 * 2
def baseEnd_8087105 : Nat := 4152571968378686898195587

theorem tailTrace_8087105 : CollatzResearch.WordTrace tailWord_8087105 prefixEnd_8087105 4152571968378686898195587 := by
  unfold tailWord_8087105
  simp only [CollatzResearch.WordTrace]
  refine ⟨294960951366807227418742769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196640634244538151612495179 294960951366807227418742769)
  ·
    refine ⟨221220713525105420564057077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294960951366807227418742769 221220713525105420564057077)
    ·
      refine ⟨20739441892978633177880351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221220713525105420564057077 20739441892978633177880351)
      ·
        refine ⟨31109162839467949766820527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20739441892978633177880351 31109162839467949766820527)
        ·
          refine ⟨46663744259201924650230791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31109162839467949766820527 46663744259201924650230791)
          ·
            refine ⟨69995616388802886975346187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46663744259201924650230791 69995616388802886975346187)
            ·
              refine ⟨104993424583204330463019281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69995616388802886975346187 104993424583204330463019281)
              ·
                refine ⟨78745068437403247847264461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104993424583204330463019281 78745068437403247847264461)
                ·
                  refine ⟨29529400664026217942724173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78745068437403247847264461 29529400664026217942724173)
                  ·
                    refine ⟨11073525249009831728521565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29529400664026217942724173 11073525249009831728521565)
                    ·
                      refine ⟨4152571968378686898195587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073525249009831728521565 4152571968378686898195587)
                      ·
                        rfl

theorem cell23_8087105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_8087105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087105 prefixEnd_8087105 := by exact prefixLift 8087105
  have htrace : WordTrace (prefixWord ++ tailWord_8087105) baseStart_8087105 baseEnd_8087105 := by
    simpa [prefixWord, tailWord_8087105, baseEnd_8087105] using wordTrace_append hprefix tailTrace_8087105
  have hstable : (prefixWord ++ tailWord_8087105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087105).length < 2 ^ (prefixWord ++ tailWord_8087105).sum := by decide
  have hdescent : baseEnd_8087105 < baseStart_8087105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087118 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_8087118 : Nat := 118140960795 + 8087118 * 2 ^ 59
def prefixEnd_8087118 : Nat := 4983230072969 + 3 ^ 40 * 8087118 * 2
def baseEnd_8087118 : Nat := 4152578643627195347333027

theorem tailTrace_8087118 : CollatzResearch.WordTrace tailWord_8087118 prefixEnd_8087118 4152578643627195347333027 := by
  unfold tailWord_8087118
  simp only [CollatzResearch.WordTrace]
  refine ⟨36870178189470016329870751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196640950343840087092644005 36870178189470016329870751)
  ·
    refine ⟨55305267284205024494806127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36870178189470016329870751 55305267284205024494806127)
    ·
      refine ⟨82957900926307536742209191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55305267284205024494806127 82957900926307536742209191)
      ·
        refine ⟨124436851389461305113313787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82957900926307536742209191 124436851389461305113313787)
        ·
          refine ⟨186655277084191957669970681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124436851389461305113313787 186655277084191957669970681)
          ·
            refine ⟨139991457813143968252478011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186655277084191957669970681 139991457813143968252478011)
            ·
              refine ⟨209987186719715952378717017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139991457813143968252478011 209987186719715952378717017)
              ·
                refine ⟨157490390039786964284037763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209987186719715952378717017 157490390039786964284037763)
                ·
                  refine ⟨236235585059680446426056645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157490390039786964284037763 236235585059680446426056645)
                  ·
                    refine ⟨44294172198690083704885621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236235585059680446426056645 44294172198690083704885621)
                    ·
                      refine ⟨4152578643627195347333027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44294172198690083704885621 4152578643627195347333027)
                      ·
                        rfl

theorem cell23_8087118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_8087118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087118 prefixEnd_8087118 := by exact prefixLift 8087118
  have htrace : WordTrace (prefixWord ++ tailWord_8087118) baseStart_8087118 baseEnd_8087118 := by
    simpa [prefixWord, tailWord_8087118, baseEnd_8087118] using wordTrace_append hprefix tailTrace_8087118
  have hstable : (prefixWord ++ tailWord_8087118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087118).length < 2 ^ (prefixWord ++ tailWord_8087118).sum := by decide
  have hdescent : baseEnd_8087118 < baseStart_8087118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087122 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_8087122 : Nat := 118140960795 + 8087122 * 2 ^ 59
def prefixEnd_8087122 : Nat := 4983230072969 + 3 ^ 40 * 8087122 * 2
def baseEnd_8087122 : Nat := 4152580697549813331683009

theorem tailTrace_8087122 : CollatzResearch.WordTrace tailWord_8087122 prefixEnd_8087122 4152580697549813331683009 := by
  unfold tailWord_8087122
  simp only [CollatzResearch.WordTrace]
  refine ⟨73740392851936409830527905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196641047605163759548074413 73740392851936409830527905)
  ·
    refine ⟨55305294638952307372895929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73740392851936409830527905 55305294638952307372895929)
    ·
      refine ⟨41478970979214230529671947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55305294638952307372895929 41478970979214230529671947)
      ·
        refine ⟨62218456468821345794507921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41478970979214230529671947 62218456468821345794507921)
        ·
          refine ⟨46663842351616009345880941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62218456468821345794507921 46663842351616009345880941)
          ·
            refine ⟨17498940881856003504705353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46663842351616009345880941 17498940881856003504705353)
            ·
              refine ⟨13124205661392002628529015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17498940881856003504705353 13124205661392002628529015)
              ·
                refine ⟨19686308492088003942793523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13124205661392002628529015 19686308492088003942793523)
                ·
                  refine ⟨29529462738132005914190285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19686308492088003942793523 29529462738132005914190285)
                  ·
                    refine ⟨11073548526799502217821357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29529462738132005914190285 11073548526799502217821357)
                    ·
                      refine ⟨4152580697549813331683009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073548526799502217821357 4152580697549813331683009)
                      ·
                        rfl

theorem cell23_8087122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_8087122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087122 prefixEnd_8087122 := by exact prefixLift 8087122
  have htrace : WordTrace (prefixWord ++ tailWord_8087122) baseStart_8087122 baseEnd_8087122 := by
    simpa [prefixWord, tailWord_8087122, baseEnd_8087122] using wordTrace_append hprefix tailTrace_8087122
  have hstable : (prefixWord ++ tailWord_8087122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087122).length < 2 ^ (prefixWord ++ tailWord_8087122).sum := by decide
  have hdescent : baseEnd_8087122 < baseStart_8087122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087128 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_8087128 : Nat := 118140960795 + 8087128 * 2 ^ 59
def prefixEnd_8087128 : Nat := 4983230072969 + 3 ^ 40 * 8087128 * 2
def baseEnd_8087128 : Nat := 4152583778433740308207981

theorem tailTrace_8087128 : CollatzResearch.WordTrace tailWord_8087128 prefixEnd_8087128 4152583778433740308207981 := by
  unfold tailWord_8087128
  simp only [CollatzResearch.WordTrace]
  refine ⟨147480895122861951173415019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196641193497149268231220025 147480895122861951173415019)
  ·
    refine ⟨221221342684292926760122529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147480895122861951173415019 221221342684292926760122529)
    ·
      refine ⟨165916007013219695070091897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221221342684292926760122529 165916007013219695070091897)
      ·
        refine ⟨124437005259914771302568923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165916007013219695070091897 124437005259914771302568923)
        ·
          refine ⟨186655507889872156953853385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124437005259914771302568923 186655507889872156953853385)
          ·
            refine ⟨139991630917404117715390039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186655507889872156953853385 139991630917404117715390039)
            ·
              refine ⟨209987446376106176573085059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139991630917404117715390039 209987446376106176573085059)
              ·
                refine ⟨314981169564159264859627589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209987446376106176573085059 314981169564159264859627589)
                ·
                  refine ⟨59058969293279862161180173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314981169564159264859627589 59058969293279862161180173)
                  ·
                    refine ⟨22147113484979948310442565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59058969293279862161180173 22147113484979948310442565)
                    ·
                      refine ⟨4152583778433740308207981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22147113484979948310442565 4152583778433740308207981)
                      ·
                        rfl

theorem cell23_8087128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_8087128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087128 prefixEnd_8087128 := by exact prefixLift 8087128
  have htrace : WordTrace (prefixWord ++ tailWord_8087128) baseStart_8087128 baseEnd_8087128 := by
    simpa [prefixWord, tailWord_8087128, baseEnd_8087128] using wordTrace_append hprefix tailTrace_8087128
  have hstable : (prefixWord ++ tailWord_8087128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087128).length < 2 ^ (prefixWord ++ tailWord_8087128).sum := by decide
  have hdescent : baseEnd_8087128 < baseStart_8087128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087148 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_8087148 : Nat := 118140960795 + 8087148 * 2 ^ 59
def prefixEnd_8087148 : Nat := 4983230072969 + 3 ^ 40 * 8087148 * 2
def baseEnd_8087148 : Nat := 4152594048046830229957889

theorem tailTrace_8087148 : CollatzResearch.WordTrace tailWord_8087148 prefixEnd_8087148 4152594048046830229957889 := by
  unfold tailWord_8087148
  simp only [CollatzResearch.WordTrace]
  refine ⟨147481259852825722881279049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196641679803767630508372065 147481259852825722881279049)
  ·
    refine ⟨110610944889619292160959287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147481259852825722881279049 110610944889619292160959287)
    ·
      refine ⟨165916417334428938241438931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110610944889619292160959287 165916417334428938241438931)
      ·
        refine ⟨248874626001643407362158397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165916417334428938241438931 248874626001643407362158397)
        ·
          refine ⟨93327984750616277760809399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248874626001643407362158397 93327984750616277760809399)
          ·
            refine ⟨139991977125924416641214099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93327984750616277760809399 139991977125924416641214099)
            ·
              refine ⟨209987965688886624961821149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139991977125924416641214099 209987965688886624961821149)
              ·
                refine ⟨78745487133332484360682931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209987965688886624961821149 78745487133332484360682931)
                ·
                  refine ⟨118118230699998726541024397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78745487133332484360682931 118118230699998726541024397)
                  ·
                    refine ⟨44294336512499522452884149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118118230699998726541024397 44294336512499522452884149)
                    ·
                      refine ⟨4152594048046830229957889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44294336512499522452884149 4152594048046830229957889)
                      ·
                        rfl

theorem cell23_8087148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_8087148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087148 prefixEnd_8087148 := by exact prefixLift 8087148
  have htrace : WordTrace (prefixWord ++ tailWord_8087148) baseStart_8087148 baseEnd_8087148 := by
    simpa [prefixWord, tailWord_8087148, baseEnd_8087148] using wordTrace_append hprefix tailTrace_8087148
  have hstable : (prefixWord ++ tailWord_8087148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087148).length < 2 ^ (prefixWord ++ tailWord_8087148).sum := by decide
  have hdescent : baseEnd_8087148 < baseStart_8087148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087175 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_8087175 : Nat := 118140960795 + 8087175 * 2 ^ 59
def prefixEnd_8087175 : Nat := 4983230072969 + 3 ^ 40 * 8087175 * 2
def baseEnd_8087175 : Nat := 4152607912024501624320265

theorem tailTrace_8087175 : CollatzResearch.WordTrace tailWord_8087175 prefixEnd_8087175 4152607912024501624320265 := by
  unfold tailWord_8087175
  simp only [CollatzResearch.WordTrace]
  refine ⟨294963504476553629373790979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196642336317702419582527319 294963504476553629373790979)
  ·
    refine ⟨442445256714830444060686469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294963504476553629373790979 442445256714830444060686469)
    ·
      refine ⟨82958485634030708261378713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442445256714830444060686469 82958485634030708261378713)
      ·
        refine ⟨62218864225523031196034035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82958485634030708261378713 62218864225523031196034035)
        ·
          refine ⟨93328296338284546794051053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62218864225523031196034035 93328296338284546794051053)
          ·
            refine ⟨34998111126856705047769145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93328296338284546794051053 34998111126856705047769145)
            ·
              refine ⟨26248583345142528785826859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34998111126856705047769145 26248583345142528785826859)
              ·
                refine ⟨39372875017713793178740289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26248583345142528785826859 39372875017713793178740289)
                ·
                  refine ⟨29529656263285344884055217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39372875017713793178740289 29529656263285344884055217)
                  ·
                    refine ⟨22147242197464008663041413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29529656263285344884055217 22147242197464008663041413)
                    ·
                      refine ⟨4152607912024501624320265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22147242197464008663041413 4152607912024501624320265)
                      ·
                        rfl

theorem cell23_8087175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_8087175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087175 prefixEnd_8087175 := by exact prefixLift 8087175
  have htrace : WordTrace (prefixWord ++ tailWord_8087175) baseStart_8087175 baseEnd_8087175 := by
    simpa [prefixWord, tailWord_8087175, baseEnd_8087175] using wordTrace_append hprefix tailTrace_8087175
  have hstable : (prefixWord ++ tailWord_8087175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087175).length < 2 ^ (prefixWord ++ tailWord_8087175).sum := by decide
  have hdescent : baseEnd_8087175 < baseStart_8087175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087215 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 2, 5]
def baseStart_8087215 : Nat := 118140960795 + 8087215 * 2 ^ 59
def prefixEnd_8087215 : Nat := 4983230072969 + 3 ^ 40 * 8087215 * 2
def baseEnd_8087215 : Nat := 1384209483750227155940027

theorem tailTrace_8087215 : CollatzResearch.WordTrace tailWord_8087215 prefixEnd_8087215 1384209483750227155940027 := by
  unfold tailWord_8087215
  simp only [CollatzResearch.WordTrace]
  refine ⟨294964963396408716205247099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196643308930939144136831399 294964963396408716205247099)
  ·
    refine ⟨442447445094613074307870649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294964963396408716205247099 442447445094613074307870649)
    ·
      refine ⟨331835583820959805730902987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442447445094613074307870649 331835583820959805730902987)
      ·
        refine ⟨497753375731439708596354481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331835583820959805730902987 497753375731439708596354481)
        ·
          refine ⟨373315031798579781447265861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497753375731439708596354481 373315031798579781447265861)
          ·
            refine ⟨69996568462233709021362349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373315031798579781447265861 69996568462233709021362349)
            ·
              refine ⟨26248713173337640883010881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69996568462233709021362349 26248713173337640883010881)
              ·
                refine ⟨19686534880003230662258161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26248713173337640883010881 19686534880003230662258161)
                ·
                  refine ⟨14764901160002422996693621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19686534880003230662258161 14764901160002422996693621)
                  ·
                    refine ⟨1384209483750227155940027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14764901160002422996693621 1384209483750227155940027)
                    ·
                      rfl

theorem cell23_8087215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_8087215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087215 prefixEnd_8087215 := by exact prefixLift 8087215
  have htrace : WordTrace (prefixWord ++ tailWord_8087215) baseStart_8087215 baseEnd_8087215 := by
    simpa [prefixWord, tailWord_8087215, baseEnd_8087215] using wordTrace_append hprefix tailTrace_8087215
  have hstable : (prefixWord ++ tailWord_8087215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087215).length < 2 ^ (prefixWord ++ tailWord_8087215).sum := by decide
  have hdescent : baseEnd_8087215 < baseStart_8087215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087275 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 6]
def baseStart_8087275 : Nat := 118140960795 + 8087275 * 2 ^ 59
def prefixEnd_8087275 : Nat := 4983230072969 + 3 ^ 40 * 8087275 * 2
def baseEnd_8087275 : Nat := 461406584454439025896645

theorem tailTrace_8087275 : CollatzResearch.WordTrace tailWord_8087275 prefixEnd_8087275 461406584454439025896645 := by
  unfold tailWord_8087275
  simp only [CollatzResearch.WordTrace]
  refine ⟨294967151776191346452431279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196644767850794230968287519 294967151776191346452431279)
  ·
    refine ⟨442450727664287019678646919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294967151776191346452431279 442450727664287019678646919)
    ·
      refine ⟨663676091496430529517970379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442450727664287019678646919 663676091496430529517970379)
      ·
        refine ⟨995514137244645794276955569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663676091496430529517970379 995514137244645794276955569)
        ·
          refine ⟨746635602933484345707716677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995514137244645794276955569 746635602933484345707716677)
          ·
            refine ⟨139994175550028314820196877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 746635602933484345707716677 139994175550028314820196877)
            ·
              refine ⟨52497815831260618057573829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139994175550028314820196877 52497815831260618057573829)
              ·
                refine ⟨9843340468361365885795093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52497815831260618057573829 9843340468361365885795093)
                ·
                  refine ⟨461406584454439025896645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9843340468361365885795093 461406584454439025896645)
                  ·
                    rfl

theorem cell23_8087275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 6].length) (baseStart_8087275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087275 prefixEnd_8087275 := by exact prefixLift 8087275
  have htrace : WordTrace (prefixWord ++ tailWord_8087275) baseStart_8087275 baseEnd_8087275 := by
    simpa [prefixWord, tailWord_8087275, baseEnd_8087275] using wordTrace_append hprefix tailTrace_8087275
  have hstable : (prefixWord ++ tailWord_8087275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087275).length < 2 ^ (prefixWord ++ tailWord_8087275).sum := by decide
  have hdescent : baseEnd_8087275 < baseStart_8087275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087279 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 1, 4]
def baseStart_8087279 : Nat := 118140960795 + 8087279 * 2 ^ 59
def prefixEnd_8087279 : Nat := 4983230072969 + 3 ^ 40 * 8087279 * 2
def baseEnd_8087279 : Nat := 1384220438004189739139929

theorem tailTrace_8087279 : CollatzResearch.WordTrace tailWord_8087279 prefixEnd_8087279 1384220438004189739139929 := by
  unfold tailWord_8087279
  simp only [CollatzResearch.WordTrace]
  refine ⟨294967297668176855135576891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196644865112117903423717927 294967297668176855135576891)
  ·
    refine ⟨442450946502265282703365337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294967297668176855135576891 442450946502265282703365337)
    ·
      refine ⟨331838209876698962027524003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442450946502265282703365337 331838209876698962027524003)
      ·
        refine ⟨497757314815048443041286005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331838209876698962027524003 497757314815048443041286005)
        ·
          refine ⟨46664748263910791535120563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497757314815048443041286005 46664748263910791535120563)
          ·
            refine ⟨69997122395866187302680845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46664748263910791535120563 69997122395866187302680845)
            ·
              refine ⟨26248920898449820238505317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69997122395866187302680845 26248920898449820238505317)
              ·
                refine ⟨4921672668459341294719747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26248920898449820238505317 4921672668459341294719747)
                ·
                  refine ⟨7382509002689011942079621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921672668459341294719747 7382509002689011942079621)
                  ·
                    refine ⟨1384220438004189739139929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382509002689011942079621 1384220438004189739139929)
                    ·
                      rfl

theorem cell23_8087279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 4].length) (baseStart_8087279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087279 prefixEnd_8087279 := by exact prefixLift 8087279
  have htrace : WordTrace (prefixWord ++ tailWord_8087279) baseStart_8087279 baseEnd_8087279 := by
    simpa [prefixWord, tailWord_8087279, baseEnd_8087279] using wordTrace_append hprefix tailTrace_8087279
  have hstable : (prefixWord ++ tailWord_8087279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087279).length < 2 ^ (prefixWord ++ tailWord_8087279).sum := by decide
  have hdescent : baseEnd_8087279 < baseStart_8087279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087326 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_8087326 : Nat := 118140960795 + 8087326 * 2 ^ 59
def prefixEnd_8087326 : Nat := 4983230072969 + 3 ^ 40 * 8087326 * 2
def baseEnd_8087326 : Nat := 461409494178147837059119

theorem tailTrace_8087326 : CollatzResearch.WordTrace tailWord_8087326 prefixEnd_8087326 461409494178147837059119 := by
  unfold tailWord_8087326
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871126487375822770317229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196646007932671054775025221 36871126487375822770317229)
  ·
    refine ⟨13826672432765933538868961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36871126487375822770317229 13826672432765933538868961)
    ·
      refine ⟨10370004324574450154151721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13826672432765933538868961 10370004324574450154151721)
      ·
        refine ⟨7777503243430837615613791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10370004324574450154151721 7777503243430837615613791)
        ·
          refine ⟨11666254865146256423420687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777503243430837615613791 11666254865146256423420687)
          ·
            refine ⟨17499382297719384635131031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666254865146256423420687 17499382297719384635131031)
            ·
              refine ⟨26249073446579076952696547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17499382297719384635131031 26249073446579076952696547)
              ·
                refine ⟨39373610169868615429044821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26249073446579076952696547 39373610169868615429044821)
                ·
                  refine ⟨461409494178147837059119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39373610169868615429044821 461409494178147837059119)
                  ·
                    rfl

theorem cell23_8087326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_8087326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087326 prefixEnd_8087326 := by exact prefixLift 8087326
  have htrace : WordTrace (prefixWord ++ tailWord_8087326) baseStart_8087326 baseEnd_8087326 := by
    simpa [prefixWord, tailWord_8087326, baseEnd_8087326] using wordTrace_append hprefix tailTrace_8087326
  have hstable : (prefixWord ++ tailWord_8087326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087326).length < 2 ^ (prefixWord ++ tailWord_8087326).sum := by decide
  have hdescent : baseEnd_8087326 < baseStart_8087326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087336 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_8087336 : Nat := 118140960795 + 8087336 * 2 ^ 59
def prefixEnd_8087336 : Nat := 4983230072969 + 3 ^ 40 * 8087336 * 2
def baseEnd_8087336 : Nat := 4152690582409875494407025

theorem tailTrace_8087336 : CollatzResearch.WordTrace tailWord_8087336 prefixEnd_8087336 4152690582409875494407025 := by
  unfold tailWord_8087336
  simp only [CollatzResearch.WordTrace]
  refine ⟨147484688314485176935200931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196646251085980235913601241 147484688314485176935200931)
  ·
    refine ⟨221227032471727765402801397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147484688314485176935200931 221227032471727765402801397)
    ·
      refine ⟨20740034294224478006512631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221227032471727765402801397 20740034294224478006512631)
      ·
        refine ⟨31110051441336717009768947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20740034294224478006512631 31110051441336717009768947)
        ·
          refine ⟨46665077162005075514653421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31110051441336717009768947 46665077162005075514653421)
          ·
            refine ⟨17499403935751903317995033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46665077162005075514653421 17499403935751903317995033)
            ·
              refine ⟨13124552951813927488496275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17499403935751903317995033 13124552951813927488496275)
              ·
                refine ⟨19686829427720891232744413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13124552951813927488496275 19686829427720891232744413)
                ·
                  refine ⟨7382561035395334212279155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19686829427720891232744413 7382561035395334212279155)
                  ·
                    refine ⟨11073841553093001318418733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382561035395334212279155 11073841553093001318418733)
                    ·
                      refine ⟨4152690582409875494407025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11073841553093001318418733 4152690582409875494407025)
                      ·
                        rfl

theorem cell23_8087336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_8087336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087336 prefixEnd_8087336 := by exact prefixLift 8087336
  have htrace : WordTrace (prefixWord ++ tailWord_8087336) baseStart_8087336 baseEnd_8087336 := by
    simpa [prefixWord, tailWord_8087336, baseEnd_8087336] using wordTrace_append hprefix tailTrace_8087336
  have hstable : (prefixWord ++ tailWord_8087336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087336).length < 2 ^ (prefixWord ++ tailWord_8087336).sum := by decide
  have hdescent : baseEnd_8087336 < baseStart_8087336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087352 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_8087352 : Nat := 118140960795 + 8087352 * 2 ^ 59
def prefixEnd_8087352 : Nat := 4983230072969 + 3 ^ 40 * 8087352 * 2
def baseEnd_8087352 : Nat := 1384232932700115810602317

theorem tailTrace_8087352 : CollatzResearch.WordTrace tailWord_8087352 prefixEnd_8087352 1384232932700115810602317 := by
  unfold tailWord_8087352
  simp only [CollatzResearch.WordTrace]
  refine ⟨147484980098456194301492155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196646640131274925735322873 147484980098456194301492155)
  ·
    refine ⟨221227470147684291452238233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147484980098456194301492155 221227470147684291452238233)
    ·
      refine ⟨165920602610763218589178675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221227470147684291452238233 165920602610763218589178675)
      ·
        refine ⟨248880903916144827883768013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165920602610763218589178675 248880903916144827883768013)
        ·
          refine ⟨93330338968554310456413005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248880903916144827883768013 93330338968554310456413005)
          ·
            refine ⟨34998877113207866421154877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93330338968554310456413005 34998877113207866421154877)
            ·
              refine ⟨13124578917452949907933079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34998877113207866421154877 13124578917452949907933079)
              ·
                refine ⟨19686868376179424861899619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13124578917452949907933079 19686868376179424861899619)
                ·
                  refine ⟨29530302564269137292849429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19686868376179424861899619 29530302564269137292849429)
                  ·
                    refine ⟨1384232932700115810602317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29530302564269137292849429 1384232932700115810602317)
                    ·
                      rfl

theorem cell23_8087352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_8087352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087352 prefixEnd_8087352 := by exact prefixLift 8087352
  have htrace : WordTrace (prefixWord ++ tailWord_8087352) baseStart_8087352 baseEnd_8087352 := by
    simpa [prefixWord, tailWord_8087352, baseEnd_8087352] using wordTrace_append hprefix tailTrace_8087352
  have hstable : (prefixWord ++ tailWord_8087352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087352).length < 2 ^ (prefixWord ++ tailWord_8087352).sum := by decide
  have hdescent : baseEnd_8087352 < baseStart_8087352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087365 : List Nat := [1, 3, 1, 1, 1, 2, 5, 9]
def baseStart_8087365 : Nat := 118140960795 + 8087365 * 2 ^ 59
def prefixEnd_8087365 : Nat := 4983230072969 + 3 ^ 40 * 8087365 * 2
def baseEnd_8087365 : Nat := 153803906420327995590533

theorem tailTrace_8087365 : CollatzResearch.WordTrace tailWord_8087365 prefixEnd_8087365 153803906420327995590533 := by
  unfold tailWord_8087365
  simp only [CollatzResearch.WordTrace]
  refine ⟨294970434345865291823207549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196646956230576861215471699 294970434345865291823207549)
  ·
    refine ⟨110613912879699484433702831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294970434345865291823207549 110613912879699484433702831)
    ·
      refine ⟨165920869319549226650554247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110613912879699484433702831 165920869319549226650554247)
      ·
        refine ⟨248881303979323839975831371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165920869319549226650554247 248881303979323839975831371)
        ·
          refine ⟨373321955968985759963747057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248881303979323839975831371 373321955968985759963747057)
          ·
            refine ⟨279991466976739319972810293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373321955968985759963747057 279991466976739319972810293)
            ·
              refine ⟨26249200029069311247450965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279991466976739319972810293 26249200029069311247450965)
              ·
                refine ⟨153803906420327995590533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26249200029069311247450965 153803906420327995590533)
                ·
                  rfl

theorem cell23_8087365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 9].length) (baseStart_8087365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087365 prefixEnd_8087365 := by exact prefixLift 8087365
  have htrace : WordTrace (prefixWord ++ tailWord_8087365) baseStart_8087365 baseEnd_8087365 := by
    simpa [prefixWord, tailWord_8087365, baseEnd_8087365] using wordTrace_append hprefix tailTrace_8087365
  have hstable : (prefixWord ++ tailWord_8087365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087365).length < 2 ^ (prefixWord ++ tailWord_8087365).sum := by decide
  have hdescent : baseEnd_8087365 < baseStart_8087365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087415 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_8087415 : Nat := 118140960795 + 8087415 * 2 ^ 59
def prefixEnd_8087415 : Nat := 4983230072969 + 3 ^ 40 * 8087415 * 2
def baseEnd_8087415 : Nat := 4152731147381580685319161

theorem tailTrace_8087415 : CollatzResearch.WordTrace tailWord_8087415 prefixEnd_8087415 4152731147381580685319161 := by
  unfold tailWord_8087415
  simp only [CollatzResearch.WordTrace]
  refine ⟨294972257995684150362527699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196648171997122766908351799 294972257995684150362527699)
  ·
    refine ⟨442458386993526225543791549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294972257995684150362527699 442458386993526225543791549)
    ·
      refine ⟨165921895122572334578921831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442458386993526225543791549 165921895122572334578921831)
      ·
        refine ⟨248882842683858501868382747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165921895122572334578921831 248882842683858501868382747)
        ·
          refine ⟨373324264025787752802574121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248882842683858501868382747 373324264025787752802574121)
          ·
            refine ⟨279993198019340814601930591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373324264025787752802574121 279993198019340814601930591)
            ·
              refine ⟨419989797029011221902895887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279993198019340814601930591 419989797029011221902895887)
              ·
                refine ⟨629984695543516832854343831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419989797029011221902895887 629984695543516832854343831)
                ·
                  refine ⟨944977043315275249281515747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629984695543516832854343831 944977043315275249281515747)
                  ·
                    refine ⟨1417465564972912873922273621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 944977043315275249281515747 1417465564972912873922273621)
                    ·
                      refine ⟨4152731147381580685319161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1417465564972912873922273621 4152731147381580685319161)
                      ·
                        rfl

theorem cell23_8087415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_8087415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087415 prefixEnd_8087415 := by exact prefixLift 8087415
  have htrace : WordTrace (prefixWord ++ tailWord_8087415) baseStart_8087415 baseEnd_8087415 := by
    simpa [prefixWord, tailWord_8087415, baseEnd_8087415] using wordTrace_append hprefix tailTrace_8087415
  have hstable : (prefixWord ++ tailWord_8087415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087415).length < 2 ^ (prefixWord ++ tailWord_8087415).sum := by decide
  have hdescent : baseEnd_8087415 < baseStart_8087415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087500 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_8087500 : Nat := 118140960795 + 8087500 * 2 ^ 59
def prefixEnd_8087500 : Nat := 4983230072969 + 3 ^ 40 * 8087500 * 2
def baseEnd_8087500 : Nat := 4152774793237212852756271

theorem tailTrace_8087500 : CollatzResearch.WordTrace tailWord_8087500 prefixEnd_8087500 4152774793237212852756271 := by
  unfold tailWord_8087500
  simp only [CollatzResearch.WordTrace]
  refine ⟨147487679100188104939685977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196650238800250806586247969 147487679100188104939685977)
  ·
    refine ⟨110615759325141078704764483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147487679100188104939685977 110615759325141078704764483)
    ·
      refine ⟨165923638987711618057146725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110615759325141078704764483 165923638987711618057146725)
      ·
        refine ⟨31110682310195928385715011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165923638987711618057146725 31110682310195928385715011)
        ·
          refine ⟨46666023465293892578572517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31110682310195928385715011 46666023465293892578572517)
          ·
            refine ⟨8749879399742604858482347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46666023465293892578572517 8749879399742604858482347)
            ·
              refine ⟨13124819099613907287723521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749879399742604858482347 13124819099613907287723521)
              ·
                refine ⟨9843614324710430465792641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13124819099613907287723521 9843614324710430465792641)
                ·
                  refine ⟨7382710743532822849344481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9843614324710430465792641 7382710743532822849344481)
                  ·
                    refine ⟨5537033057649617137008361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382710743532822849344481 5537033057649617137008361)
                    ·
                      refine ⟨4152774793237212852756271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537033057649617137008361 4152774793237212852756271)
                      ·
                        rfl

theorem cell23_8087500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_8087500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087500 prefixEnd_8087500 := by exact prefixLift 8087500
  have htrace : WordTrace (prefixWord ++ tailWord_8087500) baseStart_8087500 baseEnd_8087500 := by
    simpa [prefixWord, tailWord_8087500, baseEnd_8087500] using wordTrace_append hprefix tailTrace_8087500
  have hstable : (prefixWord ++ tailWord_8087500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087500).length < 2 ^ (prefixWord ++ tailWord_8087500).sum := by decide
  have hdescent : baseEnd_8087500 < baseStart_8087500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087506 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_8087506 : Nat := 118140960795 + 8087506 * 2 ^ 59
def prefixEnd_8087506 : Nat := 4983230072969 + 3 ^ 40 * 8087506 * 2
def baseEnd_8087506 : Nat := 461419763791237758809027

theorem tailTrace_8087506 : CollatzResearch.WordTrace tailWord_8087506 prefixEnd_8087506 461419763791237758809027 := by
  unfold tailWord_8087506
  simp only [CollatzResearch.WordTrace]
  refine ⟨73743894259588618226022593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196650384692236315269393581 73743894259588618226022593)
  ·
    refine ⟨55307920694691463669516945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73743894259588618226022593 55307920694691463669516945)
    ·
      refine ⟨41480940521018597752137709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55307920694691463669516945 41480940521018597752137709)
      ·
        refine ⟨15555352695381974157051641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41480940521018597752137709 15555352695381974157051641)
        ·
          refine ⟨11666514521536480617788731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555352695381974157051641 11666514521536480617788731)
          ·
            refine ⟨17499771782304720926683097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666514521536480617788731 17499771782304720926683097)
            ·
              refine ⟨13124828836728540695012323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17499771782304720926683097 13124828836728540695012323)
              ·
                refine ⟨19687243255092811042518485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13124828836728540695012323 19687243255092811042518485)
                ·
                  refine ⟨461419763791237758809027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19687243255092811042518485 461419763791237758809027)
                  ·
                    rfl

theorem cell23_8087506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_8087506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087506 prefixEnd_8087506 := by exact prefixLift 8087506
  have htrace : WordTrace (prefixWord ++ tailWord_8087506) baseStart_8087506 baseEnd_8087506 := by
    simpa [prefixWord, tailWord_8087506, baseEnd_8087506] using wordTrace_append hprefix tailTrace_8087506
  have hstable : (prefixWord ++ tailWord_8087506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087506).length < 2 ^ (prefixWord ++ tailWord_8087506).sum := by decide
  have hdescent : baseEnd_8087506 < baseStart_8087506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087512 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_8087512 : Nat := 118140960795 + 8087512 * 2 ^ 59
def prefixEnd_8087512 : Nat := 4983230072969 + 3 ^ 40 * 8087512 * 2
def baseEnd_8087512 : Nat := 4152780955005066805806215

theorem tailTrace_8087512 : CollatzResearch.WordTrace tailWord_8087512 prefixEnd_8087512 4152780955005066805806215 := by
  unfold tailWord_8087512
  simp only [CollatzResearch.WordTrace]
  refine ⟨147487897938166367964404395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196650530584221823952539193 147487897938166367964404395)
  ·
    refine ⟨221231846907249551946606593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147487897938166367964404395 221231846907249551946606593)
    ·
      refine ⟨165923885180437163959954945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221231846907249551946606593 165923885180437163959954945)
      ·
        refine ⟨124442913885327872969966209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165923885180437163959954945 124442913885327872969966209)
        ·
          refine ⟨93332185413995904727474657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124442913885327872969966209 93332185413995904727474657)
          ·
            refine ⟨69999139060496928545605993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93332185413995904727474657 69999139060496928545605993)
            ·
              refine ⟨52499354295372696409204495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69999139060496928545605993 52499354295372696409204495)
              ·
                refine ⟨78749031443059044613806743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52499354295372696409204495 78749031443059044613806743)
                ·
                  refine ⟨118123547164588566920710115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78749031443059044613806743 118123547164588566920710115)
                  ·
                    refine ⟨177185320746882850381065173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118123547164588566920710115 177185320746882850381065173)
                    ·
                      refine ⟨4152780955005066805806215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177185320746882850381065173 4152780955005066805806215)
                      ·
                        rfl

theorem cell23_8087512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_8087512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087512 prefixEnd_8087512 := by exact prefixLift 8087512
  have htrace : WordTrace (prefixWord ++ tailWord_8087512) baseStart_8087512 baseEnd_8087512 := by
    simpa [prefixWord, tailWord_8087512, baseEnd_8087512] using wordTrace_append hprefix tailTrace_8087512
  have hstable : (prefixWord ++ tailWord_8087512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087512).length < 2 ^ (prefixWord ++ tailWord_8087512).sum := by decide
  have hdescent : baseEnd_8087512 < baseStart_8087512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087517 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_8087517 : Nat := 118140960795 + 8087517 * 2 ^ 59
def prefixEnd_8087517 : Nat := 4983230072969 + 3 ^ 40 * 8087517 * 2
def baseEnd_8087517 : Nat := 4152783522408339286243693

theorem tailTrace_8087517 : CollatzResearch.WordTrace tailWord_8087517 prefixEnd_8087517 4152783522408339286243693 := by
  unfold tailWord_8087517
  simp only [CollatzResearch.WordTrace]
  refine ⟨294975978241314621782740805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196650652160876414521827203 294975978241314621782740805)
  ·
    refine ⟨55307995920246491584263901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294975978241314621782740805 55307995920246491584263901)
    ·
      refine ⟨20740498470092434344098963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55307995920246491584263901 20740498470092434344098963)
      ·
        refine ⟨31110747705138651516148445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20740498470092434344098963 31110747705138651516148445)
        ·
          refine ⟨11666530389426994318555667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31110747705138651516148445 11666530389426994318555667)
          ·
            refine ⟨17499795584140491477833501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666530389426994318555667 17499795584140491477833501)
            ·
              refine ⟨6562423344052684304187563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17499795584140491477833501 6562423344052684304187563)
              ·
                refine ⟨9843635016079026456281345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562423344052684304187563 9843635016079026456281345)
                ·
                  refine ⟨7382726262059269842211009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9843635016079026456281345 7382726262059269842211009)
                  ·
                    refine ⟨5537044696544452381658257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382726262059269842211009 5537044696544452381658257)
                    ·
                      refine ⟨4152783522408339286243693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537044696544452381658257 4152783522408339286243693)
                      ·
                        rfl

theorem cell23_8087517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_8087517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087517 prefixEnd_8087517 := by exact prefixLift 8087517
  have htrace : WordTrace (prefixWord ++ tailWord_8087517) baseStart_8087517 baseEnd_8087517 := by
    simpa [prefixWord, tailWord_8087517, baseEnd_8087517] using wordTrace_append hprefix tailTrace_8087517
  have hstable : (prefixWord ++ tailWord_8087517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087517).length < 2 ^ (prefixWord ++ tailWord_8087517).sum := by decide
  have hdescent : baseEnd_8087517 < baseStart_8087517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087539 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 6, 2]
def baseStart_8087539 : Nat := 118140960795 + 8087539 * 2 ^ 59
def prefixEnd_8087539 : Nat := 4983230072969 + 3 ^ 40 * 8087539 * 2
def baseEnd_8087539 : Nat := 4152794818982738200168591

theorem tailTrace_8087539 : CollatzResearch.WordTrace tailWord_8087539 prefixEnd_8087539 4152794818982738200168591 := by
  unfold tailWord_8087539
  simp only [CollatzResearch.WordTrace]
  refine ⟨294976780647234919540041671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196651187098156613026694447 294976780647234919540041671)
  ·
    refine ⟨442465170970852379310062507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294976780647234919540041671 442465170970852379310062507)
    ·
      refine ⟨663697756456278568965093761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442465170970852379310062507 663697756456278568965093761)
      ·
        refine ⟨497773317342208926723820321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663697756456278568965093761 497773317342208926723820321)
        ·
          refine ⟨373329988006656695042865241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497773317342208926723820321 373329988006656695042865241)
          ·
            refine ⟨279997491004992521282148931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373329988006656695042865241 279997491004992521282148931)
            ·
              refine ⟨419996236507488781923223397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279997491004992521282148931 419996236507488781923223397)
              ·
                refine ⟨78749294345154146610604387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419996236507488781923223397 78749294345154146610604387)
                ·
                  refine ⟨118123941517731219915906581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78749294345154146610604387 118123941517731219915906581)
                  ·
                    refine ⟨5537059758643650933558121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118123941517731219915906581 5537059758643650933558121)
                    ·
                      refine ⟨4152794818982738200168591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537059758643650933558121 4152794818982738200168591)
                      ·
                        rfl

theorem cell23_8087539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6, 2].length) (baseStart_8087539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087539 prefixEnd_8087539 := by exact prefixLift 8087539
  have htrace : WordTrace (prefixWord ++ tailWord_8087539) baseStart_8087539 baseEnd_8087539 := by
    simpa [prefixWord, tailWord_8087539, baseEnd_8087539] using wordTrace_append hprefix tailTrace_8087539
  have hstable : (prefixWord ++ tailWord_8087539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087539).length < 2 ^ (prefixWord ++ tailWord_8087539).sum := by decide
  have hdescent : baseEnd_8087539 < baseStart_8087539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087549 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_8087549 : Nat := 118140960795 + 8087549 * 2 ^ 59
def prefixEnd_8087549 : Nat := 4983230072969 + 3 ^ 40 * 8087549 * 2
def baseEnd_8087549 : Nat := 1384266651263094387014515

theorem tailTrace_8087549 : CollatzResearch.WordTrace tailWord_8087549 prefixEnd_8087549 1384266651263094387014515 := by
  unfold tailWord_8087549
  simp only [CollatzResearch.WordTrace]
  refine ⟨294977145377198691247905701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196651430251465794165270467 294977145377198691247905701)
  ·
    refine ⟨55308214758224754608982319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294977145377198691247905701 55308214758224754608982319)
    ·
      refine ⟨82962322137337131913473479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55308214758224754608982319 82962322137337131913473479)
      ·
        refine ⟨124443483206005697870210219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82962322137337131913473479 124443483206005697870210219)
        ·
          refine ⟨186665224809008546805315329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124443483206005697870210219 186665224809008546805315329)
          ·
            refine ⟨139998918606756410103986497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186665224809008546805315329 139998918606756410103986497)
            ·
              refine ⟨104999188955067307577989873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139998918606756410103986497 104999188955067307577989873)
              ·
                refine ⟨78749391716300480683492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104999188955067307577989873 78749391716300480683492405)
                ·
                  refine ⟨7382755473403170064077413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78749391716300480683492405 7382755473403170064077413)
                  ·
                    refine ⟨1384266651263094387014515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382755473403170064077413 1384266651263094387014515)
                    ·
                      rfl

theorem cell23_8087549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_8087549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087549 prefixEnd_8087549 := by exact prefixLift 8087549
  have htrace : WordTrace (prefixWord ++ tailWord_8087549) baseStart_8087549 baseEnd_8087549 := by
    simpa [prefixWord, tailWord_8087549, baseEnd_8087549] using wordTrace_append hprefix tailTrace_8087549
  have hstable : (prefixWord ++ tailWord_8087549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087549).length < 2 ^ (prefixWord ++ tailWord_8087549).sum := by decide
  have hdescent : baseEnd_8087549 < baseStart_8087549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087552 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_8087552 : Nat := 118140960795 + 8087552 * 2 ^ 59
def prefixEnd_8087552 : Nat := 4983230072969 + 3 ^ 40 * 8087552 * 2
def baseEnd_8087552 : Nat := 4152801494231246649306031

theorem tailTrace_8087552 : CollatzResearch.WordTrace tailWord_8087552 prefixEnd_8087552 4152801494231246649306031 := by
  unfold tailWord_8087552
  simp only [CollatzResearch.WordTrace]
  refine ⟨147488627398093911380132455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196651503197458548506843273 147488627398093911380132455)
  ·
    refine ⟨221232941097140867070198683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147488627398093911380132455 221232941097140867070198683)
    ·
      refine ⟨331849411645711300605298025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221232941097140867070198683 331849411645711300605298025)
      ·
        refine ⟨248887058734283475453973519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331849411645711300605298025 248887058734283475453973519)
        ·
          refine ⟨373330588101425213180960279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248887058734283475453973519 373330588101425213180960279)
          ·
            refine ⟨559995882152137819771440419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373330588101425213180960279 559995882152137819771440419)
            ·
              refine ⟨839993823228206729657160629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559995882152137819771440419 839993823228206729657160629)
              ·
                refine ⟨78749420927644380905358809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 839993823228206729657160629 78749420927644380905358809)
                ·
                  refine ⟨59062065695733285679019107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78749420927644380905358809 59062065695733285679019107)
                  ·
                    refine ⟨88593098543599928518528661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59062065695733285679019107 88593098543599928518528661)
                    ·
                      refine ⟨4152801494231246649306031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88593098543599928518528661 4152801494231246649306031)
                      ·
                        rfl

theorem cell23_8087552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_8087552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087552 prefixEnd_8087552 := by exact prefixLift 8087552
  have htrace : WordTrace (prefixWord ++ tailWord_8087552) baseStart_8087552 baseEnd_8087552 := by
    simpa [prefixWord, tailWord_8087552, baseEnd_8087552] using wordTrace_append hprefix tailTrace_8087552
  have hstable : (prefixWord ++ tailWord_8087552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087552).length < 2 ^ (prefixWord ++ tailWord_8087552).sum := by decide
  have hdescent : baseEnd_8087552 < baseStart_8087552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087617 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 1, 4]
def baseStart_8087617 : Nat := 118140960795 + 8087617 * 2 ^ 59
def prefixEnd_8087617 : Nat := 4983230072969 + 3 ^ 40 * 8087617 * 2
def baseEnd_8087617 : Nat := 1384278290157929631664411

theorem tailTrace_8087617 : CollatzResearch.WordTrace tailWord_8087617 prefixEnd_8087617 1384278290157929631664411 := by
  unfold tailWord_8087617
  simp only [CollatzResearch.WordTrace]
  refine ⟨294979625540952338861381105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196653083693968225907587403 294979625540952338861381105)
  ·
    refine ⟨221234719155714254146035829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294979625540952338861381105 221234719155714254146035829)
    ·
      refine ⟨20740754920848211326190859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221234719155714254146035829 20740754920848211326190859)
      ·
        refine ⟨31111132381272316989286289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20740754920848211326190859 31111132381272316989286289)
        ·
          refine ⟨23333349285954237741964717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31111132381272316989286289 23333349285954237741964717)
          ·
            refine ⟨8750005982232839153236769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23333349285954237741964717 8750005982232839153236769)
            ·
              refine ⟨6562504486674629364927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8750005982232839153236769 6562504486674629364927577)
              ·
                refine ⟨4921878365005972023695683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562504486674629364927577 4921878365005972023695683)
                ·
                  refine ⟨7382817547508958035543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921878365005972023695683 7382817547508958035543525)
                  ·
                    refine ⟨1384278290157929631664411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382817547508958035543525 1384278290157929631664411)
                    ·
                      rfl

theorem cell23_8087617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_8087617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087617 prefixEnd_8087617 := by exact prefixLift 8087617
  have htrace : WordTrace (prefixWord ++ tailWord_8087617) baseStart_8087617 baseEnd_8087617 := by
    simpa [prefixWord, tailWord_8087617, baseEnd_8087617] using wordTrace_append hprefix tailTrace_8087617
  have hstable : (prefixWord ++ tailWord_8087617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087617).length < 2 ^ (prefixWord ++ tailWord_8087617).sum := by decide
  have hdescent : baseEnd_8087617 < baseStart_8087617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087639 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 1, 6]
def baseStart_8087639 : Nat := 118140960795 + 8087639 * 2 ^ 59
def prefixEnd_8087639 : Nat := 4983230072969 + 3 ^ 40 * 8087639 * 2
def baseEnd_8087639 : Nat := 1384282055682729269639377

theorem tailTrace_8087639 : CollatzResearch.WordTrace tailWord_8087639 prefixEnd_8087639 1384282055682729269639377 := by
  unfold tailWord_8087639
  simp only [CollatzResearch.WordTrace]
  refine ⟨294980427946872636618681971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196653618631248424412454647 294980427946872636618681971)
  ·
    refine ⟨442470641920308954928022957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294980427946872636618681971 442470641920308954928022957)
    ·
      refine ⟨165926490720115858098008609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442470641920308954928022957 165926490720115858098008609)
      ·
        refine ⟨124444868040086893573506457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165926490720115858098008609 124444868040086893573506457)
        ·
          refine ⟨93333651030065170180129843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124444868040086893573506457 93333651030065170180129843)
          ·
            refine ⟨140000476545097755270194765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93333651030065170180129843 140000476545097755270194765)
            ·
              refine ⟨52500178704411658226323037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140000476545097755270194765 52500178704411658226323037)
              ·
                refine ⟨19687567014154371834871139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52500178704411658226323037 19687567014154371834871139)
                ·
                  refine ⟨29531350521231557752306709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19687567014154371834871139 29531350521231557752306709)
                  ·
                    refine ⟨1384282055682729269639377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29531350521231557752306709 1384282055682729269639377)
                    ·
                      rfl

theorem cell23_8087639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_8087639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087639 prefixEnd_8087639 := by exact prefixLift 8087639
  have htrace : WordTrace (prefixWord ++ tailWord_8087639) baseStart_8087639 baseEnd_8087639 := by
    simpa [prefixWord, tailWord_8087639, baseEnd_8087639] using wordTrace_append hprefix tailTrace_8087639
  have hstable : (prefixWord ++ tailWord_8087639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087639).length < 2 ^ (prefixWord ++ tailWord_8087639).sum := by decide
  have hdescent : baseEnd_8087639 < baseStart_8087639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087650 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8087650 : Nat := 118140960795 + 8087650 * 2 ^ 59
def prefixEnd_8087650 : Nat := 4983230072969 + 3 ^ 40 * 8087650 * 2
def baseEnd_8087650 : Nat := 4152851815335387265880581

theorem tailTrace_8087650 : CollatzResearch.WordTrace tailWord_8087650 prefixEnd_8087650 4152851815335387265880581 := by
  unfold tailWord_8087650
  simp only [CollatzResearch.WordTrace]
  refine ⟨73745207287458196374333101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196653886099888523664888269 73745207287458196374333101)
  ·
    refine ⟨27654452732796823640374913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73745207287458196374333101 27654452732796823640374913)
    ·
      refine ⟨20740839549597617730281185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27654452732796823640374913 20740839549597617730281185)
      ·
        refine ⟨15555629662198213297710889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20740839549597617730281185 15555629662198213297710889)
        ·
          refine ⟨11666722246648659973283167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555629662198213297710889 11666722246648659973283167)
          ·
            refine ⟨17500083369972989959924751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666722246648659973283167 17500083369972989959924751)
            ·
              refine ⟨26250125054959484939887127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500083369972989959924751 26250125054959484939887127)
              ·
                refine ⟨39375187582439227409830691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26250125054959484939887127 39375187582439227409830691)
                ·
                  refine ⟨59062781373658841114746037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39375187582439227409830691 59062781373658841114746037)
                  ·
                    refine ⟨5537135753780516354507441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59062781373658841114746037 5537135753780516354507441)
                    ·
                      refine ⟨4152851815335387265880581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537135753780516354507441 4152851815335387265880581)
                      ·
                        rfl

theorem cell23_8087650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8087650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087650 prefixEnd_8087650 := by exact prefixLift 8087650
  have htrace : WordTrace (prefixWord ++ tailWord_8087650) baseStart_8087650 baseEnd_8087650 := by
    simpa [prefixWord, tailWord_8087650, baseEnd_8087650] using wordTrace_append hprefix tailTrace_8087650
  have hstable : (prefixWord ++ tailWord_8087650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087650).length < 2 ^ (prefixWord ++ tailWord_8087650).sum := by decide
  have hdescent : baseEnd_8087650 < baseStart_8087650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087663 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 1, 1, 4]
def baseStart_8087663 : Nat := 118140960795 + 8087663 * 2 ^ 59
def prefixEnd_8087663 : Nat := 4983230072969 + 3 ^ 40 * 8087663 * 2
def baseEnd_8087663 : Nat := 4152858490583895715018021

theorem tailTrace_8087663 : CollatzResearch.WordTrace tailWord_8087663 prefixEnd_8087663 4152858490583895715018021 := by
  unfold tailWord_8087663
  simp only [CollatzResearch.WordTrace]
  refine ⟨294981303298785688717555643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196654202199190459145037095 294981303298785688717555643)
  ·
    refine ⟨442471954948178533076333465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294981303298785688717555643 442471954948178533076333465)
    ·
      refine ⟨331853966211133899807250099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442471954948178533076333465 331853966211133899807250099)
      ·
        refine ⟨497780949316700849710875149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331853966211133899807250099 497780949316700849710875149)
        ·
          refine ⟨186667855993762818641578181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497780949316700849710875149 186667855993762818641578181)
          ·
            refine ⟨35000222998830528495295909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186667855993762818641578181 35000222998830528495295909)
            ·
              refine ⟨6562541812280724092867983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35000222998830528495295909 6562541812280724092867983)
              ·
                refine ⟨9843812718421086139301975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562541812280724092867983 9843812718421086139301975)
                ·
                  refine ⟨14765719077631629208952963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9843812718421086139301975 14765719077631629208952963)
                  ·
                    refine ⟨22148578616447443813429445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14765719077631629208952963 22148578616447443813429445)
                    ·
                      refine ⟨4152858490583895715018021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22148578616447443813429445 4152858490583895715018021)
                      ·
                        rfl

theorem cell23_8087663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 1, 4].length) (baseStart_8087663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087663 prefixEnd_8087663 := by exact prefixLift 8087663
  have htrace : WordTrace (prefixWord ++ tailWord_8087663) baseStart_8087663 baseEnd_8087663 := by
    simpa [prefixWord, tailWord_8087663, baseEnd_8087663] using wordTrace_append hprefix tailTrace_8087663
  have hstable : (prefixWord ++ tailWord_8087663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087663).length < 2 ^ (prefixWord ++ tailWord_8087663).sum := by decide
  have hdescent : baseEnd_8087663 < baseStart_8087663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087673 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_8087673 : Nat := 118140960795 + 8087673 * 2 ^ 59
def prefixEnd_8087673 : Nat := 4983230072969 + 3 ^ 40 * 8087673 * 2
def baseEnd_8087673 : Nat := 1384287875130146891964325

theorem tailTrace_8087673 : CollatzResearch.WordTrace tailWord_8087673 prefixEnd_8087673 1384287875130146891964325 := by
  unfold tailWord_8087673
  simp only [CollatzResearch.WordTrace]
  refine ⟨294981668028749460425419673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196654445352499640283613115 294981668028749460425419673)
  ·
    refine ⟨221236251021562095319064755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294981668028749460425419673 221236251021562095319064755)
    ·
      refine ⟨331854376532343142978597133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221236251021562095319064755 331854376532343142978597133)
      ·
        refine ⟨124445391199628678616973925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331854376532343142978597133 124445391199628678616973925)
        ·
          refine ⟨23333510849930377240682611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124445391199628678616973925 23333510849930377240682611)
          ·
            refine ⟨35000266274895565861023917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23333510849930377240682611 35000266274895565861023917)
            ·
              refine ⟨13125099853085837197883969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35000266274895565861023917 13125099853085837197883969)
              ·
                refine ⟨9843824889814377898412977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13125099853085837197883969 9843824889814377898412977)
                ·
                  refine ⟨7382868667360783423809733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9843824889814377898412977 7382868667360783423809733)
                  ·
                    refine ⟨1384287875130146891964325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382868667360783423809733 1384287875130146891964325)
                    ·
                      rfl

theorem cell23_8087673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_8087673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087673 prefixEnd_8087673 := by exact prefixLift 8087673
  have htrace : WordTrace (prefixWord ++ tailWord_8087673) baseStart_8087673 baseEnd_8087673 := by
    simpa [prefixWord, tailWord_8087673, baseEnd_8087673] using wordTrace_append hprefix tailTrace_8087673
  have hstable : (prefixWord ++ tailWord_8087673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087673).length < 2 ^ (prefixWord ++ tailWord_8087673).sum := by decide
  have hdescent : baseEnd_8087673 < baseStart_8087673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087679 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_8087679 : Nat := 118140960795 + 8087679 * 2 ^ 59
def prefixEnd_8087679 : Nat := 4983230072969 + 3 ^ 40 * 8087679 * 2
def baseEnd_8087679 : Nat := 4152866706274367652417947

theorem tailTrace_8087679 : CollatzResearch.WordTrace tailWord_8087679 prefixEnd_8087679 4152866706274367652417947 := by
  unfold tailWord_8087679
  simp only [CollatzResearch.WordTrace]
  refine ⟨294981886866727723450138091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196654591244485148966758727 294981886866727723450138091)
  ·
    refine ⟨442472830300091585175207137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294981886866727723450138091 442472830300091585175207137)
    ·
      refine ⟨331854622725068688881405353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442472830300091585175207137 331854622725068688881405353)
      ·
        refine ⟨248890967043801516661054015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331854622725068688881405353 248890967043801516661054015)
        ·
          refine ⟨373336450565702274991581023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248890967043801516661054015 373336450565702274991581023)
          ·
            refine ⟨560004675848553412487371535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373336450565702274991581023 560004675848553412487371535)
            ·
              refine ⟨840007013772830118731057303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560004675848553412487371535 840007013772830118731057303)
              ·
                refine ⟨1260010520659245178096585955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840007013772830118731057303 1260010520659245178096585955)
                ·
                  refine ⟨1890015780988867767144878933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260010520659245178096585955 1890015780988867767144878933)
                  ·
                    refine ⟨11074311216731647073114525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1890015780988867767144878933 11074311216731647073114525)
                    ·
                      refine ⟨4152866706274367652417947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074311216731647073114525 4152866706274367652417947)
                      ·
                        rfl

theorem cell23_8087679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_8087679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087679 prefixEnd_8087679 := by exact prefixLift 8087679
  have htrace : WordTrace (prefixWord ++ tailWord_8087679) baseStart_8087679 baseEnd_8087679 := by
    simpa [prefixWord, tailWord_8087679, baseEnd_8087679] using wordTrace_append hprefix tailTrace_8087679
  have hstable : (prefixWord ++ tailWord_8087679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087679).length < 2 ^ (prefixWord ++ tailWord_8087679).sum := by decide
  have hdescent : baseEnd_8087679 < baseStart_8087679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087690 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_8087690 : Nat := 118140960795 + 8087690 * 2 ^ 59
def prefixEnd_8087690 : Nat := 4983230072969 + 3 ^ 40 * 8087690 * 2
def baseEnd_8087690 : Nat := 1384290784853855703126799

theorem tailTrace_8087690 : CollatzResearch.WordTrace tailWord_8087690 prefixEnd_8087690 1384290784853855703126799 := by
  unfold tailWord_8087690
  simp only [CollatzResearch.WordTrace]
  refine ⟨73745572017421968082197131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196654858713125248219192349 73745572017421968082197131)
  ·
    refine ⟨110618358026132952123295697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73745572017421968082197131 110618358026132952123295697)
    ·
      refine ⟨82963768519599714092471773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110618358026132952123295697 82963768519599714092471773)
      ·
        refine ⟨31111413194849892784676915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82963768519599714092471773 31111413194849892784676915)
        ·
          refine ⟨46667119792274839177015373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31111413194849892784676915 46667119792274839177015373)
          ·
            refine ⟨17500169922103064691380765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46667119792274839177015373 17500169922103064691380765)
            ·
              refine ⟨6562563720788649259267787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17500169922103064691380765 6562563720788649259267787)
              ·
                refine ⟨9843845581182973888901681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6562563720788649259267787 9843845581182973888901681)
                ·
                  refine ⟨7382884185887230416676261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9843845581182973888901681 7382884185887230416676261)
                  ·
                    refine ⟨1384290784853855703126799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382884185887230416676261 1384290784853855703126799)
                    ·
                      rfl

theorem cell23_8087690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_8087690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087690 prefixEnd_8087690 := by exact prefixLift 8087690
  have htrace : WordTrace (prefixWord ++ tailWord_8087690) baseStart_8087690 baseEnd_8087690 := by
    simpa [prefixWord, tailWord_8087690, baseEnd_8087690] using wordTrace_append hprefix tailTrace_8087690
  have hstable : (prefixWord ++ tailWord_8087690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087690).length < 2 ^ (prefixWord ++ tailWord_8087690).sum := by decide
  have hdescent : baseEnd_8087690 < baseStart_8087690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087703 : List Nat := [1, 1, 3, 3, 4, 2, 2, 7]
def baseStart_8087703 : Nat := 118140960795 + 8087703 * 2 ^ 59
def prefixEnd_8087703 : Nat := 4983230072969 + 3 ^ 40 * 8087703 * 2
def baseEnd_8087703 : Nat := 153810334437410205871031

theorem tailTrace_8087703 : CollatzResearch.WordTrace tailWord_8087703 prefixEnd_8087703 153810334437410205871031 := by
  unfold tailWord_8087703
  simp only [CollatzResearch.WordTrace]
  refine ⟨294982762218640775549011763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196655174812427183699341175 294982762218640775549011763)
  ·
    refine ⟨442474143327961163323517645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294982762218640775549011763 442474143327961163323517645)
    ·
      refine ⟨165927803747985436246319117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442474143327961163323517645 165927803747985436246319117)
      ·
        refine ⟨62222926405494538592369669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165927803747985436246319117 62222926405494538592369669)
        ·
          refine ⟨11666798701030225986069313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62222926405494538592369669 11666798701030225986069313)
          ·
            refine ⟨8750099025772669489551985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11666798701030225986069313 8750099025772669489551985)
            ·
              refine ⟨6562574269329502117163989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8750099025772669489551985 6562574269329502117163989)
              ·
                refine ⟨153810334437410205871031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6562574269329502117163989 153810334437410205871031)
                ·
                  rfl

theorem cell23_8087703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 7].length) (baseStart_8087703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087703 prefixEnd_8087703 := by exact prefixLift 8087703
  have htrace : WordTrace (prefixWord ++ tailWord_8087703) baseStart_8087703 baseEnd_8087703 := by
    simpa [prefixWord, tailWord_8087703, baseEnd_8087703] using wordTrace_append hprefix tailTrace_8087703
  have hstable : (prefixWord ++ tailWord_8087703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087703).length < 2 ^ (prefixWord ++ tailWord_8087703).sum := by decide
  have hdescent : baseEnd_8087703 < baseStart_8087703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087713 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_8087713 : Nat := 118140960795 + 8087713 * 2 ^ 59
def prefixEnd_8087713 : Nat := 4983230072969 + 3 ^ 40 * 8087713 * 2
def baseEnd_8087713 : Nat := 4152884164616620519392791

theorem tailTrace_8087713 : CollatzResearch.WordTrace tailWord_8087713 prefixEnd_8087713 4152884164616620519392791 := by
  unfold tailWord_8087713
  simp only [CollatzResearch.WordTrace]
  refine ⟨294983126948604547256875793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196655417965736364837917195 294983126948604547256875793)
  ·
    refine ⟨221237345211453410442656845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294983126948604547256875793 221237345211453410442656845)
    ·
      refine ⟨82964004454295028915996317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221237345211453410442656845 82964004454295028915996317)
      ·
        refine ⟨31111501670360635843498619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82964004454295028915996317 31111501670360635843498619)
        ·
          refine ⟨46667252505540953765247929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31111501670360635843498619 46667252505540953765247929)
          ·
            refine ⟨35000439379155715323935947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46667252505540953765247929 35000439379155715323935947)
            ·
              refine ⟨52500659068733572985903921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35000439379155715323935947 52500659068733572985903921)
              ·
                refine ⟨39375494301550179739427941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52500659068733572985903921 39375494301550179739427941)
                ·
                  refine ⟨7382905181540658701142739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39375494301550179739427941 7382905181540658701142739)
                  ·
                    refine ⟨11074357772310988051714109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382905181540658701142739 11074357772310988051714109)
                    ·
                      refine ⟨4152884164616620519392791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074357772310988051714109 4152884164616620519392791)
                      ·
                        rfl

theorem cell23_8087713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_8087713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087713 prefixEnd_8087713 := by exact prefixLift 8087713
  have htrace : WordTrace (prefixWord ++ tailWord_8087713) baseStart_8087713 baseEnd_8087713 := by
    simpa [prefixWord, tailWord_8087713, baseEnd_8087713] using wordTrace_append hprefix tailTrace_8087713
  have hstable : (prefixWord ++ tailWord_8087713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087713).length < 2 ^ (prefixWord ++ tailWord_8087713).sum := by decide
  have hdescent : baseEnd_8087713 < baseStart_8087713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087714 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_8087714 : Nat := 118140960795 + 8087714 * 2 ^ 59
def prefixEnd_8087714 : Nat := 4983230072969 + 3 ^ 40 * 8087714 * 2
def baseEnd_8087714 : Nat := 4152884678097275015480287

theorem tailTrace_8087714 : CollatzResearch.WordTrace tailWord_8087714 prefixEnd_8087714 4152884678097275015480287 := by
  unfold tailWord_8087714
  simp only [CollatzResearch.WordTrace]
  refine ⟨73745790855400231106915549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196655442281067282951774797 73745790855400231106915549)
  ·
    refine ⟨27654671570775086665093331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73745790855400231106915549 27654671570775086665093331)
    ·
      refine ⟨41482007356162629997639997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27654671570775086665093331 41482007356162629997639997)
      ·
        refine ⟨15555752758560986249114999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41482007356162629997639997 15555752758560986249114999)
        ·
          refine ⟨23333629137841479373672499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15555752758560986249114999 23333629137841479373672499)
          ·
            refine ⟨35000443706762219060508749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23333629137841479373672499 35000443706762219060508749)
            ·
              refine ⟨13125166390035832147690781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35000443706762219060508749 13125166390035832147690781)
              ·
                refine ⟨4921937396263437055384043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13125166390035832147690781 4921937396263437055384043)
                ·
                  refine ⟨7382906094395155583076065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921937396263437055384043 7382906094395155583076065)
                  ·
                    refine ⟨5537179570796366687307049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382906094395155583076065 5537179570796366687307049)
                    ·
                      refine ⟨4152884678097275015480287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537179570796366687307049 4152884678097275015480287)
                      ·
                        rfl

theorem cell23_8087714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_8087714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087714 prefixEnd_8087714 := by exact prefixLift 8087714
  have htrace : WordTrace (prefixWord ++ tailWord_8087714) baseStart_8087714 baseEnd_8087714 := by
    simpa [prefixWord, tailWord_8087714, baseEnd_8087714] using wordTrace_append hprefix tailTrace_8087714
  have hstable : (prefixWord ++ tailWord_8087714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087714).length < 2 ^ (prefixWord ++ tailWord_8087714).sum := by decide
  have hdescent : baseEnd_8087714 < baseStart_8087714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087739 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_8087739 : Nat := 118140960795 + 8087739 * 2 ^ 59
def prefixEnd_8087739 : Nat := 4983230072969 + 3 ^ 40 * 8087739 * 2
def baseEnd_8087739 : Nat := 4152897515113637417667671

theorem tailTrace_8087739 : CollatzResearch.WordTrace tailWord_8087739 prefixEnd_8087739 4152897515113637417667671 := by
  unfold tailWord_8087739
  simp only [CollatzResearch.WordTrace]
  refine ⟨294984075246510353697322271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196656050164340235798214847 294984075246510353697322271)
  ·
    refine ⟨442476112869765530545983407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294984075246510353697322271 442476112869765530545983407)
    ·
      refine ⟨663714169304648295818975111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442476112869765530545983407 663714169304648295818975111)
      ·
        refine ⟨995571253956972443728462667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663714169304648295818975111 995571253956972443728462667)
        ·
          refine ⟨1493356880935458665592694001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995571253956972443728462667 1493356880935458665592694001)
          ·
            refine ⟨1120017660701593999194520501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493356880935458665592694001 1120017660701593999194520501)
            ·
              refine ⟨105001655690774437424486297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1120017660701593999194520501 105001655690774437424486297)
              ·
                refine ⟨78751241768080828068364723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105001655690774437424486297 78751241768080828068364723)
                ·
                  refine ⟨118126862652121242102547085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78751241768080828068364723 118126862652121242102547085)
                  ·
                    refine ⟨44297573494545465788455157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118126862652121242102547085 44297573494545465788455157)
                    ·
                      refine ⟨4152897515113637417667671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44297573494545465788455157 4152897515113637417667671)
                      ·
                        rfl

theorem cell23_8087739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_8087739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087739 prefixEnd_8087739 := by exact prefixLift 8087739
  have htrace : WordTrace (prefixWord ++ tailWord_8087739) baseStart_8087739 baseEnd_8087739 := by
    simpa [prefixWord, tailWord_8087739, baseEnd_8087739] using wordTrace_append hprefix tailTrace_8087739
  have hstable : (prefixWord ++ tailWord_8087739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087739).length < 2 ^ (prefixWord ++ tailWord_8087739).sum := by decide
  have hdescent : baseEnd_8087739 < baseStart_8087739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087753 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 6, 2, 2]
def baseStart_8087753 : Nat := 118140960795 + 8087753 * 2 ^ 59
def prefixEnd_8087753 : Nat := 4983230072969 + 3 ^ 40 * 8087753 * 2
def baseEnd_8087753 : Nat := 4152904703842800362892607

theorem tailTrace_8087753 : CollatzResearch.WordTrace tailWord_8087753 prefixEnd_8087753 4152904703842800362892607 := by
  unfold tailWord_8087753
  simp only [CollatzResearch.WordTrace]
  refine ⟨294984585868459634088331913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196656390578973089392221275 294984585868459634088331913)
  ·
    refine ⟨221238439401344725566248935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294984585868459634088331913 221238439401344725566248935)
    ·
      refine ⟨331857659102017088349373403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221238439401344725566248935 331857659102017088349373403)
      ·
        refine ⟨497786488653025632524060105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331857659102017088349373403 497786488653025632524060105)
        ·
          refine ⟨373339866489769224393045079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497786488653025632524060105 373339866489769224393045079)
          ·
            refine ⟨560009799734653836589567619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373339866489769224393045079 560009799734653836589567619)
            ·
              refine ⟨840014699601980754884351429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560009799734653836589567619 840014699601980754884351429)
              ·
                refine ⟨157502756175371391540815893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840014699601980754884351429 157502756175371391540815893)
                ·
                  refine ⟨7382941695720533978475745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157502756175371391540815893 7382941695720533978475745)
                  ·
                    refine ⟨5537206271790400483856809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7382941695720533978475745 5537206271790400483856809)
                    ·
                      refine ⟨4152904703842800362892607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537206271790400483856809 4152904703842800362892607)
                      ·
                        rfl

theorem cell23_8087753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2, 2].length) (baseStart_8087753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087753 prefixEnd_8087753 := by exact prefixLift 8087753
  have htrace : WordTrace (prefixWord ++ tailWord_8087753) baseStart_8087753 baseEnd_8087753 := by
    simpa [prefixWord, tailWord_8087753, baseEnd_8087753] using wordTrace_append hprefix tailTrace_8087753
  have hstable : (prefixWord ++ tailWord_8087753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087753).length < 2 ^ (prefixWord ++ tailWord_8087753).sum := by decide
  have hdescent : baseEnd_8087753 < baseStart_8087753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087759 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 9]
def baseStart_8087759 : Nat := 118140960795 + 8087759 * 2 ^ 59
def prefixEnd_8087759 : Nat := 4983230072969 + 3 ^ 40 * 8087759 * 2
def baseEnd_8087759 : Nat := 461434198302969704379731

theorem tailTrace_8087759 : CollatzResearch.WordTrace tailWord_8087759 prefixEnd_8087759 461434198302969704379731 := by
  unfold tailWord_8087759
  simp only [CollatzResearch.WordTrace]
  refine ⟨294984804706437897113050331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196656536470958598075366887 294984804706437897113050331)
  ·
    refine ⟨442477207059656845669575497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294984804706437897113050331 442477207059656845669575497)
    ·
      refine ⟨331857905294742634252181623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442477207059656845669575497 331857905294742634252181623)
      ·
        refine ⟨497786857942113951378272435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331857905294742634252181623 497786857942113951378272435)
        ·
          refine ⟨746680286913170927067408653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497786857942113951378272435 746680286913170927067408653)
          ·
            refine ⟨280005107592439097650278245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746680286913170927067408653 280005107592439097650278245)
            ·
              refine ⟨52500957673582330809427171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280005107592439097650278245 52500957673582330809427171)
              ·
                refine ⟨78751436510373496214140757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52500957673582330809427171 78751436510373496214140757)
                ·
                  refine ⟨461434198302969704379731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78751436510373496214140757 461434198302969704379731)
                  ·
                    rfl

theorem cell23_8087759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 9].length) (baseStart_8087759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087759 prefixEnd_8087759 := by exact prefixLift 8087759
  have htrace : WordTrace (prefixWord ++ tailWord_8087759) baseStart_8087759 baseEnd_8087759 := by
    simpa [prefixWord, tailWord_8087759, baseEnd_8087759] using wordTrace_append hprefix tailTrace_8087759
  have hstable : (prefixWord ++ tailWord_8087759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087759).length < 2 ^ (prefixWord ++ tailWord_8087759).sum := by decide
  have hdescent : baseEnd_8087759 < baseStart_8087759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087773 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_8087773 : Nat := 118140960795 + 8087773 * 2 ^ 59
def prefixEnd_8087773 : Nat := 4983230072969 + 3 ^ 40 * 8087773 * 2
def baseEnd_8087773 : Nat := 4152914973455890284642515

theorem tailTrace_8087773 : CollatzResearch.WordTrace tailWord_8087773 prefixEnd_8087773 4152914973455890284642515 := by
  unfold tailWord_8087773
  simp only [CollatzResearch.WordTrace]
  refine ⟨294985315328387177504059973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196656876885591451669373315 294985315328387177504059973)
  ·
    refine ⟨55309746624072595782011245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294985315328387177504059973 55309746624072595782011245)
    ·
      refine ⟨20741154984027223418254217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55309746624072595782011245 20741154984027223418254217)
      ·
        refine ⟨15555866238020417563690663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20741154984027223418254217 15555866238020417563690663)
        ·
          refine ⟨23333799357030626345535995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15555866238020417563690663 23333799357030626345535995)
          ·
            refine ⟨35000699035545939518303993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23333799357030626345535995 35000699035545939518303993)
            ·
              refine ⟨26250524276659454638727995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35000699035545939518303993 26250524276659454638727995)
              ·
                refine ⟨39375786414989181958091993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26250524276659454638727995 39375786414989181958091993)
                ·
                  refine ⟨29531839811241886468568995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39375786414989181958091993 29531839811241886468568995)
                  ·
                    refine ⟨44297759716862829702853493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29531839811241886468568995 44297759716862829702853493)
                    ·
                      refine ⟨4152914973455890284642515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44297759716862829702853493 4152914973455890284642515)
                      ·
                        rfl

theorem cell23_8087773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_8087773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087773 prefixEnd_8087773 := by exact prefixLift 8087773
  have htrace : WordTrace (prefixWord ++ tailWord_8087773) baseStart_8087773 baseEnd_8087773 := by
    simpa [prefixWord, tailWord_8087773, baseEnd_8087773] using wordTrace_append hprefix tailTrace_8087773
  have hstable : (prefixWord ++ tailWord_8087773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087773).length < 2 ^ (prefixWord ++ tailWord_8087773).sum := by decide
  have hdescent : baseEnd_8087773 < baseStart_8087773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087843 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 4, 4, 2]
def baseStart_8087843 : Nat := 118140960795 + 8087843 * 2 ^ 59
def prefixEnd_8087843 : Nat := 4983230072969 + 3 ^ 40 * 8087843 * 2
def baseEnd_8087843 : Nat := 4152950917101705010767193

theorem tailTrace_8087843 : CollatzResearch.WordTrace tailWord_8087843 prefixEnd_8087843 4152950917101705010767193 := by
  unfold tailWord_8087843
  simp only [CollatzResearch.WordTrace]
  refine ⟨294987868438133579459108183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196658578958755719639405455 294987868438133579459108183)
  ·
    refine ⟨442481802657200369188662275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294987868438133579459108183 442481802657200369188662275)
    ·
      refine ⟨663722703985800553782993413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442481802657200369188662275 663722703985800553782993413)
      ·
        refine ⟨124448006997337603834311265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 663722703985800553782993413 124448006997337603834311265)
        ·
          refine ⟨93336005248003202875733449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124448006997337603834311265 93336005248003202875733449)
          ·
            refine ⟨70002003936002402156800087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93336005248003202875733449 70002003936002402156800087)
            ·
              refine ⟨105003005904003603235200131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70002003936002402156800087 105003005904003603235200131)
              ·
                refine ⟨157504508856005404852800197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105003005904003603235200131 157504508856005404852800197)
                ·
                  refine ⟨29532095410501013409900037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157504508856005404852800197 29532095410501013409900037)
                  ·
                    refine ⟨5537267889468940014356257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29532095410501013409900037 5537267889468940014356257)
                    ·
                      refine ⟨4152950917101705010767193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537267889468940014356257 4152950917101705010767193)
                      ·
                        rfl

theorem cell23_8087843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_8087843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087843 prefixEnd_8087843 := by exact prefixLift 8087843
  have htrace : WordTrace (prefixWord ++ tailWord_8087843) baseStart_8087843 baseEnd_8087843 := by
    simpa [prefixWord, tailWord_8087843, baseEnd_8087843] using wordTrace_append hprefix tailTrace_8087843
  have hstable : (prefixWord ++ tailWord_8087843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087843).length < 2 ^ (prefixWord ++ tailWord_8087843).sum := by decide
  have hdescent : baseEnd_8087843 < baseStart_8087843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087870 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_8087870 : Nat := 118140960795 + 8087870 * 2 ^ 59
def prefixEnd_8087870 : Nat := 4983230072969 + 3 ^ 40 * 8087870 * 2
def baseEnd_8087870 : Nat := 1384321593693125468376523

theorem tailTrace_8087870 : CollatzResearch.WordTrace tailWord_8087870 prefixEnd_8087870 1384321593693125468376523 := by
  unfold tailWord_8087870
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873606651129470383792633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196659235472690508713560709 36873606651129470383792633)
  ·
    refine ⟨27655204988347102787844475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36873606651129470383792633 27655204988347102787844475)
    ·
      refine ⟨41482807482520654181766713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655204988347102787844475 41482807482520654181766713)
      ·
        refine ⟨31112105611890490636325035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41482807482520654181766713 31112105611890490636325035)
        ·
          refine ⟨46668158417835735954487553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31112105611890490636325035 46668158417835735954487553)
          ·
            refine ⟨35001118813376801965865665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46668158417835735954487553 35001118813376801965865665)
            ·
              refine ⟨26250839110032601474399249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35001118813376801965865665 26250839110032601474399249)
              ·
                refine ⟨19688129332524451105799437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26250839110032601474399249 19688129332524451105799437)
                ·
                  refine ⟨7383048499696669164674789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19688129332524451105799437 7383048499696669164674789)
                  ·
                    refine ⟨1384321593693125468376523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383048499696669164674789 1384321593693125468376523)
                    ·
                      rfl

theorem cell23_8087870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_8087870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087870 prefixEnd_8087870 := by exact prefixLift 8087870
  have htrace : WordTrace (prefixWord ++ tailWord_8087870) baseStart_8087870 baseEnd_8087870 := by
    simpa [prefixWord, tailWord_8087870, baseEnd_8087870] using wordTrace_append hprefix tailTrace_8087870
  have hstable : (prefixWord ++ tailWord_8087870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087870).length < 2 ^ (prefixWord ++ tailWord_8087870).sum := by decide
  have hdescent : baseEnd_8087870 < baseStart_8087870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087886 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_8087886 : Nat := 118140960795 + 8087886 * 2 ^ 59
def prefixEnd_8087886 : Nat := 4983230072969 + 3 ^ 40 * 8087886 * 2
def baseEnd_8087886 : Nat := 4152972996769848342529495

theorem tailTrace_8087886 : CollatzResearch.WordTrace tailWord_8087886 prefixEnd_8087886 4152972996769848342529495 := by
  unfold tailWord_8087886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873679597122224725365439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196659624517985198535282341 36873679597122224725365439)
  ·
    refine ⟨55310519395683337088048159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36873679597122224725365439 55310519395683337088048159)
    ·
      refine ⟨82965779093525005632072239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55310519395683337088048159 82965779093525005632072239)
      ·
        refine ⟨124448668640287508448108359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82965779093525005632072239 124448668640287508448108359)
        ·
          refine ⟨186673002960431262672162539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124448668640287508448108359 186673002960431262672162539)
          ·
            refine ⟨280009504440646894008243809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186673002960431262672162539 280009504440646894008243809)
            ·
              refine ⟨210007128330485170506182857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280009504440646894008243809 210007128330485170506182857)
              ·
                refine ⟨157505346247863877879637143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210007128330485170506182857 157505346247863877879637143)
                ·
                  refine ⟨236258019371795816819455715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157505346247863877879637143 236258019371795816819455715)
                  ·
                    refine ⟨354387029057693725229183573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236258019371795816819455715 354387029057693725229183573)
                    ·
                      refine ⟨4152972996769848342529495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 354387029057693725229183573 4152972996769848342529495)
                      ·
                        rfl

theorem cell23_8087886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_8087886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087886 prefixEnd_8087886 := by exact prefixLift 8087886
  have htrace : WordTrace (prefixWord ++ tailWord_8087886) baseStart_8087886 baseEnd_8087886 := by
    simpa [prefixWord, tailWord_8087886, baseEnd_8087886] using wordTrace_append hprefix tailTrace_8087886
  have hstable : (prefixWord ++ tailWord_8087886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087886).length < 2 ^ (prefixWord ++ tailWord_8087886).sum := by decide
  have hdescent : baseEnd_8087886 < baseStart_8087886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087904 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 1, 4]
def baseStart_8087904 : Nat := 118140960795 + 8087904 * 2 ^ 59
def prefixEnd_8087904 : Nat := 4983230072969 + 3 ^ 40 * 8087904 * 2
def baseEnd_8087904 : Nat := 1384327413140543090701471

theorem tailTrace_8087904 : CollatzResearch.WordTrace tailWord_8087904 prefixEnd_8087904 1384327413140543090701471 := by
  unfold tailWord_8087904
  simp only [CollatzResearch.WordTrace]
  refine ⟨147495046645456293438539383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196660062193941724584719177 147495046645456293438539383)
  ·
    refine ⟨221242569968184440157809075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147495046645456293438539383 221242569968184440157809075)
    ·
      refine ⟨331863854952276660236713613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221242569968184440157809075 331863854952276660236713613)
      ·
        refine ⟨124448945607103747588767605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331863854952276660236713613 124448945607103747588767605)
        ·
          refine ⟨11667088650665976336446963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124448945607103747588767605 11667088650665976336446963)
          ·
            refine ⟨17500632975998964504670445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667088650665976336446963 17500632975998964504670445)
            ·
              refine ⟨6562737365999611689251417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17500632975998964504670445 6562737365999611689251417)
              ·
                refine ⟨4922053024499708766938563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562737365999611689251417 4922053024499708766938563)
                ·
                  refine ⟨7383079536749563150407845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922053024499708766938563 7383079536749563150407845)
                  ·
                    refine ⟨1384327413140543090701471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383079536749563150407845 1384327413140543090701471)
                    ·
                      rfl

theorem cell23_8087904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 4].length) (baseStart_8087904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087904 prefixEnd_8087904 := by exact prefixLift 8087904
  have htrace : WordTrace (prefixWord ++ tailWord_8087904) baseStart_8087904 baseEnd_8087904 := by
    simpa [prefixWord, tailWord_8087904, baseEnd_8087904] using wordTrace_append hprefix tailTrace_8087904
  have hstable : (prefixWord ++ tailWord_8087904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087904).length < 2 ^ (prefixWord ++ tailWord_8087904).sum := by decide
  have hdescent : baseEnd_8087904 < baseStart_8087904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087936 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_8087936 : Nat := 118140960795 + 8087936 * 2 ^ 59
def prefixEnd_8087936 : Nat := 4983230072969 + 3 ^ 40 * 8087936 * 2
def baseEnd_8087936 : Nat := 4152998670802573146904265

theorem tailTrace_8087936 : CollatzResearch.WordTrace tailWord_8087936 prefixEnd_8087936 4152998670802573146904265 := by
  unfold tailWord_8087936
  simp only [CollatzResearch.WordTrace]
  refine ⟨147495630213398328171121831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196660840284531104228162441 147495630213398328171121831)
  ·
    refine ⟨221243445320097492256682747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147495630213398328171121831 221243445320097492256682747)
    ·
      refine ⟨331865167980146238385024121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221243445320097492256682747 331865167980146238385024121)
      ·
        refine ⟨248898875985109678788768091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331865167980146238385024121 248898875985109678788768091)
        ·
          refine ⟨373348313977664518183152137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248898875985109678788768091 373348313977664518183152137)
          ·
            refine ⟨280011235483248388637364103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373348313977664518183152137 280011235483248388637364103)
            ·
              refine ⟨420016853224872582956046155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280011235483248388637364103 420016853224872582956046155)
              ·
                refine ⟨630025279837308874434069233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420016853224872582956046155 630025279837308874434069233)
                ·
                  refine ⟨472518959877981655825551925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630025279837308874434069233 472518959877981655825551925)
                  ·
                    refine ⟨44298652488560780233645493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 472518959877981655825551925 44298652488560780233645493)
                    ·
                      refine ⟨4152998670802573146904265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44298652488560780233645493 4152998670802573146904265)
                      ·
                        rfl

theorem cell23_8087936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_8087936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087936 prefixEnd_8087936 := by exact prefixLift 8087936
  have htrace : WordTrace (prefixWord ++ tailWord_8087936) baseStart_8087936 baseEnd_8087936 := by
    simpa [prefixWord, tailWord_8087936, baseEnd_8087936] using wordTrace_append hprefix tailTrace_8087936
  have hstable : (prefixWord ++ tailWord_8087936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087936).length < 2 ^ (prefixWord ++ tailWord_8087936).sum := by decide
  have hdescent : baseEnd_8087936 < baseStart_8087936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087937 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_8087937 : Nat := 118140960795 + 8087937 * 2 ^ 59
def prefixEnd_8087937 : Nat := 4983230072969 + 3 ^ 40 * 8087937 * 2
def baseEnd_8087937 : Nat := 4152999184283227642991761

theorem tailTrace_8087937 : CollatzResearch.WordTrace tailWord_8087937 prefixEnd_8087937 4152999184283227642991761 := by
  unfold tailWord_8087937
  simp only [CollatzResearch.WordTrace]
  refine ⟨294991296899793033513030065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196660864599862022342020043 294991296899793033513030065)
  ·
    refine ⟨221243472674844775134772549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294991296899793033513030065 221243472674844775134772549)
    ·
      refine ⟨41483151126533395337769853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221243472674844775134772549 41483151126533395337769853)
      ·
        refine ⟨15556181672450023251663695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41483151126533395337769853 15556181672450023251663695)
        ·
          refine ⟨23334272508675034877495543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556181672450023251663695 23334272508675034877495543)
          ·
            refine ⟨35001408763012552316243315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23334272508675034877495543 35001408763012552316243315)
            ·
              refine ⟨52502113144518828474364973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35001408763012552316243315 52502113144518828474364973)
              ·
                refine ⟨19688292429194560677886865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52502113144518828474364973 19688292429194560677886865)
                ·
                  refine ⟨14766219321895920508415149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19688292429194560677886865 14766219321895920508415149)
                  ·
                    refine ⟨5537332245710970190655681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14766219321895920508415149 5537332245710970190655681)
                    ·
                      refine ⟨4152999184283227642991761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537332245710970190655681 4152999184283227642991761)
                      ·
                        rfl

theorem cell23_8087937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_8087937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087937 prefixEnd_8087937 := by exact prefixLift 8087937
  have htrace : WordTrace (prefixWord ++ tailWord_8087937) baseStart_8087937 baseEnd_8087937 := by
    simpa [prefixWord, tailWord_8087937, baseEnd_8087937] using wordTrace_append hprefix tailTrace_8087937
  have hstable : (prefixWord ++ tailWord_8087937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087937).length < 2 ^ (prefixWord ++ tailWord_8087937).sum := by decide
  have hdescent : baseEnd_8087937 < baseStart_8087937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087943 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 1, 6]
def baseStart_8087943 : Nat := 118140960795 + 8087943 * 2 ^ 59
def prefixEnd_8087943 : Nat := 4983230072969 + 3 ^ 40 * 8087943 * 2
def baseEnd_8087943 : Nat := 1384334088389051539838911

theorem tailTrace_8087943 : CollatzResearch.WordTrace tailWord_8087943 prefixEnd_8087943 1384334088389051539838911 := by
  unfold tailWord_8087943
  simp only [CollatzResearch.WordTrace]
  refine ⟨294991515737771296537748483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196661010491847531025165655 294991515737771296537748483)
  ·
    refine ⟨442487273606656944806622725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294991515737771296537748483 442487273606656944806622725)
    ·
      refine ⟨82966363801248177151241761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442487273606656944806622725 82966363801248177151241761)
      ·
        refine ⟨62224772850936132863431321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82966363801248177151241761 62224772850936132863431321)
        ·
          refine ⟨46668579638202099647573491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62224772850936132863431321 46668579638202099647573491)
          ·
            refine ⟨70002869457303149471360237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46668579638202099647573491 70002869457303149471360237)
            ·
              refine ⟨26251076046488681051760089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70002869457303149471360237 26251076046488681051760089)
              ·
                refine ⟨19688307034866510788820067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26251076046488681051760089 19688307034866510788820067)
                ·
                  refine ⟨29532460552299766183230101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19688307034866510788820067 29532460552299766183230101)
                  ·
                    refine ⟨1384334088389051539838911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29532460552299766183230101 1384334088389051539838911)
                    ·
                      rfl

theorem cell23_8087943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_8087943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087943 prefixEnd_8087943 := by exact prefixLift 8087943
  have htrace : WordTrace (prefixWord ++ tailWord_8087943) baseStart_8087943 baseEnd_8087943 := by
    simpa [prefixWord, tailWord_8087943, baseEnd_8087943] using wordTrace_append hprefix tailTrace_8087943
  have hstable : (prefixWord ++ tailWord_8087943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087943).length < 2 ^ (prefixWord ++ tailWord_8087943).sum := by decide
  have hdescent : baseEnd_8087943 < baseStart_8087943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087953 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_8087953 : Nat := 118140960795 + 8087953 * 2 ^ 59
def prefixEnd_8087953 : Nat := 4983230072969 + 3 ^ 40 * 8087953 * 2
def baseEnd_8087953 : Nat := 4153007399973699580391687

theorem tailTrace_8087953 : CollatzResearch.WordTrace tailWord_8087953 prefixEnd_8087953 4153007399973699580391687 := by
  unfold tailWord_8087953
  simp only [CollatzResearch.WordTrace]
  refine ⟨294991880467735068245612513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196661253645156712163741675 294991880467735068245612513)
  ·
    refine ⟨221243910350801301184209385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294991880467735068245612513 221243910350801301184209385)
    ·
      refine ⟨165932932763100975888157039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221243910350801301184209385 165932932763100975888157039)
      ·
        refine ⟨248899399144651463832235559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165932932763100975888157039 248899399144651463832235559)
        ·
          refine ⟨373349098716977195748353339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248899399144651463832235559 373349098716977195748353339)
          ·
            refine ⟨560023648075465793622530009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373349098716977195748353339 560023648075465793622530009)
            ·
              refine ⟨420017736056599345216897507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560023648075465793622530009 420017736056599345216897507)
              ·
                refine ⟨630026604084899017825346261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420017736056599345216897507 630026604084899017825346261)
                ·
                  refine ⟨14766248533239820730281553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 630026604084899017825346261 14766248533239820730281553)
                  ·
                    refine ⟨11074686399929865547711165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14766248533239820730281553 11074686399929865547711165)
                    ·
                      refine ⟨4153007399973699580391687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074686399929865547711165 4153007399973699580391687)
                      ·
                        rfl

theorem cell23_8087953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_8087953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087953 prefixEnd_8087953 := by exact prefixLift 8087953
  have htrace : WordTrace (prefixWord ++ tailWord_8087953) baseStart_8087953 baseEnd_8087953 := by
    simpa [prefixWord, tailWord_8087953, baseEnd_8087953] using wordTrace_append hprefix tailTrace_8087953
  have hstable : (prefixWord ++ tailWord_8087953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087953).length < 2 ^ (prefixWord ++ tailWord_8087953).sum := by decide
  have hdescent : baseEnd_8087953 < baseStart_8087953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087967 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 3, 2, 2]
def baseStart_8087967 : Nat := 118140960795 + 8087967 * 2 ^ 59
def prefixEnd_8087967 : Nat := 4983230072969 + 3 ^ 40 * 8087967 * 2
def baseEnd_8087967 : Nat := 4153014588702862525616623

theorem tailTrace_8087967 : CollatzResearch.WordTrace tailWord_8087967 prefixEnd_8087967 4153014588702862525616623 := by
  unfold tailWord_8087967
  simp only [CollatzResearch.WordTrace]
  refine ⟨294992391089684348636622155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196661594059789565757748103 294992391089684348636622155)
  ·
    refine ⟨442488586634526522954933233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294992391089684348636622155 442488586634526522954933233)
    ·
      refine ⟨331866439975894892216199925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442488586634526522954933233 331866439975894892216199925)
      ·
        refine ⟨31112478747740146145268743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331866439975894892216199925 31112478747740146145268743)
        ·
          refine ⟨46668718121610219217903115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31112478747740146145268743 46668718121610219217903115)
          ·
            refine ⟨70003077182415328826854673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46668718121610219217903115 70003077182415328826854673)
            ·
              refine ⟨52502307886811496620141005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70003077182415328826854673 52502307886811496620141005)
              ·
                refine ⟨19688365457554311232552877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52502307886811496620141005 19688365457554311232552877)
                ·
                  refine ⟨7383137046582866712207329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19688365457554311232552877 7383137046582866712207329)
                  ·
                    refine ⟨5537352784937150034155497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7383137046582866712207329 5537352784937150034155497)
                    ·
                      refine ⟨4153014588702862525616623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537352784937150034155497 4153014588702862525616623)
                      ·
                        rfl

theorem cell23_8087967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_8087967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087967 prefixEnd_8087967 := by exact prefixLift 8087967
  have htrace : WordTrace (prefixWord ++ tailWord_8087967) baseStart_8087967 baseEnd_8087967 := by
    simpa [prefixWord, tailWord_8087967, baseEnd_8087967] using wordTrace_append hprefix tailTrace_8087967
  have hstable : (prefixWord ++ tailWord_8087967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087967).length < 2 ^ (prefixWord ++ tailWord_8087967).sum := by decide
  have hdescent : baseEnd_8087967 < baseStart_8087967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087970 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_8087970 : Nat := 118140960795 + 8087970 * 2 ^ 59
def prefixEnd_8087970 : Nat := 4983230072969 + 3 ^ 40 * 8087970 * 2
def baseEnd_8087970 : Nat := 4153016129144826013879109

theorem tailTrace_8087970 : CollatzResearch.WordTrace tailWord_8087970 prefixEnd_8087970 4153016129144826013879109 := by
  unfold tailWord_8087970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73748125127168370037245341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196661667005782320099320909 73748125127168370037245341)
  ·
    refine ⟨27655546922688138763967003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73748125127168370037245341 27655546922688138763967003)
    ·
      refine ⟨41483320384032208145950505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655546922688138763967003 41483320384032208145950505)
      ·
        refine ⟨31112490288024156109462879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41483320384032208145950505 31112490288024156109462879)
        ·
          refine ⟨46668735432036234164194319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31112490288024156109462879 46668735432036234164194319)
          ·
            refine ⟨70003103148054351246291479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46668735432036234164194319 70003103148054351246291479)
            ·
              refine ⟨105004654722081526869437219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70003103148054351246291479 105004654722081526869437219)
              ·
                refine ⟨157506982083122290304155829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105004654722081526869437219 157506982083122290304155829)
                ·
                  refine ⟨14766279570292714716014609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157506982083122290304155829 14766279570292714716014609)
                  ·
                    refine ⟨11074709677719536037010957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14766279570292714716014609 11074709677719536037010957)
                    ·
                      refine ⟨4153016129144826013879109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074709677719536037010957 4153016129144826013879109)
                      ·
                        rfl

theorem cell23_8087970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_8087970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087970 prefixEnd_8087970 := by exact prefixLift 8087970
  have htrace : WordTrace (prefixWord ++ tailWord_8087970) baseStart_8087970 baseEnd_8087970 := by
    simpa [prefixWord, tailWord_8087970, baseEnd_8087970] using wordTrace_append hprefix tailTrace_8087970
  have hstable : (prefixWord ++ tailWord_8087970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087970).length < 2 ^ (prefixWord ++ tailWord_8087970).sum := by decide
  have hdescent : baseEnd_8087970 < baseStart_8087970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087988 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_8087988 : Nat := 118140960795 + 8087988 * 2 ^ 59
def prefixEnd_8087988 : Nat := 4983230072969 + 3 ^ 40 * 8087988 * 2
def baseEnd_8087988 : Nat := 4153025371796606943454027

theorem tailTrace_8087988 : CollatzResearch.WordTrace tailWord_8087988 prefixEnd_8087988 4153025371796606943454027 := by
  unfold tailWord_8087988
  simp only [CollatzResearch.WordTrace]
  refine ⟨147496578511304134611568309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196662104681738846148757745 147496578511304134611568309)
  ·
    refine ⟨13827804235434762619834529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147496578511304134611568309 13827804235434762619834529)
    ·
      refine ⟨10370853176576071964875897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827804235434762619834529 10370853176576071964875897)
      ·
        refine ⟨7778139882432053973656923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10370853176576071964875897 7778139882432053973656923)
        ·
          refine ⟨11667209823648080960485385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778139882432053973656923 11667209823648080960485385)
          ·
            refine ⟨8750407367736060720364039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11667209823648080960485385 8750407367736060720364039)
            ·
              refine ⟨13125611051604091080546059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750407367736060720364039 13125611051604091080546059)
              ·
                refine ⟨19688416577406136620819089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13125611051604091080546059 19688416577406136620819089)
                ·
                  refine ⟨14766312433054602465614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19688416577406136620819089 14766312433054602465614317)
                  ·
                    refine ⟨5537367162395475924605369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14766312433054602465614317 5537367162395475924605369)
                    ·
                      refine ⟨4153025371796606943454027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537367162395475924605369 4153025371796606943454027)
                      ·
                        rfl

theorem cell23_8087988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_8087988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8087988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8087988 prefixEnd_8087988 := by exact prefixLift 8087988
  have htrace : WordTrace (prefixWord ++ tailWord_8087988) baseStart_8087988 baseEnd_8087988 := by
    simpa [prefixWord, tailWord_8087988, baseEnd_8087988] using wordTrace_append hprefix tailTrace_8087988
  have hstable : (prefixWord ++ tailWord_8087988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087988).length < 2 ^ (prefixWord ++ tailWord_8087988).sum := by decide
  have hdescent : baseEnd_8087988 < baseStart_8087988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088000 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3]
def baseStart_8088000 : Nat := 118140960795 + 8088000 * 2 ^ 59
def prefixEnd_8088000 : Nat := 4983230072969 + 3 ^ 40 * 8088000 * 2
def baseEnd_8088000 : Nat := 4153031533564460896503971

theorem tailTrace_8088000 : CollatzResearch.WordTrace tailWord_8088000 prefixEnd_8088000 4153031533564460896503971 := by
  unfold tailWord_8088000
  simp only [CollatzResearch.WordTrace]
  refine ⟨147496797349282397636286727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196662396465709863515048969 147496797349282397636286727)
  ·
    refine ⟨221245196023923596454430091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147496797349282397636286727 221245196023923596454430091)
    ·
      refine ⟨331867794035885394681645137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221245196023923596454430091 331867794035885394681645137)
      ·
        refine ⟨248900845526914046011233853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331867794035885394681645137 248900845526914046011233853)
        ·
          refine ⟨93337817072592767254212695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248900845526914046011233853 93337817072592767254212695)
          ·
            refine ⟨140006725608889150881319043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93337817072592767254212695 140006725608889150881319043)
            ·
              refine ⟨210010088413333726321978565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140006725608889150881319043 210010088413333726321978565)
              ·
                refine ⟨39376891577500073685370981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210010088413333726321978565 39376891577500073685370981)
                ·
                  refine ⟨7383167170781263816007059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39376891577500073685370981 7383167170781263816007059)
                  ·
                    refine ⟨11074750756171895724010589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7383167170781263816007059 11074750756171895724010589)
                    ·
                      refine ⟨4153031533564460896503971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074750756171895724010589 4153031533564460896503971)
                      ·
                        rfl

theorem cell23_8088000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_8088000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088000 prefixEnd_8088000 := by exact prefixLift 8088000
  have htrace : WordTrace (prefixWord ++ tailWord_8088000) baseStart_8088000 baseEnd_8088000 := by
    simpa [prefixWord, tailWord_8088000, baseEnd_8088000] using wordTrace_append hprefix tailTrace_8088000
  have hstable : (prefixWord ++ tailWord_8088000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088000).length < 2 ^ (prefixWord ++ tailWord_8088000).sum := by decide
  have hdescent : baseEnd_8088000 < baseStart_8088000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088001 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_8088001 : Nat := 118140960795 + 8088001 * 2 ^ 59
def prefixEnd_8088001 : Nat := 4983230072969 + 3 ^ 40 * 8088001 * 2
def baseEnd_8088001 : Nat := 4153032047045115392591467

theorem tailTrace_8088001 : CollatzResearch.WordTrace tailWord_8088001 prefixEnd_8088001 4153032047045115392591467 := by
  unfold tailWord_8088001
  simp only [CollatzResearch.WordTrace]
  refine ⟨294993631171561172443359857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196662420781040781628906571 294993631171561172443359857)
  ·
    refine ⟨221245223378670879332519893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294993631171561172443359857 221245223378670879332519893)
    ·
      refine ⟨5185434922937598734355935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 221245223378670879332519893 5185434922937598734355935)
      ·
        refine ⟨7778152384406398101533903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185434922937598734355935 7778152384406398101533903)
        ·
          refine ⟨11667228576609597152300855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778152384406398101533903 11667228576609597152300855)
          ·
            refine ⟨17500842864914395728451283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667228576609597152300855 17500842864914395728451283)
            ·
              refine ⟨26251264297371593592676925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500842864914395728451283 26251264297371593592676925)
              ·
                refine ⟨9844224111514347597253847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26251264297371593592676925 9844224111514347597253847)
                ·
                  refine ⟨14766336167271521395880771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9844224111514347597253847 14766336167271521395880771)
                  ·
                    refine ⟨22149504250907282093821157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14766336167271521395880771 22149504250907282093821157)
                    ·
                      refine ⟨4153032047045115392591467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22149504250907282093821157 4153032047045115392591467)
                      ·
                        rfl

theorem cell23_8088001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_8088001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088001 prefixEnd_8088001 := by exact prefixLift 8088001
  have htrace : WordTrace (prefixWord ++ tailWord_8088001) baseStart_8088001 baseEnd_8088001 := by
    simpa [prefixWord, tailWord_8088001, baseEnd_8088001] using wordTrace_append hprefix tailTrace_8088001
  have hstable : (prefixWord ++ tailWord_8088001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088001).length < 2 ^ (prefixWord ++ tailWord_8088001).sum := by decide
  have hdescent : baseEnd_8088001 < baseStart_8088001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088004 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_8088004 : Nat := 118140960795 + 8088004 * 2 ^ 59
def prefixEnd_8088004 : Nat := 4983230072969 + 3 ^ 40 * 8088004 * 2
def baseEnd_8088004 : Nat := 4153033587487078880853953

theorem tailTrace_8088004 : CollatzResearch.WordTrace tailWord_8088004 prefixEnd_8088004 4153033587487078880853953 := by
  unfold tailWord_8088004
  simp only [CollatzResearch.WordTrace]
  refine ⟨147496870295275151977859533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196662493727033535970479377 147496870295275151977859533)
  ·
    refine ⟨55311326360728181991697325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147496870295275151977859533 55311326360728181991697325)
    ·
      refine ⟨20741747385273068246886497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55311326360728181991697325 20741747385273068246886497)
      ·
        refine ⟨15556310538954801185164873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20741747385273068246886497 15556310538954801185164873)
        ·
          refine ⟨11667232904216100888873655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15556310538954801185164873 11667232904216100888873655)
          ·
            refine ⟨17500849356324151333310483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667232904216100888873655 17500849356324151333310483)
            ·
              refine ⟨26251274034486226999965725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500849356324151333310483 26251274034486226999965725)
              ·
                refine ⟨9844227762932335124987147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26251274034486226999965725 9844227762932335124987147)
                ·
                  refine ⟨14766341644398502687480721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9844227762932335124987147 14766341644398502687480721)
                  ·
                    refine ⟨11074756233298877015610541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14766341644398502687480721 11074756233298877015610541)
                    ·
                      refine ⟨4153033587487078880853953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074756233298877015610541 4153033587487078880853953)
                      ·
                        rfl

theorem cell23_8088004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_8088004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088004 prefixEnd_8088004 := by exact prefixLift 8088004
  have htrace : WordTrace (prefixWord ++ tailWord_8088004) baseStart_8088004 baseEnd_8088004 := by
    simpa [prefixWord, tailWord_8088004, baseEnd_8088004] using wordTrace_append hprefix tailTrace_8088004
  have hstable : (prefixWord ++ tailWord_8088004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088004).length < 2 ^ (prefixWord ++ tailWord_8088004).sum := by decide
  have hdescent : baseEnd_8088004 < baseStart_8088004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088033 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_8088033 : Nat := 118140960795 + 8088033 * 2 ^ 59
def prefixEnd_8088033 : Nat := 4983230072969 + 3 ^ 40 * 8088033 * 2
def baseEnd_8088033 : Nat := 1384349492808686422463773

theorem tailTrace_8088033 : CollatzResearch.WordTrace tailWord_8088033 prefixEnd_8088033 1384349492808686422463773 := by
  unfold tailWord_8088033
  simp only [CollatzResearch.WordTrace]
  refine ⟨294994798307445241908524753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196663198871630161272349835 294994798307445241908524753)
  ·
    refine ⟨221246098730583931431393565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294994798307445241908524753 221246098730583931431393565)
    ·
      refine ⟨82967287023968974286772587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221246098730583931431393565 82967287023968974286772587)
      ·
        refine ⟨124450930535953461430158881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82967287023968974286772587 124450930535953461430158881)
        ·
          refine ⟨93338197901965096072619161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124450930535953461430158881 93338197901965096072619161)
          ·
            refine ⟨70003648426473822054464371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93338197901965096072619161 70003648426473822054464371)
            ·
              refine ⟨105005472639710733081696557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70003648426473822054464371 105005472639710733081696557)
              ·
                refine ⟨39377052239891524905636209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105005472639710733081696557 39377052239891524905636209)
                ·
                  refine ⟨29532789179918643679227157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39377052239891524905636209 29532789179918643679227157)
                  ·
                    refine ⟨1384349492808686422463773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29532789179918643679227157 1384349492808686422463773)
                    ·
                      rfl

theorem cell23_8088033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_8088033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088033 prefixEnd_8088033 := by exact prefixLift 8088033
  have htrace : WordTrace (prefixWord ++ tailWord_8088033) baseStart_8088033 baseEnd_8088033 := by
    simpa [prefixWord, tailWord_8088033, baseEnd_8088033] using wordTrace_append hprefix tailTrace_8088033
  have hstable : (prefixWord ++ tailWord_8088033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088033).length < 2 ^ (prefixWord ++ tailWord_8088033).sum := by decide
  have hdescent : baseEnd_8088033 < baseStart_8088033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088043 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_8088043 : Nat := 118140960795 + 8088043 * 2 ^ 59
def prefixEnd_8088043 : Nat := 4983230072969 + 3 ^ 40 * 8088043 * 2
def baseEnd_8088043 : Nat := 4153053613232604228266273

theorem tailTrace_8088043 : CollatzResearch.WordTrace tailWord_8088043 prefixEnd_8088043 4153053613232604228266273 := by
  unfold tailWord_8088043
  simp only [CollatzResearch.WordTrace]
  refine ⟨294995163037409013616388783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196663442024939342410925855 294995163037409013616388783)
  ·
    refine ⟨442492744556113520424583175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294995163037409013616388783 442492744556113520424583175)
    ·
      refine ⟨663739116834170280636874763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442492744556113520424583175 663739116834170280636874763)
      ·
        refine ⟨995608675251255420955312145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663739116834170280636874763 995608675251255420955312145)
        ·
          refine ⟨746706506438441565716484109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995608675251255420955312145 746706506438441565716484109)
          ·
            refine ⟨280014939914415587143681541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746706506438441565716484109 280014939914415587143681541)
            ·
              refine ⟨52502801233952922589440289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280014939914415587143681541 52502801233952922589440289)
              ·
                refine ⟨39377100925464691942080217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52502801233952922589440289 39377100925464691942080217)
                ·
                  refine ⟨29532825694098518956560163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39377100925464691942080217 29532825694098518956560163)
                  ·
                    refine ⟨44299238541147778434840245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29532825694098518956560163 44299238541147778434840245)
                    ·
                      refine ⟨4153053613232604228266273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44299238541147778434840245 4153053613232604228266273)
                      ·
                        rfl

theorem cell23_8088043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_8088043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088043 prefixEnd_8088043 := by exact prefixLift 8088043
  have htrace : WordTrace (prefixWord ++ tailWord_8088043) baseStart_8088043 baseEnd_8088043 := by
    simpa [prefixWord, tailWord_8088043, baseEnd_8088043] using wordTrace_append hprefix tailTrace_8088043
  have hstable : (prefixWord ++ tailWord_8088043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088043).length < 2 ^ (prefixWord ++ tailWord_8088043).sum := by decide
  have hdescent : baseEnd_8088043 < baseStart_8088043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088057 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 4, 2, 2]
def baseStart_8088057 : Nat := 118140960795 + 8088057 * 2 ^ 59
def prefixEnd_8088057 : Nat := 4983230072969 + 3 ^ 40 * 8088057 * 2
def baseEnd_8088057 : Nat := 4153060801961767173491209

theorem tailTrace_8088057 : CollatzResearch.WordTrace tailWord_8088057 prefixEnd_8088057 4153060801961767173491209 := by
  unfold tailWord_8088057
  simp only [CollatzResearch.WordTrace]
  refine ⟨294995673659358294007398425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196663782439572196004932283 294995673659358294007398425)
  ·
    refine ⟨221246755244518720505548819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294995673659358294007398425 221246755244518720505548819)
    ·
      refine ⟨331870132866778080758323229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221246755244518720505548819 331870132866778080758323229)
      ·
        refine ⟨124451299825041780284371211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331870132866778080758323229 124451299825041780284371211)
        ·
          refine ⟨186676949737562670426556817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124451299825041780284371211 186676949737562670426556817)
          ·
            refine ⟨140007712303172002819917613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186676949737562670426556817 140007712303172002819917613)
            ·
              refine ⟨52502892113689501057469105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140007712303172002819917613 52502892113689501057469105)
              ·
                refine ⟨39377169085267125793101829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52502892113689501057469105 39377169085267125793101829)
                ·
                  refine ⟨7383219203487586086206593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39377169085267125793101829 7383219203487586086206593)
                  ·
                    refine ⟨5537414402615689564654945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7383219203487586086206593 5537414402615689564654945)
                    ·
                      refine ⟨4153060801961767173491209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537414402615689564654945 4153060801961767173491209)
                      ·
                        rfl

theorem cell23_8088057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_8088057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088057 prefixEnd_8088057 := by exact prefixLift 8088057
  have htrace : WordTrace (prefixWord ++ tailWord_8088057) baseStart_8088057 baseEnd_8088057 := by
    simpa [prefixWord, tailWord_8088057, baseEnd_8088057] using wordTrace_append hprefix tailTrace_8088057
  have hstable : (prefixWord ++ tailWord_8088057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088057).length < 2 ^ (prefixWord ++ tailWord_8088057).sum := by decide
  have hdescent : baseEnd_8088057 < baseStart_8088057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088074 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_8088074 : Nat := 118140960795 + 8088074 * 2 ^ 59
def prefixEnd_8088074 : Nat := 4983230072969 + 3 ^ 40 * 8088074 * 2
def baseEnd_8088074 : Nat := 4153069531132893606978631

theorem tailTrace_8088074 : CollatzResearch.WordTrace tailWord_8088074 prefixEnd_8088074 4153069531132893606978631 := by
  unfold tailWord_8088074
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749073425074176477691819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196664195800197803940511517 73749073425074176477691819)
  ·
    refine ⟨110623610137611264716537729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73749073425074176477691819 110623610137611264716537729)
    ·
      refine ⟨82967707603208448537403297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110623610137611264716537729 82967707603208448537403297)
      ·
        refine ⟨62225780702406336403052473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82967707603208448537403297 62225780702406336403052473)
        ·
          refine ⟨46669335526804752302289355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62225780702406336403052473 46669335526804752302289355)
          ·
            refine ⟨70004003290207128453434033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46669335526804752302289355 70004003290207128453434033)
            ·
              refine ⟨52503002467655346340075525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70004003290207128453434033 52503002467655346340075525)
              ·
                refine ⟨9844312962685377438764161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52503002467655346340075525 9844312962685377438764161)
                ·
                  refine ⟨7383234722014033079073121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9844312962685377438764161 7383234722014033079073121)
                  ·
                    refine ⟨5537426041510524809304841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7383234722014033079073121 5537426041510524809304841)
                    ·
                      refine ⟨4153069531132893606978631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537426041510524809304841 4153069531132893606978631)
                      ·
                        rfl

theorem cell23_8088074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_8088074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088074 prefixEnd_8088074 := by exact prefixLift 8088074
  have htrace : WordTrace (prefixWord ++ tailWord_8088074) baseStart_8088074 baseEnd_8088074 := by
    simpa [prefixWord, tailWord_8088074, baseEnd_8088074] using wordTrace_append hprefix tailTrace_8088074
  have hstable : (prefixWord ++ tailWord_8088074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088074).length < 2 ^ (prefixWord ++ tailWord_8088074).sum := by decide
  have hdescent : baseEnd_8088074 < baseStart_8088074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088090 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_8088090 : Nat := 118140960795 + 8088090 * 2 ^ 59
def prefixEnd_8088090 : Nat := 4983230072969 + 3 ^ 40 * 8088090 * 2
def baseEnd_8088090 : Nat := 4153077746823365544378557

theorem tailTrace_8088090 : CollatzResearch.WordTrace tailWord_8088090 prefixEnd_8088090 4153077746823365544378557 := by
  unfold tailWord_8088090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749219317059685160837431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196664584845492493762233149 73749219317059685160837431)
  ·
    refine ⟨110623828975589527741256147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73749219317059685160837431 110623828975589527741256147)
    ·
      refine ⟨165935743463384291611884221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110623828975589527741256147 165935743463384291611884221)
      ·
        refine ⟨62225903798769109354456583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165935743463384291611884221 62225903798769109354456583)
        ·
          refine ⟨93338855698153664031684875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62225903798769109354456583 93338855698153664031684875)
          ·
            refine ⟨140008283547230496047527313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93338855698153664031684875 140008283547230496047527313)
            ·
              refine ⟨105006212660422872035645485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140008283547230496047527313 105006212660422872035645485)
              ·
                refine ⟨39377329747658577013367057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105006212660422872035645485 39377329747658577013367057)
                ·
                  refine ⟨29532997310743932760025293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39377329747658577013367057 29532997310743932760025293)
                  ·
                    refine ⟨11074873991528974785009485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29532997310743932760025293 11074873991528974785009485)
                    ·
                      refine ⟨4153077746823365544378557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11074873991528974785009485 4153077746823365544378557)
                      ·
                        rfl

theorem cell23_8088090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_8088090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088090 prefixEnd_8088090 := by exact prefixLift 8088090
  have htrace : WordTrace (prefixWord ++ tailWord_8088090) baseStart_8088090 baseEnd_8088090 := by
    simpa [prefixWord, tailWord_8088090, baseEnd_8088090] using wordTrace_append hprefix tailTrace_8088090
  have hstable : (prefixWord ++ tailWord_8088090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088090).length < 2 ^ (prefixWord ++ tailWord_8088090).sum := by decide
  have hdescent : baseEnd_8088090 < baseStart_8088090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088153 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 12]
def baseStart_8088153 : Nat := 118140960795 + 8088153 * 2 ^ 59
def prefixEnd_8088153 : Nat := 4983230072969 + 3 ^ 40 * 8088153 * 2
def baseEnd_8088153 : Nat := 461456677344955421987863

theorem tailTrace_8088153 : CollatzResearch.WordTrace tailWord_8088153 prefixEnd_8088153 461456677344955421987863 := by
  unfold tailWord_8088153
  simp only [CollatzResearch.WordTrace]
  refine ⟨294999175067010502402893113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196666116711340334935262075 294999175067010502402893113)
  ·
    refine ⟨221249381300257876802169835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294999175067010502402893113 221249381300257876802169835)
    ·
      refine ⟨331874071950386815203254753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221249381300257876802169835 331874071950386815203254753)
      ·
        refine ⟨248905553962790111402441065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331874071950386815203254753 248905553962790111402441065)
        ·
          refine ⟨186679165472092583551830799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248905553962790111402441065 186679165472092583551830799)
          ·
            refine ⟨280018748208138875327746199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186679165472092583551830799 280018748208138875327746199)
            ·
              refine ⟨420028122312208312991619299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280018748208138875327746199 420028122312208312991619299)
              ·
                refine ⟨630042183468312469487428949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420028122312208312991619299 630042183468312469487428949)
                ·
                  refine ⟨461456677344955421987863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 630042183468312469487428949 461456677344955421987863)
                  ·
                    rfl

theorem cell23_8088153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_8088153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088153 prefixEnd_8088153 := by exact prefixLift 8088153
  have htrace : WordTrace (prefixWord ++ tailWord_8088153) baseStart_8088153 baseEnd_8088153 := by
    simpa [prefixWord, tailWord_8088153, baseEnd_8088153] using wordTrace_append hprefix tailTrace_8088153
  have hstable : (prefixWord ++ tailWord_8088153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088153).length < 2 ^ (prefixWord ++ tailWord_8088153).sum := by decide
  have hdescent : baseEnd_8088153 < baseStart_8088153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088170 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_8088170 : Nat := 118140960795 + 8088170 * 2 ^ 59
def prefixEnd_8088170 : Nat := 4983230072969 + 3 ^ 40 * 8088170 * 2
def baseEnd_8088170 : Nat := 461457647252858359042021

theorem tailTrace_8088170 : CollatzResearch.WordTrace tailWord_8088170 prefixEnd_8088170 461457647252858359042021 := by
  unfold tailWord_8088170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749948776987228576565491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196666530071965942870841309 73749948776987228576565491)
  ·
    refine ⟨110624923165480842864848237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73749948776987228576565491 110624923165480842864848237)
    ·
      refine ⟨41484346187055316074318089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110624923165480842864848237 41484346187055316074318089)
      ·
        refine ⟨31113259640291487055738567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41484346187055316074318089 31113259640291487055738567)
        ·
          refine ⟨46669889460437230583607851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31113259640291487055738567 46669889460437230583607851)
          ·
            refine ⟨70004834190655845875411777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46669889460437230583607851 70004834190655845875411777)
            ·
              refine ⟨52503625642991884406558833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70004834190655845875411777 52503625642991884406558833)
              ·
                refine ⟨39377719232243913304919125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52503625642991884406558833 39377719232243913304919125)
                ·
                  refine ⟨461457647252858359042021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39377719232243913304919125 461457647252858359042021)
                  ·
                    rfl

theorem cell23_8088170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_8088170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088170 prefixEnd_8088170 := by exact prefixLift 8088170
  have htrace : WordTrace (prefixWord ++ tailWord_8088170) baseStart_8088170 baseEnd_8088170 := by
    simpa [prefixWord, tailWord_8088170, baseEnd_8088170] using wordTrace_append hprefix tailTrace_8088170
  have hstable : (prefixWord ++ tailWord_8088170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088170).length < 2 ^ (prefixWord ++ tailWord_8088170).sum := by decide
  have hdescent : baseEnd_8088170 < baseStart_8088170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 4, 3, 2]
def baseStart_8088207 : Nat := 118140960795 + 8088207 * 2 ^ 59
def prefixEnd_8088207 : Nat := 4983230072969 + 3 ^ 40 * 8088207 * 2
def baseEnd_8088207 : Nat := 4153137824059941586615519

theorem tailTrace_8088207 : CollatzResearch.WordTrace tailWord_8088207 prefixEnd_8088207 4153137824059941586615519 := by
  unfold tailWord_8088207
  simp only [CollatzResearch.WordTrace]
  refine ⟨295001144608814869625358875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196667429739209913083572583 295001144608814869625358875)
  ·
    refine ⟨442501716913222304438038313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295001144608814869625358875 442501716913222304438038313)
    ·
      refine ⟨331876287684916728328528735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442501716913222304438038313 331876287684916728328528735)
      ·
        refine ⟨497814431527375092492793103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331876287684916728328528735 497814431527375092492793103)
        ·
          refine ⟨746721647291062638739189655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497814431527375092492793103 746721647291062638739189655)
          ·
            refine ⟨1120082470936593958108784483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746721647291062638739189655 1120082470936593958108784483)
            ·
              refine ⟨1680123706404890937163176725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120082470936593958108784483 1680123706404890937163176725)
              ·
                refine ⟨78755798737729262679523909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1680123706404890937163176725 78755798737729262679523909)
                ·
                  refine ⟨14766712263324236752410733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78755798737729262679523909 14766712263324236752410733)
                  ·
                    refine ⟨5537517098746588782154025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14766712263324236752410733 5537517098746588782154025)
                    ·
                      refine ⟨4153137824059941586615519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537517098746588782154025 4153137824059941586615519)
                      ·
                        rfl

theorem cell23_8088207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3, 2].length) (baseStart_8088207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088207 prefixEnd_8088207 := by exact prefixLift 8088207
  have htrace : WordTrace (prefixWord ++ tailWord_8088207) baseStart_8088207 baseEnd_8088207 := by
    simpa [prefixWord, tailWord_8088207, baseEnd_8088207] using wordTrace_append hprefix tailTrace_8088207
  have hstable : (prefixWord ++ tailWord_8088207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088207).length < 2 ^ (prefixWord ++ tailWord_8088207).sum := by decide
  have hdescent : baseEnd_8088207 < baseStart_8088207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088217 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_8088217 : Nat := 118140960795 + 8088217 * 2 ^ 59
def prefixEnd_8088217 : Nat := 4983230072969 + 3 ^ 40 * 8088217 * 2
def baseEnd_8088217 : Nat := 1384380986288828849163491

theorem tailTrace_8088217 : CollatzResearch.WordTrace tailWord_8088217 prefixEnd_8088217 1384380986288828849163491 := by
  unfold tailWord_8088217
  simp only [CollatzResearch.WordTrace]
  refine ⟨295001509338778641333222905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196667672892519094222148603 295001509338778641333222905)
  ·
    refine ⟨221251132004083980999917179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295001509338778641333222905 221251132004083980999917179)
    ·
      refine ⟨331876698006125971499875769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221251132004083980999917179 331876698006125971499875769)
      ·
        refine ⟨248907523504594478624906827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331876698006125971499875769 248907523504594478624906827)
        ·
          refine ⟨373361285256891717937360241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248907523504594478624906827 373361285256891717937360241)
          ·
            refine ⟨280020963942668788453020181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373361285256891717937360241 280020963942668788453020181)
            ·
              refine ⟨13125982684812599458735321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280020963942668788453020181 13125982684812599458735321)
              ·
                refine ⟨9844487013609449594051491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13125982684812599458735321 9844487013609449594051491)
                ·
                  refine ⟨14766730520414174391077237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9844487013609449594051491 14766730520414174391077237)
                  ·
                    refine ⟨1384380986288828849163491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14766730520414174391077237 1384380986288828849163491)
                    ·
                      rfl

theorem cell23_8088217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_8088217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088217 prefixEnd_8088217 := by exact prefixLift 8088217
  have htrace : WordTrace (prefixWord ++ tailWord_8088217) baseStart_8088217 baseEnd_8088217 := by
    simpa [prefixWord, tailWord_8088217, baseEnd_8088217] using wordTrace_append hprefix tailTrace_8088217
  have hstable : (prefixWord ++ tailWord_8088217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088217).length < 2 ^ (prefixWord ++ tailWord_8088217).sum := by decide
  have hdescent : baseEnd_8088217 < baseStart_8088217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088250 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_8088250 : Nat := 118140960795 + 8088250 * 2 ^ 59
def prefixEnd_8088250 : Nat := 4983230072969 + 3 ^ 40 * 8088250 * 2
def baseEnd_8088250 : Nat := 4153159903728084918377821

theorem tailTrace_8088250 : CollatzResearch.WordTrace tailWord_8088250 prefixEnd_8088250 4153159903728084918377821 := by
  unfold tailWord_8088250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73750678236914771992293551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196668475298439391979449469 73750678236914771992293551)
  ·
    refine ⟨110626017355372157988440327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73750678236914771992293551 110626017355372157988440327)
    ·
      refine ⟨165939026033058236982660491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110626017355372157988440327 165939026033058236982660491)
      ·
        refine ⟨248908539049587355473990737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165939026033058236982660491 248908539049587355473990737)
        ·
          refine ⟨186681404287190516605493053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248908539049587355473990737 186681404287190516605493053)
          ·
            refine ⟨70005526607696443727059895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186681404287190516605493053 70005526607696443727059895)
            ·
              refine ⟨105008289911544665590589843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70005526607696443727059895 105008289911544665590589843)
              ·
                refine ⟨157512434867316998385884765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105008289911544665590589843 157512434867316998385884765)
                ·
                  refine ⟨59067163075243874394706787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157512434867316998385884765 59067163075243874394706787)
                  ·
                    refine ⟨88600744612865811592060181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59067163075243874394706787 88600744612865811592060181)
                    ·
                      refine ⟨4153159903728084918377821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88600744612865811592060181 4153159903728084918377821)
                      ·
                        rfl

theorem cell23_8088250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_8088250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088250 prefixEnd_8088250 := by exact prefixLift 8088250
  have htrace : WordTrace (prefixWord ++ tailWord_8088250) baseStart_8088250 baseEnd_8088250 := by
    simpa [prefixWord, tailWord_8088250, baseEnd_8088250] using wordTrace_append hprefix tailTrace_8088250
  have hstable : (prefixWord ++ tailWord_8088250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088250).length < 2 ^ (prefixWord ++ tailWord_8088250).sum := by decide
  have hdescent : baseEnd_8088250 < baseStart_8088250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088264 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_8088264 : Nat := 118140960795 + 8088264 * 2 ^ 59
def prefixEnd_8088264 : Nat := 4983230072969 + 3 ^ 40 * 8088264 * 2
def baseEnd_8088264 : Nat := 1384389030819082621200919

theorem tailTrace_8088264 : CollatzResearch.WordTrace tailWord_8088264 prefixEnd_8088264 1384389030819082621200919 := by
  unfold tailWord_8088264
  simp only [CollatzResearch.WordTrace]
  refine ⟨147501611784804184180091923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196668815713072245573455897 147501611784804184180091923)
  ·
    refine ⟨221252417677206276270137885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147501611784804184180091923 221252417677206276270137885)
    ·
      refine ⟨82969656628952353601301707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221252417677206276270137885 82969656628952353601301707)
      ·
        refine ⟨124454484943428530401952561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82969656628952353601301707 124454484943428530401952561)
        ·
          refine ⟨93340863707571397801464421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124454484943428530401952561 93340863707571397801464421)
          ·
            refine ⟨17501411945169637087774579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93340863707571397801464421 17501411945169637087774579)
            ·
              refine ⟨26252117917754455631661869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17501411945169637087774579 26252117917754455631661869)
              ·
                refine ⟨9844544219157920861873201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26252117917754455631661869 9844544219157920861873201)
                ·
                  refine ⟨7383408164368440646404901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9844544219157920861873201 7383408164368440646404901)
                  ·
                    refine ⟨1384389030819082621200919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383408164368440646404901 1384389030819082621200919)
                    ·
                      rfl

theorem cell23_8088264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_8088264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088264 prefixEnd_8088264 := by exact prefixLift 8088264
  have htrace : WordTrace (prefixWord ++ tailWord_8088264) baseStart_8088264 baseEnd_8088264 := by
    simpa [prefixWord, tailWord_8088264, baseEnd_8088264] using wordTrace_append hprefix tailTrace_8088264
  have hstable : (prefixWord ++ tailWord_8088264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088264).length < 2 ^ (prefixWord ++ tailWord_8088264).sum := by decide
  have hdescent : baseEnd_8088264 < baseStart_8088264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088284 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_8088284 : Nat := 118140960795 + 8088284 * 2 ^ 59
def prefixEnd_8088284 : Nat := 4983230072969 + 3 ^ 40 * 8088284 * 2
def baseEnd_8088284 : Nat := 4153177362070337785352665

theorem tailTrace_8088284 : CollatzResearch.WordTrace tailWord_8088284 prefixEnd_8088284 4153177362070337785352665 := by
  unfold tailWord_8088284
  simp only [CollatzResearch.WordTrace]
  refine ⟨147501976514767955887955953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196669302019690607850607937 147501976514767955887955953)
  ·
    refine ⟨110626482386075966915966965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147501976514767955887955953 110626482386075966915966965)
    ·
      refine ⟨10371232723694621898371903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110626482386075966915966965 10371232723694621898371903)
      ·
        refine ⟨15556849085541932847557855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371232723694621898371903 15556849085541932847557855)
        ·
          refine ⟨23335273628312899271336783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556849085541932847557855 23335273628312899271336783)
          ·
            refine ⟨35002910442469348907005175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23335273628312899271336783 35002910442469348907005175)
            ·
              refine ⟨52504365663704023360507763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35002910442469348907005175 52504365663704023360507763)
              ·
                refine ⟨78756548495556035040761645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52504365663704023360507763 78756548495556035040761645)
                ·
                  refine ⟨29533705685833513140285617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78756548495556035040761645 29533705685833513140285617)
                  ·
                    refine ⟨22150279264375134855214213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29533705685833513140285617 22150279264375134855214213)
                    ·
                      refine ⟨4153177362070337785352665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22150279264375134855214213 4153177362070337785352665)
                      ·
                        rfl

theorem cell23_8088284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_8088284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088284 prefixEnd_8088284 := by exact prefixLift 8088284
  have htrace : WordTrace (prefixWord ++ tailWord_8088284) baseStart_8088284 baseEnd_8088284 := by
    simpa [prefixWord, tailWord_8088284, baseEnd_8088284] using wordTrace_append hprefix tailTrace_8088284
  have hstable : (prefixWord ++ tailWord_8088284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088284).length < 2 ^ (prefixWord ++ tailWord_8088284).sum := by decide
  have hdescent : baseEnd_8088284 < baseStart_8088284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088287 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_8088287 : Nat := 118140960795 + 8088287 * 2 ^ 59
def prefixEnd_8088287 : Nat := 4983230072969 + 3 ^ 40 * 8088287 * 2
def baseEnd_8088287 : Nat := 4153178902512301273615151

theorem tailTrace_8088287 : CollatzResearch.WordTrace tailWord_8088287 prefixEnd_8088287 4153178902512301273615151 := by
  unfold tailWord_8088287
  simp only [CollatzResearch.WordTrace]
  refine ⟨295004062448525043288271115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196669374965683362192180743 295004062448525043288271115)
  ·
    refine ⟨442506093672787564932406673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295004062448525043288271115 442506093672787564932406673)
    ·
      refine ⟨331879570254590673699305005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442506093672787564932406673 331879570254590673699305005)
      ·
        refine ⟨124454838845471502637239377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331879570254590673699305005 124454838845471502637239377)
        ·
          refine ⟨93341129134103626977929533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124454838845471502637239377 93341129134103626977929533)
          ·
            refine ⟨35002923425288860116723575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93341129134103626977929533 35002923425288860116723575)
            ·
              refine ⟨52504385137933290175085363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35002923425288860116723575 52504385137933290175085363)
              ·
                refine ⟨78756577706899935262628045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52504385137933290175085363 78756577706899935262628045)
                ·
                  refine ⟨29533716640087475723485517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78756577706899935262628045 29533716640087475723485517)
                  ·
                    refine ⟨11075143740032803396307069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29533716640087475723485517 11075143740032803396307069)
                    ·
                      refine ⟨4153178902512301273615151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11075143740032803396307069 4153178902512301273615151)
                      ·
                        rfl

theorem cell23_8088287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_8088287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088287 prefixEnd_8088287 := by exact prefixLift 8088287
  have htrace : WordTrace (prefixWord ++ tailWord_8088287) baseStart_8088287 baseEnd_8088287 := by
    simpa [prefixWord, tailWord_8088287, baseEnd_8088287] using wordTrace_append hprefix tailTrace_8088287
  have hstable : (prefixWord ++ tailWord_8088287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088287).length < 2 ^ (prefixWord ++ tailWord_8088287).sum := by decide
  have hdescent : baseEnd_8088287 < baseStart_8088287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088314 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_8088314 : Nat := 118140960795 + 8088314 * 2 ^ 59
def prefixEnd_8088314 : Nat := 4983230072969 + 3 ^ 40 * 8088314 * 2
def baseEnd_8088314 : Nat := 4153192766489972667977527

theorem tailTrace_8088314 : CollatzResearch.WordTrace tailWord_8088314 prefixEnd_8088314 4153192766489972667977527 := by
  unfold tailWord_8088314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73751261804856806724875999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196670031479618151266335997 73751261804856806724875999)
  ·
    refine ⟨110626892707285210087313999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73751261804856806724875999 110626892707285210087313999)
    ·
      refine ⟨165940339060927815130970999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110626892707285210087313999 165940339060927815130970999)
      ·
        refine ⟨248910508591391722696456499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165940339060927815130970999 248910508591391722696456499)
        ·
          refine ⟨373365762887087584044684749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248910508591391722696456499 373365762887087584044684749)
          ·
            refine ⟨140012161082657844016756781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373365762887087584044684749 140012161082657844016756781)
            ·
              refine ⟨52504560405996691506283793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140012161082657844016756781 52504560405996691506283793)
              ·
                refine ⟨39378420304497518629712845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52504560405996691506283793 39378420304497518629712845)
                ·
                  refine ⟨14766907614186569486142317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39378420304497518629712845 14766907614186569486142317)
                  ·
                    refine ⟨5537590355319963557303369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14766907614186569486142317 5537590355319963557303369)
                    ·
                      refine ⟨4153192766489972667977527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537590355319963557303369 4153192766489972667977527)
                      ·
                        rfl

theorem cell23_8088314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_8088314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088314 prefixEnd_8088314 := by exact prefixLift 8088314
  have htrace : WordTrace (prefixWord ++ tailWord_8088314) baseStart_8088314 baseEnd_8088314 := by
    simpa [prefixWord, tailWord_8088314, baseEnd_8088314] using wordTrace_append hprefix tailTrace_8088314
  have hstable : (prefixWord ++ tailWord_8088314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088314).length < 2 ^ (prefixWord ++ tailWord_8088314).sum := by decide
  have hdescent : baseEnd_8088314 < baseStart_8088314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088348 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_8088348 : Nat := 118140960795 + 8088348 * 2 ^ 59
def prefixEnd_8088348 : Nat := 4983230072969 + 3 ^ 40 * 8088348 * 2
def baseEnd_8088348 : Nat := 4153210224832225534952371

theorem tailTrace_8088348 : CollatzResearch.WordTrace tailWord_8088348 prefixEnd_8088348 4153210224832225534952371 := by
  unfold tailWord_8088348
  simp only [CollatzResearch.WordTrace]
  refine ⟨147503143650652025353120849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196670858200869367137494465 147503143650652025353120849)
  ·
    refine ⟨110627357737989019014840637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147503143650652025353120849 110627357737989019014840637)
    ·
      refine ⟨41485259151745882130565239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110627357737989019014840637 41485259151745882130565239)
      ·
        refine ⟨62227888727618823195847859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41485259151745882130565239 62227888727618823195847859)
        ·
          refine ⟨93341833091428234793771789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62227888727618823195847859 93341833091428234793771789)
          ·
            refine ⟨35003187409285588047664421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93341833091428234793771789 35003187409285588047664421)
            ·
              refine ⟨6563097639241047758937079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35003187409285588047664421 6563097639241047758937079)
              ·
                refine ⟨9844646458861571638405619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563097639241047758937079 9844646458861571638405619)
                ·
                  refine ⟨14766969688292357457608429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9844646458861571638405619 14766969688292357457608429)
                  ·
                    refine ⟨5537613633109634046603161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14766969688292357457608429 5537613633109634046603161)
                    ·
                      refine ⟨4153210224832225534952371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537613633109634046603161 4153210224832225534952371)
                      ·
                        rfl

theorem cell23_8088348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_8088348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088348 prefixEnd_8088348 := by exact prefixLift 8088348
  have htrace : WordTrace (prefixWord ++ tailWord_8088348) baseStart_8088348 baseEnd_8088348 := by
    simpa [prefixWord, tailWord_8088348, baseEnd_8088348] using wordTrace_append hprefix tailTrace_8088348
  have hstable : (prefixWord ++ tailWord_8088348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088348).length < 2 ^ (prefixWord ++ tailWord_8088348).sum := by decide
  have hdescent : baseEnd_8088348 < baseStart_8088348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088357 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_8088357 : Nat := 118140960795 + 8088357 * 2 ^ 59
def prefixEnd_8088357 : Nat := 4983230072969 + 3 ^ 40 * 8088357 * 2
def baseEnd_8088357 : Nat := 4153214846158115999739829

theorem tailTrace_8088357 : CollatzResearch.WordTrace tailWord_8088357 prefixEnd_8088357 4153214846158115999739829 := by
  unfold tailWord_8088357
  simp only [CollatzResearch.WordTrace]
  refine ⟨295006615558271445243319325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196671077038847630162212883 295006615558271445243319325)
  ·
    refine ⟨110627480834351791966244747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295006615558271445243319325 110627480834351791966244747)
    ·
      refine ⟨165941221251527687949367121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110627480834351791966244747 165941221251527687949367121)
      ·
        refine ⟨124455915938645765962025341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165941221251527687949367121 124455915938645765962025341)
        ·
          refine ⟨46670968476992162235759503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124455915938645765962025341 46670968476992162235759503)
          ·
            refine ⟨70006452715488243353639255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46670968476992162235759503 70006452715488243353639255)
            ·
              refine ⟨105009679073232365030458883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70006452715488243353639255 105009679073232365030458883)
              ·
                refine ⟨157514518609848547545688325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105009679073232365030458883 157514518609848547545688325)
                ·
                  refine ⟨29533972239346602664816561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157514518609848547545688325 29533972239346602664816561)
                  ·
                    refine ⟨22150479179509951998612421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29533972239346602664816561 22150479179509951998612421)
                    ·
                      refine ⟨4153214846158115999739829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22150479179509951998612421 4153214846158115999739829)
                      ·
                        rfl

theorem cell23_8088357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_8088357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088357 prefixEnd_8088357 := by exact prefixLift 8088357
  have htrace : WordTrace (prefixWord ++ tailWord_8088357) baseStart_8088357 baseEnd_8088357 := by
    simpa [prefixWord, tailWord_8088357, baseEnd_8088357] using wordTrace_append hprefix tailTrace_8088357
  have hstable : (prefixWord ++ tailWord_8088357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088357).length < 2 ^ (prefixWord ++ tailWord_8088357).sum := by decide
  have hdescent : baseEnd_8088357 < baseStart_8088357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088378 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_8088378 : Nat := 118140960795 + 8088378 * 2 ^ 59
def prefixEnd_8088378 : Nat := 4983230072969 + 3 ^ 40 * 8088378 * 2
def baseEnd_8088378 : Nat := 4153225629251860417577233

theorem tailTrace_8088378 : CollatzResearch.WordTrace tailWord_8088378 prefixEnd_8088378 4153225629251860417577233 := by
  unfold tailWord_8088378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73751845372798841457458447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196671587660796910553222525 73751845372798841457458447)
  ·
    refine ⟨110627768059198262186187671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73751845372798841457458447 110627768059198262186187671)
    ·
      refine ⟨165941652088797393279281507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110627768059198262186187671 165941652088797393279281507)
      ·
        refine ⟨248912478133196089918922261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165941652088797393279281507 248912478133196089918922261)
        ·
          refine ⟨11667772412493566714949481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248912478133196089918922261 11667772412493566714949481)
          ·
            refine ⟨8750829309370175036212111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11667772412493566714949481 8750829309370175036212111)
            ·
              refine ⟨13126243964055262554318167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750829309370175036212111 13126243964055262554318167)
              ·
                refine ⟨19689365946082893831477251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13126243964055262554318167 19689365946082893831477251)
                ·
                  refine ⟨29534048919124340747215877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19689365946082893831477251 29534048919124340747215877)
                  ·
                    refine ⟨5537634172335813890102977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29534048919124340747215877 5537634172335813890102977)
                    ·
                      refine ⟨4153225629251860417577233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537634172335813890102977 4153225629251860417577233)
                      ·
                        rfl

theorem cell23_8088378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_8088378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088378 prefixEnd_8088378 := by exact prefixLift 8088378
  have htrace : WordTrace (prefixWord ++ tailWord_8088378) baseStart_8088378 baseEnd_8088378 := by
    simpa [prefixWord, tailWord_8088378, baseEnd_8088378] using wordTrace_append hprefix tailTrace_8088378
  have hstable : (prefixWord ++ tailWord_8088378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088378).length < 2 ^ (prefixWord ++ tailWord_8088378).sum := by decide
  have hdescent : baseEnd_8088378 < baseStart_8088378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088417 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_8088417 : Nat := 118140960795 + 8088417 * 2 ^ 59
def prefixEnd_8088417 : Nat := 4983230072969 + 3 ^ 40 * 8088417 * 2
def baseEnd_8088417 : Nat := 4153245654997385764989553

theorem tailTrace_8088417 : CollatzResearch.WordTrace tailWord_8088417 prefixEnd_8088417 4153245654997385764989553 := by
  unfold tailWord_8088417
  simp only [CollatzResearch.WordTrace]
  refine ⟨295008803938054075490503505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196672535958702716993669003 295008803938054075490503505)
  ·
    refine ⟨221256602953540556617877629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295008803938054075490503505 221256602953540556617877629)
    ·
      refine ⟨82971226107577708731704111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221256602953540556617877629 82971226107577708731704111)
      ·
        refine ⟨124456839161366563097556167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82971226107577708731704111 124456839161366563097556167)
        ·
          refine ⟨186685258742049844646334251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124456839161366563097556167 186685258742049844646334251)
          ·
            refine ⟨280027888113074766969501377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186685258742049844646334251 280027888113074766969501377)
            ·
              refine ⟨210020916084806075227126033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280027888113074766969501377 210020916084806075227126033)
              ·
                refine ⟨157515687063604556420344525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210020916084806075227126033 157515687063604556420344525)
                ·
                  refine ⟨59068382648851708657629197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157515687063604556420344525 59068382648851708657629197)
                  ·
                    refine ⟨22150643493319390746610949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59068382648851708657629197 22150643493319390746610949)
                    ·
                      refine ⟨4153245654997385764989553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22150643493319390746610949 4153245654997385764989553)
                      ·
                        rfl

theorem cell23_8088417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_8088417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088417 prefixEnd_8088417 := by exact prefixLift 8088417
  have htrace : WordTrace (prefixWord ++ tailWord_8088417) baseStart_8088417 baseEnd_8088417 := by
    simpa [prefixWord, tailWord_8088417, baseEnd_8088417] using wordTrace_append hprefix tailTrace_8088417
  have hstable : (prefixWord ++ tailWord_8088417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088417).length < 2 ^ (prefixWord ++ tailWord_8088417).sum := by decide
  have hdescent : baseEnd_8088417 < baseStart_8088417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088418 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_8088418 : Nat := 118140960795 + 8088418 * 2 ^ 59
def prefixEnd_8088418 : Nat := 4983230072969 + 3 ^ 40 * 8088418 * 2
def baseEnd_8088418 : Nat := 461471796497560029008561

theorem tailTrace_8088418 : CollatzResearch.WordTrace tailWord_8088418 prefixEnd_8088418 461471796497560029008561 := by
  unfold tailWord_8088418
  simp only [CollatzResearch.WordTrace]
  refine ⟨73752210102762613165322477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196672560274033635107526605 73752210102762613165322477)
  ·
    refine ⟨27657078788535979936995929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73752210102762613165322477 27657078788535979936995929)
    ·
      refine ⟨20742809091401984952746947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27657078788535979936995929 20742809091401984952746947)
      ·
        refine ⟨31114213637102977429120421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20742809091401984952746947 31114213637102977429120421)
        ·
          refine ⟨5833915056956808267960079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31114213637102977429120421 5833915056956808267960079)
          ·
            refine ⟨8750872585435212401940119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833915056956808267960079 8750872585435212401940119)
            ·
              refine ⟨13126308878152818602910179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750872585435212401940119 13126308878152818602910179)
              ·
                refine ⟨19689463317229227904365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13126308878152818602910179 19689463317229227904365269)
                ·
                  refine ⟨461471796497560029008561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19689463317229227904365269 461471796497560029008561)
                  ·
                    rfl

theorem cell23_8088418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_8088418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088418 prefixEnd_8088418 := by exact prefixLift 8088418
  have htrace : WordTrace (prefixWord ++ tailWord_8088418) baseStart_8088418 baseEnd_8088418 := by
    simpa [prefixWord, tailWord_8088418, baseEnd_8088418] using wordTrace_append hprefix tailTrace_8088418
  have hstable : (prefixWord ++ tailWord_8088418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088418).length < 2 ^ (prefixWord ++ tailWord_8088418).sum := by decide
  have hdescent : baseEnd_8088418 < baseStart_8088418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088424 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_8088424 : Nat := 118140960795 + 8088424 * 2 ^ 59
def prefixEnd_8088424 : Nat := 4983230072969 + 3 ^ 40 * 8088424 * 2
def baseEnd_8088424 : Nat := 4153249249361967237602021

theorem tailTrace_8088424 : CollatzResearch.WordTrace tailWord_8088424 prefixEnd_8088424 4153249249361967237602021 := by
  unfold tailWord_8088424
  simp only [CollatzResearch.WordTrace]
  refine ⟨147504529624514357843004163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196672706166019143790672217 147504529624514357843004163)
  ·
    refine ⟨221256794436771536764506245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147504529624514357843004163 221256794436771536764506245)
    ·
      refine ⟨41485648956894663143344921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221256794436771536764506245 41485648956894663143344921)
      ·
        refine ⟨31114236717670997357508691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41485648956894663143344921 31114236717670997357508691)
        ·
          refine ⟨46671355076506496036263037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31114236717670997357508691 46671355076506496036263037)
          ·
            refine ⟨17501758153689936013598639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46671355076506496036263037 17501758153689936013598639)
            ·
              refine ⟨26252637230534904020397959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17501758153689936013598639 26252637230534904020397959)
              ·
                refine ⟨39378955845802356030596939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26252637230534904020397959 39378955845802356030596939)
                ·
                  refine ⟨59068433768703534045895409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39378955845802356030596939 59068433768703534045895409)
                  ·
                    refine ⟨44301325326527650534421557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59068433768703534045895409 44301325326527650534421557)
                    ·
                      refine ⟨4153249249361967237602021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44301325326527650534421557 4153249249361967237602021)
                      ·
                        rfl

theorem cell23_8088424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_8088424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088424 prefixEnd_8088424 := by exact prefixLift 8088424
  have htrace : WordTrace (prefixWord ++ tailWord_8088424) baseStart_8088424 baseEnd_8088424 := by
    simpa [prefixWord, tailWord_8088424, baseEnd_8088424] using wordTrace_append hprefix tailTrace_8088424
  have hstable : (prefixWord ++ tailWord_8088424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088424).length < 2 ^ (prefixWord ++ tailWord_8088424).sum := by decide
  have hdescent : baseEnd_8088424 < baseStart_8088424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088444 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_8088444 : Nat := 118140960795 + 8088444 * 2 ^ 59
def prefixEnd_8088444 : Nat := 4983230072969 + 3 ^ 40 * 8088444 * 2
def baseEnd_8088444 : Nat := 1384419839658352386450643

theorem tailTrace_8088444 : CollatzResearch.WordTrace tailWord_8088444 prefixEnd_8088444 1384419839658352386450643 := by
  unfold tailWord_8088444
  simp only [CollatzResearch.WordTrace]
  refine ⟨147504894354478129550868193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196673192472637506067824257 147504894354478129550868193)
  ·
    refine ⟨110628670765858597163151145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147504894354478129550868193 110628670765858597163151145)
    ·
      refine ⟨82971503074393947872363359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110628670765858597163151145 82971503074393947872363359)
      ·
        refine ⟨124457254611590921808545039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82971503074393947872363359 124457254611590921808545039)
        ·
          refine ⟨186685881917386382712817559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124457254611590921808545039 186685881917386382712817559)
          ·
            refine ⟨280028822876079574069226339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186685881917386382712817559 280028822876079574069226339)
            ·
              refine ⟨420043234314119361103839509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280028822876079574069226339 420043234314119361103839509)
              ·
                refine ⟨19689526608474345051742477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420043234314119361103839509 19689526608474345051742477)
                ·
                  refine ⟨7383572478177879394403429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19689526608474345051742477 7383572478177879394403429)
                  ·
                    refine ⟨1384419839658352386450643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383572478177879394403429 1384419839658352386450643)
                    ·
                      rfl

theorem cell23_8088444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_8088444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088444 prefixEnd_8088444 := by exact prefixLift 8088444
  have htrace : WordTrace (prefixWord ++ tailWord_8088444) baseStart_8088444 baseEnd_8088444 := by
    simpa [prefixWord, tailWord_8088444, baseEnd_8088444] using wordTrace_append hprefix tailTrace_8088444
  have hstable : (prefixWord ++ tailWord_8088444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088444).length < 2 ^ (prefixWord ++ tailWord_8088444).sum := by decide
  have hdescent : baseEnd_8088444 < baseStart_8088444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088447 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_8088447 : Nat := 118140960795 + 8088447 * 2 ^ 59
def prefixEnd_8088447 : Nat := 4983230072969 + 3 ^ 40 * 8088447 * 2
def baseEnd_8088447 : Nat := 4153261059417020647614415

theorem tailTrace_8088447 : CollatzResearch.WordTrace tailWord_8088447 prefixEnd_8088447 4153261059417020647614415 := by
  unfold tailWord_8088447
  simp only [CollatzResearch.WordTrace]
  refine ⟨295009898127945390614095595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196673265418630260409397063 295009898127945390614095595)
  ·
    refine ⟨442514847191918085921143393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295009898127945390614095595 442514847191918085921143393)
    ·
      refine ⟨331886135393938564440857545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442514847191918085921143393 331886135393938564440857545)
      ·
        refine ⟨248914601545453923330643159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331886135393938564440857545 248914601545453923330643159)
        ·
          refine ⟨373371902318180884995964739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248914601545453923330643159 373371902318180884995964739)
          ·
            refine ⟨560057853477271327493947109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373371902318180884995964739 560057853477271327493947109)
            ·
              refine ⟨105010847526988373905115083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 560057853477271327493947109 105010847526988373905115083)
              ·
                refine ⟨157516271290482560857672625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105010847526988373905115083 157516271290482560857672625)
                ·
                  refine ⟨118137203467861920643254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157516271290482560857672625 118137203467861920643254469)
                  ·
                    refine ⟨22150725650224110120610213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118137203467861920643254469 22150725650224110120610213)
                    ·
                      refine ⟨4153261059417020647614415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22150725650224110120610213 4153261059417020647614415)
                      ·
                        rfl

theorem cell23_8088447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_8088447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088447 prefixEnd_8088447 := by exact prefixLift 8088447
  have htrace : WordTrace (prefixWord ++ tailWord_8088447) baseStart_8088447 baseEnd_8088447 := by
    simpa [prefixWord, tailWord_8088447, baseEnd_8088447] using wordTrace_append hprefix tailTrace_8088447
  have hstable : (prefixWord ++ tailWord_8088447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088447).length < 2 ^ (prefixWord ++ tailWord_8088447).sum := by decide
  have hdescent : baseEnd_8088447 < baseStart_8088447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088504 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_8088504 : Nat := 118140960795 + 8088504 * 2 ^ 59
def prefixEnd_8088504 : Nat := 4983230072969 + 3 ^ 40 * 8088504 * 2
def baseEnd_8088504 : Nat := 1384430109271442308200551

theorem tailTrace_8088504 : CollatzResearch.WordTrace tailWord_8088504 prefixEnd_8088504 1384430109271442308200551 := by
  unfold tailWord_8088504
  simp only [CollatzResearch.WordTrace]
  refine ⟨147505988544369444674460283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196674651392492592899280377 147505988544369444674460283)
  ·
    refine ⟨221258982816554167011690425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147505988544369444674460283 221258982816554167011690425)
    ·
      refine ⟨165944237112415625258767819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221258982816554167011690425 165944237112415625258767819)
      ·
        refine ⟨248916355668623437888151729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165944237112415625258767819 248916355668623437888151729)
        ·
          refine ⟨186687266751467578416113797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248916355668623437888151729 186687266751467578416113797)
          ·
            refine ⟨35003862515900170953021337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186687266751467578416113797 35003862515900170953021337)
            ·
              refine ⟨26252896886925128214766003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35003862515900170953021337 26252896886925128214766003)
              ·
                refine ⟨39379345330387692322149005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26252896886925128214766003 39379345330387692322149005)
                ·
                  refine ⟨14767254498895384620805877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39379345330387692322149005 14767254498895384620805877)
                  ·
                    refine ⟨1384430109271442308200551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14767254498895384620805877 1384430109271442308200551)
                    ·
                      rfl

theorem cell23_8088504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_8088504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088504 prefixEnd_8088504 := by exact prefixLift 8088504
  have htrace : WordTrace (prefixWord ++ tailWord_8088504) baseStart_8088504 baseEnd_8088504 := by
    simpa [prefixWord, tailWord_8088504, baseEnd_8088504] using wordTrace_append hprefix tailTrace_8088504
  have hstable : (prefixWord ++ tailWord_8088504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088504).length < 2 ^ (prefixWord ++ tailWord_8088504).sum := by decide
  have hdescent : baseEnd_8088504 < baseStart_8088504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088511 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 2, 3, 2]
def baseStart_8088511 : Nat := 118140960795 + 8088511 * 2 ^ 59
def prefixEnd_8088511 : Nat := 4983230072969 + 3 ^ 40 * 8088511 * 2
def baseEnd_8088511 : Nat := 4153293922178908397214121

theorem tailTrace_8088511 : CollatzResearch.WordTrace tailWord_8088511 prefixEnd_8088511 4153293922178908397214121 := by
  unfold tailWord_8088511
  simp only [CollatzResearch.WordTrace]
  refine ⟨295012232399713529544425387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196674821599809019696283591 295012232399713529544425387)
  ·
    refine ⟨442518348599570294316638081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295012232399713529544425387 442518348599570294316638081)
    ·
      refine ⟨331888761449677720737478561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442518348599570294316638081 331888761449677720737478561)
      ·
        refine ⟨248916571087258290553108921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331888761449677720737478561 248916571087258290553108921)
        ·
          refine ⟨186687428315443717914831691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248916571087258290553108921 186687428315443717914831691)
          ·
            refine ⟨280031142473165576872247537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186687428315443717914831691 280031142473165576872247537)
            ·
              refine ⟨210023356854874182654185653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280031142473165576872247537 210023356854874182654185653)
              ·
                refine ⟨19689689705144454623829905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210023356854874182654185653 19689689705144454623829905)
                ·
                  refine ⟨14767267278858340967872429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19689689705144454623829905 14767267278858340967872429)
                  ·
                    refine ⟨5537725229571877862952161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14767267278858340967872429 5537725229571877862952161)
                    ·
                      refine ⟨4153293922178908397214121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537725229571877862952161 4153293922178908397214121)
                      ·
                        rfl

theorem cell23_8088511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_8088511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088511 prefixEnd_8088511 := by exact prefixLift 8088511
  have htrace : WordTrace (prefixWord ++ tailWord_8088511) baseStart_8088511 baseEnd_8088511 := by
    simpa [prefixWord, tailWord_8088511, baseEnd_8088511] using wordTrace_append hprefix tailTrace_8088511
  have hstable : (prefixWord ++ tailWord_8088511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088511).length < 2 ^ (prefixWord ++ tailWord_8088511).sum := by decide
  have hdescent : baseEnd_8088511 < baseStart_8088511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088517 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_8088517 : Nat := 118140960795 + 8088517 * 2 ^ 59
def prefixEnd_8088517 : Nat := 4983230072969 + 3 ^ 40 * 8088517 * 2
def baseEnd_8088517 : Nat := 1384432334354278457913031

theorem tailTrace_8088517 : CollatzResearch.WordTrace tailWord_8088517 prefixEnd_8088517 1384432334354278457913031 := by
  unfold tailWord_8088517
  simp only [CollatzResearch.WordTrace]
  refine ⟨295012451237691792569143805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196674967491794528379429203 295012451237691792569143805)
  ·
    refine ⟨110629669214134422213428927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295012451237691792569143805 110629669214134422213428927)
    ·
      refine ⟨165944503821201633320143391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110629669214134422213428927 165944503821201633320143391)
      ·
        refine ⟨248916755731802449980215087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165944503821201633320143391 248916755731802449980215087)
        ·
          refine ⟨373375133597703674970322631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248916755731802449980215087 373375133597703674970322631)
          ·
            refine ⟨560062700396555512455483947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373375133597703674970322631 560062700396555512455483947)
            ·
              refine ⟨840094050594833268683225921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560062700396555512455483947 840094050594833268683225921)
              ·
                refine ⟨630070537946124951512419441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840094050594833268683225921 630070537946124951512419441)
                ·
                  refine ⟨472552903459593713634314581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630070537946124951512419441 472552903459593713634314581)
                  ·
                    refine ⟨1384432334354278457913031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 472552903459593713634314581 1384432334354278457913031)
                    ·
                      rfl

theorem cell23_8088517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_8088517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088517 prefixEnd_8088517 := by exact prefixLift 8088517
  have htrace : WordTrace (prefixWord ++ tailWord_8088517) baseStart_8088517 baseEnd_8088517 := by
    simpa [prefixWord, tailWord_8088517, baseEnd_8088517] using wordTrace_append hprefix tailTrace_8088517
  have hstable : (prefixWord ++ tailWord_8088517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088517).length < 2 ^ (prefixWord ++ tailWord_8088517).sum := by decide
  have hdescent : baseEnd_8088517 < baseStart_8088517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088525 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 8]
def baseStart_8088525 : Nat := 118140960795 + 8088525 * 2 ^ 59
def prefixEnd_8088525 : Nat := 4983230072969 + 3 ^ 40 * 8088525 * 2
def baseEnd_8088525 : Nat := 461477901212007926937673

theorem tailTrace_8088525 : CollatzResearch.WordTrace tailWord_8088525 prefixEnd_8088525 461477901212007926937673 := by
  unfold tailWord_8088525
  simp only [CollatzResearch.WordTrace]
  refine ⟨295012743021662809935435029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196675162014441873290290019 295012743021662809935435029)
  ·
    refine ⟨13828722329140444215723517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 295012743021662809935435029 13828722329140444215723517)
    ·
      refine ⟨5185770873427666580896319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13828722329140444215723517 5185770873427666580896319)
      ·
        refine ⟨7778656310141499871344479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185770873427666580896319 7778656310141499871344479)
        ·
          refine ⟨11667984465212249807016719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778656310141499871344479 11667984465212249807016719)
          ·
            refine ⟨17501976697818374710525079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667984465212249807016719 17501976697818374710525079)
            ·
              refine ⟨26252965046727562065787619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17501976697818374710525079 26252965046727562065787619)
              ·
                refine ⟨39379447570091343098681429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26252965046727562065787619 39379447570091343098681429)
                ·
                  refine ⟨461477901212007926937673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39379447570091343098681429 461477901212007926937673)
                  ·
                    rfl

theorem cell23_8088525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_8088525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088525 prefixEnd_8088525 := by exact prefixLift 8088525
  have htrace : WordTrace (prefixWord ++ tailWord_8088525) baseStart_8088525 baseEnd_8088525 := by
    simpa [prefixWord, tailWord_8088525, baseEnd_8088525] using wordTrace_append hprefix tailTrace_8088525
  have hstable : (prefixWord ++ tailWord_8088525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088525).length < 2 ^ (prefixWord ++ tailWord_8088525).sum := by decide
  have hdescent : baseEnd_8088525 < baseStart_8088525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088551 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 1, 6]
def baseStart_8088551 : Nat := 118140960795 + 8088551 * 2 ^ 59
def prefixEnd_8088551 : Nat := 4983230072969 + 3 ^ 40 * 8088551 * 2
def baseEnd_8088551 : Nat := 1384438153801696080237979

theorem tailTrace_8088551 : CollatzResearch.WordTrace tailWord_8088551 prefixEnd_8088551 1384438153801696080237979 := by
  unfold tailWord_8088551
  simp only [CollatzResearch.WordTrace]
  refine ⟨295013691319568616375881507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196675794213045744250587671 295013691319568616375881507)
  ·
    refine ⟨442520536979352924563822261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295013691319568616375881507 442520536979352924563822261)
    ·
      refine ⟨41486300341814336677858337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 442520536979352924563822261 41486300341814336677858337)
      ·
        refine ⟨31114725256360752508393753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41486300341814336677858337 31114725256360752508393753)
        ·
          refine ⟨23336043942270564381295315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31114725256360752508393753 23336043942270564381295315)
          ·
            refine ⟨35004065913405846571942973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23336043942270564381295315 35004065913405846571942973)
            ·
              refine ⟨13126524717527192464478615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35004065913405846571942973 13126524717527192464478615)
              ·
                refine ⟨19689787076290788696717923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13126524717527192464478615 19689787076290788696717923)
                ·
                  refine ⟨29534680614436183045076885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19689787076290788696717923 29534680614436183045076885)
                  ·
                    refine ⟨1384438153801696080237979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29534680614436183045076885 1384438153801696080237979)
                    ·
                      rfl

theorem cell23_8088551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_8088551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088551 prefixEnd_8088551 := by exact prefixLift 8088551
  have htrace : WordTrace (prefixWord ++ tailWord_8088551) baseStart_8088551 baseEnd_8088551 := by
    simpa [prefixWord, tailWord_8088551, baseEnd_8088551] using wordTrace_append hprefix tailTrace_8088551
  have hstable : (prefixWord ++ tailWord_8088551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088551).length < 2 ^ (prefixWord ++ tailWord_8088551).sum := by decide
  have hdescent : baseEnd_8088551 < baseStart_8088551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088661 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_8088661 : Nat := 118140960795 + 8088661 * 2 ^ 59
def prefixEnd_8088661 : Nat := 4983230072969 + 3 ^ 40 * 8088661 * 2
def baseEnd_8088661 : Nat := 4153370944277082810338431

theorem tailTrace_8088661 : CollatzResearch.WordTrace tailWord_8088661 prefixEnd_8088661 4153370944277082810338431 := by
  unfold tailWord_8088661
  simp only [CollatzResearch.WordTrace]
  refine ⟨295017703349170105162385837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196678468899446736774923891 295017703349170105162385837)
  ·
    refine ⟨110631638755938789435894689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295017703349170105162385837 110631638755938789435894689)
    ·
      refine ⟨82973729066954092076921017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110631638755938789435894689 82973729066954092076921017)
      ·
        refine ⟨62230296800215569057690763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82973729066954092076921017 62230296800215569057690763)
        ·
          refine ⟨93345445200323353586536145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62230296800215569057690763 93345445200323353586536145)
          ·
            refine ⟨70009083900242515189902109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93345445200323353586536145 70009083900242515189902109)
            ·
              refine ⟨26253406462590943196213291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70009083900242515189902109 26253406462590943196213291)
              ·
                refine ⟨39380109693886414794319937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26253406462590943196213291 39380109693886414794319937)
                ·
                  refine ⟨29535082270414811095739953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39380109693886414794319937 29535082270414811095739953)
                  ·
                    refine ⟨22151311702811108321804965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29535082270414811095739953 22151311702811108321804965)
                    ·
                      refine ⟨4153370944277082810338431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22151311702811108321804965 4153370944277082810338431)
                      ·
                        rfl

theorem cell23_8088661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_8088661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088661 prefixEnd_8088661 := by exact prefixLift 8088661
  have htrace : WordTrace (prefixWord ++ tailWord_8088661) baseStart_8088661 baseEnd_8088661 := by
    simpa [prefixWord, tailWord_8088661, baseEnd_8088661] using wordTrace_append hprefix tailTrace_8088661
  have hstable : (prefixWord ++ tailWord_8088661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088661).length < 2 ^ (prefixWord ++ tailWord_8088661).sum := by decide
  have hdescent : baseEnd_8088661 < baseStart_8088661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088688 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 5]
def baseStart_8088688 : Nat := 118140960795 + 8088688 * 2 ^ 59
def prefixEnd_8088688 : Nat := 4983230072969 + 3 ^ 40 * 8088688 * 2
def baseEnd_8088688 : Nat := 461487200917194911633423

theorem tailTrace_8088688 : CollatzResearch.WordTrace tailWord_8088688 prefixEnd_8088688 461487200917194911633423 := by
  unfold tailWord_8088688
  simp only [CollatzResearch.WordTrace]
  refine ⟨147509344060036144386809359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196679125413381525849079145 147509344060036144386809359)
  ·
    refine ⟨221264016090054216580214039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147509344060036144386809359 221264016090054216580214039)
    ·
      refine ⟨331896024135081324870321059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221264016090054216580214039 331896024135081324870321059)
      ·
        refine ⟨497844036202621987305481589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331896024135081324870321059 497844036202621987305481589)
        ·
          refine ⟨46672878393995811309888899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497844036202621987305481589 46672878393995811309888899)
          ·
            refine ⟨70009317590993716964833349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46672878393995811309888899 70009317590993716964833349)
            ·
              refine ⟨13126747048311321930906253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70009317590993716964833349 13126747048311321930906253)
              ·
                refine ⟨4922530143116745724089845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13126747048311321930906253 4922530143116745724089845)
                ·
                  refine ⟨461487200917194911633423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4922530143116745724089845 461487200917194911633423)
                  ·
                    rfl

theorem cell23_8088688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 5].length) (baseStart_8088688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088688 prefixEnd_8088688 := by exact prefixLift 8088688
  have htrace : WordTrace (prefixWord ++ tailWord_8088688) baseStart_8088688 baseEnd_8088688 := by
    simpa [prefixWord, tailWord_8088688, baseEnd_8088688] using wordTrace_append hprefix tailTrace_8088688
  have hstable : (prefixWord ++ tailWord_8088688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088688).length < 2 ^ (prefixWord ++ tailWord_8088688).sum := by decide
  have hdescent : baseEnd_8088688 < baseStart_8088688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088701 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_8088701 : Nat := 118140960795 + 8088701 * 2 ^ 59
def prefixEnd_8088701 : Nat := 4983230072969 + 3 ^ 40 * 8088701 * 2
def baseEnd_8088701 : Nat := 1384463827834420884612749

theorem tailTrace_8088701 : CollatzResearch.WordTrace tailWord_8088701 prefixEnd_8088701 1384463827834420884612749 := by
  unfold tailWord_8088701
  simp only [CollatzResearch.WordTrace]
  refine ⟨295019162269025191993841957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196679441512683461329227971 295019162269025191993841957)
  ·
    refine ⟨55316092925442223498845367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295019162269025191993841957 55316092925442223498845367)
    ·
      refine ⟨82974139388163335248268051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55316092925442223498845367 82974139388163335248268051)
      ·
        refine ⟨124461209082245002872402077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82974139388163335248268051 124461209082245002872402077)
        ·
          refine ⟨46672953405841876077150779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124461209082245002872402077 46672953405841876077150779)
          ·
            refine ⟨70009430108762814115726169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46672953405841876077150779 70009430108762814115726169)
            ·
              refine ⟨52507072581572110586794627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70009430108762814115726169 52507072581572110586794627)
              ·
                refine ⟨78760608872358165880191941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52507072581572110586794627 78760608872358165880191941)
                ·
                  refine ⟨14767614163567156102535989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78760608872358165880191941 14767614163567156102535989)
                  ·
                    refine ⟨1384463827834420884612749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14767614163567156102535989 1384463827834420884612749)
                    ·
                      rfl

theorem cell23_8088701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_8088701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088701 prefixEnd_8088701 := by exact prefixLift 8088701
  have htrace : WordTrace (prefixWord ++ tailWord_8088701) baseStart_8088701 baseEnd_8088701 := by
    simpa [prefixWord, tailWord_8088701, baseEnd_8088701] using wordTrace_append hprefix tailTrace_8088701
  have hstable : (prefixWord ++ tailWord_8088701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088701).length < 2 ^ (prefixWord ++ tailWord_8088701).sum := by decide
  have hdescent : baseEnd_8088701 < baseStart_8088701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088761 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 8]
def baseStart_8088761 : Nat := 118140960795 + 8088761 * 2 ^ 59
def prefixEnd_8088761 : Nat := 4983230072969 + 3 ^ 40 * 8088761 * 2
def baseEnd_8088761 : Nat := 461491365815836935454219

theorem tailTrace_8088761 : CollatzResearch.WordTrace tailWord_8088761 prefixEnd_8088761 461491365815836935454219 := by
  unfold tailWord_8088761
  simp only [CollatzResearch.WordTrace]
  refine ⟨295021350648807822241026137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196680900432538548160684091 295021350648807822241026137)
  ·
    refine ⟨221266012986605866680769603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295021350648807822241026137 221266012986605866680769603)
    ·
      refine ⟨331899019479908800021154405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221266012986605866680769603 331899019479908800021154405)
      ·
        refine ⟨62231066152482900003966451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331899019479908800021154405 62231066152482900003966451)
        ·
          refine ⟨93346599228724350005949677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62231066152482900003966451 93346599228724350005949677)
          ·
            refine ⟨35004974710771631252231129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93346599228724350005949677 35004974710771631252231129)
            ·
              refine ⟨26253731033078723439173347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35004974710771631252231129 26253731033078723439173347)
              ·
                refine ⟨39380596549618085158760021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26253731033078723439173347 39380596549618085158760021)
                ·
                  refine ⟨461491365815836935454219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39380596549618085158760021 461491365815836935454219)
                  ·
                    rfl

theorem cell23_8088761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_8088761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088761 prefixEnd_8088761 := by exact prefixLift 8088761
  have htrace : WordTrace (prefixWord ++ tailWord_8088761) baseStart_8088761 baseEnd_8088761 := by
    simpa [prefixWord, tailWord_8088761, baseEnd_8088761] using wordTrace_append hprefix tailTrace_8088761
  have hstable : (prefixWord ++ tailWord_8088761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088761).length < 2 ^ (prefixWord ++ tailWord_8088761).sum := by decide
  have hdescent : baseEnd_8088761 < baseStart_8088761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088765 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_8088765 : Nat := 118140960795 + 8088765 * 2 ^ 59
def prefixEnd_8088765 : Nat := 4983230072969 + 3 ^ 40 * 8088765 * 2
def baseEnd_8088765 : Nat := 1384474782088383467812651

theorem tailTrace_8088765 : CollatzResearch.WordTrace tailWord_8088765 prefixEnd_8088765 1384474782088383467812651 := by
  unfold tailWord_8088765
  simp only [CollatzResearch.WordTrace]
  refine ⟨295021496540793330924171749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196680997693862220616114499 295021496540793330924171749)
  ·
    refine ⟨55316530601398749548282203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295021496540793330924171749 55316530601398749548282203)
    ·
      refine ⟨82974795902098124322423305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55316530601398749548282203 82974795902098124322423305)
      ·
        refine ⟨62231096926573593241817479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82974795902098124322423305 62231096926573593241817479)
        ·
          refine ⟨93346645389860389862726219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62231096926573593241817479 93346645389860389862726219)
          ·
            refine ⟨140019968084790584794089329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93346645389860389862726219 140019968084790584794089329)
            ·
              refine ⟨105014976063592938595566997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140019968084790584794089329 105014976063592938595566997)
              ·
                refine ⟨4922577002980918996667203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105014976063592938595566997 4922577002980918996667203)
                ·
                  refine ⟨7383865504471378495000805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922577002980918996667203 7383865504471378495000805)
                  ·
                    refine ⟨1384474782088383467812651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383865504471378495000805 1384474782088383467812651)
                    ·
                      rfl

theorem cell23_8088765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_8088765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088765 prefixEnd_8088765 := by exact prefixLift 8088765
  have htrace : WordTrace (prefixWord ++ tailWord_8088765) baseStart_8088765 baseEnd_8088765 := by
    simpa [prefixWord, tailWord_8088765, baseEnd_8088765] using wordTrace_append hprefix tailTrace_8088765
  have hstable : (prefixWord ++ tailWord_8088765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088765).length < 2 ^ (prefixWord ++ tailWord_8088765).sum := by decide
  have hdescent : baseEnd_8088765 < baseStart_8088765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088771 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3]
def baseStart_8088771 : Nat := 118140960795 + 8088771 * 2 ^ 59
def prefixEnd_8088771 : Nat := 4983230072969 + 3 ^ 40 * 8088771 * 2
def baseEnd_8088771 : Nat := 4153427427149077379962925

theorem tailTrace_8088771 : CollatzResearch.WordTrace tailWord_8088771 prefixEnd_8088771 4153427427149077379962925 := by
  unfold tailWord_8088771
  simp only [CollatzResearch.WordTrace]
  refine ⟨295021715378771593948890167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196681143585847729299260111 295021715378771593948890167)
  ·
    refine ⟨442532573068157390923335251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295021715378771593948890167 442532573068157390923335251)
    ·
      refine ⟨663798859602236086385002877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442532573068157390923335251 663798859602236086385002877)
      ·
        refine ⟨248924572350838532394376079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663798859602236086385002877 248924572350838532394376079)
        ·
          refine ⟨373386858526257798591564119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248924572350838532394376079 373386858526257798591564119)
          ·
            refine ⟨560080287789386697887346179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373386858526257798591564119 560080287789386697887346179)
            ·
              refine ⟨840120431684080046831019269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560080287789386697887346179 840120431684080046831019269)
              ·
                refine ⟨157522580940765008780816113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840120431684080046831019269 157522580940765008780816113)
                ·
                  refine ⟨118141935705573756585612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157522580940765008780816113 118141935705573756585612085)
                  ·
                    refine ⟨11075806472397539679901133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118141935705573756585612085 11075806472397539679901133)
                    ·
                      refine ⟨4153427427149077379962925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11075806472397539679901133 4153427427149077379962925)
                      ·
                        rfl

theorem cell23_8088771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_8088771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088771 prefixEnd_8088771 := by exact prefixLift 8088771
  have htrace : WordTrace (prefixWord ++ tailWord_8088771) baseStart_8088771 baseEnd_8088771 := by
    simpa [prefixWord, tailWord_8088771, baseEnd_8088771] using wordTrace_append hprefix tailTrace_8088771
  have hstable : (prefixWord ++ tailWord_8088771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088771).length < 2 ^ (prefixWord ++ tailWord_8088771).sum := by decide
  have hdescent : baseEnd_8088771 < baseStart_8088771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088778 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_8088778 : Nat := 118140960795 + 8088778 * 2 ^ 59
def prefixEnd_8088778 : Nat := 4983230072969 + 3 ^ 40 * 8088778 * 2
def baseEnd_8088778 : Nat := 461492335723739872508377

theorem tailTrace_8088778 : CollatzResearch.WordTrace tailWord_8088778 prefixEnd_8088778 461492335723739872508377 := by
  unfold tailWord_8088778
  simp only [CollatzResearch.WordTrace]
  refine ⟨73755492672436558536098747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196681313793164156096263325 73755492672436558536098747)
  ·
    refine ⟨110633239008654837804148121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73755492672436558536098747 110633239008654837804148121)
    ·
      refine ⟨82974929256491128353111091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110633239008654837804148121 82974929256491128353111091)
      ·
        refine ⟨124462393884736692529666637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82974929256491128353111091 124462393884736692529666637)
        ·
          refine ⟨46673397706776259698624989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124462393884736692529666637 46673397706776259698624989)
          ·
            refine ⟨17502524140041097386984371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46673397706776259698624989 17502524140041097386984371)
            ·
              refine ⟨26253786210061646080476557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17502524140041097386984371 26253786210061646080476557)
              ·
                refine ⟨9845169828773117280178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26253786210061646080476557 9845169828773117280178709)
                ·
                  refine ⟨461492335723739872508377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9845169828773117280178709 461492335723739872508377)
                  ·
                    rfl

theorem cell23_8088778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_8088778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088778 prefixEnd_8088778 := by exact prefixLift 8088778
  have htrace : WordTrace (prefixWord ++ tailWord_8088778) baseStart_8088778 baseEnd_8088778 := by
    simpa [prefixWord, tailWord_8088778, baseEnd_8088778] using wordTrace_append hprefix tailTrace_8088778
  have hstable : (prefixWord ++ tailWord_8088778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088778).length < 2 ^ (prefixWord ++ tailWord_8088778).sum := by decide
  have hdescent : baseEnd_8088778 < baseStart_8088778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088872 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_8088872 : Nat := 118140960795 + 8088872 * 2 ^ 59
def prefixEnd_8088872 : Nat := 4983230072969 + 3 ^ 40 * 8088872 * 2
def baseEnd_8088872 : Nat := 1384493096231727161599987

theorem tailTrace_8088872 : CollatzResearch.WordTrace tailWord_8088872 prefixEnd_8088872 1384493096231727161599987 := by
  unfold tailWord_8088872
  simp only [CollatzResearch.WordTrace]
  refine ⟨147512699575702844099158435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196683599434270458798877913 147512699575702844099158435)
  ·
    refine ⟨221269049363554266148737653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147512699575702844099158435 221269049363554266148737653)
    ·
      refine ⟨20743973377833212451444155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221269049363554266148737653 20743973377833212451444155)
      ·
        refine ⟨31115960066749818677166233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20743973377833212451444155 31115960066749818677166233)
        ·
          refine ⟨23336970050062364007874675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31115960066749818677166233 23336970050062364007874675)
          ·
            refine ⟨35005455075093546011812013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23336970050062364007874675 35005455075093546011812013)
            ·
              refine ⟨13127045653160079754429505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35005455075093546011812013 13127045653160079754429505)
              ·
                refine ⟨9845284239870059815822129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13127045653160079754429505 9845284239870059815822129)
                ·
                  refine ⟨7383963179902544861866597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9845284239870059815822129 7383963179902544861866597)
                  ·
                    refine ⟨1384493096231727161599987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383963179902544861866597 1384493096231727161599987)
                    ·
                      rfl

theorem cell23_8088872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_8088872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088872 prefixEnd_8088872 := by exact prefixLift 8088872
  have htrace : WordTrace (prefixWord ++ tailWord_8088872) baseStart_8088872 baseEnd_8088872 := by
    simpa [prefixWord, tailWord_8088872, baseEnd_8088872] using wordTrace_append hprefix tailTrace_8088872
  have hstable : (prefixWord ++ tailWord_8088872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088872).length < 2 ^ (prefixWord ++ tailWord_8088872).sum := by decide
  have hdescent : baseEnd_8088872 < baseStart_8088872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088889 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 2, 4]
def baseStart_8088889 : Nat := 118140960795 + 8088889 * 2 ^ 59
def prefixEnd_8088889 : Nat := 4983230072969 + 3 ^ 40 * 8088889 * 2
def baseEnd_8088889 : Nat := 1384496005955435972762461

theorem tailTrace_8088889 : CollatzResearch.WordTrace tailWord_8088889 prefixEnd_8088889 1384496005955435972762461 := by
  unfold tailWord_8088889
  simp only [CollatzResearch.WordTrace]
  refine ⟨295026019192344100101685721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196684012794896066734457147 295026019192344100101685721)
  ·
    refine ⟨221269514394258075076264291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295026019192344100101685721 221269514394258075076264291)
    ·
      refine ⟨331904271591387112614396437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221269514394258075076264291 331904271591387112614396437)
      ·
        refine ⟨15558012730846270903799833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331904271591387112614396437 15558012730846270903799833)
        ·
          refine ⟨11668509548134703177849875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15558012730846270903799833 11668509548134703177849875)
          ·
            refine ⟨17502764322202054766774813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11668509548134703177849875 17502764322202054766774813)
            ·
              refine ⟨6563536620825770537540555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17502764322202054766774813 6563536620825770537540555)
              ·
                refine ⟨9845304931238655806310833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563536620825770537540555 9845304931238655806310833)
                ·
                  refine ⟨7383978698428991854733125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9845304931238655806310833 7383978698428991854733125)
                  ·
                    refine ⟨1384496005955435972762461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7383978698428991854733125 1384496005955435972762461)
                    ·
                      rfl

theorem cell23_8088889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_8088889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088889 prefixEnd_8088889 := by exact prefixLift 8088889
  have htrace : WordTrace (prefixWord ++ tailWord_8088889) baseStart_8088889 baseEnd_8088889 := by
    simpa [prefixWord, tailWord_8088889, baseEnd_8088889] using wordTrace_append hprefix tailTrace_8088889
  have hstable : (prefixWord ++ tailWord_8088889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088889).length < 2 ^ (prefixWord ++ tailWord_8088889).sum := by decide
  have hdescent : baseEnd_8088889 < baseStart_8088889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088895 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_8088895 : Nat := 118140960795 + 8088895 * 2 ^ 59
def prefixEnd_8088895 : Nat := 4983230072969 + 3 ^ 40 * 8088895 * 2
def baseEnd_8088895 : Nat := 4153491098750234894812355

theorem tailTrace_8088895 : CollatzResearch.WordTrace tailWord_8088895 prefixEnd_8088895 4153491098750234894812355 := by
  unfold tailWord_8088895
  simp only [CollatzResearch.WordTrace]
  refine ⟨295026238030322363126404139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196684158686881575417602759 295026238030322363126404139)
  ·
    refine ⟨442539357045483544689606209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295026238030322363126404139 442539357045483544689606209)
    ·
      refine ⟨331904517784112658517204657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442539357045483544689606209 331904517784112658517204657)
      ·
        refine ⟨248928388338084493887903493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331904517784112658517204657 248928388338084493887903493)
        ·
          refine ⟨46674072813390842603981905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248928388338084493887903493 46674072813390842603981905)
          ·
            refine ⟨35005554610043131952986429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46674072813390842603981905 35005554610043131952986429)
            ·
              refine ⟨13127082978766174482369911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35005554610043131952986429 13127082978766174482369911)
              ·
                refine ⟨19690624468149261723554867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127082978766174482369911 19690624468149261723554867)
                ·
                  refine ⟨29535936702223892585332301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19690624468149261723554867 29535936702223892585332301)
                  ·
                    refine ⟨11075976263333959719499613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29535936702223892585332301 11075976263333959719499613)
                    ·
                      refine ⟨4153491098750234894812355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11075976263333959719499613 4153491098750234894812355)
                      ·
                        rfl

theorem cell23_8088895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_8088895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088895 prefixEnd_8088895 := by exact prefixLift 8088895
  have htrace : WordTrace (prefixWord ++ tailWord_8088895) baseStart_8088895 baseEnd_8088895 := by
    simpa [prefixWord, tailWord_8088895, baseEnd_8088895] using wordTrace_append hprefix tailTrace_8088895
  have hstable : (prefixWord ++ tailWord_8088895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088895).length < 2 ^ (prefixWord ++ tailWord_8088895).sum := by decide
  have hdescent : baseEnd_8088895 < baseStart_8088895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088905 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 3, 3, 2]
def baseStart_8088905 : Nat := 118140960795 + 8088905 * 2 ^ 59
def prefixEnd_8088905 : Nat := 4983230072969 + 3 ^ 40 * 8088905 * 2
def baseEnd_8088905 : Nat := 4153496233556779855687309

theorem tailTrace_8088905 : CollatzResearch.WordTrace tailWord_8088905 prefixEnd_8088905 4153496233556779855687309 := by
  unfold tailWord_8088905
  simp only [CollatzResearch.WordTrace]
  refine ⟨295026602760286134834268169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196684401840190756556178779 295026602760286134834268169)
  ·
    refine ⟨221269952070214601125701127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295026602760286134834268169 221269952070214601125701127)
    ·
      refine ⟨331904928105321901688551691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221269952070214601125701127 331904928105321901688551691)
      ·
        refine ⟨497857392157982852532827537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331904928105321901688551691 497857392157982852532827537)
        ·
          refine ⟨373393044118487139399620653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497857392157982852532827537 373393044118487139399620653)
          ·
            refine ⟨140022391544432677274857745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373393044118487139399620653 140022391544432677274857745)
            ·
              refine ⟨105016793658324507956143309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140022391544432677274857745 105016793658324507956143309)
              ·
                refine ⟨39381297621871690483553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105016793658324507956143309 39381297621871690483553741)
                ·
                  refine ⟨14767986608201883931332653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39381297621871690483553741 14767986608201883931332653)
                  ·
                    refine ⟨5537994978075706474249745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14767986608201883931332653 5537994978075706474249745)
                    ·
                      refine ⟨4153496233556779855687309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5537994978075706474249745 4153496233556779855687309)
                      ·
                        rfl

theorem cell23_8088905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3, 2].length) (baseStart_8088905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088905 prefixEnd_8088905 := by exact prefixLift 8088905
  have htrace : WordTrace (prefixWord ++ tailWord_8088905) baseStart_8088905 baseEnd_8088905 := by
    simpa [prefixWord, tailWord_8088905, baseEnd_8088905] using wordTrace_append hprefix tailTrace_8088905
  have hstable : (prefixWord ++ tailWord_8088905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088905).length < 2 ^ (prefixWord ++ tailWord_8088905).sum := by decide
  have hdescent : baseEnd_8088905 < baseStart_8088905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088908 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_8088908 : Nat := 118140960795 + 8088908 * 2 ^ 59
def prefixEnd_8088908 : Nat := 4983230072969 + 3 ^ 40 * 8088908 * 2
def baseEnd_8088908 : Nat := 4153497773998743343949795

theorem tailTrace_8088908 : CollatzResearch.WordTrace tailWord_8088908 prefixEnd_8088908 4153497773998743343949795 := by
  unfold tailWord_8088908
  simp only [CollatzResearch.WordTrace]
  refine ⟨147513356089637633173313689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196684474786183510897751585 147513356089637633173313689)
  ·
    refine ⟨110635017067228224879985267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147513356089637633173313689 110635017067228224879985267)
    ·
      refine ⟨165952525600842337319977901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110635017067228224879985267 165952525600842337319977901)
      ·
        refine ⟨62232197100315876494991713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165952525600842337319977901 62232197100315876494991713)
        ·
          refine ⟨46674147825236907371243785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62232197100315876494991713 46674147825236907371243785)
          ·
            refine ⟨35005610868927680528432839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46674147825236907371243785 35005610868927680528432839)
            ·
              refine ⟨52508416303391520792649259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35005610868927680528432839 52508416303391520792649259)
              ·
                refine ⟨78762624455087281188973889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52508416303391520792649259 78762624455087281188973889)
                ·
                  refine ⟨59071968341315460891730417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78762624455087281188973889 59071968341315460891730417)
                  ·
                    refine ⟨44303976255986595668797813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59071968341315460891730417 44303976255986595668797813)
                    ·
                      refine ⟨4153497773998743343949795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44303976255986595668797813 4153497773998743343949795)
                      ·
                        rfl

theorem cell23_8088908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_8088908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088908 prefixEnd_8088908 := by exact prefixLift 8088908
  have htrace : WordTrace (prefixWord ++ tailWord_8088908) baseStart_8088908 baseEnd_8088908 := by
    simpa [prefixWord, tailWord_8088908, baseEnd_8088908] using wordTrace_append hprefix tailTrace_8088908
  have hstable : (prefixWord ++ tailWord_8088908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088908).length < 2 ^ (prefixWord ++ tailWord_8088908).sum := by decide
  have hdescent : baseEnd_8088908 < baseStart_8088908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088922 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_8088922 : Nat := 118140960795 + 8088922 * 2 ^ 59
def prefixEnd_8088922 : Nat := 4983230072969 + 3 ^ 40 * 8088922 * 2
def baseEnd_8088922 : Nat := 4153504962727906289174731

theorem tailTrace_8088922 : CollatzResearch.WordTrace tailWord_8088922 prefixEnd_8088922 4153504962727906289174731 := by
  unfold tailWord_8088922
  simp only [CollatzResearch.WordTrace]
  refine ⟨73756805700306136684409255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196684815200816364491758013 73756805700306136684409255)
  ·
    refine ⟨110635208550459205026613883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73756805700306136684409255 110635208550459205026613883)
    ·
      refine ⟨165952812825688807539920825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110635208550459205026613883 165952812825688807539920825)
      ·
        refine ⟨124464609619266605654940619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165952812825688807539920825 124464609619266605654940619)
        ·
          refine ⟨186696914428899908482410929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124464609619266605654940619 186696914428899908482410929)
          ·
            refine ⟨140022685821674931361808197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186696914428899908482410929 140022685821674931361808197)
            ·
              refine ⟨26254253591564049630339037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140022685821674931361808197 26254253591564049630339037)
              ·
                refine ⟨9845345096836518611377139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26254253591564049630339037 9845345096836518611377139)
                ·
                  refine ⟨14768017645254777917065709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9845345096836518611377139 14768017645254777917065709)
                  ·
                    refine ⟨5538006616970541718899641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14768017645254777917065709 5538006616970541718899641)
                    ·
                      refine ⟨4153504962727906289174731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538006616970541718899641 4153504962727906289174731)
                      ·
                        rfl

theorem cell23_8088922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_8088922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088922 prefixEnd_8088922 := by exact prefixLift 8088922
  have htrace : WordTrace (prefixWord ++ tailWord_8088922) baseStart_8088922 baseEnd_8088922 := by
    simpa [prefixWord, tailWord_8088922, baseEnd_8088922] using wordTrace_append hprefix tailTrace_8088922
  have hstable : (prefixWord ++ tailWord_8088922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088922).length < 2 ^ (prefixWord ++ tailWord_8088922).sum := by decide
  have hdescent : baseEnd_8088922 < baseStart_8088922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088995 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 7, 2]
def baseStart_8088995 : Nat := 118140960795 + 8088995 * 2 ^ 59
def prefixEnd_8088995 : Nat := 4983230072969 + 3 ^ 40 * 8088995 * 2
def baseEnd_8088995 : Nat := 4153542446815684503561895

theorem tailTrace_8088995 : CollatzResearch.WordTrace tailWord_8088995 prefixEnd_8088995 4153542446815684503561895 := by
  unfold tailWord_8088995
  simp only [CollatzResearch.WordTrace]
  refine ⟨295029885329960080205044439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196686590219973386803362959 295029885329960080205044439)
  ·
    refine ⟨442544827994940120307566659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295029885329960080205044439 442544827994940120307566659)
    ·
      refine ⟨663817241992410180461349989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442544827994940120307566659 663817241992410180461349989)
      ·
        refine ⟨124465732873576908836503123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 663817241992410180461349989 124465732873576908836503123)
        ·
          refine ⟨186698599310365363254754685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124465732873576908836503123 186698599310365363254754685)
          ·
            refine ⟨70011974741387011220533007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186698599310365363254754685 70011974741387011220533007)
            ·
              refine ⟨105017962112080516830799511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70011974741387011220533007 105017962112080516830799511)
              ·
                refine ⟨157526943168120775246199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105017962112080516830799511 157526943168120775246199267)
                ·
                  refine ⟨236290414752181162869298901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157526943168120775246199267 236290414752181162869298901)
                  ·
                    refine ⟨5538056595754246004749193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236290414752181162869298901 5538056595754246004749193)
                    ·
                      refine ⟨4153542446815684503561895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538056595754246004749193 4153542446815684503561895)
                      ·
                        rfl

theorem cell23_8088995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_8088995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8088995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8088995 prefixEnd_8088995 := by exact prefixLift 8088995
  have htrace : WordTrace (prefixWord ++ tailWord_8088995) baseStart_8088995 baseEnd_8088995 := by
    simpa [prefixWord, tailWord_8088995, baseEnd_8088995] using wordTrace_append hprefix tailTrace_8088995
  have hstable : (prefixWord ++ tailWord_8088995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088995).length < 2 ^ (prefixWord ++ tailWord_8088995).sum := by decide
  have hdescent : baseEnd_8088995 < baseStart_8088995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089109 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 3]
def baseStart_8089109 : Nat := 118140960795 + 8089109 * 2 ^ 59
def prefixEnd_8089109 : Nat := 4983230072969 + 3 ^ 40 * 8089109 * 2
def baseEnd_8089109 : Nat := 4153600983610297057536371

theorem tailTrace_8089109 : CollatzResearch.WordTrace tailWord_8089109 prefixEnd_8089109 4153600983610297057536371 := by
  unfold tailWord_8089109
  simp only [CollatzResearch.WordTrace]
  refine ⟨295034043251547077674694381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196689362167698051783129587 295034043251547077674694381)
  ·
    refine ⟨110637766219330154128010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295034043251547077674694381 110637766219330154128010393)
    ·
      refine ⟨82978324664497615596007795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110637766219330154128010393 82978324664497615596007795)
      ·
        refine ⟨124467486996746423394011693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82978324664497615596007795 124467486996746423394011693)
        ·
          refine ⟨46675307623779908772754385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124467486996746423394011693 46675307623779908772754385)
          ·
            refine ⟨35006480717834931579565789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46675307623779908772754385 35006480717834931579565789)
            ·
              refine ⟨13127430269188099342337171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35006480717834931579565789 13127430269188099342337171)
              ·
                refine ⟨19691145403782149013505757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127430269188099342337171 19691145403782149013505757)
                ·
                  refine ⟨7384179526418305880064659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19691145403782149013505757 7384179526418305880064659)
                  ·
                    refine ⟨11076269289627458820096989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7384179526418305880064659 11076269289627458820096989)
                    ·
                      refine ⟨4153600983610297057536371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11076269289627458820096989 4153600983610297057536371)
                      ·
                        rfl

theorem cell23_8089109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_8089109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089109 prefixEnd_8089109 := by exact prefixLift 8089109
  have htrace : WordTrace (prefixWord ++ tailWord_8089109) baseStart_8089109 baseEnd_8089109 := by
    simpa [prefixWord, tailWord_8089109, baseEnd_8089109] using wordTrace_append hprefix tailTrace_8089109
  have hstable : (prefixWord ++ tailWord_8089109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089109).length < 2 ^ (prefixWord ++ tailWord_8089109).sum := by decide
  have hdescent : baseEnd_8089109 < baseStart_8089109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089125 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_8089125 : Nat := 118140960795 + 8089125 * 2 ^ 59
def prefixEnd_8089125 : Nat := 4983230072969 + 3 ^ 40 * 8089125 * 2
def baseEnd_8089125 : Nat := 1384536399766922998312099

theorem tailTrace_8089125 : CollatzResearch.WordTrace tailWord_8089125 prefixEnd_8089125 1384536399766922998312099 := by
  unfold tailWord_8089125
  simp only [CollatzResearch.WordTrace]
  refine ⟨295034626819489112407276829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196689751212992741604851219 295034626819489112407276829)
  ·
    refine ⟨110637985057308417152728811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295034626819489112407276829 110637985057308417152728811)
    ·
      refine ⟨165956977585962625729093217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110637985057308417152728811 165956977585962625729093217)
      ·
        refine ⟨124467733189471969296819913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165956977585962625729093217 124467733189471969296819913)
        ·
          refine ⟨93350799892103976972614935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124467733189471969296819913 93350799892103976972614935)
          ·
            refine ⟨140026199838155965458922403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93350799892103976972614935 140026199838155965458922403)
            ·
              refine ⟨210039299757233948188383605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140026199838155965458922403 210039299757233948188383605)
              ·
                refine ⟨19691184352240682642660963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210039299757233948188383605 19691184352240682642660963)
                ·
                  refine ⟨29536776528361023963991445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19691184352240682642660963 29536776528361023963991445)
                  ·
                    refine ⟨1384536399766922998312099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29536776528361023963991445 1384536399766922998312099)
                    ·
                      rfl

theorem cell23_8089125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_8089125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089125 prefixEnd_8089125 := by exact prefixLift 8089125
  have htrace : WordTrace (prefixWord ++ tailWord_8089125) baseStart_8089125 baseEnd_8089125 := by
    simpa [prefixWord, tailWord_8089125, baseEnd_8089125] using wordTrace_append hprefix tailTrace_8089125
  have hstable : (prefixWord ++ tailWord_8089125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089125).length < 2 ^ (prefixWord ++ tailWord_8089125).sum := by decide
  have hdescent : baseEnd_8089125 < baseStart_8089125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089185 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_8089185 : Nat := 118140960795 + 8089185 * 2 ^ 59
def prefixEnd_8089185 : Nat := 4983230072969 + 3 ^ 40 * 8089185 * 2
def baseEnd_8089185 : Nat := 1384546669380012920062007

theorem tailTrace_8089185 : CollatzResearch.WordTrace tailWord_8089185 prefixEnd_8089185 1384546669380012920062007 := by
  unfold tailWord_8089185
  simp only [CollatzResearch.WordTrace]
  refine ⟨295036815199271742654461009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196691210132847828436307339 295036815199271742654461009)
  ·
    refine ⟨221277611399453806990845757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295036815199271742654461009 221277611399453806990845757)
    ·
      refine ⟨82979104274795177621567159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221277611399453806990845757 82979104274795177621567159)
      ·
        refine ⟨124468656412192766432350739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82979104274795177621567159 124468656412192766432350739)
        ·
          refine ⟨186702984618289149648526109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124468656412192766432350739 186702984618289149648526109)
          ·
            refine ⟨70013619231858431118197291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186702984618289149648526109 70013619231858431118197291)
            ·
              refine ⟨105020428847787646677295937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70013619231858431118197291 105020428847787646677295937)
              ·
                refine ⟨78765321635840735007971953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105020428847787646677295937 78765321635840735007971953)
                ·
                  refine ⟨59073991226880551255978965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78765321635840735007971953 59073991226880551255978965)
                  ·
                    refine ⟨1384546669380012920062007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59073991226880551255978965 1384546669380012920062007)
                    ·
                      rfl

theorem cell23_8089185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_8089185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089185 prefixEnd_8089185 := by exact prefixLift 8089185
  have htrace : WordTrace (prefixWord ++ tailWord_8089185) baseStart_8089185 baseEnd_8089185 := by
    simpa [prefixWord, tailWord_8089185, baseEnd_8089185] using wordTrace_append hprefix tailTrace_8089185
  have hstable : (prefixWord ++ tailWord_8089185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089185).length < 2 ^ (prefixWord ++ tailWord_8089185).sum := by decide
  have hdescent : baseEnd_8089185 < baseStart_8089185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089272 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_8089272 : Nat := 118140960795 + 8089272 * 2 ^ 59
def prefixEnd_8089272 : Nat := 4983230072969 + 3 ^ 40 * 8089272 * 2
def baseEnd_8089272 : Nat := 4153684680956979919798121

theorem tailTrace_8089272 : CollatzResearch.WordTrace tailWord_8089272 prefixEnd_8089272 4153684680956979919798121 := by
  unfold tailWord_8089272
  simp only [CollatzResearch.WordTrace]
  refine ⟨147519994174978278256439035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196693325566637704341918713 147519994174978278256439035)
  ·
    refine ⟨221279991262467417384658553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147519994174978278256439035 221279991262467417384658553)
    ·
      refine ⟨165959993446850563038493915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221279991262467417384658553 165959993446850563038493915)
      ·
        refine ⟨248939990170275844557740873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165959993446850563038493915 248939990170275844557740873)
        ·
          refine ⟨186704992627706883418305655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248939990170275844557740873 186704992627706883418305655)
          ·
            refine ⟨280057488941560325127458483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186704992627706883418305655 280057488941560325127458483)
            ·
              refine ⟨420086233412340487691187725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280057488941560325127458483 420086233412340487691187725)
              ·
                refine ⟨157532337529627682884195397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420086233412340487691187725 157532337529627682884195397)
                ·
                  refine ⟨29537313286805190540786637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157532337529627682884195397 29537313286805190540786637)
                  ·
                    refine ⟨11076492482551946452794989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29537313286805190540786637 11076492482551946452794989)
                    ·
                      refine ⟨4153684680956979919798121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11076492482551946452794989 4153684680956979919798121)
                      ·
                        rfl

theorem cell23_8089272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_8089272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089272 prefixEnd_8089272 := by exact prefixLift 8089272
  have htrace : WordTrace (prefixWord ++ tailWord_8089272) baseStart_8089272 baseEnd_8089272 := by
    simpa [prefixWord, tailWord_8089272, baseEnd_8089272] using wordTrace_append hprefix tailTrace_8089272
  have hstable : (prefixWord ++ tailWord_8089272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089272).length < 2 ^ (prefixWord ++ tailWord_8089272).sum := by decide
  have hdescent : baseEnd_8089272 < baseStart_8089272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089312 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_8089312 : Nat := 118140960795 + 8089312 * 2 ^ 59
def prefixEnd_8089312 : Nat := 4983230072969 + 3 ^ 40 * 8089312 * 2
def baseEnd_8089312 : Nat := 4153705220183159763297937

theorem tailTrace_8089312 : CollatzResearch.WordTrace tailWord_8089312 prefixEnd_8089312 4153705220183159763297937 := by
  unfold tailWord_8089312
  simp only [CollatzResearch.WordTrace]
  refine ⟨147520723634905821672167095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196694298179874428896222793 147520723634905821672167095)
  ·
    refine ⟨221281085452358732508250643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147520723634905821672167095 221281085452358732508250643)
    ·
      refine ⟨331921628178538098762375965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221281085452358732508250643 331921628178538098762375965)
      ·
        refine ⟨124470610566951787035890987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331921628178538098762375965 124470610566951787035890987)
        ·
          refine ⟨186705915850427680553836481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124470610566951787035890987 186705915850427680553836481)
          ·
            refine ⟨140029436887820760415377361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186705915850427680553836481 140029436887820760415377361)
            ·
              refine ⟨105022077665865570311533021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140029436887820760415377361 105022077665865570311533021)
              ·
                refine ⟨39383279124699588866824883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105022077665865570311533021 39383279124699588866824883)
                ·
                  refine ⟨59074918687049383300237325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39383279124699588866824883 59074918687049383300237325)
                  ·
                    refine ⟨22153094507643518737588997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59074918687049383300237325 22153094507643518737588997)
                    ·
                      refine ⟨4153705220183159763297937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22153094507643518737588997 4153705220183159763297937)
                      ·
                        rfl

theorem cell23_8089312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_8089312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089312 prefixEnd_8089312 := by exact prefixLift 8089312
  have htrace : WordTrace (prefixWord ++ tailWord_8089312) baseStart_8089312 baseEnd_8089312 := by
    simpa [prefixWord, tailWord_8089312, baseEnd_8089312] using wordTrace_append hprefix tailTrace_8089312
  have hstable : (prefixWord ++ tailWord_8089312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089312).length < 2 ^ (prefixWord ++ tailWord_8089312).sum := by decide
  have hdescent : baseEnd_8089312 < baseStart_8089312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089329 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_8089329 : Nat := 118140960795 + 8089329 * 2 ^ 59
def prefixEnd_8089329 : Nat := 4983230072969 + 3 ^ 40 * 8089329 * 2
def baseEnd_8089329 : Nat := 4153713949354286196785359

theorem tailTrace_8089329 : CollatzResearch.WordTrace tailWord_8089329 prefixEnd_8089329 4153713949354286196785359 := by
  unfold tailWord_8089329
  simp only [CollatzResearch.WordTrace]
  refine ⟨295042067310750055247703041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196694711540500036831802027 295042067310750055247703041)
  ·
    refine ⟨221281550483062541435777281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295042067310750055247703041 221281550483062541435777281)
    ·
      refine ⟨165961162862296906076832961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221281550483062541435777281 165961162862296906076832961)
      ·
        refine ⟨124470872146722679557624721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165961162862296906076832961 124470872146722679557624721)
        ·
          refine ⟨93353154110042009668218541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124470872146722679557624721 93353154110042009668218541)
          ·
            refine ⟨35007432791265753625581953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93353154110042009668218541 35007432791265753625581953)
            ·
              refine ⟨26255574593449315219186465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35007432791265753625581953 26255574593449315219186465)
              ·
                refine ⟨19691680945086986414389849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26255574593449315219186465 19691680945086986414389849)
                ·
                  refine ⟨14768760708815239810792387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19691680945086986414389849 14768760708815239810792387)
                  ·
                    refine ⟨22153141063222859716188581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14768760708815239810792387 22153141063222859716188581)
                    ·
                      refine ⟨4153713949354286196785359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22153141063222859716188581 4153713949354286196785359)
                      ·
                        rfl

theorem cell23_8089329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_8089329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089329 prefixEnd_8089329 := by exact prefixLift 8089329
  have htrace : WordTrace (prefixWord ++ tailWord_8089329) baseStart_8089329 baseEnd_8089329 := by
    simpa [prefixWord, tailWord_8089329, baseEnd_8089329] using wordTrace_append hprefix tailTrace_8089329
  have hstable : (prefixWord ++ tailWord_8089329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089329).length < 2 ^ (prefixWord ++ tailWord_8089329).sum := by decide
  have hdescent : baseEnd_8089329 < baseStart_8089329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089416 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_8089416 : Nat := 118140960795 + 8089416 * 2 ^ 59
def prefixEnd_8089416 : Nat := 4983230072969 + 3 ^ 40 * 8089416 * 2
def baseEnd_8089416 : Nat := 1384586207390409118799153

theorem tailTrace_8089416 : CollatzResearch.WordTrace tailWord_8089416 prefixEnd_8089416 1384586207390409118799153 := by
  unfold tailWord_8089416
  simp only [CollatzResearch.WordTrace]
  refine ⟨147522620230717434553060051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196696826974289912737413401 147522620230717434553060051)
  ·
    refine ⟨221283930346076151829590077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147522620230717434553060051 221283930346076151829590077)
    ·
      refine ⟨82981473879778556936096279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221283930346076151829590077 82981473879778556936096279)
      ·
        refine ⟨124472210819667835404144419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82981473879778556936096279 124472210819667835404144419)
        ·
          refine ⟨186708316229501753106216629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124472210819667835404144419 186708316229501753106216629)
          ·
            refine ⟨17503904646515789353707809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186708316229501753106216629 17503904646515789353707809)
            ·
              refine ⟨13127928484886842015280857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17503904646515789353707809 13127928484886842015280857)
              ·
                refine ⟨9845946363665131511460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13127928484886842015280857 9845946363665131511460643)
                ·
                  refine ⟨14768919545497697267190965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9845946363665131511460643 14768919545497697267190965)
                  ·
                    refine ⟨1384586207390409118799153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14768919545497697267190965 1384586207390409118799153)
                    ·
                      rfl

theorem cell23_8089416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_8089416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089416 prefixEnd_8089416 := by exact prefixLift 8089416
  have htrace : WordTrace (prefixWord ++ tailWord_8089416) baseStart_8089416 baseEnd_8089416 := by
    simpa [prefixWord, tailWord_8089416, baseEnd_8089416] using wordTrace_append hprefix tailTrace_8089416
  have hstable : (prefixWord ++ tailWord_8089416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089416).length < 2 ^ (prefixWord ++ tailWord_8089416).sum := by decide
  have hdescent : baseEnd_8089416 < baseStart_8089416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089439 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_8089439 : Nat := 118140960795 + 8089439 * 2 ^ 59
def prefixEnd_8089439 : Nat := 4983230072969 + 3 ^ 40 * 8089439 * 2
def baseEnd_8089439 : Nat := 4153770432226280766409853

theorem tailTrace_8089439 : CollatzResearch.WordTrace tailWord_8089439 prefixEnd_8089439 4153770432226280766409853 := by
  unfold tailWord_8089439
  simp only [CollatzResearch.WordTrace]
  refine ⟨295046079340351544034207371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196697386226901029356138247 295046079340351544034207371)
  ·
    refine ⟨442569119010527316051311057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295046079340351544034207371 442569119010527316051311057)
    ·
      refine ⟨331926839257895487038483293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442569119010527316051311057 331926839257895487038483293)
      ·
        refine ⟨124472564721710807639431235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331926839257895487038483293 124472564721710807639431235)
        ·
          refine ⟨186708847082566211459146853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124472564721710807639431235 186708847082566211459146853)
          ·
            refine ⟨35007908827981164648590035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186708847082566211459146853 35007908827981164648590035)
            ·
              refine ⟨52511863241971746972885053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35007908827981164648590035 52511863241971746972885053)
              ·
                refine ⟨19691948715739405114831895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52511863241971746972885053 19691948715739405114831895)
                ·
                  refine ⟨29537923073609107672247843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19691948715739405114831895 29537923073609107672247843)
                  ·
                    refine ⟨44306884610413661508371765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29537923073609107672247843 44306884610413661508371765)
                    ·
                      refine ⟨4153770432226280766409853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44306884610413661508371765 4153770432226280766409853)
                      ·
                        rfl

theorem cell23_8089439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_8089439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089439 prefixEnd_8089439 := by exact prefixLift 8089439
  have htrace : WordTrace (prefixWord ++ tailWord_8089439) baseStart_8089439 baseEnd_8089439 := by
    simpa [prefixWord, tailWord_8089439, baseEnd_8089439] using wordTrace_append hprefix tailTrace_8089439
  have hstable : (prefixWord ++ tailWord_8089439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089439).length < 2 ^ (prefixWord ++ tailWord_8089439).sum := by decide
  have hdescent : baseEnd_8089439 < baseStart_8089439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089470 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8089470 : Nat := 118140960795 + 8089470 * 2 ^ 59
def prefixEnd_8089470 : Nat := 4983230072969 + 3 ^ 40 * 8089470 * 2
def baseEnd_8089470 : Nat := 4153786350126570145122211

theorem tailTrace_8089470 : CollatzResearch.WordTrace tailWord_8089470 prefixEnd_8089470 4153786350126570145122211 := by
  unfold tailWord_8089470
  simp only [CollatzResearch.WordTrace]
  refine ⟨36880901250404904541073233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196698140002159490885723909 36880901250404904541073233)
  ·
    refine ⟨27660675937803678405804925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36880901250404904541073233 27660675937803678405804925)
    ·
      refine ⟨10372753476676379402176847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27660675937803678405804925 10372753476676379402176847)
      ·
        refine ⟨15559130215014569103265271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10372753476676379402176847 15559130215014569103265271)
        ·
          refine ⟨23338695322521853654897907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15559130215014569103265271 23338695322521853654897907)
          ·
            refine ⟨35008042983782780482346861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23338695322521853654897907 35008042983782780482346861)
            ·
              refine ⟨13128016118918542680880073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35008042983782780482346861 13128016118918542680880073)
              ·
                refine ⟨9846012089188907010660055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128016118918542680880073 9846012089188907010660055)
                ·
                  refine ⟨14769018133783360515990083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846012089188907010660055 14769018133783360515990083)
                  ·
                    refine ⟨22153527200675040773985125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14769018133783360515990083 22153527200675040773985125)
                    ·
                      refine ⟨4153786350126570145122211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22153527200675040773985125 4153786350126570145122211)
                      ·
                        rfl

theorem cell23_8089470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8089470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089470 prefixEnd_8089470 := by exact prefixLift 8089470
  have htrace : WordTrace (prefixWord ++ tailWord_8089470) baseStart_8089470 baseEnd_8089470 := by
    simpa [prefixWord, tailWord_8089470, baseEnd_8089470] using wordTrace_append hprefix tailTrace_8089470
  have hstable : (prefixWord ++ tailWord_8089470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089470).length < 2 ^ (prefixWord ++ tailWord_8089470).sum := by decide
  have hdescent : baseEnd_8089470 < baseStart_8089470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089519 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 2, 6]
def baseStart_8089519 : Nat := 118140960795 + 8089519 * 2 ^ 59
def prefixEnd_8089519 : Nat := 4983230072969 + 3 ^ 40 * 8089519 * 2
def baseEnd_8089519 : Nat := 1384603836892880151136495

theorem tailTrace_8089519 : CollatzResearch.WordTrace tailWord_8089519 prefixEnd_8089519 1384603836892880151136495 := by
  unfold tailWord_8089519
  simp only [CollatzResearch.WordTrace]
  refine ⟨295048997180061717697119611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196699331453374478464746407 295048997180061717697119611)
  ·
    refine ⟨442573495770092576545679417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295048997180061717697119611 442573495770092576545679417)
    ·
      refine ⟨331930121827569432409259563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442573495770092576545679417 331930121827569432409259563)
      ·
        refine ⟨497895182741354148613889345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331930121827569432409259563 497895182741354148613889345)
        ·
          refine ⟨373421387056015611460417009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497895182741354148613889345 373421387056015611460417009)
          ·
            refine ⟨280066040292011708595312757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373421387056015611460417009 280066040292011708595312757)
            ·
              refine ⟨26256191277376097680810571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280066040292011708595312757 26256191277376097680810571)
              ·
                refine ⟨39384286916064146521215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26256191277376097680810571 39384286916064146521215857)
                ·
                  refine ⟨29538215187048109890911893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39384286916064146521215857 29538215187048109890911893)
                  ·
                    refine ⟨1384603836892880151136495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29538215187048109890911893 1384603836892880151136495)
                    ·
                      rfl

theorem cell23_8089519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_8089519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089519 prefixEnd_8089519 := by exact prefixLift 8089519
  have htrace : WordTrace (prefixWord ++ tailWord_8089519) baseStart_8089519 baseEnd_8089519 := by
    simpa [prefixWord, tailWord_8089519, baseEnd_8089519] using wordTrace_append hprefix tailTrace_8089519
  have hstable : (prefixWord ++ tailWord_8089519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089519).length < 2 ^ (prefixWord ++ tailWord_8089519).sum := by decide
  have hdescent : baseEnd_8089519 < baseStart_8089519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089539 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_8089539 : Nat := 118140960795 + 8089539 * 2 ^ 59
def prefixEnd_8089539 : Nat := 4983230072969 + 3 ^ 40 * 8089539 * 2
def baseEnd_8089539 : Nat := 4153821780291730375159393

theorem tailTrace_8089539 : CollatzResearch.WordTrace tailWord_8089539 prefixEnd_8089539 4153821780291730375159393 := by
  unfold tailWord_8089539
  simp only [CollatzResearch.WordTrace]
  refine ⟨295049726639989261112847671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196699817759992840741898447 295049726639989261112847671)
  ·
    refine ⟨442574589959983891669271507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295049726639989261112847671 442574589959983891669271507)
    ·
      refine ⟨663861884939975837503907261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442574589959983891669271507 663861884939975837503907261)
      ·
        refine ⟨248948206852490939063965223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663861884939975837503907261 248948206852490939063965223)
        ·
          refine ⟨373422310278736408595947835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248948206852490939063965223 373422310278736408595947835)
          ·
            refine ⟨560133465418104612893921753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373422310278736408595947835 560133465418104612893921753)
            ·
              refine ⟨420100099063578459670441315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560133465418104612893921753 420100099063578459670441315)
              ·
                refine ⟨630150148595367689505661973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420100099063578459670441315 630150148595367689505661973)
                ·
                  refine ⟨29538288215407860445577905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 630150148595367689505661973 29538288215407860445577905)
                  ·
                    refine ⟨22153716161555895334183429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29538288215407860445577905 22153716161555895334183429)
                    ·
                      refine ⟨4153821780291730375159393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22153716161555895334183429 4153821780291730375159393)
                      ·
                        rfl

theorem cell23_8089539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_8089539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089539 prefixEnd_8089539 := by exact prefixLift 8089539
  have htrace : WordTrace (prefixWord ++ tailWord_8089539) baseStart_8089539 baseEnd_8089539 := by
    simpa [prefixWord, tailWord_8089539, baseEnd_8089539] using wordTrace_append hprefix tailTrace_8089539
  have hstable : (prefixWord ++ tailWord_8089539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089539).length < 2 ^ (prefixWord ++ tailWord_8089539).sum := by decide
  have hdescent : baseEnd_8089539 < baseStart_8089539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089543 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_8089543 : Nat := 118140960795 + 8089543 * 2 ^ 59
def prefixEnd_8089543 : Nat := 4983230072969 + 3 ^ 40 * 8089543 * 2
def baseEnd_8089543 : Nat := 4153823834214348359509375

theorem tailTrace_8089543 : CollatzResearch.WordTrace tailWord_8089543 prefixEnd_8089543 4153823834214348359509375 := by
  unfold tailWord_8089543
  simp only [CollatzResearch.WordTrace]
  refine ⟨295049872531974769795993283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196699915021316513197328855 295049872531974769795993283)
  ·
    refine ⟨442574808797962154693989925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295049872531974769795993283 442574808797962154693989925)
    ·
      refine ⟨82982776649617904005123111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442574808797962154693989925 82982776649617904005123111)
      ·
        refine ⟨124474164974426856007684667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82982776649617904005123111 124474164974426856007684667)
        ·
          refine ⟨186711247461640284011527001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124474164974426856007684667 186711247461640284011527001)
          ·
            refine ⟨140033435596230213008645251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186711247461640284011527001 140033435596230213008645251)
            ·
              refine ⟨210050153394345319512967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140033435596230213008645251 210050153394345319512967877)
              ·
                refine ⟨39384403761439747408681477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210050153394345319512967877 39384403761439747408681477)
                ·
                  refine ⟨7384575705269952639127777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39384403761439747408681477 7384575705269952639127777)
                  ·
                    refine ⟨5538431778952464479345833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7384575705269952639127777 5538431778952464479345833)
                    ·
                      refine ⟨4153823834214348359509375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538431778952464479345833 4153823834214348359509375)
                      ·
                        rfl

theorem cell23_8089543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_8089543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089543 prefixEnd_8089543 := by exact prefixLift 8089543
  have htrace : WordTrace (prefixWord ++ tailWord_8089543) baseStart_8089543 baseEnd_8089543 := by
    simpa [prefixWord, tailWord_8089543, baseEnd_8089543] using wordTrace_append hprefix tailTrace_8089543
  have hstable : (prefixWord ++ tailWord_8089543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089543).length < 2 ^ (prefixWord ++ tailWord_8089543).sum := by decide
  have hdescent : baseEnd_8089543 < baseStart_8089543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089554 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_8089554 : Nat := 118140960795 + 8089554 * 2 ^ 59
def prefixEnd_8089554 : Nat := 4983230072969 + 3 ^ 40 * 8089554 * 2
def baseEnd_8089554 : Nat := 4153829482501547816471825

theorem tailTrace_8089554 : CollatzResearch.WordTrace tailWord_8089554 prefixEnd_8089554 4153829482501547816471825 := by
  unfold tailWord_8089554
  simp only [CollatzResearch.WordTrace]
  refine ⟨73762568433733729668660929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196700182489956612449762477 73762568433733729668660929)
  ·
    refine ⟨55321926325300297251495697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73762568433733729668660929 55321926325300297251495697)
    ·
      refine ⟨41491444743975222938621773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55321926325300297251495697 41491444743975222938621773)
      ·
        refine ⟨15559291778990708601983165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41491444743975222938621773 15559291778990708601983165)
        ·
          refine ⟨5834734417121515725743687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15559291778990708601983165 5834734417121515725743687)
          ·
            refine ⟨8752101625682273588615531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834734417121515725743687 8752101625682273588615531)
            ·
              refine ⟨13128152438523410382923297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752101625682273588615531 13128152438523410382923297)
              ·
                refine ⟨9846114328892557787192473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128152438523410382923297 9846114328892557787192473)
                ·
                  refine ⟨7384585746669418340394355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846114328892557787192473 7384585746669418340394355)
                  ·
                    refine ⟨11076878620004127510591533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7384585746669418340394355 11076878620004127510591533)
                    ·
                      refine ⟨4153829482501547816471825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11076878620004127510591533 4153829482501547816471825)
                      ·
                        rfl

theorem cell23_8089554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_8089554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089554 prefixEnd_8089554 := by exact prefixLift 8089554
  have htrace : WordTrace (prefixWord ++ tailWord_8089554) baseStart_8089554 baseEnd_8089554 := by
    simpa [prefixWord, tailWord_8089554, baseEnd_8089554] using wordTrace_append hprefix tailTrace_8089554
  have hstable : (prefixWord ++ tailWord_8089554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089554).length < 2 ^ (prefixWord ++ tailWord_8089554).sum := by decide
  have hdescent : baseEnd_8089554 < baseStart_8089554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089556 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_8089556 : Nat := 118140960795 + 8089556 * 2 ^ 59
def prefixEnd_8089556 : Nat := 4983230072969 + 3 ^ 40 * 8089556 * 2
def baseEnd_8089556 : Nat := 4153830509462856808646815

theorem tailTrace_8089556 : CollatzResearch.WordTrace tailWord_8089556 prefixEnd_8089556 4153830509462856808646815 := by
  unfold tailWord_8089556
  simp only [CollatzResearch.WordTrace]
  refine ⟨147525173340463836508108261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196700231120618448677477681 147525173340463836508108261)
  ·
    refine ⟨27660970001336969345270299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147525173340463836508108261 27660970001336969345270299)
    ·
      refine ⟨41491455002005454017905449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27660970001336969345270299 41491455002005454017905449)
      ·
        refine ⟨31118591251504090513429087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41491455002005454017905449 31118591251504090513429087)
        ·
          refine ⟨46677886877256135770143631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31118591251504090513429087 46677886877256135770143631)
          ·
            refine ⟨70016830315884203655215447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46677886877256135770143631 70016830315884203655215447)
            ·
              refine ⟨105025245473826305482823171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70016830315884203655215447 105025245473826305482823171)
              ·
                refine ⟨157537868210739458224234757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105025245473826305482823171 157537868210739458224234757)
                ·
                  refine ⟨29538350289513648417044017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157537868210739458224234757 29538350289513648417044017)
                  ·
                    refine ⟨22153762717135236312783013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29538350289513648417044017 22153762717135236312783013)
                    ·
                      refine ⟨4153830509462856808646815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22153762717135236312783013 4153830509462856808646815)
                      ·
                        rfl

theorem cell23_8089556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_8089556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089556 prefixEnd_8089556 := by exact prefixLift 8089556
  have htrace : WordTrace (prefixWord ++ tailWord_8089556) baseStart_8089556 baseEnd_8089556 := by
    simpa [prefixWord, tailWord_8089556, baseEnd_8089556] using wordTrace_append hprefix tailTrace_8089556
  have hstable : (prefixWord ++ tailWord_8089556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089556).length < 2 ^ (prefixWord ++ tailWord_8089556).sum := by decide
  have hdescent : baseEnd_8089556 < baseStart_8089556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089596 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_8089596 : Nat := 118140960795 + 8089596 * 2 ^ 59
def prefixEnd_8089596 : Nat := 4983230072969 + 3 ^ 40 * 8089596 * 2
def baseEnd_8089596 : Nat := 1384617016229678884048877

theorem tailTrace_8089596 : CollatzResearch.WordTrace tailWord_8089596 prefixEnd_8089596 1384617016229678884048877 := by
  unfold tailWord_8089596
  simp only [CollatzResearch.WordTrace]
  refine ⟨147525902800391379923836321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196701203733855173231781761 147525902800391379923836321)
  ·
    refine ⟨110644427100293534942877241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147525902800391379923836321 110644427100293534942877241)
    ·
      refine ⟨82983320325220151207157931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110644427100293534942877241 82983320325220151207157931)
      ·
        refine ⟨124474980487830226810736897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82983320325220151207157931 124474980487830226810736897)
        ·
          refine ⟨93356235365872670108052673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124474980487830226810736897 93356235365872670108052673)
          ·
            refine ⟨70017176524404502581039505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93356235365872670108052673 70017176524404502581039505)
            ·
              refine ⟨52512882393303376935779629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70017176524404502581039505 52512882393303376935779629)
              ·
                refine ⟨19692330897488766350917361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52512882393303376935779629 19692330897488766350917361)
                ·
                  refine ⟨14769248173116574763188021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19692330897488766350917361 14769248173116574763188021)
                  ·
                    refine ⟨1384617016229678884048877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14769248173116574763188021 1384617016229678884048877)
                    ·
                      rfl

theorem cell23_8089596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_8089596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089596 prefixEnd_8089596 := by exact prefixLift 8089596
  have htrace : WordTrace (prefixWord ++ tailWord_8089596) baseStart_8089596 baseEnd_8089596 := by
    simpa [prefixWord, tailWord_8089596, baseEnd_8089596] using wordTrace_append hprefix tailTrace_8089596
  have hstable : (prefixWord ++ tailWord_8089596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089596).length < 2 ^ (prefixWord ++ tailWord_8089596).sum := by decide
  have hdescent : baseEnd_8089596 < baseStart_8089596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089616 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_8089616 : Nat := 118140960795 + 8089616 * 2 ^ 59
def prefixEnd_8089616 : Nat := 4983230072969 + 3 ^ 40 * 8089616 * 2
def baseEnd_8089616 : Nat := 4153861318302126573896539

theorem tailTrace_8089616 : CollatzResearch.WordTrace tailWord_8089616 prefixEnd_8089616 4153861318302126573896539 := by
  unfold tailWord_8089616
  simp only [CollatzResearch.WordTrace]
  refine ⟨147526267530355151631700351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196701690040473535508933801 147526267530355151631700351)
  ·
    refine ⟨221289401295532727447550527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147526267530355151631700351 221289401295532727447550527)
    ·
      refine ⟨331934101943299091171325791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221289401295532727447550527 331934101943299091171325791)
      ·
        refine ⟨497901152914948636756988687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331934101943299091171325791 497901152914948636756988687)
        ·
          refine ⟨746851729372422955135483031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497901152914948636756988687 746851729372422955135483031)
          ·
            refine ⟨1120277594058634432703224547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746851729372422955135483031 1120277594058634432703224547)
            ·
              refine ⟨1680416391087951649054836821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120277594058634432703224547 1680416391087951649054836821)
              ·
                refine ⟨19692379583061933387361369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1680416391087951649054836821 19692379583061933387361369)
                ·
                  refine ⟨14769284687296450040521027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19692379583061933387361369 14769284687296450040521027)
                  ·
                    refine ⟨22153927030944675060781541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14769284687296450040521027 22153927030944675060781541)
                    ·
                      refine ⟨4153861318302126573896539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22153927030944675060781541 4153861318302126573896539)
                      ·
                        rfl

theorem cell23_8089616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_8089616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089616 prefixEnd_8089616 := by exact prefixLift 8089616
  have htrace : WordTrace (prefixWord ++ tailWord_8089616) baseStart_8089616 baseEnd_8089616 := by
    simpa [prefixWord, tailWord_8089616, baseEnd_8089616] using wordTrace_append hprefix tailTrace_8089616
  have hstable : (prefixWord ++ tailWord_8089616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089616).length < 2 ^ (prefixWord ++ tailWord_8089616).sum := by decide
  have hdescent : baseEnd_8089616 < baseStart_8089616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089623 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_8089623 : Nat := 118140960795 + 8089623 * 2 ^ 59
def prefixEnd_8089623 : Nat := 4983230072969 + 3 ^ 40 * 8089623 * 2
def baseEnd_8089623 : Nat := 4153864912666708046509007

theorem tailTrace_8089623 : CollatzResearch.WordTrace tailWord_8089623 prefixEnd_8089623 4153864912666708046509007 := by
  unfold tailWord_8089623
  simp only [CollatzResearch.WordTrace]
  refine ⟨295052790371684943458905523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196701860247789962305937015 295052790371684943458905523)
  ·
    refine ⟨442579185557527415188358285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295052790371684943458905523 442579185557527415188358285)
    ·
      refine ⟨165967194584072780695634357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442579185557527415188358285 165967194584072780695634357)
      ·
        refine ⟨15559424492256823190215721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165967194584072780695634357 15559424492256823190215721)
        ·
          refine ⟨11669568369192617392661791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15559424492256823190215721 11669568369192617392661791)
          ·
            refine ⟨17504352553788926088992687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11669568369192617392661791 17504352553788926088992687)
            ·
              refine ⟨26256528830683389133489031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17504352553788926088992687 26256528830683389133489031)
              ·
                refine ⟨39384793246025083700233547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26256528830683389133489031 39384793246025083700233547)
                ·
                  refine ⟨59077189869037625550350321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39384793246025083700233547 59077189869037625550350321)
                  ·
                    refine ⟨44307892401778219162762741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59077189869037625550350321 44307892401778219162762741)
                    ·
                      refine ⟨4153864912666708046509007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44307892401778219162762741 4153864912666708046509007)
                      ·
                        rfl

theorem cell23_8089623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_8089623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089623 prefixEnd_8089623 := by exact prefixLift 8089623
  have htrace : WordTrace (prefixWord ++ tailWord_8089623) baseStart_8089623 baseEnd_8089623 := by
    simpa [prefixWord, tailWord_8089623, baseEnd_8089623] using wordTrace_append hprefix tailTrace_8089623
  have hstable : (prefixWord ++ tailWord_8089623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089623).length < 2 ^ (prefixWord ++ tailWord_8089623).sum := by decide
  have hdescent : baseEnd_8089623 < baseStart_8089623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089653 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_8089653 : Nat := 118140960795 + 8089653 * 2 ^ 59
def prefixEnd_8089653 : Nat := 4983230072969 + 3 ^ 40 * 8089653 * 2
def baseEnd_8089653 : Nat := 4153880317086342929133869

theorem tailTrace_8089653 : CollatzResearch.WordTrace tailWord_8089653 prefixEnd_8089653 4153880317086342929133869 := by
  unfold tailWord_8089653
  simp only [CollatzResearch.WordTrace]
  refine ⟨295053884561576258582497613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196702589707717505721665075 295053884561576258582497613)
  ·
    refine ⟨110645206710591096968436605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295053884561576258582497613 110645206710591096968436605)
    ·
      refine ⟨41491952516471661363163727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110645206710591096968436605 41491952516471661363163727)
      ·
        refine ⟨62237928774707492044745591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41491952516471661363163727 62237928774707492044745591)
        ·
          refine ⟨93356893162061238067118387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62237928774707492044745591 93356893162061238067118387)
          ·
            refine ⟨140035339743091857100677581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93356893162061238067118387 140035339743091857100677581)
            ·
              refine ⟨52513252403659446412754093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140035339743091857100677581 52513252403659446412754093)
              ·
                refine ⟨19692469651372292404782785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52513252403659446412754093 19692469651372292404782785)
                ·
                  refine ⟨14769352238529219303587089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19692469651372292404782785 14769352238529219303587089)
                  ·
                    refine ⟨11077014178896914477690317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14769352238529219303587089 11077014178896914477690317)
                    ·
                      refine ⟨4153880317086342929133869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11077014178896914477690317 4153880317086342929133869)
                      ·
                        rfl

theorem cell23_8089653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_8089653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089653 prefixEnd_8089653 := by exact prefixLift 8089653
  have htrace : WordTrace (prefixWord ++ tailWord_8089653) baseStart_8089653 baseEnd_8089653 := by
    simpa [prefixWord, tailWord_8089653, baseEnd_8089653] using wordTrace_append hprefix tailTrace_8089653
  have hstable : (prefixWord ++ tailWord_8089653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089653).length < 2 ^ (prefixWord ++ tailWord_8089653).sum := by decide
  have hdescent : baseEnd_8089653 < baseStart_8089653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089660 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_8089660 : Nat := 118140960795 + 8089660 * 2 ^ 59
def prefixEnd_8089660 : Nat := 4983230072969 + 3 ^ 40 * 8089660 * 2
def baseEnd_8089660 : Nat := 1384627970483641467248779

theorem tailTrace_8089660 : CollatzResearch.WordTrace tailWord_8089660 prefixEnd_8089660 1384627970483641467248779 := by
  unfold tailWord_8089660
  simp only [CollatzResearch.WordTrace]
  refine ⟨147527069936275449389001217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196702759915033932518668289 147527069936275449389001217)
  ·
    refine ⟨110645302452206587041750913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147527069936275449389001217 110645302452206587041750913)
    ·
      refine ⟨82983976839154940281313185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110645302452206587041750913 82983976839154940281313185)
      ·
        refine ⟨62237982629366205210984889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82983976839154940281313185 62237982629366205210984889)
        ·
          refine ⟨46678486972024653908238667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62237982629366205210984889 46678486972024653908238667)
          ·
            refine ⟨70017730458036980862358001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46678486972024653908238667 70017730458036980862358001)
            ·
              refine ⟨52513297843527735646768501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70017730458036980862358001 52513297843527735646768501)
              ·
                refine ⟨4923121672830725216884547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52513297843527735646768501 4923121672830725216884547)
                ·
                  refine ⟨7384682509246087825326821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923121672830725216884547 7384682509246087825326821)
                  ·
                    refine ⟨1384627970483641467248779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384682509246087825326821 1384627970483641467248779)
                    ·
                      rfl

theorem cell23_8089660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_8089660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089660 prefixEnd_8089660 := by exact prefixLift 8089660
  have htrace : WordTrace (prefixWord ++ tailWord_8089660) baseStart_8089660 baseEnd_8089660 := by
    simpa [prefixWord, tailWord_8089660, baseEnd_8089660] using wordTrace_append hprefix tailTrace_8089660
  have hstable : (prefixWord ++ tailWord_8089660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089660).length < 2 ^ (prefixWord ++ tailWord_8089660).sum := by decide
  have hdescent : baseEnd_8089660 < baseStart_8089660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089677 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_8089677 : Nat := 118140960795 + 8089677 * 2 ^ 59
def prefixEnd_8089677 : Nat := 4983230072969 + 3 ^ 40 * 8089677 * 2
def baseEnd_8089677 : Nat := 1384630880207350278411253

theorem tailTrace_8089677 : CollatzResearch.WordTrace tailWord_8089677 prefixEnd_8089677 1384630880207350278411253 := by
  unfold tailWord_8089677
  simp only [CollatzResearch.WordTrace]
  refine ⟨295054759913489310681371285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196703173275659540454247523 295054759913489310681371285)
  ·
    refine ⟨13830691870944811438189279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 295054759913489310681371285 13830691870944811438189279)
    ·
      refine ⟨20746037806417217157283919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13830691870944811438189279 20746037806417217157283919)
      ·
        refine ⟨31119056709625825735925879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20746037806417217157283919 31119056709625825735925879)
        ·
          refine ⟨46678585064438738603888819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31119056709625825735925879 46678585064438738603888819)
          ·
            refine ⟨70017877596658107905833229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46678585064438738603888819 70017877596658107905833229)
            ·
              refine ⟨26256704098746790464687461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70017877596658107905833229 26256704098746790464687461)
              ·
                refine ⟨4923132018515023212128899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26256704098746790464687461 4923132018515023212128899)
                ·
                  refine ⟨7384698027772534818193349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923132018515023212128899 7384698027772534818193349)
                  ·
                    refine ⟨1384630880207350278411253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384698027772534818193349 1384630880207350278411253)
                    ·
                      rfl

theorem cell23_8089677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_8089677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089677 prefixEnd_8089677 := by exact prefixLift 8089677
  have htrace : WordTrace (prefixWord ++ tailWord_8089677) baseStart_8089677 baseEnd_8089677 := by
    simpa [prefixWord, tailWord_8089677, baseEnd_8089677] using wordTrace_append hprefix tailTrace_8089677
  have hstable : (prefixWord ++ tailWord_8089677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089677).length < 2 ^ (prefixWord ++ tailWord_8089677).sum := by decide
  have hdescent : baseEnd_8089677 < baseStart_8089677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089694 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_8089694 : Nat := 118140960795 + 8089694 * 2 ^ 59
def prefixEnd_8089694 : Nat := 4983230072969 + 3 ^ 40 * 8089694 * 2
def baseEnd_8089694 : Nat := 1384633789931059089573727

theorem tailTrace_8089694 : CollatzResearch.WordTrace tailWord_8089694 prefixEnd_8089694 1384633789931059089573727 := by
  unfold tailWord_8089694
  simp only [CollatzResearch.WordTrace]
  refine ⟨36881922494303465323092517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196703586636285148389826757 36881922494303465323092517)
  ·
    refine ⟨6915360467681899748079847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36881922494303465323092517 6915360467681899748079847)
    ·
      refine ⟨10373040701522849622119771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6915360467681899748079847 10373040701522849622119771)
      ·
        refine ⟨15559561052284274433179657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10373040701522849622119771 15559561052284274433179657)
        ·
          refine ⟨11669670789213205824884743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15559561052284274433179657 11669670789213205824884743)
          ·
            refine ⟨17504506183819808737327115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11669670789213205824884743 17504506183819808737327115)
            ·
              refine ⟨26256759275729713105990673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17504506183819808737327115 26256759275729713105990673)
              ·
                refine ⟨19692569456797284829493005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26256759275729713105990673 19692569456797284829493005)
                ·
                  refine ⟨7384713546298981811059877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19692569456797284829493005 7384713546298981811059877)
                  ·
                    refine ⟨1384633789931059089573727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384713546298981811059877 1384633789931059089573727)
                    ·
                      rfl

theorem cell23_8089694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_8089694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089694 prefixEnd_8089694 := by exact prefixLift 8089694
  have htrace : WordTrace (prefixWord ++ tailWord_8089694) baseStart_8089694 baseEnd_8089694 := by
    simpa [prefixWord, tailWord_8089694, baseEnd_8089694] using wordTrace_append hprefix tailTrace_8089694
  have hstable : (prefixWord ++ tailWord_8089694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089694).length < 2 ^ (prefixWord ++ tailWord_8089694).sum := by decide
  have hdescent : baseEnd_8089694 < baseStart_8089694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089703 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 1, 5]
def baseStart_8089703 : Nat := 118140960795 + 8089703 * 2 ^ 59
def prefixEnd_8089703 : Nat := 4983230072969 + 3 ^ 40 * 8089703 * 2
def baseEnd_8089703 : Nat := 1384635330373022577836213

theorem tailTrace_8089703 : CollatzResearch.WordTrace tailWord_8089703 prefixEnd_8089703 1384635330373022577836213 := by
  unfold tailWord_8089703
  simp only [CollatzResearch.WordTrace]
  refine ⟨295055708211395117121817763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196703805474263411414545175 295055708211395117121817763)
  ·
    refine ⟨442583562317092675682726645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295055708211395117121817763 442583562317092675682726645)
    ·
      refine ⟨41492208967227438345255623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 442583562317092675682726645 41492208967227438345255623)
      ·
        refine ⟨62238313450841157517883435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41492208967227438345255623 62238313450841157517883435)
        ·
          refine ⟨93357470176261736276825153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62238313450841157517883435 93357470176261736276825153)
          ·
            refine ⟨70018102632196302207618865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93357470176261736276825153 70018102632196302207618865)
            ·
              refine ⟨52513576974147226655714149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70018102632196302207618865 52513576974147226655714149)
              ·
                refine ⟨9846295682652604997946403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52513576974147226655714149 9846295682652604997946403)
                ·
                  refine ⟨14769443523978907496919605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846295682652604997946403 14769443523978907496919605)
                  ·
                    refine ⟨1384635330373022577836213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14769443523978907496919605 1384635330373022577836213)
                    ·
                      rfl

theorem cell23_8089703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_8089703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089703 prefixEnd_8089703 := by exact prefixLift 8089703
  have htrace : WordTrace (prefixWord ++ tailWord_8089703) baseStart_8089703 baseEnd_8089703 := by
    simpa [prefixWord, tailWord_8089703, baseEnd_8089703] using wordTrace_append hprefix tailTrace_8089703
  have hstable : (prefixWord ++ tailWord_8089703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089703).length < 2 ^ (prefixWord ++ tailWord_8089703).sum := by decide
  have hdescent : baseEnd_8089703 < baseStart_8089703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089710 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_8089710 : Nat := 118140960795 + 8089710 * 2 ^ 59
def prefixEnd_8089710 : Nat := 4983230072969 + 3 ^ 40 * 8089710 * 2
def baseEnd_8089710 : Nat := 4153909585483649206121107

theorem tailTrace_8089710 : CollatzResearch.WordTrace tailWord_8089710 prefixEnd_8089710 4153909585483649206121107 := by
  unfold tailWord_8089710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36881995440296219664665323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196703975681579838211548389 36881995440296219664665323)
  ·
    refine ⟨55322993160444329496997985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36881995440296219664665323 55322993160444329496997985)
    ·
      refine ⟨41492244870333247122748489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55322993160444329496997985 41492244870333247122748489)
      ·
        refine ⟨31119183652749935342061367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41492244870333247122748489 31119183652749935342061367)
        ·
          refine ⟨46678775479124903013092051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31119183652749935342061367 46678775479124903013092051)
          ·
            refine ⟨70018163218687354519638077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46678775479124903013092051 70018163218687354519638077)
            ·
              refine ⟨26256811207007757944864279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70018163218687354519638077 26256811207007757944864279)
              ·
                refine ⟨39385216810511636917296419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26256811207007757944864279 39385216810511636917296419)
                ·
                  refine ⟨59077825215767455375944629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39385216810511636917296419 59077825215767455375944629)
                  ·
                    refine ⟨5538546113978198941494809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59077825215767455375944629 5538546113978198941494809)
                    ·
                      refine ⟨4153909585483649206121107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538546113978198941494809 4153909585483649206121107)
                      ·
                        rfl

theorem cell23_8089710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_8089710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089710 prefixEnd_8089710 := by exact prefixLift 8089710
  have htrace : WordTrace (prefixWord ++ tailWord_8089710) baseStart_8089710 baseEnd_8089710 := by
    simpa [prefixWord, tailWord_8089710, baseEnd_8089710] using wordTrace_append hprefix tailTrace_8089710
  have hstable : (prefixWord ++ tailWord_8089710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089710).length < 2 ^ (prefixWord ++ tailWord_8089710).sum := by decide
  have hdescent : baseEnd_8089710 < baseStart_8089710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089757 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_8089757 : Nat := 118140960795 + 8089757 * 2 ^ 59
def prefixEnd_8089757 : Nat := 4983230072969 + 3 ^ 40 * 8089757 * 2
def baseEnd_8089757 : Nat := 4153933719074410522233391

theorem tailTrace_8089757 : CollatzResearch.WordTrace tailWord_8089757 prefixEnd_8089757 4153933719074410522233391 := by
  unfold tailWord_8089757
  simp only [CollatzResearch.WordTrace]
  refine ⟨295057677753199484344283525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196705118502132989562855683 295057677753199484344283525)
  ·
    refine ⟨55323314578724903314553161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295057677753199484344283525 55323314578724903314553161)
    ·
      refine ⟨41492485934043677485914871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55323314578724903314553161 41492485934043677485914871)
      ·
        refine ⟨62238728901065516228872307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41492485934043677485914871 62238728901065516228872307)
        ·
          refine ⟨93358093351598274343308461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62238728901065516228872307 93358093351598274343308461)
          ·
            refine ⟨35009285006849352878740673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93358093351598274343308461 35009285006849352878740673)
            ·
              refine ⟨26256963755137014659055505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35009285006849352878740673 26256963755137014659055505)
              ·
                refine ⟨19692722816352760994291629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26256963755137014659055505 19692722816352760994291629)
                ·
                  refine ⟨7384771056132285372859361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19692722816352760994291629 7384771056132285372859361)
                  ·
                    refine ⟨5538578292099214029644521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7384771056132285372859361 5538578292099214029644521)
                    ·
                      refine ⟨4153933719074410522233391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538578292099214029644521 4153933719074410522233391)
                      ·
                        rfl

theorem cell23_8089757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_8089757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089757 prefixEnd_8089757 := by exact prefixLift 8089757
  have htrace : WordTrace (prefixWord ++ tailWord_8089757) baseStart_8089757 baseEnd_8089757 := by
    simpa [prefixWord, tailWord_8089757, baseEnd_8089757] using wordTrace_append hprefix tailTrace_8089757
  have hstable : (prefixWord ++ tailWord_8089757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089757).length < 2 ^ (prefixWord ++ tailWord_8089757).sum := by decide
  have hdescent : baseEnd_8089757 < baseStart_8089757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089760 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_8089760 : Nat := 118140960795 + 8089760 * 2 ^ 59
def prefixEnd_8089760 : Nat := 4983230072969 + 3 ^ 40 * 8089760 * 2
def baseEnd_8089760 : Nat := 4153935259516374010495877

theorem tailTrace_8089760 : CollatzResearch.WordTrace tailWord_8089760 prefixEnd_8089760 4153935259516374010495877 := by
  unfold tailWord_8089760
  simp only [CollatzResearch.WordTrace]
  refine ⟨147528893586094307928321367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196705191448125743904428489 147528893586094307928321367)
  ·
    refine ⟨221293340379141461892482051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147528893586094307928321367 221293340379141461892482051)
    ·
      refine ⟨331940010568712192838723077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221293340379141461892482051 331940010568712192838723077)
      ·
        refine ⟨62238751981633536157260577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331940010568712192838723077 62238751981633536157260577)
        ·
          refine ⟨46679063986225152117945433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62238751981633536157260577 46679063986225152117945433)
          ·
            refine ⟨35009297989668864088459075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46679063986225152117945433 35009297989668864088459075)
            ·
              refine ⟨52513946984503296132688613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35009297989668864088459075 52513946984503296132688613)
              ·
                refine ⟨9846365059594368024879115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52513946984503296132688613 9846365059594368024879115)
                ·
                  refine ⟨14769547589391552037318673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846365059594368024879115 14769547589391552037318673)
                  ·
                    refine ⟨11077160692043664027989005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14769547589391552037318673 11077160692043664027989005)
                    ·
                      refine ⟨4153935259516374010495877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11077160692043664027989005 4153935259516374010495877)
                      ·
                        rfl

theorem cell23_8089760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_8089760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089760 prefixEnd_8089760 := by exact prefixLift 8089760
  have htrace : WordTrace (prefixWord ++ tailWord_8089760) baseStart_8089760 baseEnd_8089760 := by
    simpa [prefixWord, tailWord_8089760, baseEnd_8089760] using wordTrace_append hprefix tailTrace_8089760
  have hstable : (prefixWord ++ tailWord_8089760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089760).length < 2 ^ (prefixWord ++ tailWord_8089760).sum := by decide
  have hdescent : baseEnd_8089760 < baseStart_8089760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089800 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_8089800 : Nat := 118140960795 + 8089800 * 2 ^ 59
def prefixEnd_8089800 : Nat := 4983230072969 + 3 ^ 40 * 8089800 * 2
def baseEnd_8089800 : Nat := 4153955798742553853995693

theorem tailTrace_8089800 : CollatzResearch.WordTrace tailWord_8089800 prefixEnd_8089800 4153955798742553853995693 := by
  unfold tailWord_8089800
  simp only [CollatzResearch.WordTrace]
  refine ⟨147529623046021851344049427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196706164061362468458732569 147529623046021851344049427)
  ·
    refine ⟨221294434569032777016074141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147529623046021851344049427 221294434569032777016074141)
    ·
      refine ⟨82985412963387291381027803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221294434569032777016074141 82985412963387291381027803)
      ·
        refine ⟨124478119445080937071541705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82985412963387291381027803 124478119445080937071541705)
        ·
          refine ⟨93358589583810702803656279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124478119445080937071541705 93358589583810702803656279)
          ·
            refine ⟨140037884375716054205484419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93358589583810702803656279 140037884375716054205484419)
            ·
              refine ⟨210056826563574081308226629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140037884375716054205484419 210056826563574081308226629)
              ·
                refine ⟨39385654980670140245292493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210056826563574081308226629 39385654980670140245292493)
                ·
                  refine ⟨14769620617751302591984685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39385654980670140245292493 14769620617751302591984685)
                  ·
                    refine ⟨5538607731656738471994257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14769620617751302591984685 5538607731656738471994257)
                    ·
                      refine ⟨4153955798742553853995693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538607731656738471994257 4153955798742553853995693)
                      ·
                        rfl

theorem cell23_8089800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_8089800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089800 prefixEnd_8089800 := by exact prefixLift 8089800
  have htrace : WordTrace (prefixWord ++ tailWord_8089800) baseStart_8089800 baseEnd_8089800 := by
    simpa [prefixWord, tailWord_8089800, baseEnd_8089800] using wordTrace_append hprefix tailTrace_8089800
  have hstable : (prefixWord ++ tailWord_8089800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089800).length < 2 ^ (prefixWord ++ tailWord_8089800).sum := by decide
  have hdescent : baseEnd_8089800 < baseStart_8089800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089817 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 1, 3, 2]
def baseStart_8089817 : Nat := 118140960795 + 8089817 * 2 ^ 59
def prefixEnd_8089817 : Nat := 4983230072969 + 3 ^ 40 * 8089817 * 2
def baseEnd_8089817 : Nat := 4153964527913680287483115

theorem tailTrace_8089817 : CollatzResearch.WordTrace tailWord_8089817 prefixEnd_8089817 4153964527913680287483115 := by
  unfold tailWord_8089817
  simp only [CollatzResearch.WordTrace]
  refine ⟨295059866132982114591467705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196706577421988076394311803 295059866132982114591467705)
  ·
    refine ⟨221294899599736585943600779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295059866132982114591467705 221294899599736585943600779)
    ·
      refine ⟨331942349399604878915401169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221294899599736585943600779 331942349399604878915401169)
      ·
        refine ⟨248956762049703659186550877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331942349399604878915401169 248956762049703659186550877)
        ·
          refine ⟨93358785768638872194956579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248956762049703659186550877 93358785768638872194956579)
          ·
            refine ⟨140038178652958308292434869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93358785768638872194956579 140038178652958308292434869)
            ·
              refine ⟨13128579248714841402415769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140038178652958308292434869 13128579248714841402415769)
              ·
                refine ⟨9846434436536131051811827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128579248714841402415769 9846434436536131051811827)
                ·
                  refine ⟨14769651654804196577717741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846434436536131051811827 14769651654804196577717741)
                  ·
                    refine ⟨5538619370551573716644153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14769651654804196577717741 5538619370551573716644153)
                    ·
                      refine ⟨4153964527913680287483115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538619370551573716644153 4153964527913680287483115)
                      ·
                        rfl

theorem cell23_8089817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_8089817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089817 prefixEnd_8089817 := by exact prefixLift 8089817
  have htrace : WordTrace (prefixWord ++ tailWord_8089817) baseStart_8089817 baseEnd_8089817 := by
    simpa [prefixWord, tailWord_8089817, baseEnd_8089817] using wordTrace_append hprefix tailTrace_8089817
  have hstable : (prefixWord ++ tailWord_8089817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089817).length < 2 ^ (prefixWord ++ tailWord_8089817).sum := by decide
  have hdescent : baseEnd_8089817 < baseStart_8089817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089834 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_8089834 : Nat := 118140960795 + 8089834 * 2 ^ 59
def prefixEnd_8089834 : Nat := 4983230072969 + 3 ^ 40 * 8089834 * 2
def baseEnd_8089834 : Nat := 4153973257084806720970537

theorem tailTrace_8089834 : CollatzResearch.WordTrace tailWord_8089834 prefixEnd_8089834 4153973257084806720970537 := by
  unfold tailWord_8089834
  simp only [CollatzResearch.WordTrace]
  refine ⟨73765121543480131623709139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196706990782613684329891037 73765121543480131623709139)
  ·
    refine ⟨110647682315220197435563709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73765121543480131623709139 110647682315220197435563709)
    ·
      refine ⟨41492880868207574038336391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110647682315220197435563709 41492880868207574038336391)
      ·
        refine ⟨62239321302311361057504587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41492880868207574038336391 62239321302311361057504587)
        ·
          refine ⟨93358981953467041586256881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62239321302311361057504587 93358981953467041586256881)
          ·
            refine ⟨70019236465100281189692661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93358981953467041586256881 70019236465100281189692661)
            ·
              refine ⟨6564303418603151361533687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70019236465100281189692661 6564303418603151361533687)
              ·
                refine ⟨9846455127904727042300531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564303418603151361533687 9846455127904727042300531)
                ·
                  refine ⟨14769682691857090563450797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846455127904727042300531 14769682691857090563450797)
                  ·
                    refine ⟨5538631009446408961294049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14769682691857090563450797 5538631009446408961294049)
                    ·
                      refine ⟨4153973257084806720970537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538631009446408961294049 4153973257084806720970537)
                      ·
                        rfl

theorem cell23_8089834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_8089834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089834 prefixEnd_8089834 := by exact prefixLift 8089834
  have htrace : WordTrace (prefixWord ++ tailWord_8089834) baseStart_8089834 baseEnd_8089834 := by
    simpa [prefixWord, tailWord_8089834, baseEnd_8089834] using wordTrace_append hprefix tailTrace_8089834
  have hstable : (prefixWord ++ tailWord_8089834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089834).length < 2 ^ (prefixWord ++ tailWord_8089834).sum := by decide
  have hdescent : baseEnd_8089834 < baseStart_8089834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089843 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_8089843 : Nat := 118140960795 + 8089843 * 2 ^ 59
def prefixEnd_8089843 : Nat := 4983230072969 + 3 ^ 40 * 8089843 * 2
def baseEnd_8089843 : Nat := 4153977878410697185757995

theorem tailTrace_8089843 : CollatzResearch.WordTrace tailWord_8089843 prefixEnd_8089843 4153977878410697185757995 := by
  unfold tailWord_8089843
  simp only [CollatzResearch.WordTrace]
  refine ⟨295060814430887921031914183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196707209620591947354609455 295060814430887921031914183)
  ·
    refine ⟨442591221646331881547871275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295060814430887921031914183 442591221646331881547871275)
    ·
      refine ⟨663886832469497822321806913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442591221646331881547871275 663886832469497822321806913)
      ·
        refine ⟨497915124352123366741355185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663886832469497822321806913 497915124352123366741355185)
        ·
          refine ⟨373436343264092525056016389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497915124352123366741355185 373436343264092525056016389)
          ·
            refine ⟨70019314362017348448003073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373436343264092525056016389 70019314362017348448003073)
            ·
              refine ⟨52514485771513011336002305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70019314362017348448003073 52514485771513011336002305)
              ·
                refine ⟨39385864328634758502001729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52514485771513011336002305 39385864328634758502001729)
                ·
                  refine ⟨29539398246476068876501297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39385864328634758502001729 29539398246476068876501297)
                  ·
                    refine ⟨22154548684857051657375973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29539398246476068876501297 22154548684857051657375973)
                    ·
                      refine ⟨4153977878410697185757995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22154548684857051657375973 4153977878410697185757995)
                      ·
                        rfl

theorem cell23_8089843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_8089843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089843 prefixEnd_8089843 := by exact prefixLift 8089843
  have htrace : WordTrace (prefixWord ++ tailWord_8089843) baseStart_8089843 baseEnd_8089843 := by
    simpa [prefixWord, tailWord_8089843, baseEnd_8089843] using wordTrace_append hprefix tailTrace_8089843
  have hstable : (prefixWord ++ tailWord_8089843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089843).length < 2 ^ (prefixWord ++ tailWord_8089843).sum := by decide
  have hdescent : baseEnd_8089843 < baseStart_8089843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089864 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_8089864 : Nat := 118140960795 + 8089864 * 2 ^ 59
def prefixEnd_8089864 : Nat := 4983230072969 + 3 ^ 40 * 8089864 * 2
def baseEnd_8089864 : Nat := 4153988661504441603595399

theorem tailTrace_8089864 : CollatzResearch.WordTrace tailWord_8089864 prefixEnd_8089864 4153988661504441603595399 := by
  unfold tailWord_8089864
  simp only [CollatzResearch.WordTrace]
  refine ⟨147530790181905920809214323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196707720242541227745619097 147530790181905920809214323)
  ·
    refine ⟨221296185272858881213821485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147530790181905920809214323 221296185272858881213821485)
    ·
      refine ⟨82986069477322080455183057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221296185272858881213821485 82986069477322080455183057)
      ·
        refine ⟨62239552107991560341387293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82986069477322080455183057 62239552107991560341387293)
        ·
          refine ⟨23339832040496835128020235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62239552107991560341387293 23339832040496835128020235)
          ·
            refine ⟨35009748060745252692030353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23339832040496835128020235 35009748060745252692030353)
            ·
              refine ⟨26257311045558939519022765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35009748060745252692030353 26257311045558939519022765)
              ·
                refine ⟨9846491642084602319633537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26257311045558939519022765 9846491642084602319633537)
                ·
                  refine ⟨7384868731563451739725153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846491642084602319633537 7384868731563451739725153)
                  ·
                    refine ⟨5538651548672588804793865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7384868731563451739725153 5538651548672588804793865)
                    ·
                      refine ⟨4153988661504441603595399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538651548672588804793865 4153988661504441603595399)
                      ·
                        rfl

theorem cell23_8089864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_8089864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089864 prefixEnd_8089864 := by exact prefixLift 8089864
  have htrace : WordTrace (prefixWord ++ tailWord_8089864) baseStart_8089864 baseEnd_8089864 := by
    simpa [prefixWord, tailWord_8089864, baseEnd_8089864] using wordTrace_append hprefix tailTrace_8089864
  have hstable : (prefixWord ++ tailWord_8089864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089864).length < 2 ^ (prefixWord ++ tailWord_8089864).sum := by decide
  have hdescent : baseEnd_8089864 < baseStart_8089864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089887 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 5]
def baseStart_8089887 : Nat := 118140960795 + 8089887 * 2 ^ 59
def prefixEnd_8089887 : Nat := 4983230072969 + 3 ^ 40 * 8089887 * 2
def baseEnd_8089887 : Nat := 461555607951055001511977

theorem tailTrace_8089887 : CollatzResearch.WordTrace tailWord_8089887 prefixEnd_8089887 461555607951055001511977 := by
  unfold tailWord_8089887
  simp only [CollatzResearch.WordTrace]
  refine ⟨295062419242728516546515915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196708279495152344364343943 295062419242728516546515915)
  ·
    refine ⟨442593628864092774819773873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295062419242728516546515915 442593628864092774819773873)
    ·
      refine ⟨331945221648069581114830405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442593628864092774819773873 331945221648069581114830405)
      ·
        refine ⟨62239729059013046459030701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331945221648069581114830405 62239729059013046459030701)
        ·
          refine ⟨23339898397129892422136513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62239729059013046459030701 23339898397129892422136513)
          ·
            refine ⟨17504923797847419316602385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23339898397129892422136513 17504923797847419316602385)
            ·
              refine ⟨13128692848385564487451789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17504923797847419316602385 13128692848385564487451789)
              ·
                refine ⟨4923259818144586682794421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13128692848385564487451789 4923259818144586682794421)
                ·
                  refine ⟨461555607951055001511977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4923259818144586682794421 461555607951055001511977)
                  ·
                    rfl

theorem cell23_8089887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 5].length) (baseStart_8089887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089887 prefixEnd_8089887 := by exact prefixLift 8089887
  have htrace : WordTrace (prefixWord ++ tailWord_8089887) baseStart_8089887 baseEnd_8089887 := by
    simpa [prefixWord, tailWord_8089887, baseEnd_8089887] using wordTrace_append hprefix tailTrace_8089887
  have hstable : (prefixWord ++ tailWord_8089887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089887).length < 2 ^ (prefixWord ++ tailWord_8089887).sum := by decide
  have hdescent : baseEnd_8089887 < baseStart_8089887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089898 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_8089898 : Nat := 118140960795 + 8089898 * 2 ^ 59
def prefixEnd_8089898 : Nat := 4983230072969 + 3 ^ 40 * 8089898 * 2
def baseEnd_8089898 : Nat := 4154006119846694470570243

theorem tailTrace_8089898 : CollatzResearch.WordTrace tailWord_8089898 prefixEnd_8089898 4154006119846694470570243 := by
  unfold tailWord_8089898
  simp only [CollatzResearch.WordTrace]
  refine ⟨73765705111422166356291587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196708546963792443616777565 73765705111422166356291587)
  ·
    refine ⟨110648557667133249534437381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73765705111422166356291587 110648557667133249534437381)
    ·
      refine ⟨20746604562587484287707009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110648557667133249534437381 20746604562587484287707009)
      ·
        refine ⟨15559953421940613215780257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20746604562587484287707009 15559953421940613215780257)
        ·
          refine ⟨11669965066455459911835193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15559953421940613215780257 11669965066455459911835193)
          ·
            refine ⟨8752473799841594933876395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11669965066455459911835193 8752473799841594933876395)
            ·
              refine ⟨13128710699762392400814593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752473799841594933876395 13128710699762392400814593)
              ·
                refine ⟨9846533024821794300610945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128710699762392400814593 9846533024821794300610945)
                ·
                  refine ⟨7384899768616345725458209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846533024821794300610945 7384899768616345725458209)
                  ·
                    refine ⟨5538674826462259294093657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7384899768616345725458209 5538674826462259294093657)
                    ·
                      refine ⟨4154006119846694470570243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538674826462259294093657 4154006119846694470570243)
                      ·
                        rfl

theorem cell23_8089898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_8089898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089898 prefixEnd_8089898 := by exact prefixLift 8089898
  have htrace : WordTrace (prefixWord ++ tailWord_8089898) baseStart_8089898 baseEnd_8089898 := by
    simpa [prefixWord, tailWord_8089898, baseEnd_8089898] using wordTrace_append hprefix tailTrace_8089898
  have hstable : (prefixWord ++ tailWord_8089898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089898).length < 2 ^ (prefixWord ++ tailWord_8089898).sum := by decide
  have hdescent : baseEnd_8089898 < baseStart_8089898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089920 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2]
def baseStart_8089920 : Nat := 118140960795 + 8089920 * 2 ^ 59
def prefixEnd_8089920 : Nat := 4983230072969 + 3 ^ 40 * 8089920 * 2
def baseEnd_8089920 : Nat := 4154017416421093384495141

theorem tailTrace_8089920 : CollatzResearch.WordTrace tailWord_8089920 prefixEnd_8089920 4154017416421093384495141 := by
  unfold tailWord_8089920
  simp only [CollatzResearch.WordTrace]
  refine ⟨147531811425804481591233607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196709081901072642121644809 147531811425804481591233607)
  ·
    refine ⟨221297717138706722386850411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147531811425804481591233607 221297717138706722386850411)
    ·
      refine ⟨331946575708060083580275617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221297717138706722386850411 331946575708060083580275617)
      ·
        refine ⟨248959931781045062685206713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331946575708060083580275617 248959931781045062685206713)
        ·
          refine ⟨186719948835783797013905035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248959931781045062685206713 186719948835783797013905035)
          ·
            refine ⟨280079923253675695520857553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186719948835783797013905035 280079923253675695520857553)
            ·
              refine ⟨210059942440256771640643165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280079923253675695520857553 210059942440256771640643165)
              ·
                refine ⟨78772478415096289365241187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210059942440256771640643165 78772478415096289365241187)
                ·
                  refine ⟨118158717622644434047861781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78772478415096289365241187 118158717622644434047861781)
                  ·
                    refine ⟨5538689888561457845993521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118158717622644434047861781 5538689888561457845993521)
                    ·
                      refine ⟨4154017416421093384495141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538689888561457845993521 4154017416421093384495141)
                      ·
                        rfl

theorem cell23_8089920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_8089920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089920 prefixEnd_8089920 := by exact prefixLift 8089920
  have htrace : WordTrace (prefixWord ++ tailWord_8089920) baseStart_8089920 baseEnd_8089920 := by
    simpa [prefixWord, tailWord_8089920, baseEnd_8089920] using wordTrace_append hprefix tailTrace_8089920
  have hstable : (prefixWord ++ tailWord_8089920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089920).length < 2 ^ (prefixWord ++ tailWord_8089920).sum := by decide
  have hdescent : baseEnd_8089920 < baseStart_8089920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089943 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 10]
def baseStart_8089943 : Nat := 118140960795 + 8089943 * 2 ^ 59
def prefixEnd_8089943 : Nat := 4983230072969 + 3 ^ 40 * 8089943 * 2
def baseEnd_8089943 : Nat := 461558802941794088278615

theorem tailTrace_8089943 : CollatzResearch.WordTrace tailWord_8089943 prefixEnd_8089943 461558802941794088278615 := by
  unfold tailWord_8089943
  simp only [CollatzResearch.WordTrace]
  refine ⟨295064461730525638110554483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196709641153683758740369655 295064461730525638110554483)
  ·
    refine ⟨442596692595788457165831725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295064461730525638110554483 442596692595788457165831725)
    ·
      refine ⟨165973759723420671437186897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442596692595788457165831725 165973759723420671437186897)
      ·
        refine ⟨124480319792565503577890173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165973759723420671437186897 124480319792565503577890173)
        ·
          refine ⟨46680119922212063841708815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124480319792565503577890173 46680119922212063841708815)
          ·
            refine ⟨70020179883318095762563223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46680119922212063841708815 70020179883318095762563223)
            ·
              refine ⟨105030269824977143643844835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70020179883318095762563223 105030269824977143643844835)
              ·
                refine ⟨157545404737465715465767253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105030269824977143643844835 157545404737465715465767253)
                ·
                  refine ⟨461558802941794088278615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157545404737465715465767253 461558802941794088278615)
                  ·
                    rfl

theorem cell23_8089943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 10].length) (baseStart_8089943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089943 prefixEnd_8089943 := by exact prefixLift 8089943
  have htrace : WordTrace (prefixWord ++ tailWord_8089943) baseStart_8089943 baseEnd_8089943 := by
    simpa [prefixWord, tailWord_8089943, baseEnd_8089943] using wordTrace_append hprefix tailTrace_8089943
  have hstable : (prefixWord ++ tailWord_8089943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089943).length < 2 ^ (prefixWord ++ tailWord_8089943).sum := by decide
  have hdescent : baseEnd_8089943 < baseStart_8089943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089957 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_8089957 : Nat := 118140960795 + 8089957 * 2 ^ 59
def prefixEnd_8089957 : Nat := 4983230072969 + 3 ^ 40 * 8089957 * 2
def baseEnd_8089957 : Nat := 4154036415205309739732471

theorem tailTrace_8089957 : CollatzResearch.WordTrace tailWord_8089957 prefixEnd_8089957 4154036415205309739732471 := by
  unfold tailWord_8089957
  simp only [CollatzResearch.WordTrace]
  refine ⟨295064972352474918501564125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196709981568316612334376083 295064972352474918501564125)
  ·
    refine ⟨110649364632178094438086547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295064972352474918501564125 110649364632178094438086547)
    ·
      refine ⟨165974046948267141657129821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110649364632178094438086547 165974046948267141657129821)
      ·
        refine ⟨62240267605600178121423683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165974046948267141657129821 62240267605600178121423683)
        ·
          refine ⟨93360401408400267182135525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62240267605600178121423683 93360401408400267182135525)
          ·
            refine ⟨17505075264075050096650411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93360401408400267182135525 17505075264075050096650411)
            ·
              refine ⟨26257612896112575144975617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17505075264075050096650411 26257612896112575144975617)
              ·
                refine ⟨19693209672084431358731713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26257612896112575144975617 19693209672084431358731713)
                ·
                  refine ⟨14769907254063323519048785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19693209672084431358731713 14769907254063323519048785)
                  ·
                    refine ⟨11077430440547492639286589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14769907254063323519048785 11077430440547492639286589)
                    ·
                      refine ⟨4154036415205309739732471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11077430440547492639286589 4154036415205309739732471)
                      ·
                        rfl

theorem cell23_8089957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_8089957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089957 prefixEnd_8089957 := by exact prefixLift 8089957
  have htrace : WordTrace (prefixWord ++ tailWord_8089957) baseStart_8089957 baseEnd_8089957 := by
    simpa [prefixWord, tailWord_8089957, baseEnd_8089957] using wordTrace_append hprefix tailTrace_8089957
  have hstable : (prefixWord ++ tailWord_8089957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089957).length < 2 ^ (prefixWord ++ tailWord_8089957).sum := by decide
  have hdescent : baseEnd_8089957 < baseStart_8089957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089960 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 8]
def baseStart_8089960 : Nat := 118140960795 + 8089960 * 2 ^ 59
def prefixEnd_8089960 : Nat := 4983230072969 + 3 ^ 40 * 8089960 * 2
def baseEnd_8089960 : Nat := 461559772849697025332773

theorem tailTrace_8089960 : CollatzResearch.WordTrace tailWord_8089960 prefixEnd_8089960 461559772849697025332773 := by
  unfold tailWord_8089960
  simp only [CollatzResearch.WordTrace]
  refine ⟨147532540885732025006961667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196710054514309366675948889 147532540885732025006961667)
  ·
    refine ⟨221298811328598037510442501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147532540885732025006961667 221298811328598037510442501)
    ·
      refine ⟨41493527124112132033207969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221298811328598037510442501 41493527124112132033207969)
      ·
        refine ⟨31120145343084099024905977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41493527124112132033207969 31120145343084099024905977)
        ·
          refine ⟨23340109007313074268679483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31120145343084099024905977 23340109007313074268679483)
          ·
            refine ⟨35010163510969611403019225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23340109007313074268679483 35010163510969611403019225)
            ·
              refine ⟨26257622633227208552264419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35010163510969611403019225 26257622633227208552264419)
              ·
                refine ⟨39386433949840812828396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26257622633227208552264419 39386433949840812828396629)
                ·
                  refine ⟨461559772849697025332773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39386433949840812828396629 461559772849697025332773)
                  ·
                    rfl

theorem cell23_8089960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_8089960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089960 prefixEnd_8089960 := by exact prefixLift 8089960
  have htrace : WordTrace (prefixWord ++ tailWord_8089960) baseStart_8089960 baseEnd_8089960 := by
    simpa [prefixWord, tailWord_8089960, baseEnd_8089960] using wordTrace_append hprefix tailTrace_8089960
  have hstable : (prefixWord ++ tailWord_8089960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089960).length < 2 ^ (prefixWord ++ tailWord_8089960).sum := by decide
  have hdescent : baseEnd_8089960 < baseStart_8089960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089964 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_8089964 : Nat := 118140960795 + 8089964 * 2 ^ 59
def prefixEnd_8089964 : Nat := 4983230072969 + 3 ^ 40 * 8089964 * 2
def baseEnd_8089964 : Nat := 1384680003189963737448313

theorem tailTrace_8089964 : CollatzResearch.WordTrace tailWord_8089964 prefixEnd_8089964 1384680003189963737448313 := by
  unfold tailWord_8089964
  simp only [CollatzResearch.WordTrace]
  refine ⟨147532613831724779348534473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196710151775633039131379297 147532613831724779348534473)
  ·
    refine ⟨110649460373793584511400855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147532613831724779348534473 110649460373793584511400855)
    ·
      refine ⟨165974190560690376767101283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110649460373793584511400855 165974190560690376767101283)
      ·
        refine ⟨248961285841035565150651925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165974190560690376767101283 248961285841035565150651925)
        ·
          refine ⟨11670060273798542116436809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248961285841035565150651925 11670060273798542116436809)
          ·
            refine ⟨8752545205348906587327607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11670060273798542116436809 8752545205348906587327607)
            ·
              refine ⟨13128817808023359880991411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752545205348906587327607 13128817808023359880991411)
              ·
                refine ⟨19693226712035039821487117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13128817808023359880991411 19693226712035039821487117)
                ·
                  refine ⟨7384960017013139933057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19693226712035039821487117 7384960017013139933057669)
                  ·
                    refine ⟨1384680003189963737448313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384960017013139933057669 1384680003189963737448313)
                    ·
                      rfl

theorem cell23_8089964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_8089964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089964 prefixEnd_8089964 := by exact prefixLift 8089964
  have htrace : WordTrace (prefixWord ++ tailWord_8089964) baseStart_8089964 baseEnd_8089964 := by
    simpa [prefixWord, tailWord_8089964, baseEnd_8089964] using wordTrace_append hprefix tailTrace_8089964
  have hstable : (prefixWord ++ tailWord_8089964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089964).length < 2 ^ (prefixWord ++ tailWord_8089964).sum := by decide
  have hdescent : baseEnd_8089964 < baseStart_8089964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8089983 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_8089983 : Nat := 118140960795 + 8089983 * 2 ^ 59
def prefixEnd_8089983 : Nat := 4983230072969 + 3 ^ 40 * 8089983 * 2
def baseEnd_8089983 : Nat := 4154049765702326638007351

theorem tailTrace_8089983 : CollatzResearch.WordTrace tailWord_8089983 prefixEnd_8089983 4154049765702326638007351 := by
  unfold tailWord_8089983
  simp only [CollatzResearch.WordTrace]
  refine ⟨295065920650380724942010603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196710613766920483294673735 295065920650380724942010603)
  ·
    refine ⟨442598880975571087413015905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295065920650380724942010603 442598880975571087413015905)
    ·
      refine ⟨331949160731678315559761929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442598880975571087413015905 331949160731678315559761929)
      ·
        refine ⟨248961870548758736669821447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331949160731678315559761929 248961870548758736669821447)
        ·
          refine ⟨373442805823138105004732171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248961870548758736669821447 373442805823138105004732171)
          ·
            refine ⟨560164208734707157507098257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373442805823138105004732171 560164208734707157507098257)
            ·
              refine ⟨420123156551030368130323693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560164208734707157507098257 420123156551030368130323693)
              ·
                refine ⟨157546183706636388048871385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420123156551030368130323693 157546183706636388048871385)
                ·
                  refine ⟨118159637779977291036653539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157546183706636388048871385 118159637779977291036653539)
                  ·
                    refine ⟨177239456669965936554980309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118159637779977291036653539 177239456669965936554980309)
                    ·
                      refine ⟨4154049765702326638007351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177239456669965936554980309 4154049765702326638007351)
                      ·
                        rfl

theorem cell23_8089983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_8089983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8089983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8089983 prefixEnd_8089983 := by exact prefixLift 8089983
  have htrace : WordTrace (prefixWord ++ tailWord_8089983) baseStart_8089983 baseEnd_8089983 := by
    simpa [prefixWord, tailWord_8089983, baseEnd_8089983] using wordTrace_append hprefix tailTrace_8089983
  have hstable : (prefixWord ++ tailWord_8089983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8089983).length < 2 ^ (prefixWord ++ tailWord_8089983).sum := by decide
  have hdescent : baseEnd_8089983 < baseStart_8089983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8089983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090094 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_8090094 : Nat := 118140960795 + 8090094 * 2 ^ 59
def prefixEnd_8090094 : Nat := 4983230072969 + 3 ^ 40 * 8090094 * 2
def baseEnd_8090094 : Nat := 4154106762054975703719341

theorem tailTrace_8090094 : CollatzResearch.WordTrace tailWord_8090094 prefixEnd_8090094 4154106762054975703719341 := by
  unfold tailWord_8090094
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883746144122323862412667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196713312768652393932867557 36883746144122323862412667)
  ·
    refine ⟨55325619216183485793619001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36883746144122323862412667 55325619216183485793619001)
    ·
      refine ⟨41494214412137614345214251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55325619216183485793619001 41494214412137614345214251)
      ·
        refine ⟨62241321618206421517821377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41494214412137614345214251 62241321618206421517821377)
        ·
          refine ⟨46680991213654816138366033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62241321618206421517821377 46680991213654816138366033)
          ·
            refine ⟨35010743410241112103774525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46680991213654816138366033 35010743410241112103774525)
            ·
              refine ⟨13129028778840417038915447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35010743410241112103774525 13129028778840417038915447)
              ·
                refine ⟨19693543168260625558373171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129028778840417038915447 19693543168260625558373171)
                ·
                  refine ⟨29540314752390938337559757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19693543168260625558373171 29540314752390938337559757)
                  ·
                    refine ⟨11077618032146601876584909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29540314752390938337559757 11077618032146601876584909)
                    ·
                      refine ⟨4154106762054975703719341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11077618032146601876584909 4154106762054975703719341)
                      ·
                        rfl

theorem cell23_8090094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_8090094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090094 prefixEnd_8090094 := by exact prefixLift 8090094
  have htrace : WordTrace (prefixWord ++ tailWord_8090094) baseStart_8090094 baseEnd_8090094 := by
    simpa [prefixWord, tailWord_8090094, baseEnd_8090094] using wordTrace_append hprefix tailTrace_8090094
  have hstable : (prefixWord ++ tailWord_8090094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090094).length < 2 ^ (prefixWord ++ tailWord_8090094).sum := by decide
  have hdescent : baseEnd_8090094 < baseStart_8090094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090101 : List Nat := [1, 3, 5, 1, 2, 2, 2, 7]
def baseStart_8090101 : Nat := 118140960795 + 8090101 * 2 ^ 59
def prefixEnd_8090101 : Nat := 4983230072969 + 3 ^ 40 * 8090101 * 2
def baseEnd_8090101 : Nat := 153855939126650265790067

theorem tailTrace_8090101 : CollatzResearch.WordTrace tailWord_8090101 prefixEnd_8090101 153855939126650265790067 := by
  unfold tailWord_8090101
  simp only [CollatzResearch.WordTrace]
  refine ⟨295070224463953231094806157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196713482975968820729870771 295070224463953231094806157)
  ·
    refine ⟨110651334173982461660552309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295070224463953231094806157 110651334173982461660552309)
    ·
      refine ⟨10373562578810855780676779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110651334173982461660552309 10373562578810855780676779)
      ·
        refine ⟨15560343868216283671015169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10373562578810855780676779 15560343868216283671015169)
        ·
          refine ⟨11670257901162212753261377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15560343868216283671015169 11670257901162212753261377)
          ·
            refine ⟨8752693425871659564946033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11670257901162212753261377 8752693425871659564946033)
            ·
              refine ⟨6564520069403744673709525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8752693425871659564946033 6564520069403744673709525)
              ·
                refine ⟨153855939126650265790067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6564520069403744673709525 153855939126650265790067)
                ·
                  rfl

theorem cell23_8090101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 7].length) (baseStart_8090101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090101 prefixEnd_8090101 := by exact prefixLift 8090101
  have htrace : WordTrace (prefixWord ++ tailWord_8090101) baseStart_8090101 baseEnd_8090101 := by
    simpa [prefixWord, tailWord_8090101, baseEnd_8090101] using wordTrace_append hprefix tailTrace_8090101
  have hstable : (prefixWord ++ tailWord_8090101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090101).length < 2 ^ (prefixWord ++ tailWord_8090101).sum := by decide
  have hdescent : baseEnd_8090101 < baseStart_8090101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090187 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 2, 5]
def baseStart_8090187 : Nat := 118140960795 + 8090187 * 2 ^ 59
def prefixEnd_8090187 : Nat := 4983230072969 + 3 ^ 40 * 8090187 * 2
def baseEnd_8090187 : Nat := 1384718171918614613285471

theorem tailTrace_8090187 : CollatzResearch.WordTrace tailWord_8090187 prefixEnd_8090187 1384718171918614613285471 := by
  unfold tailWord_8090187
  simp only [CollatzResearch.WordTrace]
  refine ⟨295073361141641667782436815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196715574094427778521624543 295073361141641667782436815)
  ·
    refine ⟨442610041712462501673655223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295073361141641667782436815 442610041712462501673655223)
    ·
      refine ⟨663915062568693752510482835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442610041712462501673655223 663915062568693752510482835)
      ·
        refine ⟨995872593853040628765724253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663915062568693752510482835 995872593853040628765724253)
        ·
          refine ⟨373452222694890235787146595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 995872593853040628765724253 373452222694890235787146595)
          ·
            refine ⟨560178334042335353680719893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373452222694890235787146595 560178334042335353680719893)
            ·
              refine ⟨26258359408234469703783745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560178334042335353680719893 26258359408234469703783745)
              ·
                refine ⟨19693769556175852277837809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26258359408234469703783745 19693769556175852277837809)
                ·
                  refine ⟨14770327167131889208378357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19693769556175852277837809 14770327167131889208378357)
                  ·
                    refine ⟨1384718171918614613285471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14770327167131889208378357 1384718171918614613285471)
                    ·
                      rfl

theorem cell23_8090187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 5].length) (baseStart_8090187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090187 prefixEnd_8090187 := by exact prefixLift 8090187
  have htrace : WordTrace (prefixWord ++ tailWord_8090187) baseStart_8090187 baseEnd_8090187 := by
    simpa [prefixWord, tailWord_8090187, baseEnd_8090187] using wordTrace_append hprefix tailTrace_8090187
  have hstable : (prefixWord ++ tailWord_8090187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090187).length < 2 ^ (prefixWord ++ tailWord_8090187).sum := by decide
  have hdescent : baseEnd_8090187 < baseStart_8090187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090194 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_8090194 : Nat := 118140960795 + 8090194 * 2 ^ 59
def prefixEnd_8090194 : Nat := 4983230072969 + 3 ^ 40 * 8090194 * 2
def baseEnd_8090194 : Nat := 4154158110120425312468881

theorem tailTrace_8090194 : CollatzResearch.WordTrace tailWord_8090194 prefixEnd_8090194 4154158110120425312468881 := by
  unfold tailWord_8090194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73768404113154076994485409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196715744301744205318627757 73768404113154076994485409)
  ·
    refine ⟨55326303084865557745864057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73768404113154076994485409 55326303084865557745864057)
    ·
      refine ⟨41494727313649168309398043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55326303084865557745864057 41494727313649168309398043)
      ·
        refine ⟨62242090970473752464097065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41494727313649168309398043 62242090970473752464097065)
        ·
          refine ⟨46681568227855314348072799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62242090970473752464097065 46681568227855314348072799)
          ·
            refine ⟨70022352341782971522109199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46681568227855314348072799 70022352341782971522109199)
            ·
              refine ⟨105033528512674457283163799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70022352341782971522109199 105033528512674457283163799)
              ·
                refine ⟨157550292769011685924745699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105033528512674457283163799 157550292769011685924745699)
                ·
                  refine ⟨236325439153517528887118549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157550292769011685924745699 236325439153517528887118549)
                  ·
                    refine ⟨5538877480160567083291841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236325439153517528887118549 5538877480160567083291841)
                    ·
                      refine ⟨4154158110120425312468881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538877480160567083291841 4154158110120425312468881)
                      ·
                        rfl

theorem cell23_8090194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_8090194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090194 prefixEnd_8090194 := by exact prefixLift 8090194
  have htrace : WordTrace (prefixWord ++ tailWord_8090194) baseStart_8090194 baseEnd_8090194 := by
    simpa [prefixWord, tailWord_8090194, baseEnd_8090194] using wordTrace_append hprefix tailTrace_8090194
  have hstable : (prefixWord ++ tailWord_8090194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090194).length < 2 ^ (prefixWord ++ tailWord_8090194).sum := by decide
  have hdescent : baseEnd_8090194 < baseStart_8090194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090197 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_8090197 : Nat := 118140960795 + 8090197 * 2 ^ 59
def prefixEnd_8090197 : Nat := 4983230072969 + 3 ^ 40 * 8090197 * 2
def baseEnd_8090197 : Nat := 4154159650562388800731367

theorem tailTrace_8090197 : CollatzResearch.WordTrace tailWord_8090197 prefixEnd_8090197 4154159650562388800731367 := by
  unfold tailWord_8090197
  simp only [CollatzResearch.WordTrace]
  refine ⟨295073725871605439490300845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196715817247736959660200563 295073725871605439490300845)
  ·
    refine ⟨110652647201852039808862817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295073725871605439490300845 110652647201852039808862817)
    ·
      refine ⟨82989485401389029856647113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110652647201852039808862817 82989485401389029856647113)
      ·
        refine ⟨62242114051041772392485335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82989485401389029856647113 62242114051041772392485335)
        ·
          refine ⟨93363171076562658588728003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62242114051041772392485335 93363171076562658588728003)
          ·
            refine ⟨140044756614843987883092005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93363171076562658588728003 140044756614843987883092005)
            ·
              refine ⟨26258391865283247728079751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140044756614843987883092005 26258391865283247728079751)
              ·
                refine ⟨39387587797924871592119627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26258391865283247728079751 39387587797924871592119627)
                ·
                  refine ⟨59081381696887307388179441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39387587797924871592119627 59081381696887307388179441)
                  ·
                    refine ⟨44311036272665480541134581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59081381696887307388179441 44311036272665480541134581)
                    ·
                      refine ⟨4154159650562388800731367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44311036272665480541134581 4154159650562388800731367)
                      ·
                        rfl

theorem cell23_8090197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_8090197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090197 prefixEnd_8090197 := by exact prefixLift 8090197
  have htrace : WordTrace (prefixWord ++ tailWord_8090197) baseStart_8090197 baseEnd_8090197 := by
    simpa [prefixWord, tailWord_8090197, baseEnd_8090197] using wordTrace_append hprefix tailTrace_8090197
  have hstable : (prefixWord ++ tailWord_8090197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090197).length < 2 ^ (prefixWord ++ tailWord_8090197).sum := by decide
  have hdescent : baseEnd_8090197 < baseStart_8090197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090207 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_8090207 : Nat := 118140960795 + 8090207 * 2 ^ 59
def prefixEnd_8090207 : Nat := 4983230072969 + 3 ^ 40 * 8090207 * 2
def baseEnd_8090207 : Nat := 4154164785368933761606321

theorem tailTrace_8090207 : CollatzResearch.WordTrace tailWord_8090207 prefixEnd_8090207 4154164785368933761606321 := by
  unfold tailWord_8090207
  simp only [CollatzResearch.WordTrace]
  refine ⟨295074090601569211198164875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196716060401046140798776583 295074090601569211198164875)
  ·
    refine ⟨442611135902353816797247313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295074090601569211198164875 442611135902353816797247313)
    ·
      refine ⟨331958351926765362597935485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442611135902353816797247313 331958351926765362597935485)
      ·
        refine ⟨124484381972537010974225807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331958351926765362597935485 124484381972537010974225807)
        ·
          refine ⟨186726572958805516461338711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124484381972537010974225807 186726572958805516461338711)
          ·
            refine ⟨280089859438208274692008067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186726572958805516461338711 280089859438208274692008067)
            ·
              refine ⟨420134789157312412038012101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280089859438208274692008067 420134789157312412038012101)
              ·
                refine ⟨78775272966996077257127269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420134789157312412038012101 78775272966996077257127269)
                ·
                  refine ⟨14770363681311764485711363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78775272966996077257127269 14770363681311764485711363)
                  ·
                    refine ⟨22155545521967646728567045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14770363681311764485711363 22155545521967646728567045)
                    ·
                      refine ⟨4154164785368933761606321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22155545521967646728567045 4154164785368933761606321)
                      ·
                        rfl

theorem cell23_8090207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_8090207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090207 prefixEnd_8090207 := by exact prefixLift 8090207
  have htrace : WordTrace (prefixWord ++ tailWord_8090207) baseStart_8090207 baseEnd_8090207 := by
    simpa [prefixWord, tailWord_8090207, baseEnd_8090207] using wordTrace_append hprefix tailTrace_8090207
  have hstable : (prefixWord ++ tailWord_8090207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090207).length < 2 ^ (prefixWord ++ tailWord_8090207).sum := by decide
  have hdescent : baseEnd_8090207 < baseStart_8090207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090221 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_8090221 : Nat := 118140960795 + 8090221 * 2 ^ 59
def prefixEnd_8090221 : Nat := 4983230072969 + 3 ^ 40 * 8090221 * 2
def baseEnd_8090221 : Nat := 1384723991366032235610419

theorem tailTrace_8090221 : CollatzResearch.WordTrace tailWord_8090221 prefixEnd_8090221 1384723991366032235610419 := by
  unfold tailWord_8090221
  simp only [CollatzResearch.WordTrace]
  refine ⟨295074601223518491589174517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196716400815678994392783011 295074601223518491589174517)
  ·
    refine ⟨27663243864704858586485111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295074601223518491589174517 27663243864704858586485111)
    ·
      refine ⟨41494865797057287879727667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27663243864704858586485111 41494865797057287879727667)
      ·
        refine ⟨62242298695585931819591501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41494865797057287879727667 62242298695585931819591501)
        ·
          refine ⟨23340862010844724432346813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62242298695585931819591501 23340862010844724432346813)
          ·
            refine ⟨8752823254066771662130055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23340862010844724432346813 8752823254066771662130055)
            ·
              refine ⟨13129234881100157493195083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752823254066771662130055 13129234881100157493195083)
              ·
                refine ⟨19693852321650236239792625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129234881100157493195083 19693852321650236239792625)
                ·
                  refine ⟨14770389241237677179844469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19693852321650236239792625 14770389241237677179844469)
                  ·
                    refine ⟨1384723991366032235610419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14770389241237677179844469 1384723991366032235610419)
                    ·
                      rfl

theorem cell23_8090221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_8090221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090221 prefixEnd_8090221 := by exact prefixLift 8090221
  have htrace : WordTrace (prefixWord ++ tailWord_8090221) baseStart_8090221 baseEnd_8090221 := by
    simpa [prefixWord, tailWord_8090221, baseEnd_8090221] using wordTrace_append hprefix tailTrace_8090221
  have hstable : (prefixWord ++ tailWord_8090221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090221).length < 2 ^ (prefixWord ++ tailWord_8090221).sum := by decide
  have hdescent : baseEnd_8090221 < baseStart_8090221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090224 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_8090224 : Nat := 118140960795 + 8090224 * 2 ^ 59
def prefixEnd_8090224 : Nat := 4983230072969 + 3 ^ 40 * 8090224 * 2
def baseEnd_8090224 : Nat := 4154173514540060195093743

theorem tailTrace_8090224 : CollatzResearch.WordTrace tailWord_8090224 prefixEnd_8090224 4154173514540060195093743 := by
  unfold tailWord_8090224
  simp only [CollatzResearch.WordTrace]
  refine ⟨147537355321253811550766863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196716473761671748734355817 147537355321253811550766863)
  ·
    refine ⟨221306032981880717326150295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147537355321253811550766863 221306032981880717326150295)
    ·
      refine ⟨331959049472821075989225443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221306032981880717326150295 331959049472821075989225443)
      ·
        refine ⟨497938574209231613983838165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331959049472821075989225443 497938574209231613983838165)
        ·
          refine ⟨11670435333028865952746207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 497938574209231613983838165 11670435333028865952746207)
          ·
            refine ⟨17505652999543298929119311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670435333028865952746207 17505652999543298929119311)
            ·
              refine ⟨26258479499314948393678967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17505652999543298929119311 26258479499314948393678967)
              ·
                refine ⟨39387719248972422590518451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26258479499314948393678967 39387719248972422590518451)
                ·
                  refine ⟨59081578873458633885777677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39387719248972422590518451 59081578873458633885777677)
                  ·
                    refine ⟨22155592077546987707166629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59081578873458633885777677 22155592077546987707166629)
                    ·
                      refine ⟨4154173514540060195093743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22155592077546987707166629 4154173514540060195093743)
                      ·
                        rfl

theorem cell23_8090224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_8090224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090224 prefixEnd_8090224 := by exact prefixLift 8090224
  have htrace : WordTrace (prefixWord ++ tailWord_8090224) baseStart_8090224 baseEnd_8090224 := by
    simpa [prefixWord, tailWord_8090224, baseEnd_8090224] using wordTrace_append hprefix tailTrace_8090224
  have hstable : (prefixWord ++ tailWord_8090224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090224).length < 2 ^ (prefixWord ++ tailWord_8090224).sum := by decide
  have hdescent : baseEnd_8090224 < baseStart_8090224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090247 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 8]
def baseStart_8090247 : Nat := 118140960795 + 8090247 * 2 ^ 59
def prefixEnd_8090247 : Nat := 4983230072969 + 3 ^ 40 * 8090247 * 2
def baseEnd_8090247 : Nat := 461576147177234845011793

theorem tailTrace_8090247 : CollatzResearch.WordTrace tailWord_8090247 prefixEnd_8090247 461576147177234845011793 := by
  unfold tailWord_8090247
  simp only [CollatzResearch.WordTrace]
  refine ⟨295075549521424298029620995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196717033014282865353080663 295075549521424298029620995)
  ·
    refine ⟨442613324282136447044431493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295075549521424298029620995 442613324282136447044431493)
    ·
      refine ⟨82989998302900583820830905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442613324282136447044431493 82989998302900583820830905)
      ·
        refine ⟨62242498727175437865623179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82989998302900583820830905 62242498727175437865623179)
        ·
          refine ⟨93363748090763156798434769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62242498727175437865623179 93363748090763156798434769)
          ·
            refine ⟨70022811068072367598826077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93363748090763156798434769 70022811068072367598826077)
            ·
              refine ⟨26258554150527137849559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70022811068072367598826077 26258554150527137849559779)
              ·
                refine ⟨39387831225790706774339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26258554150527137849559779 39387831225790706774339669)
                ·
                  refine ⟨461576147177234845011793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39387831225790706774339669 461576147177234845011793)
                  ·
                    rfl

theorem cell23_8090247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 8].length) (baseStart_8090247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090247 prefixEnd_8090247 := by exact prefixLift 8090247
  have htrace : WordTrace (prefixWord ++ tailWord_8090247) baseStart_8090247 baseEnd_8090247 := by
    simpa [prefixWord, tailWord_8090247, baseEnd_8090247] using wordTrace_append hprefix tailTrace_8090247
  have hstable : (prefixWord ++ tailWord_8090247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090247).length < 2 ^ (prefixWord ++ tailWord_8090247).sum := by decide
  have hdescent : baseEnd_8090247 < baseStart_8090247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090285 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_8090285 : Nat := 118140960795 + 8090285 * 2 ^ 59
def prefixEnd_8090285 : Nat := 4983230072969 + 3 ^ 40 * 8090285 * 2
def baseEnd_8090285 : Nat := 1384734945619994818810321

theorem tailTrace_8090285 : CollatzResearch.WordTrace tailWord_8090285 prefixEnd_8090285 1384734945619994818810321 := by
  unfold tailWord_8090285
  simp only [CollatzResearch.WordTrace]
  refine ⟨295076935495286630519504309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196717956996857753679669539 295076935495286630519504309)
  ·
    refine ⟨27663462702683121611203529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295076935495286630519504309 27663462702683121611203529)
    ·
      refine ⟨20747597027012341208402647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27663462702683121611203529 20747597027012341208402647)
      ·
        refine ⟨31121395540518511812603971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747597027012341208402647 31121395540518511812603971)
        ·
          refine ⟨46682093310777767718905957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31121395540518511812603971 46682093310777767718905957)
          ·
            refine ⟨8752892495770831447294867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46682093310777767718905957 8752892495770831447294867)
            ·
              refine ⟨13129338743656247170942301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752892495770831447294867 13129338743656247170942301)
              ·
                refine ⟨4923502028871092689103363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13129338743656247170942301 4923502028871092689103363)
                ·
                  refine ⟨7385253043306639033655045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923502028871092689103363 7385253043306639033655045)
                  ·
                    refine ⟨1384734945619994818810321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385253043306639033655045 1384734945619994818810321)
                    ·
                      rfl

theorem cell23_8090285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_8090285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090285 prefixEnd_8090285 := by exact prefixLift 8090285
  have htrace : WordTrace (prefixWord ++ tailWord_8090285) baseStart_8090285 baseEnd_8090285 := by
    simpa [prefixWord, tailWord_8090285, baseEnd_8090285] using wordTrace_append hprefix tailTrace_8090285
  have hstable : (prefixWord ++ tailWord_8090285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090285).length < 2 ^ (prefixWord ++ tailWord_8090285).sum := by decide
  have hdescent : baseEnd_8090285 < baseStart_8090285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090301 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_8090301 : Nat := 118140960795 + 8090301 * 2 ^ 59
def prefixEnd_8090301 : Nat := 4983230072969 + 3 ^ 40 * 8090301 * 2
def baseEnd_8090301 : Nat := 4154213052550456393830889

theorem tailTrace_8090301 : CollatzResearch.WordTrace tailWord_8090301 prefixEnd_8090301 4154213052550456393830889 := by
  unfold tailWord_8090301
  simp only [CollatzResearch.WordTrace]
  refine ⟨295077519063228665252086757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196718346042152443501391171 295077519063228665252086757)
  ·
    refine ⟨55327034824355374734766267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295077519063228665252086757 55327034824355374734766267)
    ·
      refine ⟨82990552236533062102149401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55327034824355374734766267 82990552236533062102149401)
      ·
        refine ⟨62242914177399796576612051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82990552236533062102149401 62242914177399796576612051)
        ·
          refine ⟨93364371266099694864918077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62242914177399796576612051 93364371266099694864918077)
          ·
            refine ⟨35011639224787385574344279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93364371266099694864918077 35011639224787385574344279)
            ·
              refine ⟨52517458837181078361516419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35011639224787385574344279 52517458837181078361516419)
              ·
                refine ⟨78776188255771617542274629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52517458837181078361516419 78776188255771617542274629)
                ·
                  refine ⟨14770535297957178289176493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78776188255771617542274629 14770535297957178289176493)
                  ·
                    refine ⟨5538950736733941858441185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14770535297957178289176493 5538950736733941858441185)
                    ·
                      refine ⟨4154213052550456393830889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538950736733941858441185 4154213052550456393830889)
                      ·
                        rfl

theorem cell23_8090301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_8090301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090301 prefixEnd_8090301 := by exact prefixLift 8090301
  have htrace : WordTrace (prefixWord ++ tailWord_8090301) baseStart_8090301 baseEnd_8090301 := by
    simpa [prefixWord, tailWord_8090301, baseEnd_8090301] using wordTrace_append hprefix tailTrace_8090301
  have hstable : (prefixWord ++ tailWord_8090301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090301).length < 2 ^ (prefixWord ++ tailWord_8090301).sum := by decide
  have hdescent : baseEnd_8090301 < baseStart_8090301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090308 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_8090308 : Nat := 118140960795 + 8090308 * 2 ^ 59
def prefixEnd_8090308 : Nat := 4983230072969 + 3 ^ 40 * 8090308 * 2
def baseEnd_8090308 : Nat := 4154216646915037866443357

theorem tailTrace_8090308 : CollatzResearch.WordTrace tailWord_8090308 prefixEnd_8090308 4154216646915037866443357 := by
  unfold tailWord_8090308
  simp only [CollatzResearch.WordTrace]
  refine ⟨147538887187101652723795789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196718516249468870298394385 147538887187101652723795789)
  ·
    refine ⟨55327082695163119771423421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147538887187101652723795789 55327082695163119771423421)
    ·
      refine ⟨20747656010686169914283783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55327082695163119771423421 20747656010686169914283783)
      ·
        refine ⟨31121484016029254871425675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747656010686169914283783 31121484016029254871425675)
        ·
          refine ⟨46682226024043882307138513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31121484016029254871425675 46682226024043882307138513)
          ·
            refine ⟨35011669518032911730353885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46682226024043882307138513 35011669518032911730353885)
            ·
              refine ⟨13129376069262341898882707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35011669518032911730353885 13129376069262341898882707)
              ·
                refine ⟨19694064103893512848324061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129376069262341898882707 19694064103893512848324061)
                ·
                  refine ⟨7385274038960067318121523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19694064103893512848324061 7385274038960067318121523)
                  ·
                    refine ⟨11077911058440100977182285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385274038960067318121523 11077911058440100977182285)
                    ·
                      refine ⟨4154216646915037866443357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11077911058440100977182285 4154216646915037866443357)
                      ·
                        rfl

theorem cell23_8090308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_8090308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090308 prefixEnd_8090308 := by exact prefixLift 8090308
  have htrace : WordTrace (prefixWord ++ tailWord_8090308) baseStart_8090308 baseEnd_8090308 := by
    simpa [prefixWord, tailWord_8090308, baseEnd_8090308] using wordTrace_append hprefix tailTrace_8090308
  have hstable : (prefixWord ++ tailWord_8090308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090308).length < 2 ^ (prefixWord ++ tailWord_8090308).sum := by decide
  have hdescent : baseEnd_8090308 < baseStart_8090308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090351 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_8090351 : Nat := 118140960795 + 8090351 * 2 ^ 59
def prefixEnd_8090351 : Nat := 4983230072969 + 3 ^ 40 * 8090351 * 2
def baseEnd_8090351 : Nat := 4154238726583181198205659

theorem tailTrace_8090351 : CollatzResearch.WordTrace tailWord_8090351 prefixEnd_8090351 4154238726583181198205659 := by
  unfold tailWord_8090351
  simp only [CollatzResearch.WordTrace]
  refine ⟨295079342713047523791406907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196719561808698349194271271 295079342713047523791406907)
  ·
    refine ⟨442619014069571285687110361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295079342713047523791406907 442619014069571285687110361)
    ·
      refine ⟨331964260552178464265332771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442619014069571285687110361 331964260552178464265332771)
      ·
        refine ⟨497946390828267696397999157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331964260552178464265332771 497946390828267696397999157)
        ·
          refine ⟨46682474140150096537312421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497946390828267696397999157 46682474140150096537312421)
          ·
            refine ⟨8752963901278143100746079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46682474140150096537312421 8752963901278143100746079)
            ·
              refine ⟨13129445851917214651119119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752963901278143100746079 13129445851917214651119119)
              ·
                refine ⟨19694168777875821976678679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129445851917214651119119 19694168777875821976678679)
                ·
                  refine ⟨29541253166813732965018019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19694168777875821976678679 29541253166813732965018019)
                  ·
                    refine ⟨44311879750220599447527029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29541253166813732965018019 44311879750220599447527029)
                    ·
                      refine ⟨4154238726583181198205659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44311879750220599447527029 4154238726583181198205659)
                      ·
                        rfl

theorem cell23_8090351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_8090351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090351 prefixEnd_8090351 := by exact prefixLift 8090351
  have htrace : WordTrace (prefixWord ++ tailWord_8090351) baseStart_8090351 baseEnd_8090351 := by
    simpa [prefixWord, tailWord_8090351, baseEnd_8090351] using wordTrace_append hprefix tailTrace_8090351
  have hstable : (prefixWord ++ tailWord_8090351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090351).length < 2 ^ (prefixWord ++ tailWord_8090351).sum := by decide
  have hdescent : baseEnd_8090351 < baseStart_8090351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090358 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_8090358 : Nat := 118140960795 + 8090358 * 2 ^ 59
def prefixEnd_8090358 : Nat := 4983230072969 + 3 ^ 40 * 8090358 * 2
def baseEnd_8090358 : Nat := 1384747440315920890272709

theorem tailTrace_8090358 : CollatzResearch.WordTrace tailWord_8090358 prefixEnd_8090358 1384747440315920890272709 := by
  unfold tailWord_8090358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18442474876501385249181983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196719732016014775991274485 18442474876501385249181983)
  ·
    refine ⟨27663712314752077873772975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18442474876501385249181983 27663712314752077873772975)
    ·
      refine ⟨41495568472128116810659463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27663712314752077873772975 41495568472128116810659463)
      ·
        refine ⟨62243352708192175215989195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41495568472128116810659463 62243352708192175215989195)
        ·
          refine ⟨93365029062288262823983793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62243352708192175215989195 93365029062288262823983793)
          ·
            refine ⟨70023771796716197117987845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93365029062288262823983793 70023771796716197117987845)
            ·
              refine ⟨13129457211884286959622721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70023771796716197117987845 13129457211884286959622721)
              ·
                refine ⟨9847092908913215219717041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13129457211884286959622721 9847092908913215219717041)
                ·
                  refine ⟨7385319681684911414787781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9847092908913215219717041 7385319681684911414787781)
                  ·
                    refine ⟨1384747440315920890272709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7385319681684911414787781 1384747440315920890272709)
                    ·
                      rfl

theorem cell23_8090358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_8090358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090358 prefixEnd_8090358 := by exact prefixLift 8090358
  have htrace : WordTrace (prefixWord ++ tailWord_8090358) baseStart_8090358 baseEnd_8090358 := by
    simpa [prefixWord, tailWord_8090358, baseEnd_8090358] using wordTrace_append hprefix tailTrace_8090358
  have hstable : (prefixWord ++ tailWord_8090358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090358).length < 2 ^ (prefixWord ++ tailWord_8090358).sum := by decide
  have hdescent : baseEnd_8090358 < baseStart_8090358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090365 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_8090365 : Nat := 118140960795 + 8090365 * 2 ^ 59
def prefixEnd_8090365 : Nat := 4983230072969 + 3 ^ 40 * 8090365 * 2
def baseEnd_8090365 : Nat := 4154245915312344143430595

theorem tailTrace_8090365 : CollatzResearch.WordTrace tailWord_8090365 prefixEnd_8090365 4154245915312344143430595 := by
  unfold tailWord_8090365
  simp only [CollatzResearch.WordTrace]
  refine ⟨295079853334996804182416549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196719902223331202788277699 295079853334996804182416549)
  ·
    refine ⟨55327472500311900784203103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295079853334996804182416549 55327472500311900784203103)
    ·
      refine ⟨82991208750467851176304655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55327472500311900784203103 82991208750467851176304655)
      ·
        refine ⟨124486813125701776764456983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82991208750467851176304655 124486813125701776764456983)
        ·
          refine ⟨186730219688552665146685475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124486813125701776764456983 186730219688552665146685475)
          ·
            refine ⟨280095329532828997720028213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186730219688552665146685475 280095329532828997720028213)
            ·
              refine ⟨26258937143702718536252645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280095329532828997720028213 26258937143702718536252645)
              ·
                refine ⟨4923550714444259725547371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26258937143702718536252645 4923550714444259725547371)
                ·
                  refine ⟨7385326071666389588321057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923550714444259725547371 7385326071666389588321057)
                  ·
                    refine ⟨5538994553749792191240793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7385326071666389588321057 5538994553749792191240793)
                    ·
                      refine ⟨4154245915312344143430595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5538994553749792191240793 4154245915312344143430595)
                      ·
                        rfl

theorem cell23_8090365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_8090365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090365 prefixEnd_8090365 := by exact prefixLift 8090365
  have htrace : WordTrace (prefixWord ++ tailWord_8090365) baseStart_8090365 baseEnd_8090365 := by
    simpa [prefixWord, tailWord_8090365, baseEnd_8090365] using wordTrace_append hprefix tailTrace_8090365
  have hstable : (prefixWord ++ tailWord_8090365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090365).length < 2 ^ (prefixWord ++ tailWord_8090365).sum := by decide
  have hdescent : baseEnd_8090365 < baseStart_8090365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090394 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_8090394 : Nat := 118140960795 + 8090394 * 2 ^ 59
def prefixEnd_8090394 : Nat := 4983230072969 + 3 ^ 40 * 8090394 * 2
def baseEnd_8090394 : Nat := 4154260806251324529967961

theorem tailTrace_8090394 : CollatzResearch.WordTrace tailWord_8090394 prefixEnd_8090394 4154260806251324529967961 := by
  unfold tailWord_8090394
  simp only [CollatzResearch.WordTrace]
  refine ⟨73770227762972935533805559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196720607367927828090148157 73770227762972935533805559)
  ·
    refine ⟨110655341644459403300708339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73770227762972935533805559 110655341644459403300708339)
    ·
      refine ⟨165983012466689104951062509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110655341644459403300708339 165983012466689104951062509)
      ·
        refine ⟨62243629675008414356648441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165983012466689104951062509 62243629675008414356648441)
        ·
          refine ⟨46682722256256310767486331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62243629675008414356648441 46682722256256310767486331)
          ·
            refine ⟨70024083384384466151229497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46682722256256310767486331 70024083384384466151229497)
            ·
              refine ⟨52518062538288349613422123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70024083384384466151229497 52518062538288349613422123)
              ·
                refine ⟨78777093807432524420133185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52518062538288349613422123 78777093807432524420133185)
                ·
                  refine ⟨59082820355574393315099889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78777093807432524420133185 59082820355574393315099889)
                  ·
                    refine ⟨44312115266680794986324917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59082820355574393315099889 44312115266680794986324917)
                    ·
                      refine ⟨4154260806251324529967961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44312115266680794986324917 4154260806251324529967961)
                      ·
                        rfl

theorem cell23_8090394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_8090394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090394 prefixEnd_8090394 := by exact prefixLift 8090394
  have htrace : WordTrace (prefixWord ++ tailWord_8090394) baseStart_8090394 baseEnd_8090394 := by
    simpa [prefixWord, tailWord_8090394, baseEnd_8090394] using wordTrace_append hprefix tailTrace_8090394
  have hstable : (prefixWord ++ tailWord_8090394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090394).length < 2 ^ (prefixWord ++ tailWord_8090394).sum := by decide
  have hdescent : baseEnd_8090394 < baseStart_8090394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090545 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 2, 4, 2]
def baseStart_8090545 : Nat := 118140960795 + 8090545 * 2 ^ 59
def prefixEnd_8090545 : Nat := 4983230072969 + 3 ^ 40 * 8090545 * 2
def baseEnd_8090545 : Nat := 4154338341830153439179767

theorem tailTrace_8090545 : CollatzResearch.WordTrace tailWord_8090545 prefixEnd_8090545 4154338341830153439179767 := by
  unfold tailWord_8090545
  simp only [CollatzResearch.WordTrace]
  refine ⟨295086418474344694923969089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196724278982896463282646059 295086418474344694923969089)
  ·
    refine ⟨221314813855758521192976817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295086418474344694923969089 221314813855758521192976817)
    ·
      refine ⟨165986110391818890894732613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221314813855758521192976817 165986110391818890894732613)
      ·
        refine ⟨31122395698466042042762365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165986110391818890894732613 31122395698466042042762365)
        ·
          refine ⟨11670898386924765766035887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31122395698466042042762365 11670898386924765766035887)
          ·
            refine ⟨17506347580387148649053831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670898386924765766035887 17506347580387148649053831)
            ·
              refine ⟨26259521370580722973580747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17506347580387148649053831 26259521370580722973580747)
              ·
                refine ⟨39389282055871084460371121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26259521370580722973580747 39389282055871084460371121)
                ·
                  refine ⟨29541961541903313345278341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39389282055871084460371121 29541961541903313345278341)
                  ·
                    refine ⟨5539117789106871252239689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29541961541903313345278341 5539117789106871252239689)
                    ·
                      refine ⟨4154338341830153439179767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539117789106871252239689 4154338341830153439179767)
                      ·
                        rfl

theorem cell23_8090545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_8090545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090545 prefixEnd_8090545 := by exact prefixLift 8090545
  have htrace : WordTrace (prefixWord ++ tailWord_8090545) baseStart_8090545 baseEnd_8090545 := by
    simpa [prefixWord, tailWord_8090545, baseEnd_8090545] using wordTrace_append hprefix tailTrace_8090545
  have hstable : (prefixWord ++ tailWord_8090545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090545).length < 2 ^ (prefixWord ++ tailWord_8090545).sum := by decide
  have hdescent : baseEnd_8090545 < baseStart_8090545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090551 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 6]
def baseStart_8090551 : Nat := 118140960795 + 8090551 * 2 ^ 59
def prefixEnd_8090551 : Nat := 4983230072969 + 3 ^ 40 * 8090551 * 2
def baseEnd_8090551 : Nat := 461593491412675601744971

theorem tailTrace_8090551 : CollatzResearch.WordTrace tailWord_8090551 prefixEnd_8090551 461593491412675601744971 := by
  unfold tailWord_8090551
  simp only [CollatzResearch.WordTrace]
  refine ⟨295086637312322957948687507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196724424874881971965791671 295086637312322957948687507)
  ·
    refine ⟨442629955968484436923031261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295086637312322957948687507 442629955968484436923031261)
    ·
      refine ⟨165986233488181663846136723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442629955968484436923031261 165986233488181663846136723)
      ·
        refine ⟨248979350232272495769205085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165986233488181663846136723 248979350232272495769205085)
        ·
          refine ⟨93367256337102185913451907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248979350232272495769205085 93367256337102185913451907)
          ·
            refine ⟨140050884505653278870177861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93367256337102185913451907 140050884505653278870177861)
            ·
              refine ⟨26259540844809989788158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140050884505653278870177861 26259540844809989788158349)
              ·
                refine ⟨9847327816803746170559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26259540844809989788158349 9847327816803746170559381)
                ·
                  refine ⟨461593491412675601744971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9847327816803746170559381 461593491412675601744971)
                  ·
                    rfl

theorem cell23_8090551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 6].length) (baseStart_8090551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090551 prefixEnd_8090551 := by exact prefixLift 8090551
  have htrace : WordTrace (prefixWord ++ tailWord_8090551) baseStart_8090551 baseEnd_8090551 := by
    simpa [prefixWord, tailWord_8090551, baseEnd_8090551] using wordTrace_append hprefix tailTrace_8090551
  have hstable : (prefixWord ++ tailWord_8090551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090551).length < 2 ^ (prefixWord ++ tailWord_8090551).sum := by decide
  have hdescent : baseEnd_8090551 < baseStart_8090551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090595 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 3]
def baseStart_8090595 : Nat := 118140960795 + 8090595 * 2 ^ 59
def prefixEnd_8090595 : Nat := 4983230072969 + 3 ^ 40 * 8090595 * 2
def baseEnd_8090595 : Nat := 4154364015862878243554537

theorem tailTrace_8090595 : CollatzResearch.WordTrace tailWord_8090595 prefixEnd_8090595 4154364015862878243554537 := by
  unfold tailWord_8090595
  simp only [CollatzResearch.WordTrace]
  refine ⟨295088242124163553463289239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196725494749442368975526159 295088242124163553463289239)
  ·
    refine ⟨442632363186245330194933859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295088242124163553463289239 442632363186245330194933859)
    ·
      refine ⟨663948544779367995292400789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442632363186245330194933859 663948544779367995292400789)
      ·
        refine ⟨31122588036532874779331287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 663948544779367995292400789 31122588036532874779331287)
        ·
          refine ⟨46683882054799312168996931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122588036532874779331287 46683882054799312168996931)
          ·
            refine ⟨70025823082198968253495397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46683882054799312168996931 70025823082198968253495397)
            ·
              refine ⟨13129841827912306547530387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70025823082198968253495397 13129841827912306547530387)
              ·
                refine ⟨19694762741868459821295581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129841827912306547530387 19694762741868459821295581)
                ·
                  refine ⟨7385536028200672432985843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19694762741868459821295581 7385536028200672432985843)
                  ·
                    refine ⟨11078304042301008649478765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385536028200672432985843 11078304042301008649478765)
                    ·
                      refine ⟨4154364015862878243554537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078304042301008649478765 4154364015862878243554537)
                      ·
                        rfl

theorem cell23_8090595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_8090595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090595 prefixEnd_8090595 := by exact prefixLift 8090595
  have htrace : WordTrace (prefixWord ++ tailWord_8090595) baseStart_8090595 baseEnd_8090595 := by
    simpa [prefixWord, tailWord_8090595, baseEnd_8090595] using wordTrace_append hprefix tailTrace_8090595
  have hstable : (prefixWord ++ tailWord_8090595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090595).length < 2 ^ (prefixWord ++ tailWord_8090595).sum := by decide
  have hdescent : baseEnd_8090595 < baseStart_8090595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090621 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_8090621 : Nat := 118140960795 + 8090621 * 2 ^ 59
def prefixEnd_8090621 : Nat := 4983230072969 + 3 ^ 40 * 8090621 * 2
def baseEnd_8090621 : Nat := 4154377366359895141829417

theorem tailTrace_8090621 : CollatzResearch.WordTrace tailWord_8090621 prefixEnd_8090621 4154377366359895141829417 := by
  unfold tailWord_8090621
  simp only [CollatzResearch.WordTrace]
  refine ⟨295089190422069359903735717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196726126948046239935823811 295089190422069359903735717)
  ·
    refine ⟨55329223204138004981950447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295089190422069359903735717 55329223204138004981950447)
    ·
      refine ⟨82993834806207007472925671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55329223204138004981950447 82993834806207007472925671)
      ·
        refine ⟨124490752209310511209388507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82993834806207007472925671 124490752209310511209388507)
        ·
          refine ⟨186736128313965766814082761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124490752209310511209388507 186736128313965766814082761)
          ·
            refine ⟨140052096235474325110562071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186736128313965766814082761 140052096235474325110562071)
            ·
              refine ⟨210078144353211487665843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140052096235474325110562071 210078144353211487665843107)
              ·
                refine ⟨315117216529817231498764661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210078144353211487665843107 315117216529817231498764661)
                ·
                  refine ⟨29542239049670365453009187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315117216529817231498764661 29542239049670365453009187)
                  ·
                    refine ⟨44313358574505548179513781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29542239049670365453009187 44313358574505548179513781)
                    ·
                      refine ⟨4154377366359895141829417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44313358574505548179513781 4154377366359895141829417)
                      ·
                        rfl

theorem cell23_8090621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_8090621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090621 prefixEnd_8090621 := by exact prefixLift 8090621
  have htrace : WordTrace (prefixWord ++ tailWord_8090621) baseStart_8090621 baseEnd_8090621 := by
    simpa [prefixWord, tailWord_8090621, baseEnd_8090621] using wordTrace_append hprefix tailTrace_8090621
  have hstable : (prefixWord ++ tailWord_8090621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090621).length < 2 ^ (prefixWord ++ tailWord_8090621).sum := by decide
  have hdescent : baseEnd_8090621 < baseStart_8090621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090638 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_8090638 : Nat := 118140960795 + 8090638 * 2 ^ 59
def prefixEnd_8090638 : Nat := 4983230072969 + 3 ^ 40 * 8090638 * 2
def baseEnd_8090638 : Nat := 4154386095531021575316839

theorem tailTrace_8090638 : CollatzResearch.WordTrace tailWord_8090638 prefixEnd_8090638 4154386095531021575316839 := by
  unfold tailWord_8090638
  simp only [CollatzResearch.WordTrace]
  refine ⟨36886226307875971475888071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196726540308671847871403045 36886226307875971475888071)
  ·
    refine ⟨55329339461813957213832107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36886226307875971475888071 55329339461813957213832107)
    ·
      refine ⟨82994009192720935820748161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55329339461813957213832107 82994009192720935820748161)
      ·
        refine ⟨62245506894540701865561121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82994009192720935820748161 62245506894540701865561121)
        ·
          refine ⟨46684130170905526399170841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62245506894540701865561121 46684130170905526399170841)
          ·
            refine ⟨35013097628179144799378131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46684130170905526399170841 35013097628179144799378131)
            ·
              refine ⟨52519646442268717199067197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35013097628179144799378131 52519646442268717199067197)
              ·
                refine ⟨19694867415850768949650199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52519646442268717199067197 19694867415850768949650199)
                ·
                  refine ⟨29542301123776153424475299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19694867415850768949650199 29542301123776153424475299)
                  ·
                    refine ⟨44313451685664230136712949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29542301123776153424475299 44313451685664230136712949)
                    ·
                      refine ⟨4154386095531021575316839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44313451685664230136712949 4154386095531021575316839)
                      ·
                        rfl

theorem cell23_8090638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_8090638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090638 prefixEnd_8090638 := by exact prefixLift 8090638
  have htrace : WordTrace (prefixWord ++ tailWord_8090638) baseStart_8090638 baseEnd_8090638 := by
    simpa [prefixWord, tailWord_8090638, baseEnd_8090638] using wordTrace_append hprefix tailTrace_8090638
  have hstable : (prefixWord ++ tailWord_8090638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090638).length < 2 ^ (prefixWord ++ tailWord_8090638).sum := by decide
  have hdescent : baseEnd_8090638 < baseStart_8090638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090658 : List Nat := [3, 3, 1, 1, 1, 4, 2, 8]
def baseStart_8090658 : Nat := 118140960795 + 8090658 * 2 ^ 59
def prefixEnd_8090658 : Nat := 4983230072969 + 3 ^ 40 * 8090658 * 2
def baseEnd_8090658 : Nat := 153866532042374499891361

theorem tailTrace_8090658 : CollatzResearch.WordTrace tailWord_8090658 prefixEnd_8090658 153866532042374499891361 := by
  unfold tailWord_8090658
  simp only [CollatzResearch.WordTrace]
  refine ⟨73772634980733828805708157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196727026615290210148555085 73772634980733828805708157)
  ·
    refine ⟨27664738117775185802140559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73772634980733828805708157 27664738117775185802140559)
    ·
      refine ⟨41497107176662778703210839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27664738117775185802140559 41497107176662778703210839)
      ·
        refine ⟨62245660764994168054816259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41497107176662778703210839 62245660764994168054816259)
        ·
          refine ⟨93368491147491252082224389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62245660764994168054816259 93368491147491252082224389)
          ·
            refine ⟨17506592090154609765417073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93368491147491252082224389 17506592090154609765417073)
            ·
              refine ⟨13129944067615957324062805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17506592090154609765417073 13129944067615957324062805)
              ·
                refine ⟨153866532042374499891361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13129944067615957324062805 153866532042374499891361)
                ·
                  rfl

theorem cell23_8090658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_8090658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090658 prefixEnd_8090658 := by exact prefixLift 8090658
  have htrace : WordTrace (prefixWord ++ tailWord_8090658) baseStart_8090658 baseEnd_8090658 := by
    simpa [prefixWord, tailWord_8090658, baseEnd_8090658] using wordTrace_append hprefix tailTrace_8090658
  have hstable : (prefixWord ++ tailWord_8090658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090658).length < 2 ^ (prefixWord ++ tailWord_8090658).sum := by decide
  have hdescent : baseEnd_8090658 < baseStart_8090658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090661 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_8090661 : Nat := 118140960795 + 8090661 * 2 ^ 59
def prefixEnd_8090661 : Nat := 4983230072969 + 3 ^ 40 * 8090661 * 2
def baseEnd_8090661 : Nat := 4154397905586074985329233

theorem tailTrace_8090661 : CollatzResearch.WordTrace tailWord_8090661 prefixEnd_8090661 4154397905586074985329233 := by
  unfold tailWord_8090661
  simp only [CollatzResearch.WordTrace]
  refine ⟨295090649341924446735191837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196727099561282964490127891 295090649341924446735191837)
  ·
    refine ⟨110658993503221667525696939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295090649341924446735191837 110658993503221667525696939)
    ·
      refine ⟨165988490254832501288545409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110658993503221667525696939 165988490254832501288545409)
      ·
        refine ⟨124491367691124375966409057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165988490254832501288545409 124491367691124375966409057)
        ·
          refine ⟨93368525768343281974806793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124491367691124375966409057 93368525768343281974806793)
          ·
            refine ⟨70026394326257461481105095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93368525768343281974806793 70026394326257461481105095)
            ·
              refine ⟨105039591489386192221657643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70026394326257461481105095 105039591489386192221657643)
              ·
                refine ⟨157559387234079288332486465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105039591489386192221657643 157559387234079288332486465)
                ·
                  refine ⟨118169540425559466249364849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157559387234079288332486465 118169540425559466249364849)
                  ·
                    refine ⟨88627155319169599687023637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118169540425559466249364849 88627155319169599687023637)
                    ·
                      refine ⟨4154397905586074985329233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88627155319169599687023637 4154397905586074985329233)
                      ·
                        rfl

theorem cell23_8090661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_8090661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090661 prefixEnd_8090661 := by exact prefixLift 8090661
  have htrace : WordTrace (prefixWord ++ tailWord_8090661) baseStart_8090661 baseEnd_8090661 := by
    simpa [prefixWord, tailWord_8090661, baseEnd_8090661] using wordTrace_append hprefix tailTrace_8090661
  have hstable : (prefixWord ++ tailWord_8090661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090661).length < 2 ^ (prefixWord ++ tailWord_8090661).sum := by decide
  have hdescent : baseEnd_8090661 < baseStart_8090661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090668 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_8090668 : Nat := 118140960795 + 8090668 * 2 ^ 59
def prefixEnd_8090668 : Nat := 4983230072969 + 3 ^ 40 * 8090668 * 2
def baseEnd_8090668 : Nat := 4154401499950656457941701

theorem tailTrace_8090668 : CollatzResearch.WordTrace tailWord_8090668 prefixEnd_8090668 4154401499950656457941701 := by
  unfold tailWord_8090668
  simp only [CollatzResearch.WordTrace]
  refine ⟨147545452326449543465348329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196727269768599391287131105 147545452326449543465348329)
  ·
    refine ⟨110659089244837157599011247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147545452326449543465348329 110659089244837157599011247)
    ·
      refine ⟨165988633867255736398516871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110659089244837157599011247 165988633867255736398516871)
      ·
        refine ⟨248982950800883604597775307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165988633867255736398516871 248982950800883604597775307)
        ·
          refine ⟨373474426201325406896662961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248982950800883604597775307 373474426201325406896662961)
          ·
            refine ⟨280105819650994055172497221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373474426201325406896662961 280105819650994055172497221)
            ·
              refine ⟨52519841184561385344843229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280105819650994055172497221 52519841184561385344843229)
              ·
                refine ⟨19694940444210519504316211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52519841184561385344843229 19694940444210519504316211)
                ·
                  refine ⟨29542410666315779256474317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19694940444210519504316211 29542410666315779256474317)
                  ·
                    refine ⟨11078403999868417221177869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29542410666315779256474317 11078403999868417221177869)
                    ·
                      refine ⟨4154401499950656457941701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078403999868417221177869 4154401499950656457941701)
                      ·
                        rfl

theorem cell23_8090668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_8090668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090668 prefixEnd_8090668 := by exact prefixLift 8090668
  have htrace : WordTrace (prefixWord ++ tailWord_8090668) baseStart_8090668 baseEnd_8090668 := by
    simpa [prefixWord, tailWord_8090668, baseEnd_8090668] using wordTrace_append hprefix tailTrace_8090668
  have hstable : (prefixWord ++ tailWord_8090668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090668).length < 2 ^ (prefixWord ++ tailWord_8090668).sum := by decide
  have hdescent : baseEnd_8090668 < baseStart_8090668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090685 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_8090685 : Nat := 118140960795 + 8090685 * 2 ^ 59
def prefixEnd_8090685 : Nat := 4983230072969 + 3 ^ 40 * 8090685 * 2
def baseEnd_8090685 : Nat := 4154410229121782891429123

theorem tailTrace_8090685 : CollatzResearch.WordTrace tailWord_8090685 prefixEnd_8090685 4154410229121782891429123 := by
  unfold tailWord_8090685
  simp only [CollatzResearch.WordTrace]
  refine ⟨295091524693837498834065509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196727683129224999222710339 295091524693837498834065509)
  ·
    refine ⟨55329660880094531031387283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295091524693837498834065509 55329660880094531031387283)
    ·
      refine ⟨82994491320141796547080925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55329660880094531031387283 82994491320141796547080925)
      ·
        refine ⟨31122934245053173705155347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82994491320141796547080925 31122934245053173705155347)
        ·
          refine ⟨46684401367579760557733021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122934245053173705155347 46684401367579760557733021)
          ·
            refine ⟨17506650512842410209149883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46684401367579760557733021 17506650512842410209149883)
            ·
              refine ⟨26259975769263615313724825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17506650512842410209149883 26259975769263615313724825)
              ·
                refine ⟨19694981826947711485293619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26259975769263615313724825 19694981826947711485293619)
                ·
                  refine ⟨29542472740421567227940429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19694981826947711485293619 29542472740421567227940429)
                  ·
                    refine ⟨11078427277658087710477661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29542472740421567227940429 11078427277658087710477661)
                    ·
                      refine ⟨4154410229121782891429123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078427277658087710477661 4154410229121782891429123)
                      ·
                        rfl

theorem cell23_8090685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_8090685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090685 prefixEnd_8090685 := by exact prefixLift 8090685
  have htrace : WordTrace (prefixWord ++ tailWord_8090685) baseStart_8090685 baseEnd_8090685 := by
    simpa [prefixWord, tailWord_8090685, baseEnd_8090685] using wordTrace_append hprefix tailTrace_8090685
  have hstable : (prefixWord ++ tailWord_8090685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090685).length < 2 ^ (prefixWord ++ tailWord_8090685).sum := by decide
  have hdescent : baseEnd_8090685 < baseStart_8090685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090689 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_8090689 : Nat := 118140960795 + 8090689 * 2 ^ 59
def prefixEnd_8090689 : Nat := 4983230072969 + 3 ^ 40 * 8090689 * 2
def baseEnd_8090689 : Nat := 4154412283044400875779105

theorem tailTrace_8090689 : CollatzResearch.WordTrace tailWord_8090689 prefixEnd_8090689 4154412283044400875779105 := by
  unfold tailWord_8090689
  simp only [CollatzResearch.WordTrace]
  refine ⟨295091670585823007517211121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196727780390548671678140747 295091670585823007517211121)
  ·
    refine ⟨221318752939367255637908341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295091670585823007517211121 221318752939367255637908341)
    ·
      refine ⟨20748633088065680216053907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221318752939367255637908341 20748633088065680216053907)
      ·
        refine ⟨31122949632098520324080861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20748633088065680216053907 31122949632098520324080861)
        ·
          refine ⟨11671106112036945121530323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31122949632098520324080861 11671106112036945121530323)
          ·
            refine ⟨17506659168055417682295485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11671106112036945121530323 17506659168055417682295485)
            ·
              refine ⟨6564997188020781630860807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17506659168055417682295485 6564997188020781630860807)
              ·
                refine ⟨9847495782031172446291211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564997188020781630860807 9847495782031172446291211)
                ·
                  refine ⟨14771243673046758669436817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9847495782031172446291211 14771243673046758669436817)
                  ·
                    refine ⟨11078432754785069002077613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14771243673046758669436817 11078432754785069002077613)
                    ·
                      refine ⟨4154412283044400875779105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078432754785069002077613 4154412283044400875779105)
                      ·
                        rfl

theorem cell23_8090689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_8090689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090689 prefixEnd_8090689 := by exact prefixLift 8090689
  have htrace : WordTrace (prefixWord ++ tailWord_8090689) baseStart_8090689 baseEnd_8090689 := by
    simpa [prefixWord, tailWord_8090689, baseEnd_8090689] using wordTrace_append hprefix tailTrace_8090689
  have hstable : (prefixWord ++ tailWord_8090689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090689).length < 2 ^ (prefixWord ++ tailWord_8090689).sum := by decide
  have hdescent : baseEnd_8090689 < baseStart_8090689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090702 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_8090702 : Nat := 118140960795 + 8090702 * 2 ^ 59
def prefixEnd_8090702 : Nat := 4983230072969 + 3 ^ 40 * 8090702 * 2
def baseEnd_8090702 : Nat := 4154418958292909324916545

theorem tailTrace_8090702 : CollatzResearch.WordTrace tailWord_8090702 prefixEnd_8090702 4154418958292909324916545 := by
  unfold tailWord_8090702
  simp only [CollatzResearch.WordTrace]
  refine ⟨36886518091846988842179295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196728096489850607158289573 36886518091846988842179295)
  ·
    refine ⟨55329777137770483263268943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36886518091846988842179295 55329777137770483263268943)
    ·
      refine ⟨82994665706655724894903415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55329777137770483263268943 82994665706655724894903415)
      ·
        refine ⟨124491998559983587342355123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82994665706655724894903415 124491998559983587342355123)
        ·
          refine ⟨186737997839975381013532685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124491998559983587342355123 186737997839975381013532685)
          ·
            refine ⟨70026749189990767880074757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186737997839975381013532685 70026749189990767880074757)
            ·
              refine ⟨13130015473123268977514017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70026749189990767880074757 13130015473123268977514017)
              ·
                refine ⟨9847511604842451733135513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13130015473123268977514017 9847511604842451733135513)
                ·
                  refine ⟨7385633703631838799851635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9847511604842451733135513 7385633703631838799851635)
                  ·
                    refine ⟨11078450555447758199777453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385633703631838799851635 11078450555447758199777453)
                    ·
                      refine ⟨4154418958292909324916545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078450555447758199777453 4154418958292909324916545)
                      ·
                        rfl

theorem cell23_8090702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_8090702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090702 prefixEnd_8090702 := by exact prefixLift 8090702
  have htrace : WordTrace (prefixWord ++ tailWord_8090702) baseStart_8090702 baseEnd_8090702 := by
    simpa [prefixWord, tailWord_8090702, baseEnd_8090702] using wordTrace_append hprefix tailTrace_8090702
  have hstable : (prefixWord ++ tailWord_8090702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090702).length < 2 ^ (prefixWord ++ tailWord_8090702).sum := by decide
  have hdescent : baseEnd_8090702 < baseStart_8090702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090708 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_8090708 : Nat := 118140960795 + 8090708 * 2 ^ 59
def prefixEnd_8090708 : Nat := 4983230072969 + 3 ^ 40 * 8090708 * 2
def baseEnd_8090708 : Nat := 4154422039176836301441517

theorem tailTrace_8090708 : CollatzResearch.WordTrace tailWord_8090708 prefixEnd_8090708 4154422039176836301441517 := by
  unfold tailWord_8090708
  simp only [CollatzResearch.WordTrace]
  refine ⟨147546181786377086881076389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196728242381836115841435185 147546181786377086881076389)
  ·
    refine ⟨27664909084945703790201823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147546181786377086881076389 27664909084945703790201823)
    ·
      refine ⟨41497363627418555685302735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27664909084945703790201823 41497363627418555685302735)
      ·
        refine ⟨62246045441127833527954103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41497363627418555685302735 62246045441127833527954103)
        ·
          refine ⟨93369068161691750291931155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62246045441127833527954103 93369068161691750291931155)
          ·
            refine ⟨140053602242537625437896733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93369068161691750291931155 140053602242537625437896733)
            ·
              refine ⟨52520100840951609539211275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140053602242537625437896733 52520100840951609539211275)
              ·
                refine ⟨78780151261427414308816913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52520100840951609539211275 78780151261427414308816913)
                ·
                  refine ⟨59085113446070560731612685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78780151261427414308816913 59085113446070560731612685)
                  ·
                    refine ⟨22156917542276460274354757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59085113446070560731612685 22156917542276460274354757)
                    ·
                      refine ⟨4154422039176836301441517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22156917542276460274354757 4154422039176836301441517)
                      ·
                        rfl

theorem cell23_8090708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_8090708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090708 prefixEnd_8090708 := by exact prefixLift 8090708
  have htrace : WordTrace (prefixWord ++ tailWord_8090708) baseStart_8090708 baseEnd_8090708 := by
    simpa [prefixWord, tailWord_8090708, baseEnd_8090708] using wordTrace_append hprefix tailTrace_8090708
  have hstable : (prefixWord ++ tailWord_8090708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090708).length < 2 ^ (prefixWord ++ tailWord_8090708).sum := by decide
  have hdescent : baseEnd_8090708 < baseStart_8090708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090738 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_8090738 : Nat := 118140960795 + 8090738 * 2 ^ 59
def prefixEnd_8090738 : Nat := 4983230072969 + 3 ^ 40 * 8090738 * 2
def baseEnd_8090738 : Nat := 4154437443596471184066379

theorem tailTrace_8090738 : CollatzResearch.WordTrace tailWord_8090738 prefixEnd_8090738 4154437443596471184066379 := by
  unfold tailWord_8090738
  simp only [CollatzResearch.WordTrace]
  refine ⟨73773364440661372221436217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196728971841763659257163245 73773364440661372221436217)
  ·
    refine ⟨55330023330496029166077163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73773364440661372221436217 55330023330496029166077163)
    ·
      refine ⟨82995034995744043749115745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55330023330496029166077163 82995034995744043749115745)
      ·
        refine ⟨62246276246808032811836809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82995034995744043749115745 62246276246808032811836809)
        ·
          refine ⟨46684707185106024608877607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62246276246808032811836809 46684707185106024608877607)
          ·
            refine ⟨70027060777659036913316411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46684707185106024608877607 70027060777659036913316411)
            ·
              refine ⟨105040591166488555369974617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70027060777659036913316411 105040591166488555369974617)
              ·
                refine ⟨78780443374866416527480963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105040591166488555369974617 78780443374866416527480963)
                ·
                  refine ⟨118170665062299624791221445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78780443374866416527480963 118170665062299624791221445)
                  ·
                    refine ⟨22156999699181179648354021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118170665062299624791221445 22156999699181179648354021)
                    ·
                      refine ⟨4154437443596471184066379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22156999699181179648354021 4154437443596471184066379)
                      ·
                        rfl

theorem cell23_8090738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_8090738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090738 prefixEnd_8090738 := by exact prefixLift 8090738
  have htrace : WordTrace (prefixWord ++ tailWord_8090738) baseStart_8090738 baseEnd_8090738 := by
    simpa [prefixWord, tailWord_8090738, baseEnd_8090738] using wordTrace_append hprefix tailTrace_8090738
  have hstable : (prefixWord ++ tailWord_8090738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090738).length < 2 ^ (prefixWord ++ tailWord_8090738).sum := by decide
  have hdescent : baseEnd_8090738 < baseStart_8090738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090742 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_8090742 : Nat := 118140960795 + 8090742 * 2 ^ 59
def prefixEnd_8090742 : Nat := 4983230072969 + 3 ^ 40 * 8090742 * 2
def baseEnd_8090742 : Nat := 4154439497519089168416361

theorem tailTrace_8090742 : CollatzResearch.WordTrace tailWord_8090742 prefixEnd_8090742 4154439497519089168416361 := by
  unfold tailWord_8090742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18443350228414437348055655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196729069103087331712593653 18443350228414437348055655)
  ·
    refine ⟨27665025342621656022083483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18443350228414437348055655 27665025342621656022083483)
    ·
      refine ⟨41497538013932484033125225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27665025342621656022083483 41497538013932484033125225)
      ·
        refine ⟨31123153510449363024843919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41497538013932484033125225 31123153510449363024843919)
        ·
          refine ⟨46684730265674044537265879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31123153510449363024843919 46684730265674044537265879)
          ·
            refine ⟨70027095398511066805898819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46684730265674044537265879 70027095398511066805898819)
            ·
              refine ⟨105040643097766600208848229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70027095398511066805898819 105040643097766600208848229)
              ·
                refine ⟨19695120580831237539159043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105040643097766600208848229 19695120580831237539159043)
                ·
                  refine ⟨29542680871246856308738565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19695120580831237539159043 29542680871246856308738565)
                  ·
                    refine ⟨5539252663358785557888481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29542680871246856308738565 5539252663358785557888481)
                    ·
                      refine ⟨4154439497519089168416361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5539252663358785557888481 4154439497519089168416361)
                      ·
                        rfl

theorem cell23_8090742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_8090742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090742 prefixEnd_8090742 := by exact prefixLift 8090742
  have htrace : WordTrace (prefixWord ++ tailWord_8090742) baseStart_8090742 baseEnd_8090742 := by
    simpa [prefixWord, tailWord_8090742, baseEnd_8090742] using wordTrace_append hprefix tailTrace_8090742
  have hstable : (prefixWord ++ tailWord_8090742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090742).length < 2 ^ (prefixWord ++ tailWord_8090742).sum := by decide
  have hdescent : baseEnd_8090742 < baseStart_8090742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090775 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_8090775 : Nat := 118140960795 + 8090775 * 2 ^ 59
def prefixEnd_8090775 : Nat := 4983230072969 + 3 ^ 40 * 8090775 * 2
def baseEnd_8090775 : Nat := 4154456442380687539303709

theorem tailTrace_8090775 : CollatzResearch.WordTrace tailWord_8090775 prefixEnd_8090775 4154456442380687539303709 := by
  unfold tailWord_8090775
  simp only [CollatzResearch.WordTrace]
  refine ⟨295094807263511444204841779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196729871509007629469894519 295094807263511444204841779)
  ·
    refine ⟨442642210895267166307262669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295094807263511444204841779 442642210895267166307262669)
    ·
      refine ⟨165990829085725187365223501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442642210895267166307262669 165990829085725187365223501)
      ·
        refine ⟨62246560907146945261958813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165990829085725187365223501 62246560907146945261958813)
        ·
          refine ⟨23342460340180104473234555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62246560907146945261958813 23342460340180104473234555)
          ·
            refine ⟨35013690510270156709851833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23342460340180104473234555 35013690510270156709851833)
            ·
              refine ⟨26260267882702617532388875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35013690510270156709851833 26260267882702617532388875)
              ·
                refine ⟨39390401824053926298583313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26260267882702617532388875 39390401824053926298583313)
                ·
                  refine ⟨29542801368040444723937485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39390401824053926298583313 29542801368040444723937485)
                  ·
                    refine ⟨11078550513015166771476557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29542801368040444723937485 11078550513015166771476557)
                    ·
                      refine ⟨4154456442380687539303709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11078550513015166771476557 4154456442380687539303709)
                      ·
                        rfl

theorem cell23_8090775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_8090775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8090775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8090775 prefixEnd_8090775 := by exact prefixLift 8090775
  have htrace : WordTrace (prefixWord ++ tailWord_8090775) baseStart_8090775 baseEnd_8090775 := by
    simpa [prefixWord, tailWord_8090775, baseEnd_8090775] using wordTrace_append hprefix tailTrace_8090775
  have hstable : (prefixWord ++ tailWord_8090775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090775).length < 2 ^ (prefixWord ++ tailWord_8090775).sum := by decide
  have hdescent : baseEnd_8090775 < baseStart_8090775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
