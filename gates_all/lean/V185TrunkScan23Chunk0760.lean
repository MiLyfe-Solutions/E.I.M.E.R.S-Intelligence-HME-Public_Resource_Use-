import V185TrunkScan23Chunk0759

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4494977 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_4494977 : Nat := 118140960795 + 4494977 * 2 ^ 59
def prefixEnd_4494977 : Nat := 4983230072969 + 3 ^ 40 * 4494977 * 2
def baseEnd_4494977 : Nat := 2308083731904965115515483

theorem tailTrace_4494977 : CollatzResearch.WordTrace tailWord_4494977 prefixEnd_4494977 2308083731904965115515483 := by
  unfold tailWord_4494977
  simp only [CollatzResearch.WordTrace]
  refine ⟨163945279836473484798507185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109296853224315656532338123 163945279836473484798507185)
  ·
    refine ⟨122958959877355113598880389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163945279836473484798507185 122958959877355113598880389)
    ·
      refine ⟨23054804977004083799790073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122958959877355113598880389 23054804977004083799790073)
      ·
        refine ⟨17291103732753062849842555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23054804977004083799790073 17291103732753062849842555)
        ·
          refine ⟨25936655599129594274763833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17291103732753062849842555 25936655599129594274763833)
          ·
            refine ⟨19452491699347195706072875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25936655599129594274763833 19452491699347195706072875)
            ·
              refine ⟨29178737549020793559109313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19452491699347195706072875 29178737549020793559109313)
              ·
                refine ⟨21884053161765595169331985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29178737549020793559109313 21884053161765595169331985)
                ·
                  refine ⟨16413039871324196376998989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21884053161765595169331985 16413039871324196376998989)
                  ·
                    refine ⟨6154889951746573641374621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16413039871324196376998989 6154889951746573641374621)
                    ·
                      refine ⟨2308083731904965115515483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6154889951746573641374621 2308083731904965115515483)
                      ·
                        rfl

theorem cell23_4494977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_4494977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494977 prefixEnd_4494977 := by exact prefixLift 4494977
  have htrace : WordTrace (prefixWord ++ tailWord_4494977) baseStart_4494977 baseEnd_4494977 := by
    simpa [prefixWord, tailWord_4494977, baseEnd_4494977] using wordTrace_append hprefix tailTrace_4494977
  have hstable : (prefixWord ++ tailWord_4494977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494977).length < 2 ^ (prefixWord ++ tailWord_4494977).sum := by decide
  have hdescent : baseEnd_4494977 < baseStart_4494977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4494984 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 7]
def baseStart_4494984 : Nat := 118140960795 + 4494984 * 2 ^ 59
def prefixEnd_4494984 : Nat := 4983230072969 + 3 ^ 40 * 4494984 * 2
def baseEnd_4494984 : Nat := 256454147363282954236439

theorem tailTrace_4494984 : CollatzResearch.WordTrace tailWord_4494984 prefixEnd_4494984 256454147363282954236439 := by
  unfold tailWord_4494984
  simp only [CollatzResearch.WordTrace]
  refine ⟨81972767573724062497006003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109297023431632083329341337 81972767573724062497006003)
  ·
    refine ⟨122959151360586093745509005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81972767573724062497006003 122959151360586093745509005)
    ·
      refine ⟨46109681760219785154565877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122959151360586093745509005 46109681760219785154565877)
      ·
        refine ⟨4322782665020604858240551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46109681760219785154565877 4322782665020604858240551)
        ·
          refine ⟨6484173997530907287360827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322782665020604858240551 6484173997530907287360827)
          ·
            refine ⟨9726260996296360931041241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484173997530907287360827 9726260996296360931041241)
            ·
              refine ⟨7294695747222270698280931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9726260996296360931041241 7294695747222270698280931)
              ·
                refine ⟨10942043620833406047421397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7294695747222270698280931 10942043620833406047421397)
                ·
                  refine ⟨256454147363282954236439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10942043620833406047421397 256454147363282954236439)
                  ·
                    rfl

theorem cell23_4494984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_4494984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4494984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4494984 prefixEnd_4494984 := by exact prefixLift 4494984
  have htrace : WordTrace (prefixWord ++ tailWord_4494984) baseStart_4494984 baseEnd_4494984 := by
    simpa [prefixWord, tailWord_4494984, baseEnd_4494984] using wordTrace_append hprefix tailTrace_4494984
  have hstable : (prefixWord ++ tailWord_4494984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4494984).length < 2 ^ (prefixWord ++ tailWord_4494984).sum := by decide
  have hdescent : baseEnd_4494984 < baseStart_4494984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4494984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495040 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 8]
def baseStart_4495040 : Nat := 118140960795 + 4495040 * 2 ^ 59
def prefixEnd_4495040 : Nat := 4983230072969 + 3 ^ 40 * 4495040 * 2
def baseEnd_4495040 : Nat := 256457342354022041003077

theorem tailTrace_4495040 : CollatzResearch.WordTrace tailWord_4495040 prefixEnd_4495040 256457342354022041003077 := by
  unfold tailWord_4495040
  simp only [CollatzResearch.WordTrace]
  refine ⟨81973788817622623279025287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109298385090163497705367049 81973788817622623279025287)
  ·
    refine ⟨122960683226433934918537931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81973788817622623279025287 122960683226433934918537931)
    ·
      refine ⟨184441024839650902377806897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122960683226433934918537931 184441024839650902377806897)
      ·
        refine ⟨138330768629738176783355173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184441024839650902377806897 138330768629738176783355173)
        ·
          refine ⟨25937019118075908146879095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138330768629738176783355173 25937019118075908146879095)
          ·
            refine ⟨38905528677113862220318643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25937019118075908146879095 38905528677113862220318643)
            ·
              refine ⟨58358293015670793330477965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38905528677113862220318643 58358293015670793330477965)
              ·
                refine ⟨21884359880876547498929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58358293015670793330477965 21884359880876547498929237)
                ·
                  refine ⟨256457342354022041003077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21884359880876547498929237 256457342354022041003077)
                  ·
                    rfl

theorem cell23_4495040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_4495040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495040 prefixEnd_4495040 := by exact prefixLift 4495040
  have htrace : WordTrace (prefixWord ++ tailWord_4495040) baseStart_4495040 baseEnd_4495040 := by
    simpa [prefixWord, tailWord_4495040, baseEnd_4495040] using wordTrace_append hprefix tailTrace_4495040
  have hstable : (prefixWord ++ tailWord_4495040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495040).length < 2 ^ (prefixWord ++ tailWord_4495040).sum := by decide
  have hdescent : baseEnd_4495040 < baseStart_4495040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495057 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 6]
def baseStart_4495057 : Nat := 118140960795 + 4495057 * 2 ^ 59
def prefixEnd_4495057 : Nat := 4983230072969 + 3 ^ 40 * 4495057 * 2
def baseEnd_4495057 : Nat := 256458312261924978057235

theorem tailTrace_4495057 : CollatzResearch.WordTrace tailWord_4495057 prefixEnd_4495057 256458312261924978057235 := by
  unfold tailWord_4495057
  simp only [CollatzResearch.WordTrace]
  refine ⟨163948197676183658461419425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109298798450789105640946283 163948197676183658461419425)
  ·
    refine ⟨122961148257137743846064569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163948197676183658461419425 122961148257137743846064569)
    ·
      refine ⟨92220861192853307884548427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122961148257137743846064569 92220861192853307884548427)
      ·
        refine ⟨138331291789279961826822641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92220861192853307884548427 138331291789279961826822641)
        ·
          refine ⟨103748468841959971370116981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138331291789279961826822641 103748468841959971370116981)
          ·
            refine ⟨9726418953933747315948467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103748468841959971370116981 9726418953933747315948467)
            ·
              refine ⟨14589628430900620973922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9726418953933747315948467 14589628430900620973922701)
              ·
                refine ⟨5471110661587732865221013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14589628430900620973922701 5471110661587732865221013)
                ·
                  refine ⟨256458312261924978057235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5471110661587732865221013 256458312261924978057235)
                  ·
                    rfl

theorem cell23_4495057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 6].length) (baseStart_4495057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495057 prefixEnd_4495057 := by exact prefixLift 4495057
  have htrace : WordTrace (prefixWord ++ tailWord_4495057) baseStart_4495057 baseEnd_4495057 := by
    simpa [prefixWord, tailWord_4495057, baseEnd_4495057] using wordTrace_append hprefix tailTrace_4495057
  have hstable : (prefixWord ++ tailWord_4495057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495057).length < 2 ^ (prefixWord ++ tailWord_4495057).sum := by decide
  have hdescent : baseEnd_4495057 < baseStart_4495057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495107 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4]
def baseStart_4495107 : Nat := 118140960795 + 4495107 * 2 ^ 59
def prefixEnd_4495107 : Nat := 4983230072969 + 3 ^ 40 * 4495107 * 2
def baseEnd_4495107 : Nat := 2308150484390049606889885

theorem tailTrace_4495107 : CollatzResearch.WordTrace tailWord_4495107 prefixEnd_4495107 2308150484390049606889885 := by
  unfold tailWord_4495107
  simp only [CollatzResearch.WordTrace]
  refine ⟨163950021326002517000739575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109300014217335011333826383 163950021326002517000739575)
  ·
    refine ⟨245925031989003775501109363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163950021326002517000739575 245925031989003775501109363)
    ·
      refine ⟨368887547983505663251664045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245925031989003775501109363 368887547983505663251664045)
      ·
        refine ⟨138332830493814623719374017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368887547983505663251664045 138332830493814623719374017)
        ·
          refine ⟨103749622870360967789530513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138332830493814623719374017 103749622870360967789530513)
          ·
            refine ⟨77812217152770725842147885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103749622870360967789530513 77812217152770725842147885)
            ·
              refine ⟨29179581432289022190805457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77812217152770725842147885 29179581432289022190805457)
              ·
                refine ⟨21884686074216766643104093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29179581432289022190805457 21884686074216766643104093)
                ·
                  refine ⟨8206757277831287491164035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21884686074216766643104093 8206757277831287491164035)
                  ·
                    refine ⟨12310135916746931236746053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8206757277831287491164035 12310135916746931236746053)
                    ·
                      refine ⟨2308150484390049606889885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12310135916746931236746053 2308150484390049606889885)
                      ·
                        rfl

theorem cell23_4495107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_4495107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495107 prefixEnd_4495107 := by exact prefixLift 4495107
  have htrace : WordTrace (prefixWord ++ tailWord_4495107) baseStart_4495107 baseEnd_4495107 := by
    simpa [prefixWord, tailWord_4495107, baseEnd_4495107] using wordTrace_append hprefix tailTrace_4495107
  have hstable : (prefixWord ++ tailWord_4495107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495107).length < 2 ^ (prefixWord ++ tailWord_4495107).sum := by decide
  have hdescent : baseEnd_4495107 < baseStart_4495107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495141 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_4495141 : Nat := 118140960795 + 4495141 * 2 ^ 59
def prefixEnd_4495141 : Nat := 4983230072969 + 3 ^ 40 * 4495141 * 2
def baseEnd_4495141 : Nat := 2308167942732302473864729

theorem tailTrace_4495141 : CollatzResearch.WordTrace tailWord_4495141 prefixEnd_4495141 2308167942732302473864729 := by
  unfold tailWord_4495141
  simp only [CollatzResearch.WordTrace]
  refine ⟨163951261407879340807477277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109300840938586227204984851 163951261407879340807477277)
  ·
    refine ⟨61481723027954752802803979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163951261407879340807477277 61481723027954752802803979)
    ·
      refine ⟨92222584541932129204205969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61481723027954752802803979 92222584541932129204205969)
      ·
        refine ⟨69166938406449096903154477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92222584541932129204205969 69166938406449096903154477)
        ·
          refine ⟨25937601902418411338682929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69166938406449096903154477 25937601902418411338682929)
          ·
            refine ⟨19453201426813808504012197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25937601902418411338682929 19453201426813808504012197)
            ·
              refine ⟨3647475267527589094502287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19453201426813808504012197 3647475267527589094502287)
              ·
                refine ⟨5471212901291383641753431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647475267527589094502287 5471212901291383641753431)
                ·
                  refine ⟨8206819351937075462630147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471212901291383641753431 8206819351937075462630147)
                  ·
                    refine ⟨12310229027905613193945221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8206819351937075462630147 12310229027905613193945221)
                    ·
                      refine ⟨2308167942732302473864729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12310229027905613193945221 2308167942732302473864729)
                      ·
                        rfl

theorem cell23_4495141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_4495141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495141 prefixEnd_4495141 := by exact prefixLift 4495141
  have htrace : WordTrace (prefixWord ++ tailWord_4495141) baseStart_4495141 baseEnd_4495141 := by
    simpa [prefixWord, tailWord_4495141, baseEnd_4495141] using wordTrace_append hprefix tailTrace_4495141
  have hstable : (prefixWord ++ tailWord_4495141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495141).length < 2 ^ (prefixWord ++ tailWord_4495141).sum := by decide
  have hdescent : baseEnd_4495141 < baseStart_4495141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495161 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4495161 : Nat := 118140960795 + 4495161 * 2 ^ 59
def prefixEnd_4495161 : Nat := 4983230072969 + 3 ^ 40 * 4495161 * 2
def baseEnd_4495161 : Nat := 2308178212345392395614637

theorem tailTrace_4495161 : CollatzResearch.WordTrace tailWord_4495161 prefixEnd_4495161 2308178212345392395614637 := by
  unfold tailWord_4495161
  simp only [CollatzResearch.WordTrace]
  refine ⟨163951990867806884223205337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109301327245204589482136891 163951990867806884223205337)
  ·
    refine ⟨122963993150855163167404003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163951990867806884223205337 122963993150855163167404003)
    ·
      refine ⟨184445989726282744751106005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122963993150855163167404003 184445989726282744751106005)
      ·
        refine ⟨4322952884209751830104047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 184445989726282744751106005 4322952884209751830104047)
        ·
          refine ⟨6484429326314627745156071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322952884209751830104047 6484429326314627745156071)
          ·
            refine ⟨9726643989471941617734107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484429326314627745156071 9726643989471941617734107)
            ·
              refine ⟨14589965984207912426601161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9726643989471941617734107 14589965984207912426601161)
              ·
                refine ⟨10942474488155934319950871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14589965984207912426601161 10942474488155934319950871)
                ·
                  refine ⟨16413711732233901479926307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10942474488155934319950871 16413711732233901479926307)
                  ·
                    refine ⟨24620567598350852219889461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16413711732233901479926307 24620567598350852219889461)
                    ·
                      refine ⟨2308178212345392395614637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24620567598350852219889461 2308178212345392395614637)
                      ·
                        rfl

theorem cell23_4495161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4495161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495161 prefixEnd_4495161 := by exact prefixLift 4495161
  have htrace : WordTrace (prefixWord ++ tailWord_4495161) baseStart_4495161 baseEnd_4495161 := by
    simpa [prefixWord, tailWord_4495161, baseEnd_4495161] using wordTrace_append hprefix tailTrace_4495161
  have hstable : (prefixWord ++ tailWord_4495161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495161).length < 2 ^ (prefixWord ++ tailWord_4495161).sum := by decide
  have hdescent : baseEnd_4495161 < baseStart_4495161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495181 : List Nat := [1, 6, 1, 2, 1, 1, 4, 7]
def baseStart_4495181 : Nat := 118140960795 + 4495181 * 2 ^ 59
def prefixEnd_4495181 : Nat := 4983230072969 + 3 ^ 40 * 4495181 * 2
def baseEnd_4495181 : Nat := 85488462294758604346835

theorem tailTrace_4495181 : CollatzResearch.WordTrace tailWord_4495181 prefixEnd_4495181 85488462294758604346835 := by
  unfold tailWord_4495181
  simp only [CollatzResearch.WordTrace]
  refine ⟨163952720327734427638933397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109301813551822951759288931 163952720327734427638933397)
  ·
    refine ⟨7685283765362551295575003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163952720327734427638933397 7685283765362551295575003)
    ·
      refine ⟨11527925648043826943362505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7685283765362551295575003 11527925648043826943362505)
      ·
        refine ⟨8645944236032870207521879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11527925648043826943362505 8645944236032870207521879)
        ·
          refine ⟨12968916354049305311282819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8645944236032870207521879 12968916354049305311282819)
          ·
            refine ⟨19453374531073957966924229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12968916354049305311282819 19453374531073957966924229)
            ·
              refine ⟨3647507724576367118798293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19453374531073957966924229 3647507724576367118798293)
              ·
                refine ⟨85488462294758604346835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3647507724576367118798293 85488462294758604346835)
                ·
                  rfl

theorem cell23_4495181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 7].length) (baseStart_4495181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495181 prefixEnd_4495181 := by exact prefixLift 4495181
  have htrace : WordTrace (prefixWord ++ tailWord_4495181) baseStart_4495181 baseEnd_4495181 := by
    simpa [prefixWord, tailWord_4495181, baseEnd_4495181] using wordTrace_append hprefix tailTrace_4495181
  have hstable : (prefixWord ++ tailWord_4495181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495181).length < 2 ^ (prefixWord ++ tailWord_4495181).sum := by decide
  have hdescent : baseEnd_4495181 < baseStart_4495181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495201 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_4495201 : Nat := 118140960795 + 4495201 * 2 ^ 59
def prefixEnd_4495201 : Nat := 4983230072969 + 3 ^ 40 * 4495201 * 2
def baseEnd_4495201 : Nat := 2308198751571572239114453

theorem tailTrace_4495201 : CollatzResearch.WordTrace tailWord_4495201 prefixEnd_4495201 2308198751571572239114453 := by
  unfold tailWord_4495201
  simp only [CollatzResearch.WordTrace]
  refine ⟨163953449787661971054661457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109302299858441314036440971 163953449787661971054661457)
  ·
    refine ⟨122965087340746478290996093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163953449787661971054661457 122965087340746478290996093)
    ·
      refine ⟨46111907752779929359123535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122965087340746478290996093 46111907752779929359123535)
      ·
        refine ⟨69167861629169894038685303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46111907752779929359123535 69167861629169894038685303)
        ·
          refine ⟨103751792443754841058027955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69167861629169894038685303 103751792443754841058027955)
          ·
            refine ⟨155627688665632261587041933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103751792443754841058027955 155627688665632261587041933)
            ·
              refine ⟨58360383249612098095140725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155627688665632261587041933 58360383249612098095140725)
              ·
                refine ⟨5471285929651134196419443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58360383249612098095140725 5471285929651134196419443)
                ·
                  refine ⟨8206928894476701294629165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471285929651134196419443 8206928894476701294629165)
                  ·
                    refine ⟨3077598335428762985485937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8206928894476701294629165 3077598335428762985485937)
                    ·
                      refine ⟨2308198751571572239114453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077598335428762985485937 2308198751571572239114453)
                      ·
                        rfl

theorem cell23_4495201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_4495201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495201 prefixEnd_4495201 := by exact prefixLift 4495201
  have htrace : WordTrace (prefixWord ++ tailWord_4495201) baseStart_4495201 baseEnd_4495201 := by
    simpa [prefixWord, tailWord_4495201, baseEnd_4495201] using wordTrace_append hprefix tailTrace_4495201
  have hstable : (prefixWord ++ tailWord_4495201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495201).length < 2 ^ (prefixWord ++ tailWord_4495201).sum := by decide
  have hdescent : baseEnd_4495201 < baseStart_4495201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495217 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_4495217 : Nat := 118140960795 + 4495217 * 2 ^ 59
def prefixEnd_4495217 : Nat := 4983230072969 + 3 ^ 40 * 4495217 * 2
def baseEnd_4495217 : Nat := 2308206967262044176514379

theorem tailTrace_4495217 : CollatzResearch.WordTrace tailWord_4495217 prefixEnd_4495217 2308206967262044176514379 := by
  unfold tailWord_4495217
  simp only [CollatzResearch.WordTrace]
  refine ⟨163954033355604005787243905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109302688903736003858162603 163954033355604005787243905)
  ·
    refine ⟨122965525016703004340432929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163954033355604005787243905 122965525016703004340432929)
    ·
      refine ⟨92224143762527253255324697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122965525016703004340432929 92224143762527253255324697)
      ·
        refine ⟨69168107821895439941493523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92224143762527253255324697 69168107821895439941493523)
        ·
          refine ⟨103752161732843159912240285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69168107821895439941493523 103752161732843159912240285)
          ·
            refine ⟨38907060649816184967090107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103752161732843159912240285 38907060649816184967090107)
            ·
              refine ⟨58360590974724277450635161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38907060649816184967090107 58360590974724277450635161)
              ·
                refine ⟨43770443231043208087976371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58360590974724277450635161 43770443231043208087976371)
                ·
                  refine ⟨65655664846564812131964557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43770443231043208087976371 65655664846564812131964557)
                  ·
                    refine ⟨24620874317461804549486709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65655664846564812131964557 24620874317461804549486709)
                    ·
                      refine ⟨2308206967262044176514379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24620874317461804549486709 2308206967262044176514379)
                      ·
                        rfl

theorem cell23_4495217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_4495217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495217 prefixEnd_4495217 := by exact prefixLift 4495217
  have htrace : WordTrace (prefixWord ++ tailWord_4495217) baseStart_4495217 baseEnd_4495217 := by
    simpa [prefixWord, tailWord_4495217, baseEnd_4495217] using wordTrace_append hprefix tailTrace_4495217
  have hstable : (prefixWord ++ tailWord_4495217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495217).length < 2 ^ (prefixWord ++ tailWord_4495217).sum := by decide
  have hdescent : baseEnd_4495217 < baseStart_4495217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495227 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_4495227 : Nat := 118140960795 + 4495227 * 2 ^ 59
def prefixEnd_4495227 : Nat := 4983230072969 + 3 ^ 40 * 4495227 * 2
def baseEnd_4495227 : Nat := 2308212102068589137389333

theorem tailTrace_4495227 : CollatzResearch.WordTrace tailWord_4495227 prefixEnd_4495227 2308212102068589137389333 := by
  unfold tailWord_4495227
  simp only [CollatzResearch.WordTrace]
  refine ⟨163954398085567777495107935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109302932057045184996738623 163954398085567777495107935)
  ·
    refine ⟨245931597128351666242661903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163954398085567777495107935 245931597128351666242661903)
    ·
      refine ⟨368897395692527499363992855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245931597128351666242661903 368897395692527499363992855)
      ·
        refine ⟨553346093538791249045989283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368897395692527499363992855 553346093538791249045989283)
        ·
          refine ⟨830019140308186873568983925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553346093538791249045989283 830019140308186873568983925)
          ·
            refine ⟨77814294403892519397092243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 830019140308186873568983925 77814294403892519397092243)
            ·
              refine ⟨116721441605838779095638365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77814294403892519397092243 116721441605838779095638365)
              ·
                refine ⟨43770540602189542160864387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116721441605838779095638365 43770540602189542160864387)
                ·
                  refine ⟨65655810903284313241296581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43770540602189542160864387 65655810903284313241296581)
                  ·
                    refine ⟨12310464544365808732743109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65655810903284313241296581 12310464544365808732743109)
                    ·
                      refine ⟨2308212102068589137389333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12310464544365808732743109 2308212102068589137389333)
                      ·
                        rfl

theorem cell23_4495227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_4495227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495227 prefixEnd_4495227 := by exact prefixLift 4495227
  have htrace : WordTrace (prefixWord ++ tailWord_4495227) baseStart_4495227 baseEnd_4495227 := by
    simpa [prefixWord, tailWord_4495227, baseEnd_4495227] using wordTrace_append hprefix tailTrace_4495227
  have hstable : (prefixWord ++ tailWord_4495227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495227).length < 2 ^ (prefixWord ++ tailWord_4495227).sum := by decide
  have hdescent : baseEnd_4495227 < baseStart_4495227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495237 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 9]
def baseStart_4495237 : Nat := 118140960795 + 4495237 * 2 ^ 59
def prefixEnd_4495237 : Nat := 4983230072969 + 3 ^ 40 * 4495237 * 2
def baseEnd_4495237 : Nat := 256468581875014899807143

theorem tailTrace_4495237 : CollatzResearch.WordTrace tailWord_4495237 prefixEnd_4495237 256468581875014899807143 := by
  unfold tailWord_4495237
  simp only [CollatzResearch.WordTrace]
  refine ⟨163954762815531549202971965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109303175210354366135314643 163954762815531549202971965)
  ·
    refine ⟨61483036055824330951114487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163954762815531549202971965 61483036055824330951114487)
    ·
      refine ⟨92224554083736496426671731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61483036055824330951114487 92224554083736496426671731)
      ·
        refine ⟨138336831125604744640007597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92224554083736496426671731 138336831125604744640007597)
        ·
          refine ⟨51876311672101779240002849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138336831125604744640007597 51876311672101779240002849)
          ·
            refine ⟨38907233754076334430002137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51876311672101779240002849 38907233754076334430002137)
            ·
              refine ⟨29180425315557250822501603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38907233754076334430002137 29180425315557250822501603)
              ·
                refine ⟨43770637973335876233752405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29180425315557250822501603 43770637973335876233752405)
                ·
                  refine ⟨256468581875014899807143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43770637973335876233752405 256468581875014899807143)
                  ·
                    rfl

theorem cell23_4495237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_4495237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495237 prefixEnd_4495237 := by exact prefixLift 4495237
  have htrace : WordTrace (prefixWord ++ tailWord_4495237) baseStart_4495237 baseEnd_4495237 := by
    simpa [prefixWord, tailWord_4495237, baseEnd_4495237] using wordTrace_append hprefix tailTrace_4495237
  have hstable : (prefixWord ++ tailWord_4495237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495237).length < 2 ^ (prefixWord ++ tailWord_4495237).sum := by decide
  have hdescent : baseEnd_4495237 < baseStart_4495237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495264 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_4495264 : Nat := 118140960795 + 4495264 * 2 ^ 59
def prefixEnd_4495264 : Nat := 4983230072969 + 3 ^ 40 * 4495264 * 2
def baseEnd_4495264 : Nat := 2308231100852805492626663

theorem tailTrace_4495264 : CollatzResearch.WordTrace tailWord_4495264 prefixEnd_4495264 2308231100852805492626663 := by
  unfold tailWord_4495264
  simp only [CollatzResearch.WordTrace]
  refine ⟨81977873793216866407102423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109303831724289155209469897 81977873793216866407102423)
  ·
    refine ⟨122966810689825299610653635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81977873793216866407102423 122966810689825299610653635)
    ·
      refine ⟨184450216034737949415980453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122966810689825299610653635 184450216034737949415980453)
      ·
        refine ⟨34584415506513365515496335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184450216034737949415980453 34584415506513365515496335)
        ·
          refine ⟨51876623259770048273244503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34584415506513365515496335 51876623259770048273244503)
          ·
            refine ⟨77814934889655072409866755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51876623259770048273244503 77814934889655072409866755)
            ·
              refine ⟨116722402334482608614800133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77814934889655072409866755 116722402334482608614800133)
              ·
                refine ⟨21885450437715489115275025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116722402334482608614800133 21885450437715489115275025)
                ·
                  refine ⟨16414087828286616836456269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21885450437715489115275025 16414087828286616836456269)
                  ·
                    refine ⟨6155282935607481313671101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16414087828286616836456269 6155282935607481313671101)
                    ·
                      refine ⟨2308231100852805492626663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6155282935607481313671101 2308231100852805492626663)
                      ·
                        rfl

theorem cell23_4495264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_4495264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495264 prefixEnd_4495264 := by exact prefixLift 4495264
  have htrace : WordTrace (prefixWord ++ tailWord_4495264) baseStart_4495264 baseEnd_4495264 := by
    simpa [prefixWord, tailWord_4495264, baseEnd_4495264] using wordTrace_append hprefix tailTrace_4495264
  have hstable : (prefixWord ++ tailWord_4495264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495264).length < 2 ^ (prefixWord ++ tailWord_4495264).sum := by decide
  have hdescent : baseEnd_4495264 < baseStart_4495264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495267 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 7]
def baseStart_4495267 : Nat := 118140960795 + 4495267 * 2 ^ 59
def prefixEnd_4495267 : Nat := 4983230072969 + 3 ^ 40 * 4495267 * 2
def baseEnd_4495267 : Nat := 769410880431589660296383

theorem tailTrace_4495267 : CollatzResearch.WordTrace tailWord_4495267 prefixEnd_4495267 769410880431589660296383 := by
  unfold tailWord_4495267
  simp only [CollatzResearch.WordTrace]
  refine ⟨163955857005422864326564055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109303904670281909551042703 163955857005422864326564055)
  ·
    refine ⟨245933785508134296489846083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163955857005422864326564055 245933785508134296489846083)
    ·
      refine ⟨368900678262201444734769125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245933785508134296489846083 368900678262201444734769125)
      ·
        refine ⟨69168877174162770887769211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 368900678262201444734769125 69168877174162770887769211)
        ·
          refine ⟨103753315761244156331653817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69168877174162770887769211 103753315761244156331653817)
          ·
            refine ⟨77814986820933117248740363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103753315761244156331653817 77814986820933117248740363)
            ·
              refine ⟨116722480231399675873110545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77814986820933117248740363 116722480231399675873110545)
              ·
                refine ⟨87541860173549756904832909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116722480231399675873110545 87541860173549756904832909)
                ·
                  refine ⟨32828197565081158839312341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87541860173549756904832909 32828197565081158839312341)
                  ·
                    refine ⟨769410880431589660296383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32828197565081158839312341 769410880431589660296383)
                    ·
                      rfl

theorem cell23_4495267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_4495267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495267 prefixEnd_4495267 := by exact prefixLift 4495267
  have htrace : WordTrace (prefixWord ++ tailWord_4495267) baseStart_4495267 baseEnd_4495267 := by
    simpa [prefixWord, tailWord_4495267, baseEnd_4495267] using wordTrace_append hprefix tailTrace_4495267
  have hstable : (prefixWord ++ tailWord_4495267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495267).length < 2 ^ (prefixWord ++ tailWord_4495267).sum := by decide
  have hdescent : baseEnd_4495267 < baseStart_4495267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495281 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_4495281 : Nat := 118140960795 + 4495281 * 2 ^ 59
def prefixEnd_4495281 : Nat := 4983230072969 + 3 ^ 40 * 4495281 * 2
def baseEnd_4495281 : Nat := 2308239830023931926114085

theorem tailTrace_4495281 : CollatzResearch.WordTrace tailWord_4495281 prefixEnd_4495281 2308239830023931926114085 := by
  unfold tailWord_4495281
  simp only [CollatzResearch.WordTrace]
  refine ⟨163956367627372144717573697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109304245084914763145049131 163956367627372144717573697)
  ·
    refine ⟨122967275720529108538180273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163956367627372144717573697 122967275720529108538180273)
    ·
      refine ⟨92225456790396831403635205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122967275720529108538180273 92225456790396831403635205)
      ·
        refine ⟨17292273148199405888181601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92225456790396831403635205 17292273148199405888181601)
        ·
          refine ⟨12969204861149554416136201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17292273148199405888181601 12969204861149554416136201)
          ·
            refine ⟨9726903645862165812102151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12969204861149554416136201 9726903645862165812102151)
            ·
              refine ⟨14590355468793248718153227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9726903645862165812102151 14590355468793248718153227)
              ·
                refine ⟨21885533203189873077229841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14590355468793248718153227 21885533203189873077229841)
                ·
                  refine ⟨16414149902392404807922381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21885533203189873077229841 16414149902392404807922381)
                  ·
                    refine ⟨6155306213397151802970893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16414149902392404807922381 6155306213397151802970893)
                    ·
                      refine ⟨2308239830023931926114085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6155306213397151802970893 2308239830023931926114085)
                      ·
                        rfl

theorem cell23_4495281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_4495281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495281 prefixEnd_4495281 := by exact prefixLift 4495281
  have htrace : WordTrace (prefixWord ++ tailWord_4495281) baseStart_4495281 baseEnd_4495281 := by
    simpa [prefixWord, tailWord_4495281, baseEnd_4495281] using wordTrace_append hprefix tailTrace_4495281
  have hstable : (prefixWord ++ tailWord_4495281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495281).length < 2 ^ (prefixWord ++ tailWord_4495281).sum := by decide
  have hdescent : baseEnd_4495281 < baseStart_4495281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495331 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 3, 4]
def baseStart_4495331 : Nat := 118140960795 + 4495331 * 2 ^ 59
def prefixEnd_4495331 : Nat := 4983230072969 + 3 ^ 40 * 4495331 * 2
def baseEnd_4495331 : Nat := 769421834685552243496285

theorem tailTrace_4495331 : CollatzResearch.WordTrace tailWord_4495331 prefixEnd_4495331 769421834685552243496285 := by
  unfold tailWord_4495331
  simp only [CollatzResearch.WordTrace]
  refine ⟨163958191277191003256893847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109305460851460668837929231 163958191277191003256893847)
  ·
    refine ⟨245937286915786504885340771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163958191277191003256893847 245937286915786504885340771)
    ·
      refine ⟨368905930373679757328011157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245937286915786504885340771 368905930373679757328011157)
      ·
        refine ⟨17292465486266238624750523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 368905930373679757328011157 17292465486266238624750523)
        ·
          refine ⟨25938698229399357937125785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17292465486266238624750523 25938698229399357937125785)
          ·
            refine ⟨19454023672049518452844339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25938698229399357937125785 19454023672049518452844339)
            ·
              refine ⟨29181035508074277679266509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19454023672049518452844339 29181035508074277679266509)
              ·
                refine ⟨10942888315527854129724941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29181035508074277679266509 10942888315527854129724941)
                ·
                  refine ⟨4103583118322945298646853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10942888315527854129724941 4103583118322945298646853)
                  ·
                    refine ⟨769421834685552243496285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4103583118322945298646853 769421834685552243496285)
                    ·
                      rfl

theorem cell23_4495331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 4].length) (baseStart_4495331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495331 prefixEnd_4495331 := by exact prefixLift 4495331
  have htrace : WordTrace (prefixWord ++ tailWord_4495331) baseStart_4495331 baseEnd_4495331 := by
    simpa [prefixWord, tailWord_4495331, baseEnd_4495331] using wordTrace_append hprefix tailTrace_4495331
  have hstable : (prefixWord ++ tailWord_4495331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495331).length < 2 ^ (prefixWord ++ tailWord_4495331).sum := by decide
  have hdescent : baseEnd_4495331 < baseStart_4495331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495344 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 6]
def baseStart_4495344 : Nat := 118140960795 + 4495344 * 2 ^ 59
def prefixEnd_4495344 : Nat := 4983230072969 + 3 ^ 40 * 4495344 * 2
def baseEnd_4495344 : Nat := 256474686589462797736255

theorem tailTrace_4495344 : CollatzResearch.WordTrace tailWord_4495344 prefixEnd_4495344 256474686589462797736255 := by
  unfold tailWord_4495344
  simp only [CollatzResearch.WordTrace]
  refine ⟨81979332713071953238558543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109305776950762604318078057 81979332713071953238558543)
  ·
    refine ⟨122968999069607929857837815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81979332713071953238558543 122968999069607929857837815)
    ·
      refine ⟨184453498604411894786756723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122968999069607929857837815 184453498604411894786756723)
      ·
        refine ⟨276680247906617842180135085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184453498604411894786756723 276680247906617842180135085)
        ·
          refine ⟨103755092964981690817550657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276680247906617842180135085 103755092964981690817550657)
          ·
            refine ⟨77816319723736268113162993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103755092964981690817550657 77816319723736268113162993)
            ·
              refine ⟨58362239792802201084872245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77816319723736268113162993 58362239792802201084872245)
              ·
                refine ⟨5471459980575206351706773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58362239792802201084872245 5471459980575206351706773)
                ·
                  refine ⟨256474686589462797736255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5471459980575206351706773 256474686589462797736255)
                  ·
                    rfl

theorem cell23_4495344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_4495344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495344 prefixEnd_4495344 := by exact prefixLift 4495344
  have htrace : WordTrace (prefixWord ++ tailWord_4495344) baseStart_4495344 baseEnd_4495344 := by
    simpa [prefixWord, tailWord_4495344, baseEnd_4495344] using wordTrace_append hprefix tailTrace_4495344
  have hstable : (prefixWord ++ tailWord_4495344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495344).length < 2 ^ (prefixWord ++ tailWord_4495344).sum := by decide
  have hdescent : baseEnd_4495344 < baseStart_4495344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495358 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4495358 : Nat := 118140960795 + 4495358 * 2 ^ 59
def prefixEnd_4495358 : Nat := 4983230072969 + 3 ^ 40 * 4495358 * 2
def baseEnd_4495358 : Nat := 2308279368034328124851231

theorem tailTrace_4495358 : CollatzResearch.WordTrace tailWord_4495358 prefixEnd_4495358 2308279368034328124851231 := by
  unfold tailWord_4495358
  simp only [CollatzResearch.WordTrace]
  refine ⟨20494897006011648358515841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109306117365395457912084485 20494897006011648358515841)
  ·
    refine ⟨15371172754508736268886881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20494897006011648358515841 15371172754508736268886881)
    ·
      refine ⟨11528379565881552201665161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15371172754508736268886881 11528379565881552201665161)
      ·
        refine ⟨8646284674411164151248871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11528379565881552201665161 8646284674411164151248871)
        ·
          refine ⟨12969427011616746226873307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8646284674411164151248871 12969427011616746226873307)
          ·
            refine ⟨19454140517425119340309961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12969427011616746226873307 19454140517425119340309961)
            ·
              refine ⟨14590605388068839505232471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19454140517425119340309961 14590605388068839505232471)
              ·
                refine ⟨21885908082103259257848707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14590605388068839505232471 21885908082103259257848707)
                ·
                  refine ⟨32828862123154888886773061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21885908082103259257848707 32828862123154888886773061)
                  ·
                    refine ⟨6155411648091541666269949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32828862123154888886773061 6155411648091541666269949)
                    ·
                      refine ⟨2308279368034328124851231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6155411648091541666269949 2308279368034328124851231)
                      ·
                        rfl

theorem cell23_4495358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4495358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495358 prefixEnd_4495358 := by exact prefixLift 4495358
  have htrace : WordTrace (prefixWord ++ tailWord_4495358) baseStart_4495358 baseEnd_4495358 := by
    simpa [prefixWord, tailWord_4495358, baseEnd_4495358] using wordTrace_append hprefix tailTrace_4495358
  have hstable : (prefixWord ++ tailWord_4495358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495358).length < 2 ^ (prefixWord ++ tailWord_4495358).sum := by decide
  have hdescent : baseEnd_4495358 < baseStart_4495358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495365 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_4495365 : Nat := 118140960795 + 4495365 * 2 ^ 59
def prefixEnd_4495365 : Nat := 4983230072969 + 3 ^ 40 * 4495365 * 2
def baseEnd_4495365 : Nat := 769427654132969865821233

theorem tailTrace_4495365 : CollatzResearch.WordTrace tailWord_4495365 prefixEnd_4495365 769427654132969865821233 := by
  unfold tailWord_4495365
  simp only [CollatzResearch.WordTrace]
  refine ⟨163959431359067827063631549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109306287572711884709087699 163959431359067827063631549)
  ·
    refine ⟨61484786759650435148861831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163959431359067827063631549 61484786759650435148861831)
    ·
      refine ⟨92227180139475652723292747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61484786759650435148861831 92227180139475652723292747)
      ·
        refine ⟨138340770209213479084939121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92227180139475652723292747 138340770209213479084939121)
        ·
          refine ⟨103755577656910109313704341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138340770209213479084939121 103755577656910109313704341)
          ·
            refine ⟨4863542702667661374079891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103755577656910109313704341 4863542702667661374079891)
            ·
              refine ⟨7295314054001492061119837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863542702667661374079891 7295314054001492061119837)
              ·
                refine ⟨2735742770250559522919939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7295314054001492061119837 2735742770250559522919939)
                ·
                  refine ⟨4103614155375839284379909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735742770250559522919939 4103614155375839284379909)
                  ·
                    refine ⟨769427654132969865821233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4103614155375839284379909 769427654132969865821233)
                    ·
                      rfl

theorem cell23_4495365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_4495365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495365 prefixEnd_4495365 := by exact prefixLift 4495365
  have htrace : WordTrace (prefixWord ++ tailWord_4495365) baseStart_4495365 baseEnd_4495365 := by
    simpa [prefixWord, tailWord_4495365, baseEnd_4495365] using wordTrace_append hprefix tailTrace_4495365
  have hstable : (prefixWord ++ tailWord_4495365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495365).length < 2 ^ (prefixWord ++ tailWord_4495365).sum := by decide
  have hdescent : baseEnd_4495365 < baseStart_4495365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495408 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_4495408 : Nat := 118140960795 + 4495408 * 2 ^ 59
def prefixEnd_4495408 : Nat := 4983230072969 + 3 ^ 40 * 4495408 * 2
def baseEnd_4495408 : Nat := 769435014022350976408667

theorem tailTrace_4495408 : CollatzResearch.WordTrace tailWord_4495408 prefixEnd_4495408 769435014022350976408667 := by
  unfold tailWord_4495408
  simp only [CollatzResearch.WordTrace]
  refine ⟨81980499848956022703723439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109307333131941363604964585 81980499848956022703723439)
  ·
    refine ⟨122970749773434034055585159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81980499848956022703723439 122970749773434034055585159)
    ·
      refine ⟨184456124660151051083377739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122970749773434034055585159 184456124660151051083377739)
      ·
        refine ⟨276684186990226576625066609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184456124660151051083377739 276684186990226576625066609)
        ·
          refine ⟨207513140242669932468799957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276684186990226576625066609 207513140242669932468799957)
          ·
            refine ⟨4863589224437576542237499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 207513140242669932468799957 4863589224437576542237499)
            ·
              refine ⟨7295383836656364813356249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863589224437576542237499 7295383836656364813356249)
              ·
                refine ⟨5471537877492273610017187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7295383836656364813356249 5471537877492273610017187)
                ·
                  refine ⟨8207306816238410415025781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471537877492273610017187 8207306816238410415025781)
                  ·
                    refine ⟨769435014022350976408667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8207306816238410415025781 769435014022350976408667)
                    ·
                      rfl

theorem cell23_4495408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_4495408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495408 prefixEnd_4495408 := by exact prefixLift 4495408
  have htrace : WordTrace (prefixWord ++ tailWord_4495408) baseStart_4495408 baseEnd_4495408 := by
    simpa [prefixWord, tailWord_4495408, baseEnd_4495408] using wordTrace_append hprefix tailTrace_4495408
  have hstable : (prefixWord ++ tailWord_4495408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495408).length < 2 ^ (prefixWord ++ tailWord_4495408).sum := by decide
  have hdescent : baseEnd_4495408 < baseStart_4495408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495411 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 6, 2]
def baseStart_4495411 : Nat := 118140960795 + 4495411 * 2 ^ 59
def prefixEnd_4495411 : Nat := 4983230072969 + 3 ^ 40 * 4495411 * 2
def baseEnd_4495411 : Nat := 2308306582509016417488487

theorem tailTrace_4495411 : CollatzResearch.WordTrace tailWord_4495411 prefixEnd_4495411 2308306582509016417488487 := by
  unfold tailWord_4495411
  simp only [CollatzResearch.WordTrace]
  refine ⟨163961109116901176919806087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109307406077934117946537391 163961109116901176919806087)
  ·
    refine ⟨245941663675351765379709131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163961109116901176919806087 245941663675351765379709131)
    ·
      refine ⟨368912495513027648069563697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245941663675351765379709131 368912495513027648069563697)
      ·
        refine ⟨276684371634770736052172773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368912495513027648069563697 276684371634770736052172773)
        ·
          refine ⟨51878319681519513009782395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276684371634770736052172773 51878319681519513009782395)
          ·
            refine ⟨77817479522279269514673593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51878319681519513009782395 77817479522279269514673593)
            ·
              refine ⟨58363109641709452136005195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77817479522279269514673593 58363109641709452136005195)
              ·
                refine ⟨87544664462564178204007793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58363109641709452136005195 87544664462564178204007793)
                ·
                  refine ⟨65658498346923133653005845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87544664462564178204007793 65658498346923133653005845)
                  ·
                    refine ⟨3077742110012021889984649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65658498346923133653005845 3077742110012021889984649)
                    ·
                      refine ⟨2308306582509016417488487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077742110012021889984649 2308306582509016417488487)
                      ·
                        rfl

theorem cell23_4495411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6, 2].length) (baseStart_4495411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495411 prefixEnd_4495411 := by exact prefixLift 4495411
  have htrace : WordTrace (prefixWord ++ tailWord_4495411) baseStart_4495411 baseEnd_4495411 := by
    simpa [prefixWord, tailWord_4495411, baseEnd_4495411] using wordTrace_append hprefix tailTrace_4495411
  have hstable : (prefixWord ++ tailWord_4495411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495411).length < 2 ^ (prefixWord ++ tailWord_4495411).sum := by decide
  have hdescent : baseEnd_4495411 < baseStart_4495411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495421 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_4495421 : Nat := 118140960795 + 4495421 * 2 ^ 59
def prefixEnd_4495421 : Nat := 4983230072969 + 3 ^ 40 * 4495421 * 2
def baseEnd_4495421 : Nat := 769437239105187126121147

theorem tailTrace_4495421 : CollatzResearch.WordTrace tailWord_4495421 prefixEnd_4495421 769437239105187126121147 := by
  unfold tailWord_4495421
  simp only [CollatzResearch.WordTrace]
  refine ⟨163961473846864948627670117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109307649231243299085113411 163961473846864948627670117)
  ·
    refine ⟨30742776346287177867688147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163961473846864948627670117 30742776346287177867688147)
    ·
      refine ⟨46114164519430766801532221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30742776346287177867688147 46114164519430766801532221)
      ·
        refine ⟨17292811694786537550574583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46114164519430766801532221 17292811694786537550574583)
        ·
          refine ⟨25939217542179806325861875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17292811694786537550574583 25939217542179806325861875)
          ·
            refine ⟨38908826313269709488792813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25939217542179806325861875 38908826313269709488792813)
            ·
              refine ⟨14590809867476141058297305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38908826313269709488792813 14590809867476141058297305)
              ·
                refine ⟨10943107400607105793722979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14590809867476141058297305 10943107400607105793722979)
                ·
                  refine ⟨16414661100910658690584469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10943107400607105793722979 16414661100910658690584469)
                  ·
                    refine ⟨769437239105187126121147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16414661100910658690584469 769437239105187126121147)
                    ·
                      rfl

theorem cell23_4495421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_4495421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495421 prefixEnd_4495421 := by exact prefixLift 4495421
  have htrace : WordTrace (prefixWord ++ tailWord_4495421) baseStart_4495421 baseEnd_4495421 := by
    simpa [prefixWord, tailWord_4495421, baseEnd_4495421] using wordTrace_append hprefix tailTrace_4495421
  have hstable : (prefixWord ++ tailWord_4495421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495421).length < 2 ^ (prefixWord ++ tailWord_4495421).sum := by decide
  have hdescent : baseEnd_4495421 < baseStart_4495421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495425 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4495425 : Nat := 118140960795 + 4495425 * 2 ^ 59
def prefixEnd_4495425 : Nat := 4983230072969 + 3 ^ 40 * 4495425 * 2
def baseEnd_4495425 : Nat := 769437923746059787571141

theorem tailTrace_4495425 : CollatzResearch.WordTrace tailWord_4495425 prefixEnd_4495425 769437923746059787571141 := by
  unfold tailWord_4495425
  simp only [CollatzResearch.WordTrace]
  refine ⟨163961619738850457310815729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109307746492566971540543819 163961619738850457310815729)
  ·
    refine ⟨122971214804137842983111797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163961619738850457310815729 122971214804137842983111797)
    ·
      refine ⟨11528551387887922779666731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122971214804137842983111797 11528551387887922779666731)
      ·
        refine ⟨17292827081831884169500097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11528551387887922779666731 17292827081831884169500097)
        ·
          refine ⟨12969620311373913127125073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17292827081831884169500097 12969620311373913127125073)
          ·
            refine ⟨9727215233530434845343805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12969620311373913127125073 9727215233530434845343805)
            ·
              refine ⟨3647705712573913067003927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9727215233530434845343805 3647705712573913067003927)
              ·
                refine ⟨5471558568860869600505891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3647705712573913067003927 5471558568860869600505891)
                ·
                  refine ⟨8207337853291304400758837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471558568860869600505891 8207337853291304400758837)
                  ·
                    refine ⟨769437923746059787571141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8207337853291304400758837 769437923746059787571141)
                    ·
                      rfl

theorem cell23_4495425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4495425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495425 prefixEnd_4495425 := by exact prefixLift 4495425
  have htrace : WordTrace (prefixWord ++ tailWord_4495425) baseStart_4495425 baseEnd_4495425 := by
    simpa [prefixWord, tailWord_4495425, baseEnd_4495425] using wordTrace_append hprefix tailTrace_4495425
  have hstable : (prefixWord ++ tailWord_4495425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495425).length < 2 ^ (prefixWord ++ tailWord_4495425).sum := by decide
  have hdescent : baseEnd_4495425 < baseStart_4495425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495438 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_4495438 : Nat := 118140960795 + 4495438 * 2 ^ 59
def prefixEnd_4495438 : Nat := 4983230072969 + 3 ^ 40 * 4495438 * 2
def baseEnd_4495438 : Nat := 769440148828895937283621

theorem tailTrace_4495438 : CollatzResearch.WordTrace tailWord_4495438 prefixEnd_4495438 769440148828895937283621 := by
  unfold tailWord_4495438
  simp only [CollatzResearch.WordTrace]
  refine ⟨20495261735975420066379871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109308062591868907020692645 20495261735975420066379871)
  ·
    refine ⟨30742892603963130099569807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20495261735975420066379871 30742892603963130099569807)
    ·
      refine ⟨46114338905944695149354711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30742892603963130099569807 46114338905944695149354711)
      ·
        refine ⟨69171508358917042724032067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46114338905944695149354711 69171508358917042724032067)
        ·
          refine ⟨103757262538375564086048101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69171508358917042724032067 103757262538375564086048101)
          ·
            refine ⟨19454486725945418266134019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103757262538375564086048101 19454486725945418266134019)
            ·
              refine ⟨29181730088918127399201029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19454486725945418266134019 29181730088918127399201029)
              ·
                refine ⟨5471574391672148887350193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29181730088918127399201029 5471574391672148887350193)
                ·
                  refine ⟨4103680793754111665512645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5471574391672148887350193 4103680793754111665512645)
                  ·
                    refine ⟨769440148828895937283621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4103680793754111665512645 769440148828895937283621)
                    ·
                      rfl

theorem cell23_4495438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_4495438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495438 prefixEnd_4495438 := by exact prefixLift 4495438
  have htrace : WordTrace (prefixWord ++ tailWord_4495438) baseStart_4495438 baseEnd_4495438 := by
    simpa [prefixWord, tailWord_4495438, baseEnd_4495438] using wordTrace_append hprefix tailTrace_4495438
  have hstable : (prefixWord ++ tailWord_4495438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495438).length < 2 ^ (prefixWord ++ tailWord_4495438).sum := by decide
  have hdescent : baseEnd_4495438 < baseStart_4495438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495495 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_4495495 : Nat := 118140960795 + 4495495 * 2 ^ 59
def prefixEnd_4495495 : Nat := 4983230072969 + 3 ^ 40 * 4495495 * 2
def baseEnd_4495495 : Nat := 2308349714883994088838101

theorem tailTrace_4495495 : CollatzResearch.WordTrace tailWord_4495495 prefixEnd_4495495 2308349714883994088838101 := by
  unfold tailWord_4495495
  simp only [CollatzResearch.WordTrace]
  refine ⟨163964172848596859265863939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109309448565731239510575959 163964172848596859265863939)
  ·
    refine ⟨245946259272895288898795909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163964172848596859265863939 245946259272895288898795909)
    ·
      refine ⟨46114923613667866668524233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245946259272895288898795909 46114923613667866668524233)
      ·
        refine ⟨34586192710250900001393175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46114923613667866668524233 34586192710250900001393175)
        ·
          refine ⟨51879289065376350002089763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34586192710250900001393175 51879289065376350002089763)
          ·
            refine ⟨77818933598064525003134645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51879289065376350002089763 77818933598064525003134645)
            ·
              refine ⟨7295525024818549219043873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77818933598064525003134645 7295525024818549219043873)
              ·
                refine ⟨5471643768613911914282905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7295525024818549219043873 5471643768613911914282905)
                ·
                  refine ⟨4103732826460433935712179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5471643768613911914282905 4103732826460433935712179)
                  ·
                    refine ⟨6155599239690650903568269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4103732826460433935712179 6155599239690650903568269)
                    ·
                      refine ⟨2308349714883994088838101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6155599239690650903568269 2308349714883994088838101)
                      ·
                        rfl

theorem cell23_4495495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_4495495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495495 prefixEnd_4495495 := by exact prefixLift 4495495
  have htrace : WordTrace (prefixWord ++ tailWord_4495495) baseStart_4495495 baseEnd_4495495 := by
    simpa [prefixWord, tailWord_4495495, baseEnd_4495495] using wordTrace_append hprefix tailTrace_4495495
  have hstable : (prefixWord ++ tailWord_4495495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495495).length < 2 ^ (prefixWord ++ tailWord_4495495).sum := by decide
  have hdescent : baseEnd_4495495 < baseStart_4495495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495512 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4495512 : Nat := 118140960795 + 4495512 * 2 ^ 59
def prefixEnd_4495512 : Nat := 4983230072969 + 3 ^ 40 * 4495512 * 2
def baseEnd_4495512 : Nat := 2308358444055120522325523

theorem tailTrace_4495512 : CollatzResearch.WordTrace tailWord_4495512 prefixEnd_4495512 2308358444055120522325523 := by
  unfold tailWord_4495512
  simp only [CollatzResearch.WordTrace]
  refine ⟨81982396444767635584616395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109309861926356847446155193 81982396444767635584616395)
  ·
    refine ⟨122973594667151453376924593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81982396444767635584616395 122973594667151453376924593)
    ·
      refine ⟨92230196000363590032693445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122973594667151453376924593 92230196000363590032693445)
      ·
        refine ⟨17293161750068173131130021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92230196000363590032693445 17293161750068173131130021)
        ·
          refine ⟨3242467828137782462086879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17293161750068173131130021 3242467828137782462086879)
          ·
            refine ⟨4863701742206673693130319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242467828137782462086879 4863701742206673693130319)
            ·
              refine ⟨7295552613310010539695479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863701742206673693130319 7295552613310010539695479)
              ·
                refine ⟨10943328919965015809543219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295552613310010539695479 10943328919965015809543219)
                ·
                  refine ⟨16414993379947523714314829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10943328919965015809543219 16414993379947523714314829)
                  ·
                    refine ⟨6155622517480321392868061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16414993379947523714314829 6155622517480321392868061)
                    ·
                      refine ⟨2308358444055120522325523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6155622517480321392868061 2308358444055120522325523)
                      ·
                        rfl

theorem cell23_4495512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4495512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495512 prefixEnd_4495512 := by exact prefixLift 4495512
  have htrace : WordTrace (prefixWord ++ tailWord_4495512) baseStart_4495512 baseEnd_4495512 := by
    simpa [prefixWord, tailWord_4495512, baseEnd_4495512] using wordTrace_append hprefix tailTrace_4495512
  have hstable : (prefixWord ++ tailWord_4495512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495512).length < 2 ^ (prefixWord ++ tailWord_4495512).sum := by decide
  have hdescent : baseEnd_4495512 < baseStart_4495512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495522 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_4495522 : Nat := 118140960795 + 4495522 * 2 ^ 59
def prefixEnd_4495522 : Nat := 4983230072969 + 3 ^ 40 * 4495522 * 2
def baseEnd_4495522 : Nat := 2308363578861665483200477

theorem tailTrace_4495522 : CollatzResearch.WordTrace tailWord_4495522 prefixEnd_4495522 2308363578861665483200477 := by
  unfold tailWord_4495522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40991289404874760719274205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109310105079666028584731213 40991289404874760719274205)
  ·
    refine ⟨15371733526828035269727827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40991289404874760719274205 15371733526828035269727827)
    ·
      refine ⟨23057600290242052904591741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15371733526828035269727827 23057600290242052904591741)
      ·
        refine ⟨8646600108840769839221903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23057600290242052904591741 8646600108840769839221903)
        ·
          refine ⟨12969900163261154758832855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8646600108840769839221903 12969900163261154758832855)
          ·
            refine ⟨19454850244891732138249283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12969900163261154758832855 19454850244891732138249283)
            ·
              refine ⟨29182275367337598207373925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19454850244891732138249283 29182275367337598207373925)
              ·
                refine ⟨5471676631375799663882611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29182275367337598207373925 5471676631375799663882611)
                ·
                  refine ⟨8207514947063699495823917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471676631375799663882611 8207514947063699495823917)
                  ·
                    refine ⟨3077818105148887310933969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8207514947063699495823917 3077818105148887310933969)
                    ·
                      refine ⟨2308363578861665483200477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077818105148887310933969 2308363578861665483200477)
                      ·
                        rfl

theorem cell23_4495522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_4495522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495522 prefixEnd_4495522 := by exact prefixLift 4495522
  have htrace : WordTrace (prefixWord ++ tailWord_4495522) baseStart_4495522 baseEnd_4495522 := by
    simpa [prefixWord, tailWord_4495522, baseEnd_4495522] using wordTrace_append hprefix tailTrace_4495522
  have hstable : (prefixWord ++ tailWord_4495522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495522).length < 2 ^ (prefixWord ++ tailWord_4495522).sum := by decide
  have hdescent : baseEnd_4495522 < baseStart_4495522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495586 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4495586 : Nat := 118140960795 + 4495586 * 2 ^ 59
def prefixEnd_4495586 : Nat := 4983230072969 + 3 ^ 40 * 4495586 * 2
def baseEnd_4495586 : Nat := 2308396441623553232800183

theorem tailTrace_4495586 : CollatzResearch.WordTrace tailWord_4495586 prefixEnd_4495586 2308396441623553232800183 := by
  unfold tailWord_4495586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40991872972816795451856653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109311661260844787871617741 40991872972816795451856653)
  ·
    refine ⟨15371952364806298294446245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40991872972816795451856653 15371952364806298294446245)
    ·
      refine ⟨2882241068401180930208671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15371952364806298294446245 2882241068401180930208671)
      ·
        refine ⟨4323361602601771395313007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882241068401180930208671 4323361602601771395313007)
        ·
          refine ⟨6485042403902657092969511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323361602601771395313007 6485042403902657092969511)
          ·
            refine ⟨9727563605853985639454267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6485042403902657092969511 9727563605853985639454267)
            ·
              refine ⟨14591345408780978459181401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9727563605853985639454267 14591345408780978459181401)
              ·
                refine ⟨10943509056585733844386051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14591345408780978459181401 10943509056585733844386051)
                ·
                  refine ⟨16415263584878600766579077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10943509056585733844386051 16415263584878600766579077)
                  ·
                    refine ⟨3077861922164737643733577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16415263584878600766579077 3077861922164737643733577)
                    ·
                      refine ⟨2308396441623553232800183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077861922164737643733577 2308396441623553232800183)
                      ·
                        rfl

theorem cell23_4495586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4495586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495586 prefixEnd_4495586 := by exact prefixLift 4495586
  have htrace : WordTrace (prefixWord ++ tailWord_4495586) baseStart_4495586 baseEnd_4495586 := by
    simpa [prefixWord, tailWord_4495586, baseEnd_4495586] using wordTrace_append hprefix tailTrace_4495586
  have hstable : (prefixWord ++ tailWord_4495586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495586).length < 2 ^ (prefixWord ++ tailWord_4495586).sum := by decide
  have hdescent : baseEnd_4495586 < baseStart_4495586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495608 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_4495608 : Nat := 118140960795 + 4495608 * 2 ^ 59
def prefixEnd_4495608 : Nat := 4983230072969 + 3 ^ 40 * 4495608 * 2
def baseEnd_4495608 : Nat := 2308407738197952146725081

theorem tailTrace_4495608 : CollatzResearch.WordTrace tailWord_4495608 prefixEnd_4495608 2308407738197952146725081 := by
  unfold tailWord_4495608
  simp only [CollatzResearch.WordTrace]
  refine ⟨81984147148593739782363739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109312196198124986376484985 81984147148593739782363739)
  ·
    refine ⟨122976220722890609673545609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81984147148593739782363739 122976220722890609673545609)
    ·
      refine ⟨92232165542167957255159207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122976220722890609673545609 92232165542167957255159207)
      ·
        refine ⟨138348248313251935882738811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92232165542167957255159207 138348248313251935882738811)
        ·
          refine ⟨207522372469877903824108217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138348248313251935882738811 207522372469877903824108217)
          ·
            refine ⟨155641779352408427868081163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207522372469877903824108217 155641779352408427868081163)
            ·
              refine ⟨233462669028612641802121745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155641779352408427868081163 233462669028612641802121745)
              ·
                refine ⟨175097001771459481351591309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233462669028612641802121745 175097001771459481351591309)
                ·
                  refine ⟨65661375664297305506846741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175097001771459481351591309 65661375664297305506846741)
                  ·
                    refine ⟨3077876984263936195633441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65661375664297305506846741 3077876984263936195633441)
                    ·
                      refine ⟨2308407738197952146725081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077876984263936195633441 2308407738197952146725081)
                      ·
                        rfl

theorem cell23_4495608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_4495608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495608 prefixEnd_4495608 := by exact prefixLift 4495608
  have htrace : WordTrace (prefixWord ++ tailWord_4495608) baseStart_4495608 baseEnd_4495608 := by
    simpa [prefixWord, tailWord_4495608, baseEnd_4495608] using wordTrace_append hprefix tailTrace_4495608
  have hstable : (prefixWord ++ tailWord_4495608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495608).length < 2 ^ (prefixWord ++ tailWord_4495608).sum := by decide
  have hdescent : baseEnd_4495608 < baseStart_4495608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495621 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_4495621 : Nat := 118140960795 + 4495621 * 2 ^ 59
def prefixEnd_4495621 : Nat := 4983230072969 + 3 ^ 40 * 4495621 * 2
def baseEnd_4495621 : Nat := 2308414413446460595862521

theorem tailTrace_4495621 : CollatzResearch.WordTrace tailWord_4495621 prefixEnd_4495621 2308414413446460595862521 := by
  unfold tailWord_4495621
  simp only [CollatzResearch.WordTrace]
  refine ⟨163968768446140382784950717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109312512297426921856633811 163968768446140382784950717)
  ·
    refine ⟨61488288167302643544356519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163968768446140382784950717 61488288167302643544356519)
    ·
      refine ⟨92232432250953965316534779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61488288167302643544356519 92232432250953965316534779)
      ·
        refine ⟨138348648376430947974802169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92232432250953965316534779 138348648376430947974802169)
        ·
          refine ⟨103761486282323210981101627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138348648376430947974802169 103761486282323210981101627)
          ·
            refine ⟨155642229423484816471652441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103761486282323210981101627 155642229423484816471652441)
            ·
              refine ⟨116731672067613612353739331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155642229423484816471652441 116731672067613612353739331)
              ·
                refine ⟨175097508101420418530608997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116731672067613612353739331 175097508101420418530608997)
                ·
                  refine ⟨32830782769016328474489187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175097508101420418530608997 32830782769016328474489187)
                  ·
                    refine ⟨49246174153524492711733781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32830782769016328474489187 49246174153524492711733781)
                    ·
                      refine ⟨2308414413446460595862521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49246174153524492711733781 2308414413446460595862521)
                      ·
                        rfl

theorem cell23_4495621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_4495621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495621 prefixEnd_4495621 := by exact prefixLift 4495621
  have htrace : WordTrace (prefixWord ++ tailWord_4495621) baseStart_4495621 baseEnd_4495621 := by
    simpa [prefixWord, tailWord_4495621, baseEnd_4495621] using wordTrace_append hprefix tailTrace_4495621
  have hstable : (prefixWord ++ tailWord_4495621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495621).length < 2 ^ (prefixWord ++ tailWord_4495621).sum := by decide
  have hdescent : baseEnd_4495621 < baseStart_4495621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495625 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 2, 4, 2]
def baseStart_4495625 : Nat := 118140960795 + 4495625 * 2 ^ 59
def prefixEnd_4495625 : Nat := 4983230072969 + 3 ^ 40 * 4495625 * 2
def baseEnd_4495625 : Nat := 2308416467369078580212503

theorem tailTrace_4495625 : CollatzResearch.WordTrace tailWord_4495625 prefixEnd_4495625 2308416467369078580212503 := by
  unfold tailWord_4495625
  simp only [CollatzResearch.WordTrace]
  refine ⟨163968914338125891468096329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109312609558750594312064219 163968914338125891468096329)
  ·
    refine ⟨122976685753594418601072247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163968914338125891468096329 122976685753594418601072247)
    ·
      refine ⟨184465028630391627901608371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122976685753594418601072247 184465028630391627901608371)
      ·
        refine ⟨276697542945587441852412557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184465028630391627901608371 276697542945587441852412557)
        ·
          refine ⟨103761578604595290694654709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276697542945587441852412557 103761578604595290694654709)
          ·
            refine ⟨9727647994180808502623879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103761578604595290694654709 9727647994180808502623879)
            ·
              refine ⟨14591471991271212753935819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9727647994180808502623879 14591471991271212753935819)
              ·
                refine ⟨21887207986906819130903729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14591471991271212753935819 21887207986906819130903729)
                ·
                  refine ⟨16415405990180114348177797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21887207986906819130903729 16415405990180114348177797)
                  ·
                    refine ⟨3077888623158771440283337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16415405990180114348177797 3077888623158771440283337)
                    ·
                      refine ⟨2308416467369078580212503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077888623158771440283337 2308416467369078580212503)
                      ·
                        rfl

theorem cell23_4495625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4, 2].length) (baseStart_4495625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495625 prefixEnd_4495625 := by exact prefixLift 4495625
  have htrace : WordTrace (prefixWord ++ tailWord_4495625) baseStart_4495625 baseEnd_4495625 := by
    simpa [prefixWord, tailWord_4495625, baseEnd_4495625] using wordTrace_append hprefix tailTrace_4495625
  have hstable : (prefixWord ++ tailWord_4495625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495625).length < 2 ^ (prefixWord ++ tailWord_4495625).sum := by decide
  have hdescent : baseEnd_4495625 < baseStart_4495625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495628 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_4495628 : Nat := 118140960795 + 4495628 * 2 ^ 59
def prefixEnd_4495628 : Nat := 4983230072969 + 3 ^ 40 * 4495628 * 2
def baseEnd_4495628 : Nat := 2308418007811042068474989

theorem tailTrace_4495628 : CollatzResearch.WordTrace tailWord_4495628 prefixEnd_4495628 2308418007811042068474989 := by
  unfold tailWord_4495628
  simp only [CollatzResearch.WordTrace]
  refine ⟨81984511878557511490227769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109312682504743348653637025 81984511878557511490227769)
  ·
    refine ⟨61488383908918133617670827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81984511878557511490227769 61488383908918133617670827)
    ·
      refine ⟨92232575863377200426506241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61488383908918133617670827 92232575863377200426506241)
      ·
        refine ⟨69174431897532900319879681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92232575863377200426506241 69174431897532900319879681)
        ·
          refine ⟨51880823923149675239909761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69174431897532900319879681 51880823923149675239909761)
          ·
            refine ⟨38910617942362256429932321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51880823923149675239909761 38910617942362256429932321)
            ·
              refine ⟨29182963456771692322449241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38910617942362256429932321 29182963456771692322449241)
              ·
                refine ⟨21887222592578769241836931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29182963456771692322449241 21887222592578769241836931)
                ·
                  refine ⟨32830833888868153862755397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21887222592578769241836931 32830833888868153862755397)
                  ·
                    refine ⟨6155781354162778849266637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32830833888868153862755397 6155781354162778849266637)
                    ·
                      refine ⟨2308418007811042068474989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6155781354162778849266637 2308418007811042068474989)
                      ·
                        rfl

theorem cell23_4495628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_4495628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495628 prefixEnd_4495628 := by exact prefixLift 4495628
  have htrace : WordTrace (prefixWord ++ tailWord_4495628) baseStart_4495628 baseEnd_4495628 := by
    simpa [prefixWord, tailWord_4495628, baseEnd_4495628] using wordTrace_append hprefix tailTrace_4495628
  have hstable : (prefixWord ++ tailWord_4495628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495628).length < 2 ^ (prefixWord ++ tailWord_4495628).sum := by decide
  have hdescent : baseEnd_4495628 < baseStart_4495628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495642 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_4495642 : Nat := 118140960795 + 4495642 * 2 ^ 59
def prefixEnd_4495642 : Nat := 4983230072969 + 3 ^ 40 * 4495642 * 2
def baseEnd_4495642 : Nat := 2308425196540205013699925

theorem tailTrace_4495642 : CollatzResearch.WordTrace tailWord_4495642 prefixEnd_4495642 2308425196540205013699925 := by
  unfold tailWord_4495642
  simp only [CollatzResearch.WordTrace]
  refine ⟨40992383594766075842866295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109313022919376202247643453 40992383594766075842866295)
  ·
    refine ⟨61488575392149113764299443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40992383594766075842866295 61488575392149113764299443)
    ·
      refine ⟨92232863088223670646449165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61488575392149113764299443 92232863088223670646449165)
      ·
        refine ⟨34587323658083876492418437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92232863088223670646449165 34587323658083876492418437)
        ·
          refine ⟨6485123185890726842328457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34587323658083876492418437 6485123185890726842328457)
          ·
            refine ⟨4863842389418045131746343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6485123185890726842328457 4863842389418045131746343)
            ·
              refine ⟨7295763584127067697619515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863842389418045131746343 7295763584127067697619515)
              ·
                refine ⟨10943645376190601546429273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295763584127067697619515 10943645376190601546429273)
                ·
                  refine ⟨8207734032142951159821955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10943645376190601546429273 8207734032142951159821955)
                  ·
                    refine ⟨12311601048214426739732933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8207734032142951159821955 12311601048214426739732933)
                    ·
                      refine ⟨2308425196540205013699925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12311601048214426739732933 2308425196540205013699925)
                      ·
                        rfl

theorem cell23_4495642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_4495642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495642 prefixEnd_4495642 := by exact prefixLift 4495642
  have htrace : WordTrace (prefixWord ++ tailWord_4495642) baseStart_4495642 baseEnd_4495642 := by
    simpa [prefixWord, tailWord_4495642, baseEnd_4495642] using wordTrace_append hprefix tailTrace_4495642
  have hstable : (prefixWord ++ tailWord_4495642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495642).length < 2 ^ (prefixWord ++ tailWord_4495642).sum := by decide
  have hdescent : baseEnd_4495642 < baseStart_4495642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495652 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_4495652 : Nat := 118140960795 + 4495652 * 2 ^ 59
def prefixEnd_4495652 : Nat := 4983230072969 + 3 ^ 40 * 4495652 * 2
def baseEnd_4495652 : Nat := 769476777115583324858293

theorem tailTrace_4495652 : CollatzResearch.WordTrace tailWord_4495652 prefixEnd_4495652 769476777115583324858293 := by
  unfold tailWord_4495652
  simp only [CollatzResearch.WordTrace]
  refine ⟨81984949554514037539664605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109313266072685383386219473 81984949554514037539664605)
  ·
    refine ⟨30744356082942764077374227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81984949554514037539664605 30744356082942764077374227)
    ·
      refine ⟨46116534124414146116061341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30744356082942764077374227 46116534124414146116061341)
      ·
        refine ⟨17293700296655304793523003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46116534124414146116061341 17293700296655304793523003)
        ·
          refine ⟨25940550444982957190284505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17293700296655304793523003 25940550444982957190284505)
          ·
            refine ⟨19455412833737217892713379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25940550444982957190284505 19455412833737217892713379)
            ·
              refine ⟨29183119250605826839070069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19455412833737217892713379 29183119250605826839070069)
              ·
                refine ⟨2735917429744296266162819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29183119250605826839070069 2735917429744296266162819)
                ·
                  refine ⟨4103876144616444399244229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735917429744296266162819 4103876144616444399244229)
                  ·
                    refine ⟨769476777115583324858293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4103876144616444399244229 769476777115583324858293)
                    ·
                      rfl

theorem cell23_4495652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_4495652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495652 prefixEnd_4495652 := by exact prefixLift 4495652
  have htrace : WordTrace (prefixWord ++ tailWord_4495652) baseStart_4495652 baseEnd_4495652 := by
    simpa [prefixWord, tailWord_4495652, baseEnd_4495652] using wordTrace_append hprefix tailTrace_4495652
  have hstable : (prefixWord ++ tailWord_4495652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495652).length < 2 ^ (prefixWord ++ tailWord_4495652).sum := by decide
  have hdescent : baseEnd_4495652 < baseStart_4495652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495715 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 4]
def baseStart_4495715 : Nat := 118140960795 + 4495715 * 2 ^ 59
def prefixEnd_4495715 : Nat := 4983230072969 + 3 ^ 40 * 4495715 * 2
def baseEnd_4495715 : Nat := 2308462680627983228087089

theorem tailTrace_4495715 : CollatzResearch.WordTrace tailWord_4495715 prefixEnd_4495715 2308462680627983228087089 := by
  unfold tailWord_4495715
  simp only [CollatzResearch.WordTrace]
  refine ⟨163972196907799836838872599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109314797938533224559248399 163972196907799836838872599)
  ·
    refine ⟨245958295361699755258308899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163972196907799836838872599 245958295361699755258308899)
    ·
      refine ⟨368937443042549632887463349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245958295361699755258308899 368937443042549632887463349)
      ·
        refine ⟨34587885285239028083199689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 368937443042549632887463349 34587885285239028083199689)
        ·
          refine ⟨25940913963929271062399767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34587885285239028083199689 25940913963929271062399767)
          ·
            refine ⟨38911370945893906593599651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25940913963929271062399767 38911370945893906593599651)
            ·
              refine ⟨58367056418840859890399477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38911370945893906593599651 58367056418840859890399477)
              ·
                refine ⟨5471911539266330614724951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58367056418840859890399477 5471911539266330614724951)
                ·
                  refine ⟨8207867308899495922087427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471911539266330614724951 8207867308899495922087427)
                  ·
                    refine ⟨12311800963349243883131141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8207867308899495922087427 12311800963349243883131141)
                    ·
                      refine ⟨2308462680627983228087089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12311800963349243883131141 2308462680627983228087089)
                      ·
                        rfl

theorem cell23_4495715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_4495715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495715 prefixEnd_4495715 := by exact prefixLift 4495715
  have htrace : WordTrace (prefixWord ++ tailWord_4495715) baseStart_4495715 baseEnd_4495715 := by
    simpa [prefixWord, tailWord_4495715, baseEnd_4495715] using wordTrace_append hprefix tailTrace_4495715
  have hstable : (prefixWord ++ tailWord_4495715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495715).length < 2 ^ (prefixWord ++ tailWord_4495715).sum := by decide
  have hdescent : baseEnd_4495715 < baseStart_4495715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495725 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_4495725 : Nat := 118140960795 + 4495725 * 2 ^ 59
def prefixEnd_4495725 : Nat := 4983230072969 + 3 ^ 40 * 4495725 * 2
def baseEnd_4495725 : Nat := 769489271811509396320681

theorem tailTrace_4495725 : CollatzResearch.WordTrace tailWord_4495725 prefixEnd_4495725 769489271811509396320681 := by
  unfold tailWord_4495725
  simp only [CollatzResearch.WordTrace]
  refine ⟨163972561637763608546736629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109315041091842405697824419 163972561637763608546736629)
  ·
    refine ⟨15372427653540338301256559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163972561637763608546736629 15372427653540338301256559)
    ·
      refine ⟨23058641480310507451884839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15372427653540338301256559 23058641480310507451884839)
      ·
        refine ⟨34587962220465761177827259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23058641480310507451884839 34587962220465761177827259)
        ·
          refine ⟨51881943330698641766740889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34587962220465761177827259 51881943330698641766740889)
          ·
            refine ⟨38911457498023981325055667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51881943330698641766740889 38911457498023981325055667)
            ·
              refine ⟨58367186247035971987583501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38911457498023981325055667 58367186247035971987583501)
              ·
                refine ⟨21887694842638489495343813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58367186247035971987583501 21887694842638489495343813)
                ·
                  refine ⟨4103942782994716780376965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21887694842638489495343813 4103942782994716780376965)
                  ·
                    refine ⟨769489271811509396320681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4103942782994716780376965 769489271811509396320681)
                    ·
                      rfl

theorem cell23_4495725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_4495725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495725 prefixEnd_4495725 := by exact prefixLift 4495725
  have htrace : WordTrace (prefixWord ++ tailWord_4495725) baseStart_4495725 baseEnd_4495725 := by
    simpa [prefixWord, tailWord_4495725, baseEnd_4495725] using wordTrace_append hprefix tailTrace_4495725
  have hstable : (prefixWord ++ tailWord_4495725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495725).length < 2 ^ (prefixWord ++ tailWord_4495725).sum := by decide
  have hdescent : baseEnd_4495725 < baseStart_4495725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495728 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_4495728 : Nat := 118140960795 + 4495728 * 2 ^ 59
def prefixEnd_4495728 : Nat := 4983230072969 + 3 ^ 40 * 4495728 * 2
def baseEnd_4495728 : Nat := 2308469355876491677224529

theorem tailTrace_4495728 : CollatzResearch.WordTrace tailWord_4495728 prefixEnd_4495728 2308469355876491677224529 := by
  unfold tailWord_4495728
  simp only [CollatzResearch.WordTrace]
  refine ⟨81986335528376370029547919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109315114037835160039397225 81986335528376370029547919)
  ·
    refine ⟨122979503292564555044321879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81986335528376370029547919 122979503292564555044321879)
    ·
      refine ⟨184469254938846832566482819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122979503292564555044321879 184469254938846832566482819)
      ·
        refine ⟨276703882408270248849724229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184469254938846832566482819 276703882408270248849724229)
        ·
          refine ⟨51881977951550671659323293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276703882408270248849724229 51881977951550671659323293)
          ·
            refine ⟨19455741731831501872246235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51881977951550671659323293 19455741731831501872246235)
            ·
              refine ⟨29183612597747252808369353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19455741731831501872246235 29183612597747252808369353)
              ·
                refine ⟨21887709448310439606277015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29183612597747252808369353 21887709448310439606277015)
                ·
                  refine ⟨32831564172465659409415523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21887709448310439606277015 32831564172465659409415523)
                  ·
                    refine ⟨49247346258698489114123285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32831564172465659409415523 49247346258698489114123285)
                    ·
                      refine ⟨2308469355876491677224529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49247346258698489114123285 2308469355876491677224529)
                      ·
                        rfl

theorem cell23_4495728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_4495728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495728 prefixEnd_4495728 := by exact prefixLift 4495728
  have htrace : WordTrace (prefixWord ++ tailWord_4495728) baseStart_4495728 baseEnd_4495728 := by
    simpa [prefixWord, tailWord_4495728, baseEnd_4495728] using wordTrace_append hprefix tailTrace_4495728
  have hstable : (prefixWord ++ tailWord_4495728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495728).length < 2 ^ (prefixWord ++ tailWord_4495728).sum := by decide
  have hdescent : baseEnd_4495728 < baseStart_4495728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495745 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4495745 : Nat := 118140960795 + 4495745 * 2 ^ 59
def prefixEnd_4495745 : Nat := 4983230072969 + 3 ^ 40 * 4495745 * 2
def baseEnd_4495745 : Nat := 2308478085047618110711951

theorem tailTrace_4495745 : CollatzResearch.WordTrace tailWord_4495745 prefixEnd_4495745 2308478085047618110711951 := by
  unfold tailWord_4495745
  simp only [CollatzResearch.WordTrace]
  refine ⟨163973291097691151962464689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109315527398460767974976459 163973291097691151962464689)
  ·
    refine ⟨122979968323268363971848517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163973291097691151962464689 122979968323268363971848517)
    ·
      refine ⟨23058744060612818244721597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122979968323268363971848517 23058744060612818244721597)
      ·
        refine ⟨8647029022729806841770599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23058744060612818244721597 8647029022729806841770599)
        ·
          refine ⟨12970543534094710262655899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8647029022729806841770599 12970543534094710262655899)
          ·
            refine ⟨19455815301142065393983849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12970543534094710262655899 19455815301142065393983849)
            ·
              refine ⟨14591861475856549045487887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19455815301142065393983849 14591861475856549045487887)
              ·
                refine ⟨21887792213784823568231831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14591861475856549045487887 21887792213784823568231831)
                ·
                  refine ⟨32831688320677235352347747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21887792213784823568231831 32831688320677235352347747)
                  ·
                    refine ⟨49247532481015853028521621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32831688320677235352347747 49247532481015853028521621)
                    ·
                      refine ⟨2308478085047618110711951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49247532481015853028521621 2308478085047618110711951)
                      ·
                        rfl

theorem cell23_4495745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4495745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495745 prefixEnd_4495745 := by exact prefixLift 4495745
  have htrace : WordTrace (prefixWord ++ tailWord_4495745) baseStart_4495745 baseEnd_4495745 := by
    simpa [prefixWord, tailWord_4495745, baseEnd_4495745] using wordTrace_append hprefix tailTrace_4495745
  have hstable : (prefixWord ++ tailWord_4495745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495745).length < 2 ^ (prefixWord ++ tailWord_4495745).sum := by decide
  have hdescent : baseEnd_4495745 < baseStart_4495745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495746 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4495746 : Nat := 118140960795 + 4495746 * 2 ^ 59
def prefixEnd_4495746 : Nat := 4983230072969 + 3 ^ 40 * 4495746 * 2
def baseEnd_4495746 : Nat := 769492866176090868933149

theorem tailTrace_4495746 : CollatzResearch.WordTrace tailWord_4495746 prefixEnd_4495746 769492866176090868933149 := by
  unfold tailWord_4495746
  simp only [CollatzResearch.WordTrace]
  refine ⟨40993331892671882283312773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109315551713791686088834061 40993331892671882283312773)
  ·
    refine ⟨7686249729875977928121145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40993331892671882283312773 7686249729875977928121145)
    ·
      refine ⟨5764687297406983446090859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7686249729875977928121145 5764687297406983446090859)
      ·
        refine ⟨8647030946110475169136289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5764687297406983446090859 8647030946110475169136289)
        ·
          refine ⟨6485273209582856376852217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8647030946110475169136289 6485273209582856376852217)
          ·
            refine ⟨4863954907187142282639163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6485273209582856376852217 4863954907187142282639163)
            ·
              refine ⟨7295932360780713423958745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863954907187142282639163 7295932360780713423958745)
              ·
                refine ⟨5471949270585535067969059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7295932360780713423958745 5471949270585535067969059)
                ·
                  refine ⟨8207923905878302601953589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5471949270585535067969059 8207923905878302601953589)
                  ·
                    refine ⟨769492866176090868933149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8207923905878302601953589 769492866176090868933149)
                    ·
                      rfl

theorem cell23_4495746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4495746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495746 prefixEnd_4495746 := by exact prefixLift 4495746
  have htrace : WordTrace (prefixWord ++ tailWord_4495746) baseStart_4495746 baseEnd_4495746 := by
    simpa [prefixWord, tailWord_4495746, baseEnd_4495746] using wordTrace_append hprefix tailTrace_4495746
  have hstable : (prefixWord ++ tailWord_4495746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495746).length < 2 ^ (prefixWord ++ tailWord_4495746).sum := by decide
  have hdescent : baseEnd_4495746 < baseStart_4495746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495783 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4495783 : Nat := 118140960795 + 4495783 * 2 ^ 59
def prefixEnd_4495783 : Nat := 4983230072969 + 3 ^ 40 * 4495783 * 2
def baseEnd_4495783 : Nat := 2308497597312488962036777

theorem tailTrace_4495783 : CollatzResearch.WordTrace tailWord_4495783 prefixEnd_4495783 2308497597312488962036777 := by
  unfold tailWord_4495783
  simp only [CollatzResearch.WordTrace]
  refine ⟨163974677071553484452348003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109316451381035656301565335 163974677071553484452348003)
  ·
    refine ⟨245962015607330226678522005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163974677071553484452348003 245962015607330226678522005)
    ·
      refine ⟨11529469481593604375555719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 245962015607330226678522005 11529469481593604375555719)
      ·
        refine ⟨17294204222390406563333579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11529469481593604375555719 17294204222390406563333579)
        ·
          refine ⟨25941306333585609845000369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17294204222390406563333579 25941306333585609845000369)
          ·
            refine ⟨19455979750189207383750277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25941306333585609845000369 19455979750189207383750277)
            ·
              refine ⟨3647996203160476384453177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19455979750189207383750277 3647996203160476384453177)
              ·
                refine ⟨2735997152370357288339883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647996203160476384453177 2735997152370357288339883)
                ·
                  refine ⟨4103995728555535932509825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735997152370357288339883 4103995728555535932509825)
                  ·
                    refine ⟨3077996796416651949382369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4103995728555535932509825 3077996796416651949382369)
                    ·
                      refine ⟨2308497597312488962036777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3077996796416651949382369 2308497597312488962036777)
                      ·
                        rfl

theorem cell23_4495783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4495783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495783 prefixEnd_4495783 := by exact prefixLift 4495783
  have htrace : WordTrace (prefixWord ++ tailWord_4495783) baseStart_4495783 baseEnd_4495783 := by
    simpa [prefixWord, tailWord_4495783, baseEnd_4495783] using wordTrace_append hprefix tailTrace_4495783
  have hstable : (prefixWord ++ tailWord_4495783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495783).length < 2 ^ (prefixWord ++ tailWord_4495783).sum := by decide
  have hdescent : baseEnd_4495783 < baseStart_4495783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495789 : List Nat := [1, 5, 2, 2, 3, 1, 1, 8]
def baseStart_4495789 : Nat := 118140960795 + 4495789 * 2 ^ 59
def prefixEnd_4495789 : Nat := 4983230072969 + 3 ^ 40 * 4495789 * 2
def baseEnd_4495789 : Nat := 85500025118385775502287

theorem tailTrace_4495789 : CollatzResearch.WordTrace tailWord_4495789 prefixEnd_4495789 85500025118385775502287 := by
  unfold tailWord_4495789
  simp only [CollatzResearch.WordTrace]
  refine ⟨163974895909531747477066421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109316597273021164984710947 163974895909531747477066421)
  ·
    refine ⟨15372646491518601325974977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163974895909531747477066421 15372646491518601325974977)
    ·
      refine ⟨11529484868638950994481233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15372646491518601325974977 11529484868638950994481233)
      ·
        refine ⟨8647113651479213245860925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11529484868638950994481233 8647113651479213245860925)
        ·
          refine ⟨3242667619304704967197847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8647113651479213245860925 3242667619304704967197847)
          ·
            refine ⟨4864001428957057450796771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242667619304704967197847 4864001428957057450796771)
            ·
              refine ⟨7296002143435586176195157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4864001428957057450796771 7296002143435586176195157)
              ·
                refine ⟨85500025118385775502287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7296002143435586176195157 85500025118385775502287)
                ·
                  rfl

theorem cell23_4495789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 8].length) (baseStart_4495789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495789 prefixEnd_4495789 := by exact prefixLift 4495789
  have htrace : WordTrace (prefixWord ++ tailWord_4495789) baseStart_4495789 baseEnd_4495789 := by
    simpa [prefixWord, tailWord_4495789, baseEnd_4495789] using wordTrace_append hprefix tailTrace_4495789
  have hstable : (prefixWord ++ tailWord_4495789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495789).length < 2 ^ (prefixWord ++ tailWord_4495789).sum := by decide
  have hdescent : baseEnd_4495789 < baseStart_4495789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495796 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4495796 : Nat := 118140960795 + 4495796 * 2 ^ 59
def prefixEnd_4495796 : Nat := 4983230072969 + 3 ^ 40 * 4495796 * 2
def baseEnd_4495796 : Nat := 2308504272560997411174217

theorem tailTrace_4495796 : CollatzResearch.WordTrace tailWord_4495796 prefixEnd_4495796 2308504272560997411174217 := by
  unfold tailWord_4495796
  simp only [CollatzResearch.WordTrace]
  refine ⟨81987575610253193836285621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109316767480337591781714161 81987575610253193836285621)
  ·
    refine ⟨7686335213461236922151777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81987575610253193836285621 7686335213461236922151777)
    ·
      refine ⟨5764751410095927691613833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7686335213461236922151777 5764751410095927691613833)
      ·
        refine ⟨4323563557571945768710375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5764751410095927691613833 4323563557571945768710375)
        ·
          refine ⟨6485345336357918653065563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323563557571945768710375 6485345336357918653065563)
          ·
            refine ⟨9728018004536877979598345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6485345336357918653065563 9728018004536877979598345)
            ·
              refine ⟨7296013503402658484698759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9728018004536877979598345 7296013503402658484698759)
              ·
                refine ⟨10944020255103987727048139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7296013503402658484698759 10944020255103987727048139)
                ·
                  refine ⟨16416030382655981590572209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10944020255103987727048139 16416030382655981590572209)
                  ·
                    refine ⟨12312022786991986192929157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16416030382655981590572209 12312022786991986192929157)
                    ·
                      refine ⟨2308504272560997411174217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12312022786991986192929157 2308504272560997411174217)
                      ·
                        rfl

theorem cell23_4495796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4495796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495796 prefixEnd_4495796 := by exact prefixLift 4495796
  have htrace : WordTrace (prefixWord ++ tailWord_4495796) baseStart_4495796 baseEnd_4495796 := by
    simpa [prefixWord, tailWord_4495796, baseEnd_4495796] using wordTrace_append hprefix tailTrace_4495796
  have hstable : (prefixWord ++ tailWord_4495796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495796).length < 2 ^ (prefixWord ++ tailWord_4495796).sum := by decide
  have hdescent : baseEnd_4495796 < baseStart_4495796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495839 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 4, 2, 2]
def baseStart_4495839 : Nat := 118140960795 + 4495839 * 2 ^ 59
def prefixEnd_4495839 : Nat := 4983230072969 + 3 ^ 40 * 4495839 * 2
def baseEnd_4495839 : Nat := 2308526352229140742936519

theorem tailTrace_4495839 : CollatzResearch.WordTrace tailWord_4495839 prefixEnd_4495839 2308526352229140742936519 := by
  unfold tailWord_4495839
  simp only [CollatzResearch.WordTrace]
  refine ⟨163976719559350606016386571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109317813039567070677591047 163976719559350606016386571)
  ·
    refine ⟨245965079339025909024579857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163976719559350606016386571 245965079339025909024579857)
    ·
      refine ⟨184473809504269431768434893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245965079339025909024579857 184473809504269431768434893)
      ·
        refine ⟨69177678564101036913163085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184473809504269431768434893 69177678564101036913163085)
        ·
          refine ⟨25941629461537888842436157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69177678564101036913163085 25941629461537888842436157)
          ·
            refine ⟨9728111048076708315913559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25941629461537888842436157 9728111048076708315913559)
            ·
              refine ⟨14592166572115062473870339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9728111048076708315913559 14592166572115062473870339)
              ·
                refine ⟨21888249858172593710805509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14592166572115062473870339 21888249858172593710805509)
                ·
                  refine ⟨4104046848407361320776033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21888249858172593710805509 4104046848407361320776033)
                  ·
                    refine ⟨3078035136305520990582025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104046848407361320776033 3078035136305520990582025)
                    ·
                      refine ⟨2308526352229140742936519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078035136305520990582025 2308526352229140742936519)
                      ·
                        rfl

theorem cell23_4495839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_4495839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495839 prefixEnd_4495839 := by exact prefixLift 4495839
  have htrace : WordTrace (prefixWord ++ tailWord_4495839) baseStart_4495839 baseEnd_4495839 := by
    simpa [prefixWord, tailWord_4495839, baseEnd_4495839] using wordTrace_append hprefix tailTrace_4495839
  have hstable : (prefixWord ++ tailWord_4495839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495839).length < 2 ^ (prefixWord ++ tailWord_4495839).sum := by decide
  have hdescent : baseEnd_4495839 < baseStart_4495839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495856 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2]
def baseStart_4495856 : Nat := 118140960795 + 4495856 * 2 ^ 59
def prefixEnd_4495856 : Nat := 4983230072969 + 3 ^ 40 * 4495856 * 2
def baseEnd_4495856 : Nat := 2308535081400267176423941

theorem tailTrace_4495856 : CollatzResearch.WordTrace tailWord_4495856 prefixEnd_4495856 2308535081400267176423941 := by
  unfold tailWord_4495856
  simp only [CollatzResearch.WordTrace]
  refine ⟨81988669800144508959877711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109318226400192678613170281 81988669800144508959877711)
  ·
    refine ⟨122983004700216763439816567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81988669800144508959877711 122983004700216763439816567)
    ·
      refine ⟨184474507050325145159724851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122983004700216763439816567 184474507050325145159724851)
      ·
        refine ⟨276711760575487717739587277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184474507050325145159724851 276711760575487717739587277)
        ·
          refine ⟨103766910215807894152345229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276711760575487717739587277 103766910215807894152345229)
          ·
            refine ⟨38912591330927960307129461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103766910215807894152345229 38912591330927960307129461)
            ·
              refine ⟨3648055437274496278793387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38912591330927960307129461 3648055437274496278793387)
              ·
                refine ⟨5472083155911744418190081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648055437274496278793387 5472083155911744418190081)
                ·
                  refine ⟨4104062366933808313642561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5472083155911744418190081 4104062366933808313642561)
                  ·
                    refine ⟨3078046775200356235231921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104062366933808313642561 3078046775200356235231921)
                    ·
                      refine ⟨2308535081400267176423941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078046775200356235231921 2308535081400267176423941)
                      ·
                        rfl

theorem cell23_4495856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2].length) (baseStart_4495856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495856 prefixEnd_4495856 := by exact prefixLift 4495856
  have htrace : WordTrace (prefixWord ++ tailWord_4495856) baseStart_4495856 baseEnd_4495856 := by
    simpa [prefixWord, tailWord_4495856, baseEnd_4495856] using wordTrace_append hprefix tailTrace_4495856
  have hstable : (prefixWord ++ tailWord_4495856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495856).length < 2 ^ (prefixWord ++ tailWord_4495856).sum := by decide
  have hdescent : baseEnd_4495856 < baseStart_4495856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495875 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 2, 5]
def baseStart_4495875 : Nat := 118140960795 + 4495875 * 2 ^ 59
def prefixEnd_4495875 : Nat := 4983230072969 + 3 ^ 40 * 4495875 * 2
def baseEnd_4495875 : Nat := 769514945844234200695451

theorem tailTrace_4495875 : CollatzResearch.WordTrace tailWord_4495875 prefixEnd_4495875 769514945844234200695451 := by
  unfold tailWord_4495875
  simp only [CollatzResearch.WordTrace]
  refine ⟨163978032587220184164697079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109318688391480122776464719 163978032587220184164697079)
  ·
    refine ⟨245967048880830276247045619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163978032587220184164697079 245967048880830276247045619)
    ·
      refine ⟨368950573321245414370568429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245967048880830276247045619 368950573321245414370568429)
      ·
        refine ⟨138356464995467030388963161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368950573321245414370568429 138356464995467030388963161)
        ·
          refine ⟨103767348746600272791722371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138356464995467030388963161 103767348746600272791722371)
          ·
            refine ⟨155651023119900409187583557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103767348746600272791722371 155651023119900409187583557)
            ·
              refine ⟨29184566834981326722671917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155651023119900409187583557 29184566834981326722671917)
              ·
                refine ⟨10944212563117997521001969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29184566834981326722671917 10944212563117997521001969)
                ·
                  refine ⟨8208159422338498140751477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10944212563117997521001969 8208159422338498140751477)
                  ·
                    refine ⟨769514945844234200695451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8208159422338498140751477 769514945844234200695451)
                    ·
                      rfl

theorem cell23_4495875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 5].length) (baseStart_4495875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495875 prefixEnd_4495875 := by exact prefixLift 4495875
  have htrace : WordTrace (prefixWord ++ tailWord_4495875) baseStart_4495875 baseEnd_4495875 := by
    simpa [prefixWord, tailWord_4495875, baseEnd_4495875] using wordTrace_append hprefix tailTrace_4495875
  have hstable : (prefixWord ++ tailWord_4495875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495875).length < 2 ^ (prefixWord ++ tailWord_4495875).sum := by decide
  have hdescent : baseEnd_4495875 < baseStart_4495875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495915 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3]
def baseStart_4495915 : Nat := 118140960795 + 4495915 * 2 ^ 59
def prefixEnd_4495915 : Nat := 4983230072969 + 3 ^ 40 * 4495915 * 2
def baseEnd_4495915 : Nat := 2308565376758882445586169

theorem tailTrace_4495915 : CollatzResearch.WordTrace tailWord_4495915 prefixEnd_4495915 2308565376758882445586169 := by
  unfold tailWord_4495915
  simp only [CollatzResearch.WordTrace]
  refine ⟨163979491507075270996153199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109319661004716847330768799 163979491507075270996153199)
  ·
    refine ⟨245969237260612906494229799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163979491507075270996153199 245969237260612906494229799)
    ·
      refine ⟨368953855890919359741344699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245969237260612906494229799 368953855890919359741344699)
      ·
        refine ⟨553430783836379039612017049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368953855890919359741344699 553430783836379039612017049)
        ·
          refine ⟨415073087877284279709012787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553430783836379039612017049 415073087877284279709012787)
          ·
            refine ⟨622609631815926419563519181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415073087877284279709012787 622609631815926419563519181)
            ·
              refine ⟨233478611930972407336319693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 622609631815926419563519181 233478611930972407336319693)
              ·
                refine ⟨87554479474114652751119885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233478611930972407336319693 87554479474114652751119885)
                ·
                  refine ⟨32832929802792994781669957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87554479474114652751119885 32832929802792994781669957)
                  ·
                    refine ⟨6156174338023686521563117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32832929802792994781669957 6156174338023686521563117)
                    ·
                      refine ⟨2308565376758882445586169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6156174338023686521563117 2308565376758882445586169)
                      ·
                        rfl

theorem cell23_4495915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 3].length) (baseStart_4495915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495915 prefixEnd_4495915 := by exact prefixLift 4495915
  have htrace : WordTrace (prefixWord ++ tailWord_4495915) baseStart_4495915 baseEnd_4495915 := by
    simpa [prefixWord, tailWord_4495915, baseEnd_4495915] using wordTrace_append hprefix tailTrace_4495915
  have hstable : (prefixWord ++ tailWord_4495915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495915).length < 2 ^ (prefixWord ++ tailWord_4495915).sum := by decide
  have hdescent : baseEnd_4495915 < baseStart_4495915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495922 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_4495922 : Nat := 118140960795 + 4495922 * 2 ^ 59
def prefixEnd_4495922 : Nat := 4983230072969 + 3 ^ 40 * 4495922 * 2
def baseEnd_4495922 : Nat := 769522990374487972732879

theorem tailTrace_4495922 : CollatzResearch.WordTrace tailWord_4495922 prefixEnd_4495922 769522990374487972732879 := by
  unfold tailWord_4495922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40994936704512477797914505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109319831212033274127772013 40994936704512477797914505)
  ·
    refine ⟨30746202528384358348435879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40994936704512477797914505 30746202528384358348435879)
    ·
      refine ⟨46119303792576537522653819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30746202528384358348435879 46119303792576537522653819)
      ·
        refine ⟨69178955688864806283980729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46119303792576537522653819 69178955688864806283980729)
        ·
          refine ⟨51884216766648604712985547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69178955688864806283980729 51884216766648604712985547)
          ·
            refine ⟨77826325149972907069478321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51884216766648604712985547 77826325149972907069478321)
            ·
              refine ⟨58369743862479680302108741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77826325149972907069478321 58369743862479680302108741)
              ·
                refine ⟨10944326974214940056645389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58369743862479680302108741 10944326974214940056645389)
                ·
                  refine ⟨4104122615330602521242021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10944326974214940056645389 4104122615330602521242021)
                  ·
                    refine ⟨769522990374487972732879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104122615330602521242021 769522990374487972732879)
                    ·
                      rfl

theorem cell23_4495922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_4495922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495922 prefixEnd_4495922 := by exact prefixLift 4495922
  have htrace : WordTrace (prefixWord ++ tailWord_4495922) baseStart_4495922 baseEnd_4495922 := by
    simpa [prefixWord, tailWord_4495922, baseEnd_4495922] using wordTrace_append hprefix tailTrace_4495922
  have hstable : (prefixWord ++ tailWord_4495922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495922).length < 2 ^ (prefixWord ++ tailWord_4495922).sum := by decide
  have hdescent : baseEnd_4495922 < baseStart_4495922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495956 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4495956 : Nat := 118140960795 + 4495956 * 2 ^ 59
def prefixEnd_4495956 : Nat := 4983230072969 + 3 ^ 40 * 4495956 * 2
def baseEnd_4495956 : Nat := 769528809821905595057827

theorem tailTrace_4495956 : CollatzResearch.WordTrace tailWord_4495956 prefixEnd_4495956 769528809821905595057827 := by
  unfold tailWord_4495956
  simp only [CollatzResearch.WordTrace]
  refine ⟨81990493449963367499197861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109320657933284489998930481 81990493449963367499197861)
  ·
    refine ⟨15373217521868131406099599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81990493449963367499197861 15373217521868131406099599)
    ·
      refine ⟨23059826282802197109149399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15373217521868131406099599 23059826282802197109149399)
      ·
        refine ⟨34589739424203295663724099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23059826282802197109149399 34589739424203295663724099)
        ·
          refine ⟨51884609136304943495586149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34589739424203295663724099 51884609136304943495586149)
          ·
            refine ⟨9728364213057176905422403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51884609136304943495586149 9728364213057176905422403)
            ·
              refine ⟨14592546319585765358133605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9728364213057176905422403 14592546319585765358133605)
              ·
                refine ⟨2736102434922331004650051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14592546319585765358133605 2736102434922331004650051)
                ·
                  refine ⟨4104153652383496506975077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736102434922331004650051 4104153652383496506975077)
                  ·
                    refine ⟨769528809821905595057827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104153652383496506975077 769528809821905595057827)
                    ·
                      rfl

theorem cell23_4495956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4495956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495956 prefixEnd_4495956 := by exact prefixLift 4495956
  have htrace : WordTrace (prefixWord ++ tailWord_4495956) baseStart_4495956 baseEnd_4495956 := by
    simpa [prefixWord, tailWord_4495956, baseEnd_4495956] using wordTrace_append hprefix tailTrace_4495956
  have hstable : (prefixWord ++ tailWord_4495956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495956).length < 2 ^ (prefixWord ++ tailWord_4495956).sum := by decide
  have hdescent : baseEnd_4495956 < baseStart_4495956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495975 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4495975 : Nat := 118140960795 + 4495975 * 2 ^ 59
def prefixEnd_4495975 : Nat := 4983230072969 + 3 ^ 40 * 4495975 * 2
def baseEnd_4495975 : Nat := 2308596185598152210835893

theorem tailTrace_4495975 : CollatzResearch.WordTrace tailWord_4495975 prefixEnd_4495975 2308596185598152210835893 := by
  unfold tailWord_4495975
  simp only [CollatzResearch.WordTrace]
  refine ⟨163981679886857901243337379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109321119924571934162224919 163981679886857901243337379)
  ·
    refine ⟨245972519830286851865006069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163981679886857901243337379 245972519830286851865006069)
    ·
      refine ⟨23059923734089392362344319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245972519830286851865006069 23059923734089392362344319)
      ·
        refine ⟨34589885601134088543516479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23059923734089392362344319 34589885601134088543516479)
        ·
          refine ⟨51884828401701132815274719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34589885601134088543516479 51884828401701132815274719)
          ·
            refine ⟨77827242602551699222912079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51884828401701132815274719 77827242602551699222912079)
            ·
              refine ⟨116740863903827548834368119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77827242602551699222912079 116740863903827548834368119)
              ·
                refine ⟨175111295855741323251552179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116740863903827548834368119 175111295855741323251552179)
                ·
                  refine ⟨262666943783611984877328269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175111295855741323251552179 262666943783611984877328269)
                  ·
                    refine ⟨98500103918854494328998101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 262666943783611984877328269 98500103918854494328998101)
                    ·
                      refine ⟨2308596185598152210835893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98500103918854494328998101 2308596185598152210835893)
                      ·
                        rfl

theorem cell23_4495975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4495975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495975 prefixEnd_4495975 := by exact prefixLift 4495975
  have htrace : WordTrace (prefixWord ++ tailWord_4495975) baseStart_4495975 baseEnd_4495975 := by
    simpa [prefixWord, tailWord_4495975, baseEnd_4495975] using wordTrace_append hprefix tailTrace_4495975
  have hstable : (prefixWord ++ tailWord_4495975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495975).length < 2 ^ (prefixWord ++ tailWord_4495975).sum := by decide
  have hdescent : baseEnd_4495975 < baseStart_4495975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495995 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 3, 6]
def baseStart_4495995 : Nat := 118140960795 + 4495995 * 2 ^ 59
def prefixEnd_4495995 : Nat := 4983230072969 + 3 ^ 40 * 4495995 * 2
def baseEnd_4495995 : Nat := 769535485070414044195267

theorem tailTrace_4495995 : CollatzResearch.WordTrace tailWord_4495995 prefixEnd_4495995 769535485070414044195267 := by
  unfold tailWord_4495995
  simp only [CollatzResearch.WordTrace]
  refine ⟨163982409346785444659065439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109321606231190296439376959 163982409346785444659065439)
  ·
    refine ⟨245973614020178166988598159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163982409346785444659065439 245973614020178166988598159)
    ·
      refine ⟨368960421030267250482897239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245973614020178166988598159 368960421030267250482897239)
      ·
        refine ⟨553440631545400875724345859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368960421030267250482897239 553440631545400875724345859)
        ·
          refine ⟨830160947318101313586518789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553440631545400875724345859 830160947318101313586518789)
          ·
            refine ⟨155655177622143996297472273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 830160947318101313586518789 155655177622143996297472273)
            ·
              refine ⟨116741383216607997223104205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155655177622143996297472273 116741383216607997223104205)
              ·
                refine ⟨43778018706227998958664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116741383216607997223104205 43778018706227998958664077)
                ·
                  refine ⟨16416757014835499609499029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43778018706227998958664077 16416757014835499609499029)
                  ·
                    refine ⟨769535485070414044195267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16416757014835499609499029 769535485070414044195267)
                    ·
                      rfl

theorem cell23_4495995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_4495995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495995 prefixEnd_4495995 := by exact prefixLift 4495995
  have htrace : WordTrace (prefixWord ++ tailWord_4495995) baseStart_4495995 baseEnd_4495995 := by
    simpa [prefixWord, tailWord_4495995, baseEnd_4495995] using wordTrace_append hprefix tailTrace_4495995
  have hstable : (prefixWord ++ tailWord_4495995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495995).length < 2 ^ (prefixWord ++ tailWord_4495995).sum := by decide
  have hdescent : baseEnd_4495995 < baseStart_4495995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4495996 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_4495996 : Nat := 118140960795 + 4495996 * 2 ^ 59
def prefixEnd_4495996 : Nat := 4983230072969 + 3 ^ 40 * 4495996 * 2
def baseEnd_4495996 : Nat := 2308606968691896628673297

theorem tailTrace_4495996 : CollatzResearch.WordTrace tailWord_4495996 prefixEnd_4495996 2308606968691896628673297 := by
  unfold tailWord_4495996
  simp only [CollatzResearch.WordTrace]
  refine ⟨81991222909890910914925921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109321630546521214553234561 81991222909890910914925921)
  ·
    refine ⟨61493417182418183186194441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81991222909890910914925921 61493417182418183186194441)
    ·
      refine ⟨46120062886813637389645831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61493417182418183186194441 46120062886813637389645831)
      ·
        refine ⟨69180094330220456084468747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46120062886813637389645831 69180094330220456084468747)
        ·
          refine ⟨103770141495330684126703121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69180094330220456084468747 103770141495330684126703121)
          ·
            refine ⟨77827606121498013095027341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103770141495330684126703121 77827606121498013095027341)
            ·
              refine ⟨29185352295561754910635253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77827606121498013095027341 29185352295561754910635253)
              ·
                refine ⟨2736126777708914522872055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29185352295561754910635253 2736126777708914522872055)
                ·
                  refine ⟨4104190166563371784308083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736126777708914522872055 4104190166563371784308083)
                  ·
                    refine ⟨6156285249845057676462125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4104190166563371784308083 6156285249845057676462125)
                    ·
                      refine ⟨2308606968691896628673297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6156285249845057676462125 2308606968691896628673297)
                      ·
                        rfl

theorem cell23_4495996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_4495996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4495996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4495996 prefixEnd_4495996 := by exact prefixLift 4495996
  have htrace : WordTrace (prefixWord ++ tailWord_4495996) baseStart_4495996 baseEnd_4495996 := by
    simpa [prefixWord, tailWord_4495996, baseEnd_4495996] using wordTrace_append hprefix tailTrace_4495996
  have hstable : (prefixWord ++ tailWord_4495996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4495996).length < 2 ^ (prefixWord ++ tailWord_4495996).sum := by decide
  have hdescent : baseEnd_4495996 < baseStart_4495996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4495996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496015 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_4496015 : Nat := 118140960795 + 4496015 * 2 ^ 59
def prefixEnd_4496015 : Nat := 4983230072969 + 3 ^ 40 * 4496015 * 2
def baseEnd_4496015 : Nat := 2308616724824332054335709

theorem tailTrace_4496015 : CollatzResearch.WordTrace tailWord_4496015 prefixEnd_4496015 2308616724824332054335709 := by
  unfold tailWord_4496015
  simp only [CollatzResearch.WordTrace]
  refine ⟨163983138806712988074793499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109322092537808658716528999 163983138806712988074793499)
  ·
    refine ⟨245974708210069482112190249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163983138806712988074793499 245974708210069482112190249)
    ·
      refine ⟨184481031157552111584142687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245974708210069482112190249 184481031157552111584142687)
      ·
        refine ⟨276721546736328167376214031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184481031157552111584142687 276721546736328167376214031)
        ·
          refine ⟨415082320104492251064321047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276721546736328167376214031 415082320104492251064321047)
          ·
            refine ⟨622623480156738376596481571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415082320104492251064321047 622623480156738376596481571)
            ·
              refine ⟨933935220235107564894722357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622623480156738376596481571 933935220235107564894722357)
              ·
                refine ⟨87556426897041334208880221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 933935220235107564894722357 87556426897041334208880221)
                ·
                  refine ⟨32833660086390500328330083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87556426897041334208880221 32833660086390500328330083)
                  ·
                    refine ⟨49250490129585750492495125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32833660086390500328330083 49250490129585750492495125)
                    ·
                      refine ⟨2308616724824332054335709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49250490129585750492495125 2308616724824332054335709)
                      ·
                        rfl

theorem cell23_4496015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_4496015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496015 prefixEnd_4496015 := by exact prefixLift 4496015
  have htrace : WordTrace (prefixWord ++ tailWord_4496015) baseStart_4496015 baseEnd_4496015 := by
    simpa [prefixWord, tailWord_4496015, baseEnd_4496015] using wordTrace_append hprefix tailTrace_4496015
  have hstable : (prefixWord ++ tailWord_4496015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496015).length < 2 ^ (prefixWord ++ tailWord_4496015).sum := by decide
  have hdescent : baseEnd_4496015 < baseStart_4496015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496019 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 7, 2, 2]
def baseStart_4496019 : Nat := 118140960795 + 4496019 * 2 ^ 59
def prefixEnd_4496019 : Nat := 4983230072969 + 3 ^ 40 * 4496019 * 2
def baseEnd_4496019 : Nat := 2308618778746950038685691

theorem tailTrace_4496019 : CollatzResearch.WordTrace tailWord_4496019 prefixEnd_4496019 2308618778746950038685691 := by
  unfold tailWord_4496019
  simp only [CollatzResearch.WordTrace]
  refine ⟨163983284698698496757939111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109322189799132331171959407 163983284698698496757939111)
  ·
    refine ⟨245974927048047745136908667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163983284698698496757939111 245974927048047745136908667)
    ·
      refine ⟨368962390572071617705363001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245974927048047745136908667 368962390572071617705363001)
      ·
        refine ⟨276721792929053713279022251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368962390572071617705363001 276721792929053713279022251)
        ·
          refine ⟨415082689393580569918533377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276721792929053713279022251 415082689393580569918533377)
          ·
            refine ⟨311312017045185427438900033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415082689393580569918533377 311312017045185427438900033)
            ·
              refine ⟨233484012783889070579175025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311312017045185427438900033 233484012783889070579175025)
              ·
                refine ⟨175113009587916802934381269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233484012783889070579175025 175113009587916802934381269)
                ·
                  refine ⟨4104211162216800068774561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 175113009587916802934381269 4104211162216800068774561)
                  ·
                    refine ⟨3078158371662600051580921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104211162216800068774561 3078158371662600051580921)
                    ·
                      refine ⟨2308618778746950038685691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078158371662600051580921 2308618778746950038685691)
                      ·
                        rfl

theorem cell23_4496019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 2, 2].length) (baseStart_4496019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496019 prefixEnd_4496019 := by exact prefixLift 4496019
  have htrace : WordTrace (prefixWord ++ tailWord_4496019) baseStart_4496019 baseEnd_4496019 := by
    simpa [prefixWord, tailWord_4496019, baseEnd_4496019] using wordTrace_append hprefix tailTrace_4496019
  have hstable : (prefixWord ++ tailWord_4496019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496019).length < 2 ^ (prefixWord ++ tailWord_4496019).sum := by decide
  have hdescent : baseEnd_4496019 < baseStart_4496019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496025 : List Nat := [1, 2, 1, 2, 1, 2, 4, 10]
def baseStart_4496025 : Nat := 118140960795 + 4496025 * 2 ^ 59
def prefixEnd_4496025 : Nat := 4983230072969 + 3 ^ 40 * 4496025 * 2
def baseEnd_4496025 : Nat := 85504513319662111674469

theorem tailTrace_4496025 : CollatzResearch.WordTrace tailWord_4496025 prefixEnd_4496025 85504513319662111674469 := by
  unfold tailWord_4496025
  simp only [CollatzResearch.WordTrace]
  refine ⟨163983503536676759782657529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109322335691117839855105019 163983503536676759782657529)
  ·
    refine ⟨122987627652507569836993147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163983503536676759782657529 122987627652507569836993147)
    ·
      refine ⟨184481441478761354755489721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122987627652507569836993147 184481441478761354755489721)
      ·
        refine ⟨138361081109071016066617291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184481441478761354755489721 138361081109071016066617291)
        ·
          refine ⟨207541621663606524099925937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138361081109071016066617291 207541621663606524099925937)
          ·
            refine ⟨155656216247704893074944453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207541621663606524099925937 155656216247704893074944453)
            ·
              refine ⟨29185540546444667451552085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155656216247704893074944453 29185540546444667451552085)
              ·
                refine ⟨85504513319662111674469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29185540546444667451552085 85504513319662111674469)
                ·
                  rfl

theorem cell23_4496025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 10].length) (baseStart_4496025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496025 prefixEnd_4496025 := by exact prefixLift 4496025
  have htrace : WordTrace (prefixWord ++ tailWord_4496025) baseStart_4496025 baseEnd_4496025 := by
    simpa [prefixWord, tailWord_4496025, baseEnd_4496025] using wordTrace_append hprefix tailTrace_4496025
  have hstable : (prefixWord ++ tailWord_4496025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496025).length < 2 ^ (prefixWord ++ tailWord_4496025).sum := by decide
  have hdescent : baseEnd_4496025 < baseStart_4496025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496029 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4496029 : Nat := 118140960795 + 4496029 * 2 ^ 59
def prefixEnd_4496029 : Nat := 4983230072969 + 3 ^ 40 * 4496029 * 2
def baseEnd_4496029 : Nat := 769541304517831666520215

theorem tailTrace_4496029 : CollatzResearch.WordTrace tailWord_4496029 prefixEnd_4496029 769541304517831666520215 := by
  unfold tailWord_4496029
  simp only [CollatzResearch.WordTrace]
  refine ⟨163983649428662268465803141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109322432952441512310535427 163983649428662268465803141)
  ·
    refine ⟨30746934267874175337338089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163983649428662268465803141 30746934267874175337338089)
    ·
      refine ⟨23060200700905631503003567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30746934267874175337338089 23060200700905631503003567)
      ·
        refine ⟨34590301051358447254505351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23060200700905631503003567 34590301051358447254505351)
        ·
          refine ⟨51885451577037670881758027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34590301051358447254505351 51885451577037670881758027)
          ·
            refine ⟨77828177365556506322637041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51885451577037670881758027 77828177365556506322637041)
            ·
              refine ⟨58371133024167379741977781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77828177365556506322637041 58371133024167379741977781)
              ·
                refine ⟨5472293721015691850810417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58371133024167379741977781 5472293721015691850810417)
                ·
                  refine ⟨4104220290761768888107813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5472293721015691850810417 4104220290761768888107813)
                  ·
                    refine ⟨769541304517831666520215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104220290761768888107813 769541304517831666520215)
                    ·
                      rfl

theorem cell23_4496029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4496029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496029 prefixEnd_4496029 := by exact prefixLift 4496029
  have htrace : WordTrace (prefixWord ++ tailWord_4496029) baseStart_4496029 baseEnd_4496029 := by
    simpa [prefixWord, tailWord_4496029, baseEnd_4496029] using wordTrace_append hprefix tailTrace_4496029
  have hstable : (prefixWord ++ tailWord_4496029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496029).length < 2 ^ (prefixWord ++ tailWord_4496029).sum := by decide
  have hdescent : baseEnd_4496029 < baseStart_4496029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496036 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_4496036 : Nat := 118140960795 + 4496036 * 2 ^ 59
def prefixEnd_4496036 : Nat := 4983230072969 + 3 ^ 40 * 4496036 * 2
def baseEnd_4496036 : Nat := 2308627507918076472173113

theorem tailTrace_4496036 : CollatzResearch.WordTrace tailWord_4496036 prefixEnd_4496036 2308627507918076472173113 := by
  unfold tailWord_4496036
  simp only [CollatzResearch.WordTrace]
  refine ⟨81991952369818454330653981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109322603159757939107538641 81991952369818454330653981)
  ·
    refine ⟨30746982138681920373995243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81991952369818454330653981 30746982138681920373995243)
    ·
      refine ⟨46120473208022880560992865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30746982138681920373995243 46120473208022880560992865)
      ·
        refine ⟨34590354906017160420744649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46120473208022880560992865 34590354906017160420744649)
        ·
          refine ⟨25942766179512870315558487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34590354906017160420744649 25942766179512870315558487)
          ·
            refine ⟨38914149269269305473337731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25942766179512870315558487 38914149269269305473337731)
            ·
              refine ⟨58371223903903958210006597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38914149269269305473337731 58371223903903958210006597)
              ·
                refine ⟨10944604481981992164376237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58371223903903958210006597 10944604481981992164376237)
                ·
                  refine ⟨4104226680743247061641089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10944604481981992164376237 4104226680743247061641089)
                  ·
                    refine ⟨3078170010557435296230817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104226680743247061641089 3078170010557435296230817)
                    ·
                      refine ⟨2308627507918076472173113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078170010557435296230817 2308627507918076472173113)
                      ·
                        rfl

theorem cell23_4496036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_4496036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496036 prefixEnd_4496036 := by exact prefixLift 4496036
  have htrace : WordTrace (prefixWord ++ tailWord_4496036) baseStart_4496036 baseEnd_4496036 := by
    simpa [prefixWord, tailWord_4496036, baseEnd_4496036] using wordTrace_append hprefix tailTrace_4496036
  have hstable : (prefixWord ++ tailWord_4496036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496036).length < 2 ^ (prefixWord ++ tailWord_4496036).sum := by decide
  have hdescent : baseEnd_4496036 < baseStart_4496036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496046 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4496046 : Nat := 118140960795 + 4496046 * 2 ^ 59
def prefixEnd_4496046 : Nat := 4983230072969 + 3 ^ 40 * 4496046 * 2
def baseEnd_4496046 : Nat := 769544214241540477682689

theorem tailTrace_4496046 : CollatzResearch.WordTrace tailWord_4496046 prefixEnd_4496046 769544214241540477682689 := by
  unfold tailWord_4496046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20498033683700085046146499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109322846313067120246114661 20498033683700085046146499)
  ·
    refine ⟨30747050525550127569219749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20498033683700085046146499 30747050525550127569219749)
    ·
      refine ⟨5765071973540648919228703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30747050525550127569219749 5765071973540648919228703)
      ·
        refine ⟨8647607960310973378843055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5765071973540648919228703 8647607960310973378843055)
        ·
          refine ⟨12971411940466460068264583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8647607960310973378843055 12971411940466460068264583)
          ·
            refine ⟨19457117910699690102396875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12971411940466460068264583 19457117910699690102396875)
            ·
              refine ⟨29185676866049535153595313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19457117910699690102396875 29185676866049535153595313)
              ·
                refine ⟨21889257649537151365196485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29185676866049535153595313 21889257649537151365196485)
                ·
                  refine ⟨4104235809288215880974341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21889257649537151365196485 4104235809288215880974341)
                  ·
                    refine ⟨769544214241540477682689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104235809288215880974341 769544214241540477682689)
                    ·
                      rfl

theorem cell23_4496046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4496046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496046 prefixEnd_4496046 := by exact prefixLift 4496046
  have htrace : WordTrace (prefixWord ++ tailWord_4496046) baseStart_4496046 baseEnd_4496046 := by
    simpa [prefixWord, tailWord_4496046, baseEnd_4496046] using wordTrace_append hprefix tailTrace_4496046
  have hstable : (prefixWord ++ tailWord_4496046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496046).length < 2 ^ (prefixWord ++ tailWord_4496046).sum := by decide
  have hdescent : baseEnd_4496046 < baseStart_4496046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496112 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_4496112 : Nat := 118140960795 + 4496112 * 2 ^ 59
def prefixEnd_4496112 : Nat := 4983230072969 + 3 ^ 40 * 4496112 * 2
def baseEnd_4496112 : Nat := 2308666532447818174822763

theorem tailTrace_4496112 : CollatzResearch.WordTrace tailWord_4496112 prefixEnd_4496112 2308666532447818174822763 := by
  unfold tailWord_4496112
  simp only [CollatzResearch.WordTrace]
  refine ⟨81993338343680786820537295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109324451124907715760716393 81993338343680786820537295)
  ·
    refine ⟨122990007515521180230805943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81993338343680786820537295 122990007515521180230805943)
    ·
      refine ⟨184485011273281770346208915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122990007515521180230805943 184485011273281770346208915)
      ·
        refine ⟨276727516909922655519313373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184485011273281770346208915 276727516909922655519313373)
        ·
          refine ⟨103772818841220995819742515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276727516909922655519313373 103772818841220995819742515)
          ·
            refine ⟨155659228261831493729613773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103772818841220995819742515 155659228261831493729613773)
            ·
              refine ⟨58372210598186810148605165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155659228261831493729613773 58372210598186810148605165)
              ·
                refine ⟨21889578974320053805726937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58372210598186810148605165 21889578974320053805726937)
                ·
                  refine ⟨16417184230740040354295203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21889578974320053805726937 16417184230740040354295203)
                  ·
                    refine ⟨24625776346110060531442805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16417184230740040354295203 24625776346110060531442805)
                    ·
                      refine ⟨2308666532447818174822763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24625776346110060531442805 2308666532447818174822763)
                      ·
                        rfl

theorem cell23_4496112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_4496112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496112 prefixEnd_4496112 := by exact prefixLift 4496112
  have htrace : WordTrace (prefixWord ++ tailWord_4496112) baseStart_4496112 baseEnd_4496112 := by
    simpa [prefixWord, tailWord_4496112, baseEnd_4496112] using wordTrace_append hprefix tailTrace_4496112
  have hstable : (prefixWord ++ tailWord_4496112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496112).length < 2 ^ (prefixWord ++ tailWord_4496112).sum := by decide
  have hdescent : baseEnd_4496112 < baseStart_4496112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496113 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_4496113 : Nat := 118140960795 + 4496113 * 2 ^ 59
def prefixEnd_4496113 : Nat := 4983230072969 + 3 ^ 40 * 4496113 * 2
def baseEnd_4496113 : Nat := 2308667045928472670910259

theorem tailTrace_4496113 : CollatzResearch.WordTrace tailWord_4496113 prefixEnd_4496113 2308667045928472670910259 := by
  unfold tailWord_4496113
  simp only [CollatzResearch.WordTrace]
  refine ⟨163986713160357950811860993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109324475440238633874573995 163986713160357950811860993)
  ·
    refine ⟨122990034870268463108895745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163986713160357950811860993 122990034870268463108895745)
    ·
      refine ⟨92242526152701347331671809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122990034870268463108895745 92242526152701347331671809)
      ·
        refine ⟨69181894614526010498753857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92242526152701347331671809 69181894614526010498753857)
        ·
          refine ⟨51886420960894507874065393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69181894614526010498753857 51886420960894507874065393)
          ·
            refine ⟨38914815720670880905549045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51886420960894507874065393 38914815720670880905549045)
            ·
              refine ⟨3648263973812895084895223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38914815720670880905549045 3648263973812895084895223)
              ·
                refine ⟨5472395960719342627342835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648263973812895084895223 5472395960719342627342835)
                ·
                  refine ⟨8208593941079013941014253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5472395960719342627342835 8208593941079013941014253)
                  ·
                    refine ⟨3078222727904630227880345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8208593941079013941014253 3078222727904630227880345)
                    ·
                      refine ⟨2308667045928472670910259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078222727904630227880345 2308667045928472670910259)
                      ·
                        rfl

theorem cell23_4496113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_4496113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496113 prefixEnd_4496113 := by exact prefixLift 4496113
  have htrace : WordTrace (prefixWord ++ tailWord_4496113) baseStart_4496113 baseEnd_4496113 := by
    simpa [prefixWord, tailWord_4496113, baseEnd_4496113] using wordTrace_append hprefix tailTrace_4496113
  have hstable : (prefixWord ++ tailWord_4496113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496113).length < 2 ^ (prefixWord ++ tailWord_4496113).sum := by decide
  have hdescent : baseEnd_4496113 < baseStart_4496113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496169 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 5, 2]
def baseStart_4496169 : Nat := 118140960795 + 4496169 * 2 ^ 59
def prefixEnd_4496169 : Nat := 4983230072969 + 3 ^ 40 * 4496169 * 2
def baseEnd_4496169 : Nat := 2308695800845124451810001

theorem tailTrace_4496169 : CollatzResearch.WordTrace tailWord_4496169 prefixEnd_4496169 2308695800845124451810001 := by
  unfold tailWord_4496169
  simp only [CollatzResearch.WordTrace]
  refine ⟨163988755648155072375899561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109325837098770048250599707 163988755648155072375899561)
  ·
    refine ⟨122991566736116304281924671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163988755648155072375899561 122991566736116304281924671)
    ·
      refine ⟨184487350104174456422887007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122991566736116304281924671 184487350104174456422887007)
      ·
        refine ⟨276731025156261684634330511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184487350104174456422887007 276731025156261684634330511)
        ·
          refine ⟨415096537734392526951495767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276731025156261684634330511 415096537734392526951495767)
          ·
            refine ⟨622644806601588790427243651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415096537734392526951495767 622644806601588790427243651)
            ·
              refine ⟨933967209902383185640865477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622644806601588790427243651 933967209902383185640865477)
              ·
                refine ⟨175118851856696847307662277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 933967209902383185640865477 175118851856696847307662277)
                ·
                  refine ⟨32834784723130658870186677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175118851856696847307662277 32834784723130658870186677)
                  ·
                    refine ⟨3078261067793499269080001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32834784723130658870186677 3078261067793499269080001)
                    ·
                      refine ⟨2308695800845124451810001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078261067793499269080001 2308695800845124451810001)
                      ·
                        rfl

theorem cell23_4496169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 5, 2].length) (baseStart_4496169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496169 prefixEnd_4496169 := by exact prefixLift 4496169
  have htrace : WordTrace (prefixWord ++ tailWord_4496169) baseStart_4496169 baseEnd_4496169 := by
    simpa [prefixWord, tailWord_4496169, baseEnd_4496169] using wordTrace_append hprefix tailTrace_4496169
  have hstable : (prefixWord ++ tailWord_4496169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496169).length < 2 ^ (prefixWord ++ tailWord_4496169).sum := by decide
  have hdescent : baseEnd_4496169 < baseStart_4496169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496236 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_4496236 : Nat := 118140960795 + 4496236 * 2 ^ 59
def prefixEnd_4496236 : Nat := 4983230072969 + 3 ^ 40 * 4496236 * 2
def baseEnd_4496236 : Nat := 2308730204048975689672193

theorem tailTrace_4496236 : CollatzResearch.WordTrace tailWord_4496236 prefixEnd_4496236 2308730204048975689672193 := by
  unfold tailWord_4496236
  simp only [CollatzResearch.WordTrace]
  refine ⟨81995599669456171409294281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109327466225941561879059041 81995599669456171409294281)
  ·
    refine ⟨61496699752092128556970711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81995599669456171409294281 61496699752092128556970711)
    ·
      refine ⟨92245049628138192835456067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61496699752092128556970711 92245049628138192835456067)
      ·
        refine ⟨138367574442207289253184101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92245049628138192835456067 138367574442207289253184101)
        ·
          refine ⟨25943920207913866734972019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138367574442207289253184101 25943920207913866734972019)
          ·
            refine ⟨38915880311870800102458029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25943920207913866734972019 38915880311870800102458029)
            ·
              refine ⟨14593455116951550038421761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38915880311870800102458029 14593455116951550038421761)
              ·
                refine ⟨10945091337713662528816321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14593455116951550038421761 10945091337713662528816321)
                ·
                  refine ⟨8208818503285246896612241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10945091337713662528816321 8208818503285246896612241)
                  ·
                    refine ⟨6156613877463935172459181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8208818503285246896612241 6156613877463935172459181)
                    ·
                      refine ⟨2308730204048975689672193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6156613877463935172459181 2308730204048975689672193)
                      ·
                        rfl

theorem cell23_4496236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_4496236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496236 prefixEnd_4496236 := by exact prefixLift 4496236
  have htrace : WordTrace (prefixWord ++ tailWord_4496236) baseStart_4496236 baseEnd_4496236 := by
    simpa [prefixWord, tailWord_4496236, baseEnd_4496236] using wordTrace_append hprefix tailTrace_4496236
  have hstable : (prefixWord ++ tailWord_4496236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496236).length < 2 ^ (prefixWord ++ tailWord_4496236).sum := by decide
  have hdescent : baseEnd_4496236 < baseStart_4496236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496306 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_4496306 : Nat := 118140960795 + 4496306 * 2 ^ 59
def prefixEnd_4496306 : Nat := 4983230072969 + 3 ^ 40 * 4496306 * 2
def baseEnd_4496306 : Nat := 2308766147694790415796871

theorem tailTrace_4496306 : CollatzResearch.WordTrace tailWord_4496306 prefixEnd_4496306 2308766147694790415796871 := by
  unfold tailWord_4496306
  simp only [CollatzResearch.WordTrace]
  refine ⟨40998438112164686193409193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109329168299105829849091181 40998438112164686193409193)
  ·
    refine ⟨30748828584123514645056895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40998438112164686193409193 30748828584123514645056895)
    ·
      refine ⟨46123242876185271967585343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30748828584123514645056895 46123242876185271967585343)
      ·
        refine ⟨69184864314277907951378015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46123242876185271967585343 69184864314277907951378015)
        ·
          refine ⟨103777296471416861927067023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69184864314277907951378015 103777296471416861927067023)
          ·
            refine ⟨155665944707125292890600535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103777296471416861927067023 155665944707125292890600535)
            ·
              refine ⟨233498917060687939335900803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155665944707125292890600535 233498917060687939335900803)
              ·
                refine ⟨350248375591031909003851205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233498917060687939335900803 350248375591031909003851205)
                ·
                  refine ⟨65671570423318482938222101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350248375591031909003851205 65671570423318482938222101)
                  ·
                    refine ⟨3078354863593053887729161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65671570423318482938222101 3078354863593053887729161)
                    ·
                      refine ⟨2308766147694790415796871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078354863593053887729161 2308766147694790415796871)
                      ·
                        rfl

theorem cell23_4496306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_4496306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496306 prefixEnd_4496306 := by exact prefixLift 4496306
  have htrace : WordTrace (prefixWord ++ tailWord_4496306) baseStart_4496306 baseEnd_4496306 := by
    simpa [prefixWord, tailWord_4496306, baseEnd_4496306] using wordTrace_append hprefix tailTrace_4496306
  have hstable : (prefixWord ++ tailWord_4496306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496306).length < 2 ^ (prefixWord ++ tailWord_4496306).sum := by decide
  have hdescent : baseEnd_4496306 < baseStart_4496306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496323 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 3, 2, 2]
def baseStart_4496323 : Nat := 118140960795 + 4496323 * 2 ^ 59
def prefixEnd_4496323 : Nat := 4983230072969 + 3 ^ 40 * 4496323 * 2
def baseEnd_4496323 : Nat := 2308774876865916849284293

theorem tailTrace_4496323 : CollatzResearch.WordTrace tailWord_4496323 prefixEnd_4496323 2308774876865916849284293 := by
  unfold tailWord_4496323
  simp only [CollatzResearch.WordTrace]
  refine ⟨163994372489597156677005623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109329581659731437784670415 163994372489597156677005623)
  ·
    refine ⟨245991558734395735015508435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163994372489597156677005623 245991558734395735015508435)
    ·
      refine ⟨368987338101593602523262653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245991558734395735015508435 368987338101593602523262653)
      ·
        refine ⟨138370251788097600946223495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368987338101593602523262653 138370251788097600946223495)
        ·
          refine ⟨207555377682146401419335243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138370251788097600946223495 207555377682146401419335243)
          ·
            refine ⟨311333066523219602129002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207555377682146401419335243 311333066523219602129002865)
            ·
              refine ⟨233499799892414701596752149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311333066523219602129002865 233499799892414701596752149)
              ·
                refine ⟨10945303119956939137347757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233499799892414701596752149 10945303119956939137347757)
                ·
                  refine ⟨4104488669983852176505409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10945303119956939137347757 4104488669983852176505409)
                  ·
                    refine ⟨3078366502487889132379057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4104488669983852176505409 3078366502487889132379057)
                    ·
                      refine ⟨2308774876865916849284293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078366502487889132379057 2308774876865916849284293)
                      ·
                        rfl

theorem cell23_4496323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_4496323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496323 prefixEnd_4496323 := by exact prefixLift 4496323
  have htrace : WordTrace (prefixWord ++ tailWord_4496323) baseStart_4496323 baseEnd_4496323 := by
    simpa [prefixWord, tailWord_4496323, baseEnd_4496323] using wordTrace_append hprefix tailTrace_4496323
  have hstable : (prefixWord ++ tailWord_4496323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496323).length < 2 ^ (prefixWord ++ tailWord_4496323).sum := by decide
  have hdescent : baseEnd_4496323 < baseStart_4496323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496340 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4496340 : Nat := 118140960795 + 4496340 * 2 ^ 59
def prefixEnd_4496340 : Nat := 4983230072969 + 3 ^ 40 * 4496340 * 2
def baseEnd_4496340 : Nat := 2308783606037043282771715

theorem tailTrace_4496340 : CollatzResearch.WordTrace tailWord_4496340 prefixEnd_4496340 2308783606037043282771715 := by
  unfold tailWord_4496340
  simp only [CollatzResearch.WordTrace]
  refine ⟨81997496265267784290187237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109329995020357045720249649 81997496265267784290187237)
  ·
    refine ⟨15374530549737709554410107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81997496265267784290187237 15374530549737709554410107)
    ·
      refine ⟨23061795824606564331615161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15374530549737709554410107 23061795824606564331615161)
      ·
        refine ⟨17296346868454923248711371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23061795824606564331615161 17296346868454923248711371)
        ·
          refine ⟨25944520302682384873067057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17296346868454923248711371 25944520302682384873067057)
          ·
            refine ⟨19458390227011788654800293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25944520302682384873067057 19458390227011788654800293)
            ·
              refine ⟨3648448167564710372775055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19458390227011788654800293 3648448167564710372775055)
              ·
                refine ⟨5472672251347065559162583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648448167564710372775055 5472672251347065559162583)
                ·
                  refine ⟨8209008377020598338743875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5472672251347065559162583 8209008377020598338743875)
                  ·
                    refine ⟨12313512565530897508115813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8209008377020598338743875 12313512565530897508115813)
                    ·
                      refine ⟨2308783606037043282771715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12313512565530897508115813 2308783606037043282771715)
                      ·
                        rfl

theorem cell23_4496340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4496340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496340 prefixEnd_4496340 := by exact prefixLift 4496340
  have htrace : WordTrace (prefixWord ++ tailWord_4496340) baseStart_4496340 baseEnd_4496340 := by
    simpa [prefixWord, tailWord_4496340, baseEnd_4496340] using wordTrace_append hprefix tailTrace_4496340
  have hstable : (prefixWord ++ tailWord_4496340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496340).length < 2 ^ (prefixWord ++ tailWord_4496340).sum := by decide
  have hdescent : baseEnd_4496340 < baseStart_4496340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496430 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4496430 : Nat := 118140960795 + 4496430 * 2 ^ 59
def prefixEnd_4496430 : Nat := 4983230072969 + 3 ^ 40 * 4496430 * 2
def baseEnd_4496430 : Nat := 2308829819295947930646301

theorem tailTrace_4496430 : CollatzResearch.WordTrace tailWord_4496430 prefixEnd_4496430 2308829819295947930646301 := by
  unfold tailWord_4496430
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499784387526189243893843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109332183400139675967433829 20499784387526189243893843)
  ·
    refine ⟨30749676581289283865840765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20499784387526189243893843 30749676581289283865840765)
    ·
      refine ⟨11531128717983481449690287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30749676581289283865840765 11531128717983481449690287)
      ·
        refine ⟨17296693076975222174535431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531128717983481449690287 17296693076975222174535431)
        ·
          refine ⟨25945039615462833261803147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17296693076975222174535431 25945039615462833261803147)
          ·
            refine ⟨38917559423194249892704721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25945039615462833261803147 38917559423194249892704721)
            ·
              refine ⟨29188169567395687419528541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38917559423194249892704721 29188169567395687419528541)
              ·
                refine ⟨10945563587773382782323203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29188169567395687419528541 10945563587773382782323203)
                ·
                  refine ⟨16418345381660074173484805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10945563587773382782323203 16418345381660074173484805)
                  ·
                    refine ⟨3078439759061263907528401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16418345381660074173484805 3078439759061263907528401)
                    ·
                      refine ⟨2308829819295947930646301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078439759061263907528401 2308829819295947930646301)
                      ·
                        rfl

theorem cell23_4496430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4496430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496430 prefixEnd_4496430 := by exact prefixLift 4496430
  have htrace : WordTrace (prefixWord ++ tailWord_4496430) baseStart_4496430 baseEnd_4496430 := by
    simpa [prefixWord, tailWord_4496430, baseEnd_4496430] using wordTrace_append hprefix tailTrace_4496430
  have hstable : (prefixWord ++ tailWord_4496430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496430).length < 2 ^ (prefixWord ++ tailWord_4496430).sum := by decide
  have hdescent : baseEnd_4496430 < baseStart_4496430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496503 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_4496503 : Nat := 118140960795 + 4496503 * 2 ^ 59
def prefixEnd_4496503 : Nat := 4983230072969 + 3 ^ 40 * 4496503 * 2
def baseEnd_4496503 : Nat := 2308867303383726145033465

theorem tailTrace_4496503 : CollatzResearch.WordTrace tailWord_4496503 prefixEnd_4496503 2308867303383726145033465 := by
  unfold tailWord_4496503
  simp only [CollatzResearch.WordTrace]
  refine ⟨164000937628945047418558163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109333958419296698279038775 164000937628945047418558163)
  ·
    refine ⟨246001406443417571127837245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164000937628945047418558163 246001406443417571127837245)
    ·
      refine ⟨92250527416281589172938967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246001406443417571127837245 92250527416281589172938967)
      ·
        refine ⟨138375791124422383759408451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92250527416281589172938967 138375791124422383759408451)
        ·
          refine ⟨207563686686633575639112677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138375791124422383759408451 207563686686633575639112677)
          ·
            refine ⟨38918191253743795432333627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207563686686633575639112677 38918191253743795432333627)
            ·
              refine ⟨58377286880615693148500441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38918191253743795432333627 58377286880615693148500441)
              ·
                refine ⟨43782965160461769861375331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58377286880615693148500441 43782965160461769861375331)
                ·
                  refine ⟨65674447740692654792062997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43782965160461769861375331 65674447740692654792062997)
                  ·
                    refine ⟨3078489737844968193377953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65674447740692654792062997 3078489737844968193377953)
                    ·
                      refine ⟨2308867303383726145033465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078489737844968193377953 2308867303383726145033465)
                      ·
                        rfl

theorem cell23_4496503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_4496503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496503 prefixEnd_4496503 := by exact prefixLift 4496503
  have htrace : WordTrace (prefixWord ++ tailWord_4496503) baseStart_4496503 baseEnd_4496503 := by
    simpa [prefixWord, tailWord_4496503, baseEnd_4496503] using wordTrace_append hprefix tailTrace_4496503
  have hstable : (prefixWord ++ tailWord_4496503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496503).length < 2 ^ (prefixWord ++ tailWord_4496503).sum := by decide
  have hdescent : baseEnd_4496503 < baseStart_4496503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496523 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3]
def baseStart_4496523 : Nat := 118140960795 + 4496523 * 2 ^ 59
def prefixEnd_4496523 : Nat := 4983230072969 + 3 ^ 40 * 4496523 * 2
def baseEnd_4496523 : Nat := 2308877572996816066783373

theorem tailTrace_4496523 : CollatzResearch.WordTrace tailWord_4496523 prefixEnd_4496523 2308877572996816066783373 := by
  unfold tailWord_4496523
  simp only [CollatzResearch.WordTrace]
  refine ⟨164001667088872590834286223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109334444725915060556190815 164001667088872590834286223)
  ·
    refine ⟨246002500633308886251429335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164001667088872590834286223 246002500633308886251429335)
    ·
      refine ⟨369003750949963329377144003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246002500633308886251429335 369003750949963329377144003)
      ·
        refine ⟨553505626424944994065716005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369003750949963329377144003 553505626424944994065716005)
        ·
          refine ⟨103782304954677186387321751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 553505626424944994065716005 103782304954677186387321751)
          ·
            refine ⟨155673457432015779580982627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103782304954677186387321751 155673457432015779580982627)
            ·
              refine ⟨233510186148023669371473941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155673457432015779580982627 233510186148023669371473941)
              ·
                refine ⟨10945789975688609501787841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233510186148023669371473941 10945789975688609501787841)
                ·
                  refine ⟨8209342481766457126340881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10945789975688609501787841 8209342481766457126340881)
                  ·
                    refine ⟨6157006861324842844755661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8209342481766457126340881 6157006861324842844755661)
                    ·
                      refine ⟨2308877572996816066783373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157006861324842844755661 2308877572996816066783373)
                      ·
                        rfl

theorem cell23_4496523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 3].length) (baseStart_4496523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496523 prefixEnd_4496523 := by exact prefixLift 4496523
  have htrace : WordTrace (prefixWord ++ tailWord_4496523) baseStart_4496523 baseEnd_4496523 := by
    simpa [prefixWord, tailWord_4496523, baseEnd_4496523] using wordTrace_append hprefix tailTrace_4496523
  have hstable : (prefixWord ++ tailWord_4496523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496523).length < 2 ^ (prefixWord ++ tailWord_4496523).sum := by decide
  have hdescent : baseEnd_4496523 < baseStart_4496523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496530 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4496530 : Nat := 118140960795 + 4496530 * 2 ^ 59
def prefixEnd_4496530 : Nat := 4983230072969 + 3 ^ 40 * 4496530 * 2
def baseEnd_4496530 : Nat := 769627055787132513131947

theorem tailTrace_4496530 : CollatzResearch.WordTrace tailWord_4496530 prefixEnd_4496530 769627055787132513131947 := by
  unfold tailWord_4496530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41000480599961807757447761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109334614933231487353194029 41000480599961807757447761)
  ·
    refine ⟨30750360449971355818085821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41000480599961807757447761 30750360449971355818085821)
    ·
      refine ⟨11531385168739258431782183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30750360449971355818085821 11531385168739258431782183)
      ·
        refine ⟨17297077753108887647673275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531385168739258431782183 17297077753108887647673275)
        ·
          refine ⟨25945616629663331471509913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17297077753108887647673275 25945616629663331471509913)
          ·
            refine ⟨19459212472247498603632435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25945616629663331471509913 19459212472247498603632435)
            ·
              refine ⟨29188818708371247905448653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19459212472247498603632435 29188818708371247905448653)
              ·
                refine ⟨10945807015639217964543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29188818708371247905448653 10945807015639217964543245)
                ·
                  refine ⟨4104677630864706736703717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10945807015639217964543245 4104677630864706736703717)
                  ·
                    refine ⟨769627055787132513131947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104677630864706736703717 769627055787132513131947)
                    ·
                      rfl

theorem cell23_4496530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4496530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496530 prefixEnd_4496530 := by exact prefixLift 4496530
  have htrace : WordTrace (prefixWord ++ tailWord_4496530) baseStart_4496530 baseEnd_4496530 := by
    simpa [prefixWord, tailWord_4496530, baseEnd_4496530] using wordTrace_append hprefix tailTrace_4496530
  have hstable : (prefixWord ++ tailWord_4496530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496530).length < 2 ^ (prefixWord ++ tailWord_4496530).sum := by decide
  have hdescent : baseEnd_4496530 < baseStart_4496530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496593 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_4496593 : Nat := 118140960795 + 4496593 * 2 ^ 59
def prefixEnd_4496593 : Nat := 4983230072969 + 3 ^ 40 * 4496593 * 2
def baseEnd_4496593 : Nat := 2308913516642630792908051

theorem tailTrace_4496593 : CollatzResearch.WordTrace tailWord_4496593 prefixEnd_4496593 2308913516642630792908051 := by
  unfold tailWord_4496593
  simp only [CollatzResearch.WordTrace]
  refine ⟨164004220198618992789334433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109336146799079328526222955 164004220198618992789334433)
  ·
    refine ⟨123003165148964244592000825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164004220198618992789334433 123003165148964244592000825)
    ·
      refine ⟨92252373861723183444000619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123003165148964244592000825 92252373861723183444000619)
      ·
        refine ⟨138378560792584775166000929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92252373861723183444000619 138378560792584775166000929)
        ·
          refine ⟨103783920594438581374500697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138378560792584775166000929 103783920594438581374500697)
          ·
            refine ⟨77837940445828936030875523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103783920594438581374500697 77837940445828936030875523)
            ·
              refine ⟨116756910668743404046313285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77837940445828936030875523 116756910668743404046313285)
              ·
                refine ⟨21891920750389388258683741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116756910668743404046313285 21891920750389388258683741)
                ·
                  refine ⟨8209470281396020597006403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21891920750389388258683741 8209470281396020597006403)
                  ·
                    refine ⟨12314205422094030895509605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8209470281396020597006403 12314205422094030895509605)
                    ·
                      refine ⟨2308913516642630792908051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12314205422094030895509605 2308913516642630792908051)
                      ·
                        rfl

theorem cell23_4496593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_4496593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496593 prefixEnd_4496593 := by exact prefixLift 4496593
  have htrace : WordTrace (prefixWord ++ tailWord_4496593) baseStart_4496593 baseEnd_4496593 := by
    simpa [prefixWord, tailWord_4496593, baseEnd_4496593] using wordTrace_append hprefix tailTrace_4496593
  have hstable : (prefixWord ++ tailWord_4496593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496593).length < 2 ^ (prefixWord ++ tailWord_4496593).sum := by decide
  have hdescent : baseEnd_4496593 < baseStart_4496593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496627 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 1, 1, 4]
def baseStart_4496627 : Nat := 118140960795 + 4496627 * 2 ^ 59
def prefixEnd_4496627 : Nat := 4983230072969 + 3 ^ 40 * 4496627 * 2
def baseEnd_4496627 : Nat := 2308930974984883659882895

theorem tailTrace_4496627 : CollatzResearch.WordTrace tailWord_4496627 prefixEnd_4496627 2308930974984883659882895 := by
  unfold tailWord_4496627
  simp only [CollatzResearch.WordTrace]
  refine ⟨164005460280495816596072135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109336973520330544397381423 164005460280495816596072135)
  ·
    refine ⟨246008190420743724894108203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164005460280495816596072135 246008190420743724894108203)
    ·
      refine ⟨369012285631115587341162305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246008190420743724894108203 369012285631115587341162305)
      ·
        refine ⟨276759214223336690505871729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369012285631115587341162305 276759214223336690505871729)
        ·
          refine ⟨207569410667502517879403797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276759214223336690505871729 207569410667502517879403797)
          ·
            refine ⟨9729816125039180525597053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 207569410667502517879403797 9729816125039180525597053)
            ·
              refine ⟨3648681046889692697098895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9729816125039180525597053 3648681046889692697098895)
              ·
                refine ⟨5473021570334539045648343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648681046889692697098895 5473021570334539045648343)
                ·
                  refine ⟨8209532355501808568472515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5473021570334539045648343 8209532355501808568472515)
                  ·
                    refine ⟨12314298533252712852708773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8209532355501808568472515 12314298533252712852708773)
                    ·
                      refine ⟨2308930974984883659882895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12314298533252712852708773 2308930974984883659882895)
                      ·
                        rfl

theorem cell23_4496627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 1, 4].length) (baseStart_4496627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496627 prefixEnd_4496627 := by exact prefixLift 4496627
  have htrace : WordTrace (prefixWord ++ tailWord_4496627) baseStart_4496627 baseEnd_4496627 := by
    simpa [prefixWord, tailWord_4496627, baseEnd_4496627] using wordTrace_append hprefix tailTrace_4496627
  have hstable : (prefixWord ++ tailWord_4496627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496627).length < 2 ^ (prefixWord ++ tailWord_4496627).sum := by decide
  have hdescent : baseEnd_4496627 < baseStart_4496627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496638 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4496638 : Nat := 118140960795 + 4496638 * 2 ^ 59
def prefixEnd_4496638 : Nat := 4983230072969 + 3 ^ 40 * 4496638 * 2
def baseEnd_4496638 : Nat := 2308936623272083116845345

theorem tailTrace_4496638 : CollatzResearch.WordTrace tailWord_4496638 prefixEnd_4496638 2308936623272083116845345 := by
  unfold tailWord_4496638
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500732685431995684340321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109337240988970643649815045 20500732685431995684340321)
  ·
    refine ⟨15375549514073996763255241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20500732685431995684340321 15375549514073996763255241)
    ·
      refine ⟨11531662135555497572441431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15375549514073996763255241 11531662135555497572441431)
      ·
        refine ⟨17297493203333246358662147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531662135555497572441431 17297493203333246358662147)
        ·
          refine ⟨25946239804999869537993221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17297493203333246358662147 25946239804999869537993221)
          ·
            refine ⟨4864919963437475538373729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25946239804999869537993221 4864919963437475538373729)
            ·
              refine ⟨3648689972578106653780297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864919963437475538373729 3648689972578106653780297)
              ·
                refine ⟨2736517479433579990335223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648689972578106653780297 2736517479433579990335223)
                ·
                  refine ⟨4104776219150369985502835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736517479433579990335223 4104776219150369985502835)
                  ·
                    refine ⟨6157164328725554978254253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4104776219150369985502835 6157164328725554978254253)
                    ·
                      refine ⟨2308936623272083116845345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157164328725554978254253 2308936623272083116845345)
                      ·
                        rfl

theorem cell23_4496638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4496638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496638 prefixEnd_4496638 := by exact prefixLift 4496638
  have htrace : WordTrace (prefixWord ++ tailWord_4496638) baseStart_4496638 baseEnd_4496638 := by
    simpa [prefixWord, tailWord_4496638, baseEnd_4496638] using wordTrace_append hprefix tailTrace_4496638
  have hstable : (prefixWord ++ tailWord_4496638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496638).length < 2 ^ (prefixWord ++ tailWord_4496638).sum := by decide
  have hdescent : baseEnd_4496638 < baseStart_4496638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496663 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 7]
def baseStart_4496663 : Nat := 118140960795 + 4496663 * 2 ^ 59
def prefixEnd_4496663 : Nat := 4983230072969 + 3 ^ 40 * 4496663 * 2
def baseEnd_4496663 : Nat := 769649820096148506344243

theorem tailTrace_4496663 : CollatzResearch.WordTrace tailWord_4496663 prefixEnd_4496663 769649820096148506344243 := by
  unfold tailWord_4496663
  simp only [CollatzResearch.WordTrace]
  refine ⟨164006773308365394744382643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109337848872243596496255095 164006773308365394744382643)
  ·
    refine ⟨246010159962548092116573965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164006773308365394744382643 246010159962548092116573965)
    ·
      refine ⟨92253809985955534543715237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246010159962548092116573965 92253809985955534543715237)
      ·
        refine ⟨17297589372366662726946607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92253809985955534543715237 17297589372366662726946607)
        ·
          refine ⟨25946384058549994090419911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17297589372366662726946607 25946384058549994090419911)
          ·
            refine ⟨38919576087824991135629867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25946384058549994090419911 38919576087824991135629867)
            ·
              refine ⟨58379364131737486703444801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38919576087824991135629867 58379364131737486703444801)
              ·
                refine ⟨43784523098803115027583601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58379364131737486703444801 43784523098803115027583601)
                ·
                  refine ⟨32838392324102336270687701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43784523098803115027583601 32838392324102336270687701)
                  ·
                    refine ⟨769649820096148506344243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32838392324102336270687701 769649820096148506344243)
                    ·
                      rfl

theorem cell23_4496663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_4496663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496663 prefixEnd_4496663 := by exact prefixLift 4496663
  have htrace : WordTrace (prefixWord ++ tailWord_4496663) baseStart_4496663 baseEnd_4496663 := by
    simpa [prefixWord, tailWord_4496663, baseEnd_4496663] using wordTrace_append hprefix tailTrace_4496663
  have hstable : (prefixWord ++ tailWord_4496663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496663).length < 2 ^ (prefixWord ++ tailWord_4496663).sum := by decide
  have hdescent : baseEnd_4496663 < baseStart_4496663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496673 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4496673 : Nat := 118140960795 + 4496673 * 2 ^ 59
def prefixEnd_4496673 : Nat := 4983230072969 + 3 ^ 40 * 4496673 * 2
def baseEnd_4496673 : Nat := 2308954595094990479907683

theorem tailTrace_4496673 : CollatzResearch.WordTrace tailWord_4496673 prefixEnd_4496673 2308954595094990479907683 := by
  unfold tailWord_4496673
  simp only [CollatzResearch.WordTrace]
  refine ⟨164007138038329166452246673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109338092025552777634831115 164007138038329166452246673)
  ·
    refine ⟨123005353528746874839185005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164007138038329166452246673 123005353528746874839185005)
    ·
      refine ⟨46127007573280078064694377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123005353528746874839185005 46127007573280078064694377)
      ·
        refine ⟨34595255679960058548520783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46127007573280078064694377 34595255679960058548520783)
        ·
          refine ⟨51892883519940087822781175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34595255679960058548520783 51892883519940087822781175)
          ·
            refine ⟨77839325279910131734171763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51892883519940087822781175 77839325279910131734171763)
            ·
              refine ⟨116758987919865197601257645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77839325279910131734171763 116758987919865197601257645)
              ·
                refine ⟨43784620469949449100471617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116758987919865197601257645 43784620469949449100471617)
                ·
                  refine ⟨32838465352462086825353713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43784620469949449100471617 32838465352462086825353713)
                  ·
                    refine ⟨24628849014346565119015285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32838465352462086825353713 24628849014346565119015285)
                    ·
                      refine ⟨2308954595094990479907683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24628849014346565119015285 2308954595094990479907683)
                      ·
                        rfl

theorem cell23_4496673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4496673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496673 prefixEnd_4496673 := by exact prefixLift 4496673
  have htrace : WordTrace (prefixWord ++ tailWord_4496673) baseStart_4496673 baseEnd_4496673 := by
    simpa [prefixWord, tailWord_4496673, baseEnd_4496673] using wordTrace_append hprefix tailTrace_4496673
  have hstable : (prefixWord ++ tailWord_4496673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496673).length < 2 ^ (prefixWord ++ tailWord_4496673).sum := by decide
  have hdescent : baseEnd_4496673 < baseStart_4496673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496723 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 7]
def baseStart_4496723 : Nat := 118140960795 + 4496723 * 2 ^ 59
def prefixEnd_4496723 : Nat := 4983230072969 + 3 ^ 40 * 4496723 * 2
def baseEnd_4496723 : Nat := 256553363236412809364717

theorem tailTrace_4496723 : CollatzResearch.WordTrace tailWord_4496723 prefixEnd_4496723 256553363236412809364717 := by
  unfold tailWord_4496723
  simp only [CollatzResearch.WordTrace]
  refine ⟨164008961688148024991566823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109339307792098683327711215 164008961688148024991566823)
  ·
    refine ⟨246013442532222037487350235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164008961688148024991566823 246013442532222037487350235)
    ·
      refine ⟨369020163798333056231025353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246013442532222037487350235 369020163798333056231025353)
      ·
        refine ⟨276765122848749792173269015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369020163798333056231025353 276765122848749792173269015)
        ·
          refine ⟨415147684273124688259903523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276765122848749792173269015 415147684273124688259903523)
          ·
            refine ⟨622721526409687032389855285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415147684273124688259903523 622721526409687032389855285)
            ·
              refine ⟨58380143100908159286548933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 622721526409687032389855285 58380143100908159286548933)
              ·
                refine ⟨10946276831420279866227925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58380143100908159286548933 10946276831420279866227925)
                ·
                  refine ⟨256553363236412809364717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10946276831420279866227925 256553363236412809364717)
                  ·
                    rfl

theorem cell23_4496723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 7].length) (baseStart_4496723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496723 prefixEnd_4496723 := by exact prefixLift 4496723
  have htrace : WordTrace (prefixWord ++ tailWord_4496723) baseStart_4496723 baseEnd_4496723 := by
    simpa [prefixWord, tailWord_4496723, baseEnd_4496723] using wordTrace_append hprefix tailTrace_4496723
  have hstable : (prefixWord ++ tailWord_4496723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496723).length < 2 ^ (prefixWord ++ tailWord_4496723).sum := by decide
  have hdescent : baseEnd_4496723 < baseStart_4496723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496807 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4496807 : Nat := 118140960795 + 4496807 * 2 ^ 59
def prefixEnd_4496807 : Nat := 4983230072969 + 3 ^ 40 * 4496807 * 2
def baseEnd_4496807 : Nat := 2309023401502692955632067

theorem tailTrace_4496807 : CollatzResearch.WordTrace tailWord_4496807 prefixEnd_4496807 2309023401502692955632067 := by
  unfold tailWord_4496807
  simp only [CollatzResearch.WordTrace]
  refine ⟨164012025419843707337624675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109341350279895804891749783 164012025419843707337624675)
  ·
    refine ⟨246018038129765561006437013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164012025419843707337624675 246018038129765561006437013)
    ·
      refine ⟨11532095537332760672176735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246018038129765561006437013 11532095537332760672176735)
      ·
        refine ⟨17298143305999141008265103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11532095537332760672176735 17298143305999141008265103)
        ·
          refine ⟨25947214958998711512397655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17298143305999141008265103 25947214958998711512397655)
          ·
            refine ⟨38920822438498067268596483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25947214958998711512397655 38920822438498067268596483)
            ·
              refine ⟨58381233657747100902894725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38920822438498067268596483 58381233657747100902894725)
              ·
                refine ⟨10946481310827581419292761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58381233657747100902894725 10946481310827581419292761)
                ·
                  refine ⟨8209860983120686064469571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10946481310827581419292761 8209860983120686064469571)
                  ·
                    refine ⟨12314791474681029096704357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8209860983120686064469571 12314791474681029096704357)
                    ·
                      refine ⟨2309023401502692955632067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12314791474681029096704357 2309023401502692955632067)
                      ·
                        rfl

theorem cell23_4496807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4496807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496807 prefixEnd_4496807 := by exact prefixLift 4496807
  have htrace : WordTrace (prefixWord ++ tailWord_4496807) baseStart_4496807 baseEnd_4496807 := by
    simpa [prefixWord, tailWord_4496807, baseEnd_4496807] using wordTrace_append hprefix tailTrace_4496807
  have hstable : (prefixWord ++ tailWord_4496807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496807).length < 2 ^ (prefixWord ++ tailWord_4496807).sum := by decide
  have hdescent : baseEnd_4496807 < baseStart_4496807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496808 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 5]
def baseStart_4496808 : Nat := 118140960795 + 4496808 * 2 ^ 59
def prefixEnd_4496808 : Nat := 4983230072969 + 3 ^ 40 * 4496808 * 2
def baseEnd_4496808 : Nat := 256558212775927494635507

theorem tailTrace_4496808 : CollatzResearch.WordTrace tailWord_4496808 prefixEnd_4496808 256558212775927494635507 := by
  unfold tailWord_4496808
  simp only [CollatzResearch.WordTrace]
  refine ⟨82006030946420042254205539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109341374595226723005607385 82006030946420042254205539)
  ·
    refine ⟨123009046419630063381308309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82006030946420042254205539 123009046419630063381308309)
    ·
      refine ⟨5766049050920159220998827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123009046419630063381308309 5766049050920159220998827)
      ·
        refine ⟨8649073576380238831498241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5766049050920159220998827 8649073576380238831498241)
        ·
          refine ⟨6486805182285179123623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8649073576380238831498241 6486805182285179123623681)
          ·
            refine ⟨4865103886713884342717761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6486805182285179123623681 4865103886713884342717761)
            ·
              refine ⟨3648827915035413257038321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865103886713884342717761 3648827915035413257038321)
              ·
                refine ⟨2736620936276559942778741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648827915035413257038321 2736620936276559942778741)
                ·
                  refine ⟨256558212775927494635507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736620936276559942778741 256558212775927494635507)
                  ·
                    rfl

theorem cell23_4496808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 5].length) (baseStart_4496808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496808 prefixEnd_4496808 := by exact prefixLift 4496808
  have htrace : WordTrace (prefixWord ++ tailWord_4496808) baseStart_4496808 baseEnd_4496808 := by
    simpa [prefixWord, tailWord_4496808, baseEnd_4496808] using wordTrace_append hprefix tailTrace_4496808
  have hstable : (prefixWord ++ tailWord_4496808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496808).length < 2 ^ (prefixWord ++ tailWord_4496808).sum := by decide
  have hdescent : baseEnd_4496808 < baseStart_4496808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496817 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 3, 4]
def baseStart_4496817 : Nat := 118140960795 + 4496817 * 2 ^ 59
def prefixEnd_4496817 : Nat := 4983230072969 + 3 ^ 40 * 4496817 * 2
def baseEnd_4496817 : Nat := 769676178769745972169007

theorem tailTrace_4496817 : CollatzResearch.WordTrace tailWord_4496817 prefixEnd_4496817 769676178769745972169007 := by
  unfold tailWord_4496817
  simp only [CollatzResearch.WordTrace]
  refine ⟨164012390149807479045488705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109341593433204986030325803 164012390149807479045488705)
  ·
    refine ⟨123009292612355609284116529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164012390149807479045488705 123009292612355609284116529)
    ·
      refine ⟨92256969459266706963087397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123009292612355609284116529 92256969459266706963087397)
      ·
        refine ⟨17298181773612507555578887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92256969459266706963087397 17298181773612507555578887)
        ·
          refine ⟨25947272660418761333368331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17298181773612507555578887 25947272660418761333368331)
          ·
            refine ⟨38920908990628142000052497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25947272660418761333368331 38920908990628142000052497)
            ·
              refine ⟨29190681742971106500039373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38920908990628142000052497 29190681742971106500039373)
              ·
                refine ⟨10946505653614164937514765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29190681742971106500039373 10946505653614164937514765)
                ·
                  refine ⟨4104939620105311851568037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10946505653614164937514765 4104939620105311851568037)
                  ·
                    refine ⟨769676178769745972169007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4104939620105311851568037 769676178769745972169007)
                    ·
                      rfl

theorem cell23_4496817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_4496817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496817 prefixEnd_4496817 := by exact prefixLift 4496817
  have htrace : WordTrace (prefixWord ++ tailWord_4496817) baseStart_4496817 baseEnd_4496817 := by
    simpa [prefixWord, tailWord_4496817, baseEnd_4496817] using wordTrace_append hprefix tailTrace_4496817
  have hstable : (prefixWord ++ tailWord_4496817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496817).length < 2 ^ (prefixWord ++ tailWord_4496817).sum := by decide
  have hdescent : baseEnd_4496817 < baseStart_4496817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496830 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_4496830 : Nat := 118140960795 + 4496830 * 2 ^ 59
def prefixEnd_4496830 : Nat := 4983230072969 + 3 ^ 40 * 4496830 * 2
def baseEnd_4496830 : Nat := 256559467950860707293829

theorem tailTrace_4496830 : CollatzResearch.WordTrace tailWord_4496830 prefixEnd_4496830 256559467950860707293829 := by
  unfold tailWord_4496830
  simp only [CollatzResearch.WordTrace]
  refine ⟨20501608037345047783213993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109341909532506921510474629 20501608037345047783213993)
  ·
    refine ⟨15376206028008785837410495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20501608037345047783213993 15376206028008785837410495)
    ·
      refine ⟨23064309042013178756115743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15376206028008785837410495 23064309042013178756115743)
      ·
        refine ⟨34596463563019768134173615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23064309042013178756115743 34596463563019768134173615)
        ·
          refine ⟨51894695344529652201260423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34596463563019768134173615 51894695344529652201260423)
          ·
            refine ⟨77842043016794478301890635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51894695344529652201260423 77842043016794478301890635)
            ·
              refine ⟨116763064525191717452835953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77842043016794478301890635 116763064525191717452835953)
              ·
                refine ⟨87572298393893788089626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116763064525191717452835953 87572298393893788089626965)
                ·
                  refine ⟨256559467950860707293829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87572298393893788089626965 256559467950860707293829)
                  ·
                    rfl

theorem cell23_4496830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_4496830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496830 prefixEnd_4496830 := by exact prefixLift 4496830
  have htrace : WordTrace (prefixWord ++ tailWord_4496830) baseStart_4496830 baseEnd_4496830 := by
    simpa [prefixWord, tailWord_4496830, baseEnd_4496830] using wordTrace_append hprefix tailTrace_4496830
  have hstable : (prefixWord ++ tailWord_4496830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496830).length < 2 ^ (prefixWord ++ tailWord_4496830).sum := by decide
  have hdescent : baseEnd_4496830 < baseStart_4496830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496844 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4496844 : Nat := 118140960795 + 4496844 * 2 ^ 59
def prefixEnd_4496844 : Nat := 4983230072969 + 3 ^ 40 * 4496844 * 2
def baseEnd_4496844 : Nat := 2309042400286909310869397

theorem tailTrace_4496844 : CollatzResearch.WordTrace tailWord_4496844 prefixEnd_4496844 2309042400286909310869397 := by
  unfold tailWord_4496844
  simp only [CollatzResearch.WordTrace]
  refine ⟨82006687460354831328360793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109342249947139775104481057 82006687460354831328360793)
  ·
    refine ⟨61505015595266123496270595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82006687460354831328360793 61505015595266123496270595)
    ·
      refine ⟨92257523392899185244405893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61505015595266123496270595 92257523392899185244405893)
      ·
        refine ⟨17298285636168597233326105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92257523392899185244405893 17298285636168597233326105)
        ·
          refine ⟨12973714227126447924994579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17298285636168597233326105 12973714227126447924994579)
          ·
            refine ⟨19460571340689671887491869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12973714227126447924994579 19460571340689671887491869)
            ·
              refine ⟨7297714252758626957809451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19460571340689671887491869 7297714252758626957809451)
              ·
                refine ⟨10946571379137940436714177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7297714252758626957809451 10946571379137940436714177)
                ·
                  refine ⟨8209928534353455327535633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10946571379137940436714177 8209928534353455327535633)
                  ·
                    refine ⟨6157446400765091495651725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8209928534353455327535633 6157446400765091495651725)
                    ·
                      refine ⟨2309042400286909310869397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157446400765091495651725 2309042400286909310869397)
                      ·
                        rfl

theorem cell23_4496844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4496844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496844 prefixEnd_4496844 := by exact prefixLift 4496844
  have htrace : WordTrace (prefixWord ++ tailWord_4496844) baseStart_4496844 baseEnd_4496844 := by
    simpa [prefixWord, tailWord_4496844, baseEnd_4496844] using wordTrace_append hprefix tailTrace_4496844
  have hstable : (prefixWord ++ tailWord_4496844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496844).length < 2 ^ (prefixWord ++ tailWord_4496844).sum := by decide
  have hdescent : baseEnd_4496844 < baseStart_4496844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496917 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_4496917 : Nat := 118140960795 + 4496917 * 2 ^ 59
def prefixEnd_4496917 : Nat := 4983230072969 + 3 ^ 40 * 4496917 * 2
def baseEnd_4496917 : Nat := 2309079884374687525256561

theorem tailTrace_4496917 : CollatzResearch.WordTrace tailWord_4496917 prefixEnd_4496917 2309079884374687525256561 := by
  unfold tailWord_4496917
  simp only [CollatzResearch.WordTrace]
  refine ⟨164016037449445196124129005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109344024966296797416086003 164016037449445196124129005)
  ·
    refine ⟨61506014043541948546548377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164016037449445196124129005 61506014043541948546548377)
    ·
      refine ⟨46129510532656461409911283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61506014043541948546548377 46129510532656461409911283)
      ·
        refine ⟨69194265798984692114866925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46129510532656461409911283 69194265798984692114866925)
        ·
          refine ⟨25947849674619259543075097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69194265798984692114866925 25947849674619259543075097)
          ·
            refine ⟨19460887255964444657306323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25947849674619259543075097 19460887255964444657306323)
            ·
              refine ⟨29191330883946666985959485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19460887255964444657306323 29191330883946666985959485)
              ·
                refine ⟨10946749081480000119734807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29191330883946666985959485 10946749081480000119734807)
                ·
                  refine ⟨16420123622220000179602211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10946749081480000119734807 16420123622220000179602211)
                  ·
                    refine ⟨24630185433330000269403317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16420123622220000179602211 24630185433330000269403317)
                    ·
                      refine ⟨2309079884374687525256561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24630185433330000269403317 2309079884374687525256561)
                      ·
                        rfl

theorem cell23_4496917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_4496917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496917 prefixEnd_4496917 := by exact prefixLift 4496917
  have htrace : WordTrace (prefixWord ++ tailWord_4496917) baseStart_4496917 baseEnd_4496917 := by
    simpa [prefixWord, tailWord_4496917, baseEnd_4496917] using wordTrace_append hprefix tailTrace_4496917
  have hstable : (prefixWord ++ tailWord_4496917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496917).length < 2 ^ (prefixWord ++ tailWord_4496917).sum := by decide
  have hdescent : baseEnd_4496917 < baseStart_4496917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496924 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_4496924 : Nat := 118140960795 + 4496924 * 2 ^ 59
def prefixEnd_4496924 : Nat := 4983230072969 + 3 ^ 40 * 4496924 * 2
def baseEnd_4496924 : Nat := 769694492913089665956343

theorem tailTrace_4496924 : CollatzResearch.WordTrace tailWord_4496924 prefixEnd_4496924 769694492913089665956343 := by
  unfold tailWord_4496924
  simp only [CollatzResearch.WordTrace]
  refine ⟨82008146380209918159816913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109344195173613224213089217 82008146380209918159816913)
  ·
    refine ⟨61506109785157438619862685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82008146380209918159816913 61506109785157438619862685)
    ·
      refine ⟨23064791169434039482448507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61506109785157438619862685 23064791169434039482448507)
      ·
        refine ⟨34597186754151059223672761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23064791169434039482448507 34597186754151059223672761)
        ·
          refine ⟨25947890065613294417754571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34597186754151059223672761 25947890065613294417754571)
          ·
            refine ⟨38921835098419941626631857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25947890065613294417754571 38921835098419941626631857)
            ·
              refine ⟨29191376323814956219973893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38921835098419941626631857 29191376323814956219973893)
              ·
                refine ⟨5473383060715304291245105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29191376323814956219973893 5473383060715304291245105)
                ·
                  refine ⟨4105037295536478218433829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473383060715304291245105 4105037295536478218433829)
                  ·
                    refine ⟨769694492913089665956343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105037295536478218433829 769694492913089665956343)
                    ·
                      rfl

theorem cell23_4496924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_4496924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496924 prefixEnd_4496924 := by exact prefixLift 4496924
  have htrace : WordTrace (prefixWord ++ tailWord_4496924) baseStart_4496924 baseEnd_4496924 := by
    simpa [prefixWord, tailWord_4496924, baseEnd_4496924] using wordTrace_append hprefix tailTrace_4496924
  have hstable : (prefixWord ++ tailWord_4496924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496924).length < 2 ^ (prefixWord ++ tailWord_4496924).sum := by decide
  have hdescent : baseEnd_4496924 < baseStart_4496924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496951 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_4496951 : Nat := 118140960795 + 4496951 * 2 ^ 59
def prefixEnd_4496951 : Nat := 4983230072969 + 3 ^ 40 * 4496951 * 2
def baseEnd_4496951 : Nat := 2309097342716940392231405

theorem tailTrace_4496951 : CollatzResearch.WordTrace tailWord_4496951 prefixEnd_4496951 2309097342716940392231405 := by
  unfold tailWord_4496951
  simp only [CollatzResearch.WordTrace]
  refine ⟨164017277531322019930866707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109344851687548013287244471 164017277531322019930866707)
  ·
    refine ⟨246025916296983029896300061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164017277531322019930866707 246025916296983029896300061)
    ·
      refine ⟨92259718611368636211112523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246025916296983029896300061 92259718611368636211112523)
      ·
        refine ⟨138389577917052954316668785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92259718611368636211112523 138389577917052954316668785)
        ·
          refine ⟨103792183437789715737501589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138389577917052954316668785 103792183437789715737501589)
          ·
            refine ⟨4865258598646392925195387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103792183437789715737501589 4865258598646392925195387)
            ·
              refine ⟨7297887897969589387793081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865258598646392925195387 7297887897969589387793081)
              ·
                refine ⟨5473415923477192040844811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7297887897969589387793081 5473415923477192040844811)
                ·
                  refine ⟨8210123885215788061267217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5473415923477192040844811 8210123885215788061267217)
                  ·
                    refine ⟨6157592913911841045950413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8210123885215788061267217 6157592913911841045950413)
                    ·
                      refine ⟨2309097342716940392231405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157592913911841045950413 2309097342716940392231405)
                      ·
                        rfl

theorem cell23_4496951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_4496951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496951 prefixEnd_4496951 := by exact prefixLift 4496951
  have htrace : WordTrace (prefixWord ++ tailWord_4496951) baseStart_4496951 baseEnd_4496951 := by
    simpa [prefixWord, tailWord_4496951, baseEnd_4496951] using wordTrace_append hprefix tailTrace_4496951
  have hstable : (prefixWord ++ tailWord_4496951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496951).length < 2 ^ (prefixWord ++ tailWord_4496951).sum := by decide
  have hdescent : baseEnd_4496951 < baseStart_4496951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4496997 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_4496997 : Nat := 118140960795 + 4496997 * 2 ^ 59
def prefixEnd_4496997 : Nat := 4983230072969 + 3 ^ 40 * 4496997 * 2
def baseEnd_4496997 : Nat := 769706987609015737418731

theorem tailTrace_4496997 : CollatzResearch.WordTrace tailWord_4496997 prefixEnd_4496997 769706987609015737418731 := by
  unfold tailWord_4496997
  simp only [CollatzResearch.WordTrace]
  refine ⟨164018955289155369787041245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109345970192770246524694163 164018955289155369787041245)
  ·
    refine ⟨61507108233433263670140467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164018955289155369787041245 61507108233433263670140467)
    ·
      refine ⟨92260662350149895505210701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61507108233433263670140467 92260662350149895505210701)
      ·
        refine ⟨34597748381306210814454013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92260662350149895505210701 34597748381306210814454013)
        ·
          refine ⟨12974155642989829055420255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34597748381306210814454013 12974155642989829055420255)
          ·
            refine ⟨19461233464484743583130383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12974155642989829055420255 19461233464484743583130383)
            ·
              refine ⟨29191850196727115374695575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19461233464484743583130383 29191850196727115374695575)
              ·
                refine ⟨43787775295090673062043363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29191850196727115374695575 43787775295090673062043363)
                ·
                  refine ⟨65681662942636009593065045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43787775295090673062043363 65681662942636009593065045)
                  ·
                    refine ⟨769706987609015737418731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65681662942636009593065045 769706987609015737418731)
                    ·
                      rfl

theorem cell23_4496997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_4496997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4496997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4496997 prefixEnd_4496997 := by exact prefixLift 4496997
  have htrace : WordTrace (prefixWord ++ tailWord_4496997) baseStart_4496997 baseEnd_4496997 := by
    simpa [prefixWord, tailWord_4496997, baseEnd_4496997] using wordTrace_append hprefix tailTrace_4496997
  have hstable : (prefixWord ++ tailWord_4496997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4496997).length < 2 ^ (prefixWord ++ tailWord_4496997).sum := by decide
  have hdescent : baseEnd_4496997 < baseStart_4496997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4496997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497007 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_4497007 : Nat := 118140960795 + 4497007 * 2 ^ 59
def prefixEnd_4497007 : Nat := 4983230072969 + 3 ^ 40 * 4497007 * 2
def baseEnd_4497007 : Nat := 2309126097633592173131147

theorem tailTrace_4497007 : CollatzResearch.WordTrace tailWord_4497007 prefixEnd_4497007 2309126097633592173131147 := by
  unfold tailWord_4497007
  simp only [CollatzResearch.WordTrace]
  refine ⟨164019320019119141494905275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109346213346079427663270183 164019320019119141494905275)
  ·
    refine ⟨246028980028678712242357913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164019320019119141494905275 246028980028678712242357913)
    ·
      refine ⟨184521735021509034181768435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246028980028678712242357913 184521735021509034181768435)
      ·
        refine ⟨276782602532263551272652653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184521735021509034181768435 276782602532263551272652653)
        ·
          refine ⟨103793475949598831727244745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276782602532263551272652653 103793475949598831727244745)
          ·
            refine ⟨77845106962199123795433559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103793475949598831727244745 77845106962199123795433559)
            ·
              refine ⟨116767660443298685693150339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77845106962199123795433559 116767660443298685693150339)
              ·
                refine ⟨175151490664948028539725509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116767660443298685693150339 175151490664948028539725509)
                ·
                  refine ⟨32840904499677755351198533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175151490664948028539725509 32840904499677755351198533)
                  ·
                    refine ⟨6157669593689579128349725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32840904499677755351198533 6157669593689579128349725)
                    ·
                      refine ⟨2309126097633592173131147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157669593689579128349725 2309126097633592173131147)
                      ·
                        rfl

theorem cell23_4497007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_4497007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497007 prefixEnd_4497007 := by exact prefixLift 4497007
  have htrace : WordTrace (prefixWord ++ tailWord_4497007) baseStart_4497007 baseEnd_4497007 := by
    simpa [prefixWord, tailWord_4497007, baseEnd_4497007] using wordTrace_append hprefix tailTrace_4497007
  have hstable : (prefixWord ++ tailWord_4497007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497007).length < 2 ^ (prefixWord ++ tailWord_4497007).sum := by decide
  have hdescent : baseEnd_4497007 < baseStart_4497007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497017 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_4497017 : Nat := 118140960795 + 4497017 * 2 ^ 59
def prefixEnd_4497017 : Nat := 4983230072969 + 3 ^ 40 * 4497017 * 2
def baseEnd_4497017 : Nat := 2309131232440137134006101

theorem tailTrace_4497017 : CollatzResearch.WordTrace tailWord_4497017 prefixEnd_4497017 2309131232440137134006101 := by
  unfold tailWord_4497017
  simp only [CollatzResearch.WordTrace]
  refine ⟨164019684749082913202769305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109346456499388608801846203 164019684749082913202769305)
  ·
    refine ⟨123014763561812184902076979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164019684749082913202769305 123014763561812184902076979)
    ·
      refine ⟨184522145342718277353115469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123014763561812184902076979 184522145342718277353115469)
      ·
        refine ⟨69195804503519354007418301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184522145342718277353115469 69195804503519354007418301)
        ·
          refine ⟨25948426688819757752781863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69195804503519354007418301 25948426688819757752781863)
          ·
            refine ⟨38922640033229636629172795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25948426688819757752781863 38922640033229636629172795)
            ·
              refine ⟨58383960049844454943759193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38922640033229636629172795 58383960049844454943759193)
              ·
                refine ⟨43787970037383341207819395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58383960049844454943759193 43787970037383341207819395)
                ·
                  refine ⟨65681955056075011811729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43787970037383341207819395 65681955056075011811729093)
                  ·
                    refine ⟨12315366573014064714699205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65681955056075011811729093 12315366573014064714699205)
                    ·
                      refine ⟨2309131232440137134006101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12315366573014064714699205 2309131232440137134006101)
                      ·
                        rfl

theorem cell23_4497017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_4497017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497017 prefixEnd_4497017 := by exact prefixLift 4497017
  have htrace : WordTrace (prefixWord ++ tailWord_4497017) baseStart_4497017 baseEnd_4497017 := by
    simpa [prefixWord, tailWord_4497017, baseEnd_4497017] using wordTrace_append hprefix tailTrace_4497017
  have hstable : (prefixWord ++ tailWord_4497017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497017).length < 2 ^ (prefixWord ++ tailWord_4497017).sum := by decide
  have hdescent : baseEnd_4497017 < baseStart_4497017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497021 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_4497021 : Nat := 118140960795 + 4497021 * 2 ^ 59
def prefixEnd_4497021 : Nat := 4983230072969 + 3 ^ 40 * 4497021 * 2
def baseEnd_4497021 : Nat := 2309133286362755118356083

theorem tailTrace_4497021 : CollatzResearch.WordTrace tailWord_4497021 prefixEnd_4497021 2309133286362755118356083 := by
  unfold tailWord_4497021
  simp only [CollatzResearch.WordTrace]
  refine ⟨164019830641068421885914917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109346553760712281257276611 164019830641068421885914917)
  ·
    refine ⟨30753718245200329103609047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164019830641068421885914917 30753718245200329103609047)
    ·
      refine ⟨46130577367800493655413571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30753718245200329103609047 46130577367800493655413571)
      ·
        refine ⟨69195866051700740483120357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46130577367800493655413571 69195866051700740483120357)
        ·
          refine ⟨12974224884693888840585067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69195866051700740483120357 12974224884693888840585067)
          ·
            refine ⟨19461337327040833260877601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12974224884693888840585067 19461337327040833260877601)
            ·
              refine ⟨14596002995280624945658201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19461337327040833260877601 14596002995280624945658201)
              ·
                refine ⟨10947002246460468709243651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14596002995280624945658201 10947002246460468709243651)
                ·
                  refine ⟨16420503369690703063865477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10947002246460468709243651 16420503369690703063865477)
                  ·
                    refine ⟨3078844381817006824474777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16420503369690703063865477 3078844381817006824474777)
                    ·
                      refine ⟨2309133286362755118356083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078844381817006824474777 2309133286362755118356083)
                      ·
                        rfl

theorem cell23_4497021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_4497021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497021 prefixEnd_4497021 := by exact prefixLift 4497021
  have htrace : WordTrace (prefixWord ++ tailWord_4497021) baseStart_4497021 baseEnd_4497021 := by
    simpa [prefixWord, tailWord_4497021, baseEnd_4497021] using wordTrace_append hprefix tailTrace_4497021
  have hstable : (prefixWord ++ tailWord_4497021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497021).length < 2 ^ (prefixWord ++ tailWord_4497021).sum := by decide
  have hdescent : baseEnd_4497021 < baseStart_4497021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497025 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_4497025 : Nat := 118140960795 + 4497025 * 2 ^ 59
def prefixEnd_4497025 : Nat := 4983230072969 + 3 ^ 40 * 4497025 * 2
def baseEnd_4497025 : Nat := 2309135340285373102706065

theorem tailTrace_4497025 : CollatzResearch.WordTrace tailWord_4497025 prefixEnd_4497025 2309135340285373102706065 := by
  unfold tailWord_4497025
  simp only [CollatzResearch.WordTrace]
  refine ⟨164019976533053930569060529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109346651022035953712707019 164019976533053930569060529)
  ·
    refine ⟨123014982399790447926795397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164019976533053930569060529 123014982399790447926795397)
    ·
      refine ⟨23065309199960708986274137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123014982399790447926795397 23065309199960708986274137)
      ·
        refine ⟨17298981899970531739705603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23065309199960708986274137 17298981899970531739705603)
        ·
          refine ⟨25948472849955797609558405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17298981899970531739705603 25948472849955797609558405)
          ·
            refine ⟨4865338659366712051792201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25948472849955797609558405 4865338659366712051792201)
            ·
              refine ⟨3649003994525034038844151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865338659366712051792201 3649003994525034038844151)
              ·
                refine ⟨5473505991787551058266227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649003994525034038844151 5473505991787551058266227)
                ·
                  refine ⟨8210258987681326587399341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5473505991787551058266227 8210258987681326587399341)
                  ·
                    refine ⟨3078847120380497470274753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8210258987681326587399341 3078847120380497470274753)
                    ·
                      refine ⟨2309135340285373102706065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078847120380497470274753 2309135340285373102706065)
                      ·
                        rfl

theorem cell23_4497025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_4497025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497025 prefixEnd_4497025 := by exact prefixLift 4497025
  have htrace : WordTrace (prefixWord ++ tailWord_4497025) baseStart_4497025 baseEnd_4497025 := by
    simpa [prefixWord, tailWord_4497025, baseEnd_4497025] using wordTrace_append hprefix tailTrace_4497025
  have hstable : (prefixWord ++ tailWord_4497025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497025).length < 2 ^ (prefixWord ++ tailWord_4497025).sum := by decide
  have hdescent : baseEnd_4497025 < baseStart_4497025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497032 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4497032 : Nat := 118140960795 + 4497032 * 2 ^ 59
def prefixEnd_4497032 : Nat := 4983230072969 + 3 ^ 40 * 4497032 * 2
def baseEnd_4497032 : Nat := 2309138934649954575318533

theorem tailTrace_4497032 : CollatzResearch.WordTrace tailWord_4497032 prefixEnd_4497032 2309138934649954575318533 := by
  unfold tailWord_4497032
  simp only [CollatzResearch.WordTrace]
  refine ⟨82010115922014285382282675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109346821229352380509710233 82010115922014285382282675)
  ·
    refine ⟨123015173883021428073424013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82010115922014285382282675 123015173883021428073424013)
    ·
      refine ⟨46130690206133035527534005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123015173883021428073424013 46130690206133035527534005)
      ·
        refine ⟨4324752206824972080706313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46130690206133035527534005 4324752206824972080706313)
        ·
          refine ⟨3243564155118729060529735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4324752206824972080706313 3243564155118729060529735)
          ·
            refine ⟨4865346232678093590794603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243564155118729060529735 4865346232678093590794603)
            ·
              refine ⟨7298019349017140386191905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865346232678093590794603 7298019349017140386191905)
              ·
                refine ⟨5473514511762855289643929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7298019349017140386191905 5473514511762855289643929)
                ·
                  refine ⟨4105135883822141467232947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473514511762855289643929 4105135883822141467232947)
                  ·
                    refine ⟨6157703825733212200849421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105135883822141467232947 6157703825733212200849421)
                    ·
                      refine ⟨2309138934649954575318533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157703825733212200849421 2309138934649954575318533)
                      ·
                        rfl

theorem cell23_4497032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4497032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497032 prefixEnd_4497032 := by exact prefixLift 4497032
  have htrace : WordTrace (prefixWord ++ tailWord_4497032) baseStart_4497032 baseEnd_4497032 := by
    simpa [prefixWord, tailWord_4497032, baseEnd_4497032] using wordTrace_append hprefix tailTrace_4497032
  have hstable : (prefixWord ++ tailWord_4497032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497032).length < 2 ^ (prefixWord ++ tailWord_4497032).sum := by decide
  have hdescent : baseEnd_4497032 < baseStart_4497032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497034 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4497034 : Nat := 118140960795 + 4497034 * 2 ^ 59
def prefixEnd_4497034 : Nat := 4983230072969 + 3 ^ 40 * 4497034 * 2
def baseEnd_4497034 : Nat := 2309139961611263567493523

theorem tailTrace_4497034 : CollatzResearch.WordTrace tailWord_4497034 prefixEnd_4497034 2309139961611263567493523 := by
  unfold tailWord_4497034
  simp only [CollatzResearch.WordTrace]
  refine ⟨41005076197505331276534539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109346869860014216737425437 41005076197505331276534539)
  ·
    refine ⟨61507614296257996914801809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41005076197505331276534539 61507614296257996914801809)
    ·
      refine ⟨46130710722193497686101357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61507614296257996914801809 46130710722193497686101357)
      ·
        refine ⟨17299016520822561632288009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46130710722193497686101357 17299016520822561632288009)
        ·
          refine ⟨12974262390616921224216007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17299016520822561632288009 12974262390616921224216007)
          ·
            refine ⟨19461393585925381836324011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12974262390616921224216007 19461393585925381836324011)
            ·
              refine ⟨29192090378888072754486017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19461393585925381836324011 29192090378888072754486017)
              ·
                refine ⟨21894067784166054565864513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29192090378888072754486017 21894067784166054565864513)
                ·
                  refine ⟨16420550838124540924398385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21894067784166054565864513 16420550838124540924398385)
                  ·
                    refine ⟨12315413128593405693298789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16420550838124540924398385 12315413128593405693298789)
                    ·
                      refine ⟨2309139961611263567493523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12315413128593405693298789 2309139961611263567493523)
                      ·
                        rfl

theorem cell23_4497034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4497034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497034 prefixEnd_4497034 := by exact prefixLift 4497034
  have htrace : WordTrace (prefixWord ++ tailWord_4497034) baseStart_4497034 baseEnd_4497034 := by
    simpa [prefixWord, tailWord_4497034, baseEnd_4497034] using wordTrace_append hprefix tailTrace_4497034
  have hstable : (prefixWord ++ tailWord_4497034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497034).length < 2 ^ (prefixWord ++ tailWord_4497034).sum := by decide
  have hdescent : baseEnd_4497034 < baseStart_4497034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497038 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4497038 : Nat := 118140960795 + 4497038 * 2 ^ 59
def prefixEnd_4497038 : Nat := 4983230072969 + 3 ^ 40 * 4497038 * 2
def baseEnd_4497038 : Nat := 2309142015533881551843505

theorem tailTrace_4497038 : CollatzResearch.WordTrace tailWord_4497038 prefixEnd_4497038 2309142015533881551843505 := by
  unfold tailWord_4497038
  simp only [CollatzResearch.WordTrace]
  refine ⟨20502556335250854223660471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109346967121337889192855845 20502556335250854223660471)
  ·
    refine ⟨30753834502876281335490707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20502556335250854223660471 30753834502876281335490707)
    ·
      refine ⟨46130751754314422003236061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30753834502876281335490707 46130751754314422003236061)
      ·
        refine ⟨17299031907867908251213523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46130751754314422003236061 17299031907867908251213523)
        ·
          refine ⟨25948547861801862376820285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17299031907867908251213523 25948547861801862376820285)
          ·
            refine ⟨9730705448175698391307607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25948547861801862376820285 9730705448175698391307607)
            ·
              refine ⟨14596058172263547586961411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9730705448175698391307607 14596058172263547586961411)
              ·
                refine ⟨21894087258395321380442117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14596058172263547586961411 21894087258395321380442117)
                ·
                  refine ⟨4105141360949122758832897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21894087258395321380442117 4105141360949122758832897)
                  ·
                    refine ⟨3078856020711842069124673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105141360949122758832897 3078856020711842069124673)
                    ·
                      refine ⟨2309142015533881551843505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078856020711842069124673 2309142015533881551843505)
                      ·
                        rfl

theorem cell23_4497038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4497038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497038 prefixEnd_4497038 := by exact prefixLift 4497038
  have htrace : WordTrace (prefixWord ++ tailWord_4497038) baseStart_4497038 baseEnd_4497038 := by
    simpa [prefixWord, tailWord_4497038, baseEnd_4497038] using wordTrace_append hprefix tailTrace_4497038
  have hstable : (prefixWord ++ tailWord_4497038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497038).length < 2 ^ (prefixWord ++ tailWord_4497038).sum := by decide
  have hdescent : baseEnd_4497038 < baseStart_4497038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497055 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4497055 : Nat := 118140960795 + 4497055 * 2 ^ 59
def prefixEnd_4497055 : Nat := 4983230072969 + 3 ^ 40 * 4497055 * 2
def baseEnd_4497055 : Nat := 2309150744705007985330927

theorem tailTrace_4497055 : CollatzResearch.WordTrace tailWord_4497055 prefixEnd_4497055 2309150744705007985330927 := by
  unfold tailWord_4497055
  simp only [CollatzResearch.WordTrace]
  refine ⟨164021070722945245692652619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109347380481963497128435079 164021070722945245692652619)
  ·
    refine ⟨246031606084417868538978929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164021070722945245692652619 246031606084417868538978929)
    ·
      refine ⟨184523704563313401404234197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246031606084417868538978929 184523704563313401404234197)
      ·
        refine ⟨4324774325702657845411739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 184523704563313401404234197 4324774325702657845411739)
        ·
          refine ⟨6487161488553986768117609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324774325702657845411739 6487161488553986768117609)
          ·
            refine ⟨4865371116415490076088207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6487161488553986768117609 4865371116415490076088207)
            ·
              refine ⟨7298056674623235114132311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865371116415490076088207 7298056674623235114132311)
              ·
                refine ⟨10947085011934852671198467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7298056674623235114132311 10947085011934852671198467)
                ·
                  refine ⟨16420627517902279006797701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10947085011934852671198467 16420627517902279006797701)
                  ·
                    refine ⟨3078867659606677313774569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16420627517902279006797701 3078867659606677313774569)
                    ·
                      refine ⟨2309150744705007985330927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078867659606677313774569 2309150744705007985330927)
                      ·
                        rfl

theorem cell23_4497055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4497055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497055 prefixEnd_4497055 := by exact prefixLift 4497055
  have htrace : WordTrace (prefixWord ++ tailWord_4497055) baseStart_4497055 baseEnd_4497055 := by
    simpa [prefixWord, tailWord_4497055, baseEnd_4497055] using wordTrace_append hprefix tailTrace_4497055
  have hstable : (prefixWord ++ tailWord_4497055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497055).length < 2 ^ (prefixWord ++ tailWord_4497055).sum := by decide
  have hdescent : baseEnd_4497055 < baseStart_4497055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497101 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4497101 : Nat := 118140960795 + 4497101 * 2 ^ 59
def prefixEnd_4497101 : Nat := 4983230072969 + 3 ^ 40 * 4497101 * 2
def baseEnd_4497101 : Nat := 2309174364815114805355715

theorem tailTrace_4497101 : CollatzResearch.WordTrace tailWord_4497101 prefixEnd_4497101 2309174364815114805355715 := by
  unfold tailWord_4497101
  simp only [CollatzResearch.WordTrace]
  refine ⟨164022748480778595548827157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109348498987185730365884771 164022748480778595548827157)
  ·
    refine ⟨7688566335036496666351273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164022748480778595548827157 7688566335036496666351273)
    ·
      refine ⟨5766424751277372499763455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7688566335036496666351273 5766424751277372499763455)
      ·
        refine ⟨8649637126916058749645183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5766424751277372499763455 8649637126916058749645183)
        ·
          refine ⟨12974455690374088124467775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8649637126916058749645183 12974455690374088124467775)
          ·
            refine ⟨19461683535561132186701663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12974455690374088124467775 19461683535561132186701663)
            ·
              refine ⟨29192525303341698280052495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19461683535561132186701663 29192525303341698280052495)
              ·
                refine ⟨43788787955012547420078743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29192525303341698280052495 43788787955012547420078743)
                ·
                  refine ⟨65683181932518821130118115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43788787955012547420078743 65683181932518821130118115)
                  ·
                    refine ⟨98524772898778231695177173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65683181932518821130118115 98524772898778231695177173)
                    ·
                      refine ⟨2309174364815114805355715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98524772898778231695177173 2309174364815114805355715)
                      ·
                        rfl

theorem cell23_4497101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4497101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497101 prefixEnd_4497101 := by exact prefixLift 4497101
  have htrace : WordTrace (prefixWord ++ tailWord_4497101) baseStart_4497101 baseEnd_4497101 := by
    simpa [prefixWord, tailWord_4497101, baseEnd_4497101] using wordTrace_append hprefix tailTrace_4497101
  have hstable : (prefixWord ++ tailWord_4497101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497101).length < 2 ^ (prefixWord ++ tailWord_4497101).sum := by decide
  have hdescent : baseEnd_4497101 < baseStart_4497101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497104 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_4497104 : Nat := 118140960795 + 4497104 * 2 ^ 59
def prefixEnd_4497104 : Nat := 4983230072969 + 3 ^ 40 * 4497104 * 2
def baseEnd_4497104 : Nat := 769725301752359431206067

theorem tailTrace_4497104 : CollatzResearch.WordTrace tailWord_4497104 prefixEnd_4497104 769725301752359431206067 := by
  unfold tailWord_4497104
  simp only [CollatzResearch.WordTrace]
  refine ⟨82011428949883863530593183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109348571933178484707457577 82011428949883863530593183)
  ·
    refine ⟨123017143424825795295889775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82011428949883863530593183 123017143424825795295889775)
    ·
      refine ⟨184525715137238692943834663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123017143424825795295889775 184525715137238692943834663)
      ·
        refine ⟨276788572705858039415751995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184525715137238692943834663 276788572705858039415751995)
        ·
          refine ⟨415182859058787059123627993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276788572705858039415751995 415182859058787059123627993)
          ·
            refine ⟨311387144294090294342720995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415182859058787059123627993 311387144294090294342720995)
            ·
              refine ⟨467080716441135441514081493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311387144294090294342720995 467080716441135441514081493)
              ·
                refine ⟨10947204291589111910486285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 467080716441135441514081493 10947204291589111910486285)
                ·
                  refine ⟨4105201609345916966432357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10947204291589111910486285 4105201609345916966432357)
                  ·
                    refine ⟨769725301752359431206067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105201609345916966432357 769725301752359431206067)
                    ·
                      rfl

theorem cell23_4497104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_4497104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497104 prefixEnd_4497104 := by exact prefixLift 4497104
  have htrace : WordTrace (prefixWord ++ tailWord_4497104) baseStart_4497104 baseEnd_4497104 := by
    simpa [prefixWord, tailWord_4497104, baseEnd_4497104] using wordTrace_append hprefix tailTrace_4497104
  have hstable : (prefixWord ++ tailWord_4497104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497104).length < 2 ^ (prefixWord ++ tailWord_4497104).sum := by decide
  have hdescent : baseEnd_4497104 < baseStart_4497104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497107 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_4497107 : Nat := 118140960795 + 4497107 * 2 ^ 59
def prefixEnd_4497107 : Nat := 4983230072969 + 3 ^ 40 * 4497107 * 2
def baseEnd_4497107 : Nat := 2309177445699041781880687

theorem tailTrace_4497107 : CollatzResearch.WordTrace tailWord_4497107 prefixEnd_4497107 2309177445699041781880687 := by
  unfold tailWord_4497107
  simp only [CollatzResearch.WordTrace]
  refine ⟨164022967318756858573545575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109348644879171239049030383 164022967318756858573545575)
  ·
    refine ⟨246034450978135287860318363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164022967318756858573545575 246034450978135287860318363)
    ·
      refine ⟨369051676467202931790477545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246034450978135287860318363 369051676467202931790477545)
      ·
        refine ⟨276788757350402198842858159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369051676467202931790477545 276788757350402198842858159)
        ·
          refine ⟨415183136025603298264287239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276788757350402198842858159 415183136025603298264287239)
          ·
            refine ⟨622774704038404947396430859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415183136025603298264287239 622774704038404947396430859)
            ·
              refine ⟨934162056057607421094646289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622774704038404947396430859 934162056057607421094646289)
              ·
                refine ⟨700621542043205565820984717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934162056057607421094646289 700621542043205565820984717)
                ·
                  refine ⟨262733078266202087182869269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700621542043205565820984717 262733078266202087182869269)
                  ·
                    refine ⟨12315613043728222836696997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 262733078266202087182869269 12315613043728222836696997)
                    ·
                      refine ⟨2309177445699041781880687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12315613043728222836696997 2309177445699041781880687)
                      ·
                        rfl

theorem cell23_4497107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_4497107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497107 prefixEnd_4497107 := by exact prefixLift 4497107
  have htrace : WordTrace (prefixWord ++ tailWord_4497107) baseStart_4497107 baseEnd_4497107 := by
    simpa [prefixWord, tailWord_4497107, baseEnd_4497107] using wordTrace_append hprefix tailTrace_4497107
  have hstable : (prefixWord ++ tailWord_4497107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497107).length < 2 ^ (prefixWord ++ tailWord_4497107).sum := by decide
  have hdescent : baseEnd_4497107 < baseStart_4497107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497138 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_4497138 : Nat := 118140960795 + 4497138 * 2 ^ 59
def prefixEnd_4497138 : Nat := 4983230072969 + 3 ^ 40 * 4497138 * 2
def baseEnd_4497138 : Nat := 769731121199777053531015

theorem tailTrace_4497138 : CollatzResearch.WordTrace tailWord_4497138 prefixEnd_4497138 769731121199777053531015 := by
  unfold tailWord_4497138
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006024495411137716981017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109349398654429700578616045 41006024495411137716981017)
  ·
    refine ⟨30754518371558353287735763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41006024495411137716981017 30754518371558353287735763)
    ·
      refine ⟨46131777557337529931603645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30754518371558353287735763 46131777557337529931603645)
      ·
        refine ⟨17299416584001573724351367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46131777557337529931603645 17299416584001573724351367)
        ·
          refine ⟨25949124876002360586527051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17299416584001573724351367 25949124876002360586527051)
          ·
            refine ⟨38923687314003540879790577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25949124876002360586527051 38923687314003540879790577)
            ·
              refine ⟨29192765485502655659842933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38923687314003540879790577 29192765485502655659842933)
              ·
                refine ⟨2736821764265873968110275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29192765485502655659842933 2736821764265873968110275)
                ·
                  refine ⟨4105232646398810952165413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736821764265873968110275 4105232646398810952165413)
                  ·
                    refine ⟨769731121199777053531015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105232646398810952165413 769731121199777053531015)
                    ·
                      rfl

theorem cell23_4497138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_4497138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497138 prefixEnd_4497138 := by exact prefixLift 4497138
  have htrace : WordTrace (prefixWord ++ tailWord_4497138) baseStart_4497138 baseEnd_4497138 := by
    simpa [prefixWord, tailWord_4497138, baseEnd_4497138] using wordTrace_append hprefix tailTrace_4497138
  have hstable : (prefixWord ++ tailWord_4497138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497138).length < 2 ^ (prefixWord ++ tailWord_4497138).sum := by decide
  have hdescent : baseEnd_4497138 < baseStart_4497138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497161 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 3]
def baseStart_4497161 : Nat := 118140960795 + 4497161 * 2 ^ 59
def prefixEnd_4497161 : Nat := 4983230072969 + 3 ^ 40 * 4497161 * 2
def baseEnd_4497161 : Nat := 2309205173654384570605439

theorem tailTrace_4497161 : CollatzResearch.WordTrace tailWord_4497161 prefixEnd_4497161 2309205173654384570605439 := by
  unfold tailWord_4497161
  simp only [CollatzResearch.WordTrace]
  refine ⟨164024936860561225796011337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109349957907040817197340891 164024936860561225796011337)
  ·
    refine ⟨123018702645420919347008503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164024936860561225796011337 123018702645420919347008503)
    ·
      refine ⟨184528053968131379020512755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123018702645420919347008503 184528053968131379020512755)
      ·
        refine ⟨276792080952197068530769133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184528053968131379020512755 276792080952197068530769133)
        ·
          refine ⟨103797030357073900699038425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276792080952197068530769133 103797030357073900699038425)
          ·
            refine ⟨77847772767805425524278819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103797030357073900699038425 77847772767805425524278819)
            ·
              refine ⟨116771659151708138286418229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77847772767805425524278819 116771659151708138286418229)
              ·
                refine ⟨10947343045472637964351709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116771659151708138286418229 10947343045472637964351709)
                ·
                  refine ⟨4105253642052239236631891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10947343045472637964351709 4105253642052239236631891)
                  ·
                    refine ⟨6157880463078358854947837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105253642052239236631891 6157880463078358854947837)
                    ·
                      refine ⟨2309205173654384570605439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157880463078358854947837 2309205173654384570605439)
                      ·
                        rfl

theorem cell23_4497161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_4497161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497161 prefixEnd_4497161 := by exact prefixLift 4497161
  have htrace : WordTrace (prefixWord ++ tailWord_4497161) baseStart_4497161 baseEnd_4497161 := by
    simpa [prefixWord, tailWord_4497161, baseEnd_4497161] using wordTrace_append hprefix tailTrace_4497161
  have hstable : (prefixWord ++ tailWord_4497161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497161).length < 2 ^ (prefixWord ++ tailWord_4497161).sum := by decide
  have hdescent : baseEnd_4497161 < baseStart_4497161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497164 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_4497164 : Nat := 118140960795 + 4497164 * 2 ^ 59
def prefixEnd_4497164 : Nat := 4983230072969 + 3 ^ 40 * 4497164 * 2
def baseEnd_4497164 : Nat := 769735571365449352955975

theorem tailTrace_4497164 : CollatzResearch.WordTrace tailWord_4497164 prefixEnd_4497164 769735571365449352955975 := by
  unfold tailWord_4497164
  simp only [CollatzResearch.WordTrace]
  refine ⟨82012523139775178654185273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109350030853033571538913697 82012523139775178654185273)
  ·
    refine ⟨61509392354831383990638955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82012523139775178654185273 61509392354831383990638955)
    ·
      refine ⟨92264088532247075985958433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61509392354831383990638955 92264088532247075985958433)
      ·
        refine ⟨69198066399185306989468825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92264088532247075985958433 69198066399185306989468825)
        ·
          refine ⟨51898549799388980242101619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69198066399185306989468825 51898549799388980242101619)
          ·
            refine ⟨77847824699083470363152429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51898549799388980242101619 77847824699083470363152429)
            ·
              refine ⟨29192934262156301386182161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77847824699083470363152429 29192934262156301386182161)
              ·
                refine ⟨21894700696617226039636621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29192934262156301386182161 21894700696617226039636621)
                ·
                  refine ⟨8210512761231459764863733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21894700696617226039636621 8210512761231459764863733)
                  ·
                    refine ⟨769735571365449352955975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8210512761231459764863733 769735571365449352955975)
                    ·
                      rfl

theorem cell23_4497164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_4497164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497164 prefixEnd_4497164 := by exact prefixLift 4497164
  have htrace : WordTrace (prefixWord ++ tailWord_4497164) baseStart_4497164 baseEnd_4497164 := by
    simpa [prefixWord, tailWord_4497164, baseEnd_4497164] using wordTrace_append hprefix tailTrace_4497164
  have hstable : (prefixWord ++ tailWord_4497164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497164).length < 2 ^ (prefixWord ++ tailWord_4497164).sum := by decide
  have hdescent : baseEnd_4497164 < baseStart_4497164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497172 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4497172 : Nat := 118140960795 + 4497172 * 2 ^ 59
def prefixEnd_4497172 : Nat := 4983230072969 + 3 ^ 40 * 4497172 * 2
def baseEnd_4497172 : Nat := 769736940647194675855963

theorem tailTrace_4497172 : CollatzResearch.WordTrace tailWord_4497172 prefixEnd_4497172 769736940647194675855963 := by
  unfold tailWord_4497172
  simp only [CollatzResearch.WordTrace]
  refine ⟨82012669031760687337330885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109350225375680916449774513 82012669031760687337330885)
  ·
    refine ⟨15377375443455128875749541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82012669031760687337330885 15377375443455128875749541)
    ·
      refine ⟨2883257895647836664203039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15377375443455128875749541 2883257895647836664203039)
      ·
        refine ⟨4324886843471754996304559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883257895647836664203039 4324886843471754996304559)
        ·
          refine ⟨6487330265207632494456839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324886843471754996304559 6487330265207632494456839)
          ·
            refine ⟨9730995397811448741685259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6487330265207632494456839 9730995397811448741685259)
            ·
              refine ⟨14596493096717173112527889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9730995397811448741685259 14596493096717173112527889)
              ·
                refine ⟨10947369822537879834395917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14596493096717173112527889 10947369822537879834395917)
                ·
                  refine ⟨4105263683451704937898469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10947369822537879834395917 4105263683451704937898469)
                  ·
                    refine ⟨769736940647194675855963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105263683451704937898469 769736940647194675855963)
                    ·
                      rfl

theorem cell23_4497172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4497172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497172 prefixEnd_4497172 := by exact prefixLift 4497172
  have htrace : WordTrace (prefixWord ++ tailWord_4497172) baseStart_4497172 baseEnd_4497172 := by
    simpa [prefixWord, tailWord_4497172, baseEnd_4497172] using wordTrace_append hprefix tailTrace_4497172
  have hstable : (prefixWord ++ tailWord_4497172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497172).length < 2 ^ (prefixWord ++ tailWord_4497172).sum := by decide
  have hdescent : baseEnd_4497172 < baseStart_4497172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497178 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_4497178 : Nat := 118140960795 + 4497178 * 2 ^ 59
def prefixEnd_4497178 : Nat := 4983230072969 + 3 ^ 40 * 4497178 * 2
def baseEnd_4497178 : Nat := 2309213902825511004092861

theorem tailTrace_4497178 : CollatzResearch.WordTrace tailWord_4497178 prefixEnd_4497178 2309213902825511004092861 := by
  unfold tailWord_4497178
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006389225374909424845047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109350371267666425132920125 41006389225374909424845047)
  ·
    refine ⟨61509583838062364137267571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41006389225374909424845047 61509583838062364137267571)
    ·
      refine ⟨92264375757093546205901357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61509583838062364137267571 92264375757093546205901357)
      ·
        refine ⟨34599140908910079827213009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92264375757093546205901357 34599140908910079827213009)
        ·
          refine ⟨25949355681682559870409757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34599140908910079827213009 25949355681682559870409757)
          ·
            refine ⟨9731008380630959951403659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25949355681682559870409757 9731008380630959951403659)
            ·
              refine ⟨14596512570946439927105489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9731008380630959951403659 14596512570946439927105489)
              ·
                refine ⟨10947384428209829945329117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14596512570946439927105489 10947384428209829945329117)
                ·
                  refine ⟨4105269160578686229498419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10947384428209829945329117 4105269160578686229498419)
                  ·
                    refine ⟨6157903740868029344247629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105269160578686229498419 6157903740868029344247629)
                    ·
                      refine ⟨2309213902825511004092861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6157903740868029344247629 2309213902825511004092861)
                      ·
                        rfl

theorem cell23_4497178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_4497178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497178 prefixEnd_4497178 := by exact prefixLift 4497178
  have htrace : WordTrace (prefixWord ++ tailWord_4497178) baseStart_4497178 baseEnd_4497178 := by
    simpa [prefixWord, tailWord_4497178, baseEnd_4497178] using wordTrace_append hprefix tailTrace_4497178
  have hstable : (prefixWord ++ tailWord_4497178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497178).length < 2 ^ (prefixWord ++ tailWord_4497178).sum := by decide
  have hdescent : baseEnd_4497178 < baseStart_4497178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497188 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_4497188 : Nat := 118140960795 + 4497188 * 2 ^ 59
def prefixEnd_4497188 : Nat := 4983230072969 + 3 ^ 40 * 4497188 * 2
def baseEnd_4497188 : Nat := 2309219037632055964967815

theorem tailTrace_4497188 : CollatzResearch.WordTrace tailWord_4497188 prefixEnd_4497188 2309219037632055964967815 := by
  unfold tailWord_4497188
  simp only [CollatzResearch.WordTrace]
  refine ⟨82012960815731704703622109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109350614420975606271496145 82012960815731704703622109)
  ·
    refine ⟨30754860305899389263858291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82012960815731704703622109 30754860305899389263858291)
    ·
      refine ⟨46132290458849083895787437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30754860305899389263858291 46132290458849083895787437)
      ·
        refine ⟨17299608922068406460920289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46132290458849083895787437 17299608922068406460920289)
        ·
          refine ⟨12974706691551304845690217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17299608922068406460920289 12974706691551304845690217)
          ·
            refine ⟨9731030018663478634267663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12974706691551304845690217 9731030018663478634267663)
            ·
              refine ⟨14596545027995217951401495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9731030018663478634267663 14596545027995217951401495)
              ·
                refine ⟨21894817541992826927102243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14596545027995217951401495 21894817541992826927102243)
                ·
                  refine ⟨32842226312989240390653365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21894817541992826927102243 32842226312989240390653365)
                  ·
                    refine ⟨3078958716842741286623753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32842226312989240390653365 3078958716842741286623753)
                    ·
                      refine ⟨2309219037632055964967815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3078958716842741286623753 2309219037632055964967815)
                      ·
                        rfl

theorem cell23_4497188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_4497188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497188 prefixEnd_4497188 := by exact prefixLift 4497188
  have htrace : WordTrace (prefixWord ++ tailWord_4497188) baseStart_4497188 baseEnd_4497188 := by
    simpa [prefixWord, tailWord_4497188, baseEnd_4497188] using wordTrace_append hprefix tailTrace_4497188
  have hstable : (prefixWord ++ tailWord_4497188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497188).length < 2 ^ (prefixWord ++ tailWord_4497188).sum := by decide
  have hdescent : baseEnd_4497188 < baseStart_4497188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497228 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_4497228 : Nat := 118140960795 + 4497228 * 2 ^ 59
def prefixEnd_4497228 : Nat := 4983230072969 + 3 ^ 40 * 4497228 * 2
def baseEnd_4497228 : Nat := 769746525619411936155877

theorem tailTrace_4497228 : CollatzResearch.WordTrace tailWord_4497228 prefixEnd_4497228 769746525619411936155877 := by
  unfold tailWord_4497228
  simp only [CollatzResearch.WordTrace]
  refine ⟨82013690275659248119350169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109351587034212330825800225 82013690275659248119350169)
  ·
    refine ⟨61510267706744436089512627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82013690275659248119350169 61510267706744436089512627)
    ·
      refine ⟨92265401560116654134268941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61510267706744436089512627 92265401560116654134268941)
      ·
        refine ⟨34599525585043745300350853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92265401560116654134268941 34599525585043745300350853)
        ·
          refine ⟨6487411047195702243815785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34599525585043745300350853 6487411047195702243815785)
          ·
            refine ⟨4865558285396776682861839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6487411047195702243815785 4865558285396776682861839)
            ·
              refine ⟨7298337428095165024292759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4865558285396776682861839 7298337428095165024292759)
              ·
                refine ⟨10947506142142747536439139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7298337428095165024292759 10947506142142747536439139)
                ·
                  refine ⟨16421259213214121304658709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10947506142142747536439139 16421259213214121304658709)
                  ·
                    refine ⟨769746525619411936155877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16421259213214121304658709 769746525619411936155877)
                    ·
                      rfl

theorem cell23_4497228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_4497228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497228 prefixEnd_4497228 := by exact prefixLift 4497228
  have htrace : WordTrace (prefixWord ++ tailWord_4497228) baseStart_4497228 baseEnd_4497228 := by
    simpa [prefixWord, tailWord_4497228, baseEnd_4497228] using wordTrace_append hprefix tailTrace_4497228
  have hstable : (prefixWord ++ tailWord_4497228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497228).length < 2 ^ (prefixWord ++ tailWord_4497228).sum := by decide
  have hdescent : baseEnd_4497228 < baseStart_4497228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497258 : List Nat := [3, 1, 3, 4, 1, 2, 9]
def baseStart_4497258 : Nat := 118140960795 + 4497258 * 2 ^ 59
def prefixEnd_4497258 : Nat := 4983230072969 + 3 ^ 40 * 4497258 * 2
def baseEnd_4497258 : Nat := 28509320756516922112253

theorem tailTrace_4497258 : CollatzResearch.WordTrace tailWord_4497258 prefixEnd_4497258 28509320756516922112253 := by
  unfold tailWord_4497258
  simp only [CollatzResearch.WordTrace]
  refine ⟨41007118685302452840573107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109352316494139874241528285 41007118685302452840573107)
  ·
    refine ⟨61510678027953679260859661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41007118685302452840573107 61510678027953679260859661)
    ·
      refine ⟨23066504260482629722822373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61510678027953679260859661 23066504260482629722822373)
      ·
        refine ⟨4324969548840493073029195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23066504260482629722822373 4324969548840493073029195)
        ·
          refine ⟨6487454323260739609543793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4324969548840493073029195 6487454323260739609543793)
          ·
            refine ⟨4865590742445554707157845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6487454323260739609543793 4865590742445554707157845)
            ·
              refine ⟨28509320756516922112253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4865590742445554707157845 28509320756516922112253)
              ·
                rfl

theorem cell23_4497258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 9].length) (baseStart_4497258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497258 prefixEnd_4497258 := by exact prefixLift 4497258
  have htrace : WordTrace (prefixWord ++ tailWord_4497258) baseStart_4497258 baseEnd_4497258 := by
    simpa [prefixWord, tailWord_4497258, baseEnd_4497258] using wordTrace_append hprefix tailTrace_4497258
  have hstable : (prefixWord ++ tailWord_4497258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497258).length < 2 ^ (prefixWord ++ tailWord_4497258).sum := by decide
  have hdescent : baseEnd_4497258 < baseStart_4497258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497264 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_4497264 : Nat := 118140960795 + 4497264 * 2 ^ 59
def prefixEnd_4497264 : Nat := 4983230072969 + 3 ^ 40 * 4497264 * 2
def baseEnd_4497264 : Nat := 2309258062161797667617465

theorem tailTrace_4497264 : CollatzResearch.WordTrace tailWord_4497264 prefixEnd_4497264 2309258062161797667617465 := by
  unfold tailWord_4497264
  simp only [CollatzResearch.WordTrace]
  refine ⟨82014346789594037193505423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109352462386125382924673897 82014346789594037193505423)
  ·
    refine ⟨123021520184391055790258135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82014346789594037193505423 123021520184391055790258135)
    ·
      refine ⟨184532280276586583685387203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123021520184391055790258135 184532280276586583685387203)
      ·
        refine ⟨276798420414879875528080805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184532280276586583685387203 276798420414879875528080805)
        ·
          refine ⟨51899703827789976661515151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276798420414879875528080805 51899703827789976661515151)
          ·
            refine ⟨77849555741684964992272727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51899703827789976661515151 77849555741684964992272727)
            ·
              refine ⟨116774333612527447488409091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77849555741684964992272727 116774333612527447488409091)
              ·
                refine ⟨175161500418791171232613637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116774333612527447488409091 175161500418791171232613637)
                ·
                  refine ⟨32842781328523344606115057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175161500418791171232613637 32842781328523344606115057)
                  ·
                    refine ⟨24632085996392508454586293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32842781328523344606115057 24632085996392508454586293)
                    ·
                      refine ⟨2309258062161797667617465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24632085996392508454586293 2309258062161797667617465)
                      ·
                        rfl

theorem cell23_4497264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_4497264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497264 prefixEnd_4497264 := by exact prefixLift 4497264
  have htrace : WordTrace (prefixWord ++ tailWord_4497264) baseStart_4497264 baseEnd_4497264 := by
    simpa [prefixWord, tailWord_4497264, baseEnd_4497264] using wordTrace_append hprefix tailTrace_4497264
  have hstable : (prefixWord ++ tailWord_4497264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497264).length < 2 ^ (prefixWord ++ tailWord_4497264).sum := by decide
  have hdescent : baseEnd_4497264 < baseStart_4497264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497269 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4497269 : Nat := 118140960795 + 4497269 * 2 ^ 59
def prefixEnd_4497269 : Nat := 4983230072969 + 3 ^ 40 * 4497269 * 2
def baseEnd_4497269 : Nat := 2309260629565070148054943

theorem tailTrace_4497269 : CollatzResearch.WordTrace tailWord_4497269 prefixEnd_4497269 2309260629565070148054943 := by
  unfold tailWord_4497269
  simp only [CollatzResearch.WordTrace]
  refine ⟨164028875944169960240942861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109352583962779973493961907 164028875944169960240942861)
  ·
    refine ⟨61510828479063735090353573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164028875944169960240942861 61510828479063735090353573)
    ·
      refine ⟨11533280339824450329441295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61510828479063735090353573 11533280339824450329441295)
      ·
        refine ⟨17299920509736675494161943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11533280339824450329441295 17299920509736675494161943)
        ·
          refine ⟨25949880764605013241242915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17299920509736675494161943 25949880764605013241242915)
          ·
            refine ⟨38924821146907519861864373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25949880764605013241242915 38924821146907519861864373)
            ·
              refine ⟨3649201982522579987049785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38924821146907519861864373 3649201982522579987049785)
              ·
                refine ⟨2736901486891934990287339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649201982522579987049785 2736901486891934990287339)
                ·
                  refine ⟨4105352230337902485431009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736901486891934990287339 4105352230337902485431009)
                  ·
                    refine ⟨3079014172753426864073257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105352230337902485431009 3079014172753426864073257)
                    ·
                      refine ⟨2309260629565070148054943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079014172753426864073257 2309260629565070148054943)
                      ·
                        rfl

theorem cell23_4497269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4497269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497269 prefixEnd_4497269 := by exact prefixLift 4497269
  have htrace : WordTrace (prefixWord ++ tailWord_4497269) baseStart_4497269 baseEnd_4497269 := by
    simpa [prefixWord, tailWord_4497269, baseEnd_4497269] using wordTrace_append hprefix tailTrace_4497269
  have hstable : (prefixWord ++ tailWord_4497269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497269).length < 2 ^ (prefixWord ++ tailWord_4497269).sum := by decide
  have hdescent : baseEnd_4497269 < baseStart_4497269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497320 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4497320 : Nat := 118140960795 + 4497320 * 2 ^ 59
def prefixEnd_4497320 : Nat := 4983230072969 + 3 ^ 40 * 4497320 * 2
def baseEnd_4497320 : Nat := 2309286817078449448517209

theorem tailTrace_4497320 : CollatzResearch.WordTrace tailWord_4497320 prefixEnd_4497320 2309286817078449448517209 := by
  unfold tailWord_4497320
  simp only [CollatzResearch.WordTrace]
  refine ⟨82015368033492597975524707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109353824044656797300699609 82015368033492597975524707)
  ·
    refine ⟨123023052050238896963287061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82015368033492597975524707 123023052050238896963287061)
    ·
      refine ⟨5766705564854948295154081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123023052050238896963287061 5766705564854948295154081)
      ·
        refine ⟨4325029173641211221365561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5766705564854948295154081 4325029173641211221365561)
        ·
          refine ⟨3243771880230908416024171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4325029173641211221365561 3243771880230908416024171)
          ·
            refine ⟨4865657820346362624036257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243771880230908416024171 4865657820346362624036257)
            ·
              refine ⟨3649243365259771968027193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865657820346362624036257 3649243365259771968027193)
              ·
                refine ⟨2736932523944828976020395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649243365259771968027193 2736932523944828976020395)
                ·
                  refine ⟨4105398785917243464030593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736932523944828976020395 4105398785917243464030593)
                  ·
                    refine ⟨3079049089437932598022945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105398785917243464030593 3079049089437932598022945)
                    ·
                      refine ⟨2309286817078449448517209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079049089437932598022945 2309286817078449448517209)
                      ·
                        rfl

theorem cell23_4497320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4497320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497320 prefixEnd_4497320 := by exact prefixLift 4497320
  have htrace : WordTrace (prefixWord ++ tailWord_4497320) baseStart_4497320 baseEnd_4497320 := by
    simpa [prefixWord, tailWord_4497320, baseEnd_4497320] using wordTrace_append hprefix tailTrace_4497320
  have hstable : (prefixWord ++ tailWord_4497320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497320).length < 2 ^ (prefixWord ++ tailWord_4497320).sum := by decide
  have hdescent : baseEnd_4497320 < baseStart_4497320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497342 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_4497342 : Nat := 118140960795 + 4497342 * 2 ^ 59
def prefixEnd_4497342 : Nat := 4983230072969 + 3 ^ 40 * 4497342 * 2
def baseEnd_4497342 : Nat := 2309298113652848362442107

theorem tailTrace_4497342 : CollatzResearch.WordTrace tailWord_4497342 prefixEnd_4497342 2309298113652848362442107 := by
  unfold tailWord_4497342
  simp only [CollatzResearch.WordTrace]
  refine ⟨20503942309113186713543785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109354358981936995805566853 20503942309113186713543785)
  ·
    refine ⟨15377956731834890035157839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20503942309113186713543785 15377956731834890035157839)
    ·
      refine ⟨23066935097752335052736759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15377956731834890035157839 23066935097752335052736759)
      ·
        refine ⟨34600402646628502579105139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23066935097752335052736759 34600402646628502579105139)
        ·
          refine ⟨51900603969942753868657709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34600402646628502579105139 51900603969942753868657709)
          ·
            refine ⟨19462726488728532700746641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51900603969942753868657709 19462726488728532700746641)
            ·
              refine ⟨14597044866546399525559981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19462726488728532700746641 14597044866546399525559981)
              ·
                refine ⟨5473891824954899822084993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14597044866546399525559981 5473891824954899822084993)
                ·
                  refine ⟨4105418868716174866563745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5473891824954899822084993 4105418868716174866563745)
                  ·
                    refine ⟨3079064151537131149922809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105418868716174866563745 3079064151537131149922809)
                    ·
                      refine ⟨2309298113652848362442107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079064151537131149922809 2309298113652848362442107)
                      ·
                        rfl

theorem cell23_4497342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_4497342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497342 prefixEnd_4497342 := by exact prefixLift 4497342
  have htrace : WordTrace (prefixWord ++ tailWord_4497342) baseStart_4497342 baseEnd_4497342 := by
    simpa [prefixWord, tailWord_4497342, baseEnd_4497342] using wordTrace_append hprefix tailTrace_4497342
  have hstable : (prefixWord ++ tailWord_4497342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497342).length < 2 ^ (prefixWord ++ tailWord_4497342).sum := by decide
  have hdescent : baseEnd_4497342 < baseStart_4497342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497361 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_4497361 : Nat := 118140960795 + 4497361 * 2 ^ 59
def prefixEnd_4497361 : Nat := 4983230072969 + 3 ^ 40 * 4497361 * 2
def baseEnd_4497361 : Nat := 769769289928427929368173

theorem tailTrace_4497361 : CollatzResearch.WordTrace tailWord_4497361 prefixEnd_4497361 769769289928427929368173 := by
  unfold tailWord_4497361
  simp only [CollatzResearch.WordTrace]
  refine ⟨164032231459836659953291937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109354820973224439968861291 164032231459836659953291937)
  ·
    refine ⟨123024173594877494964968953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164032231459836659953291937 123024173594877494964968953)
    ·
      refine ⟨92268130196158121223726715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123024173594877494964968953 92268130196158121223726715)
      ·
        refine ⟨138402195294237181835590073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92268130196158121223726715 138402195294237181835590073)
        ·
          refine ⟨103801646470677886376692555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138402195294237181835590073 103801646470677886376692555)
          ·
            refine ⟨155702469706016829565038833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103801646470677886376692555 155702469706016829565038833)
            ·
              refine ⟨116776852279512622173779125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155702469706016829565038833 116776852279512622173779125)
              ·
                refine ⟨10947829901204308328791793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116776852279512622173779125 10947829901204308328791793)
                ·
                  refine ⟨8210872425903231246593845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10947829901204308328791793 8210872425903231246593845)
                  ·
                    refine ⟨769769289928427929368173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8210872425903231246593845 769769289928427929368173)
                    ·
                      rfl

theorem cell23_4497361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_4497361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497361 prefixEnd_4497361 := by exact prefixLift 4497361
  have htrace : WordTrace (prefixWord ++ tailWord_4497361) baseStart_4497361 baseEnd_4497361 := by
    simpa [prefixWord, tailWord_4497361, baseEnd_4497361] using wordTrace_append hprefix tailTrace_4497361
  have hstable : (prefixWord ++ tailWord_4497361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497361).length < 2 ^ (prefixWord ++ tailWord_4497361).sum := by decide
  have hdescent : baseEnd_4497361 < baseStart_4497361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497365 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 5]
def baseStart_4497365 : Nat := 118140960795 + 4497365 * 2 ^ 59
def prefixEnd_4497365 : Nat := 4983230072969 + 3 ^ 40 * 4497365 * 2
def baseEnd_4497365 : Nat := 256589991523100196939389

theorem tailTrace_4497365 : CollatzResearch.WordTrace tailWord_4497365 prefixEnd_4497365 256589991523100196939389 := by
  unfold tailWord_4497365
  simp only [CollatzResearch.WordTrace]
  refine ⟨164032377351822168636437549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109354918234548112424291699 164032377351822168636437549)
  ·
    refine ⟨61512141506933313238664081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164032377351822168636437549 61512141506933313238664081)
    ·
      refine ⟨46134106130199984928998061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61512141506933313238664081 46134106130199984928998061)
      ·
        refine ⟨17300289798824994348374273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46134106130199984928998061 17300289798824994348374273)
        ·
          refine ⟨12975217349118745761280705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17300289798824994348374273 12975217349118745761280705)
          ·
            refine ⟨9731413011839059320960529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12975217349118745761280705 9731413011839059320960529)
            ·
              refine ⟨7298559758879294490720397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9731413011839059320960529 7298559758879294490720397)
              ·
                refine ⟨2736959909579735434020149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7298559758879294490720397 2736959909579735434020149)
                ·
                  refine ⟨256589991523100196939389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736959909579735434020149 256589991523100196939389)
                  ·
                    rfl

theorem cell23_4497365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_4497365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497365 prefixEnd_4497365 := by exact prefixLift 4497365
  have htrace : WordTrace (prefixWord ++ tailWord_4497365) baseStart_4497365 baseEnd_4497365 := by
    simpa [prefixWord, tailWord_4497365, baseEnd_4497365] using wordTrace_append hprefix tailTrace_4497365
  have hstable : (prefixWord ++ tailWord_4497365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497365).length < 2 ^ (prefixWord ++ tailWord_4497365).sum := by decide
  have hdescent : baseEnd_4497365 < baseStart_4497365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497468 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_4497468 : Nat := 118140960795 + 4497468 * 2 ^ 59
def prefixEnd_4497468 : Nat := 4983230072969 + 3 ^ 40 * 4497468 * 2
def baseEnd_4497468 : Nat := 769787604071771623155509

theorem tailTrace_4497468 : CollatzResearch.WordTrace tailWord_4497468 prefixEnd_4497468 769787604071771623155509 := by
  unfold tailWord_4497468
  simp only [CollatzResearch.WordTrace]
  refine ⟨82018067035224508613718529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109357422713632678151624705 82018067035224508613718529)
  ·
    refine ⟨61513550276418381460288897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82018067035224508613718529 61513550276418381460288897)
    ·
      refine ⟨46135162707313786095216673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61513550276418381460288897 46135162707313786095216673)
      ·
        refine ⟨34601372030485339571412505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46135162707313786095216673 34601372030485339571412505)
        ·
          refine ⟨25951029022864004678559379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34601372030485339571412505 25951029022864004678559379)
          ·
            refine ⟨38926543534296007017839069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25951029022864004678559379 38926543534296007017839069)
            ·
              refine ⟨14597453825361002631689651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38926543534296007017839069 14597453825361002631689651)
              ·
                refine ⟨21896180738041503947534477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14597453825361002631689651 21896180738041503947534477)
                ·
                  refine ⟨8211067776765563980325429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21896180738041503947534477 8211067776765563980325429)
                  ·
                    refine ⟨769787604071771623155509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8211067776765563980325429 769787604071771623155509)
                    ·
                      rfl

theorem cell23_4497468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_4497468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497468 prefixEnd_4497468 := by exact prefixLift 4497468
  have htrace : WordTrace (prefixWord ++ tailWord_4497468) baseStart_4497468 baseEnd_4497468 := by
    simpa [prefixWord, tailWord_4497468, baseEnd_4497468] using wordTrace_append hprefix tailTrace_4497468
  have hstable : (prefixWord ++ tailWord_4497468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497468).length < 2 ^ (prefixWord ++ tailWord_4497468).sum := by decide
  have hdescent : baseEnd_4497468 < baseStart_4497468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_4497482 : Nat := 118140960795 + 4497482 * 2 ^ 59
def prefixEnd_4497482 : Nat := 4983230072969 + 3 ^ 40 * 4497482 * 2
def baseEnd_4497482 : Nat := 2309370000944477814691463

theorem tailTrace_4497482 : CollatzResearch.WordTrace tailWord_4497482 prefixEnd_4497482 2309370000944477814691463 := by
  unfold tailWord_4497482
  simp only [CollatzResearch.WordTrace]
  refine ⟨41009161173099574404611675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109357763128265531745631133 41009161173099574404611675)
  ·
    refine ⟨61513741759649361606917513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41009161173099574404611675 61513741759649361606917513)
    ·
      refine ⟨46135306319737021205188135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61513741759649361606917513 46135306319737021205188135)
      ·
        refine ⟨69202959479605531807782203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46135306319737021205188135 69202959479605531807782203)
        ·
          refine ⟨103804439219408297711673305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69202959479605531807782203 103804439219408297711673305)
          ·
            refine ⟨77853329414556223283754979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103804439219408297711673305 77853329414556223283754979)
            ·
              refine ⟨116779994121834334925632469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77853329414556223283754979 116779994121834334925632469)
              ·
                refine ⟨2737031112230492224819511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116779994121834334925632469 2737031112230492224819511)
                ·
                  refine ⟨4105546668345738337229267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737031112230492224819511 4105546668345738337229267)
                  ·
                    refine ⟨6158320002518607505843901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105546668345738337229267 6158320002518607505843901)
                    ·
                      refine ⟨2309370000944477814691463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6158320002518607505843901 2309370000944477814691463)
                      ·
                        rfl

theorem cell23_4497482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_4497482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497482 prefixEnd_4497482 := by exact prefixLift 4497482
  have htrace : WordTrace (prefixWord ++ tailWord_4497482) baseStart_4497482 baseEnd_4497482 := by
    simpa [prefixWord, tailWord_4497482, baseEnd_4497482] using wordTrace_append hprefix tailTrace_4497482
  have hstable : (prefixWord ++ tailWord_4497482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497482).length < 2 ^ (prefixWord ++ tailWord_4497482).sum := by decide
  have hdescent : baseEnd_4497482 < baseStart_4497482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497508 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_4497508 : Nat := 118140960795 + 4497508 * 2 ^ 59
def prefixEnd_4497508 : Nat := 4983230072969 + 3 ^ 40 * 4497508 * 2
def baseEnd_4497508 : Nat := 2309383351441494712966343

theorem tailTrace_4497508 : CollatzResearch.WordTrace tailWord_4497508 prefixEnd_4497508 2309383351441494712966343 := by
  unfold tailWord_4497508
  simp only [CollatzResearch.WordTrace]
  refine ⟨82018796495152052029446589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109358395326869402705928785 82018796495152052029446589)
  ·
    refine ⟨30757048685682019511042471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82018796495152052029446589 30757048685682019511042471)
    ·
      refine ⟨46135573028523029266563707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30757048685682019511042471 46135573028523029266563707)
      ·
        refine ⟨69203359542784543899845561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46135573028523029266563707 69203359542784543899845561)
        ·
          refine ⟨51902519657088407924884171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69203359542784543899845561 51902519657088407924884171)
          ·
            refine ⟨77853779485632611887326257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51902519657088407924884171 77853779485632611887326257)
            ·
              refine ⟨58390334614224458915494693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77853779485632611887326257 58390334614224458915494693)
              ·
                refine ⟨10948187740167086046655255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58390334614224458915494693 10948187740167086046655255)
                ·
                  refine ⟨16422281610250629069982883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10948187740167086046655255 16422281610250629069982883)
                  ·
                    refine ⟨24633422415375943604974325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16422281610250629069982883 24633422415375943604974325)
                    ·
                      refine ⟨2309383351441494712966343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24633422415375943604974325 2309383351441494712966343)
                      ·
                        rfl

theorem cell23_4497508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_4497508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497508 prefixEnd_4497508 := by exact prefixLift 4497508
  have htrace : WordTrace (prefixWord ++ tailWord_4497508) baseStart_4497508 baseEnd_4497508 := by
    simpa [prefixWord, tailWord_4497508, baseEnd_4497508] using wordTrace_append hprefix tailTrace_4497508
  have hstable : (prefixWord ++ tailWord_4497508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497508).length < 2 ^ (prefixWord ++ tailWord_4497508).sum := by decide
  have hdescent : baseEnd_4497508 < baseStart_4497508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497522 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_4497522 : Nat := 118140960795 + 4497522 * 2 ^ 59
def prefixEnd_4497522 : Nat := 4983230072969 + 3 ^ 40 * 4497522 * 2
def baseEnd_4497522 : Nat := 2309390540170657658191279

theorem tailTrace_4497522 : CollatzResearch.WordTrace tailWord_4497522 prefixEnd_4497522 2309390540170657658191279 := by
  unfold tailWord_4497522
  simp only [CollatzResearch.WordTrace]
  refine ⟨41009525903063346112475705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109358735741502256299935213 41009525903063346112475705)
  ·
    refine ⟨30757144427297509584356779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41009525903063346112475705 30757144427297509584356779)
    ·
      refine ⟨46135716640946264376535169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30757144427297509584356779 46135716640946264376535169)
      ·
        refine ⟨34601787480709698282401377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46135716640946264376535169 34601787480709698282401377)
        ·
          refine ⟨25951340610532273711801033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34601787480709698282401377 25951340610532273711801033)
          ·
            refine ⟨19463505457899205283850775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25951340610532273711801033 19463505457899205283850775)
            ·
              refine ⟨29195258186848807925776163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19463505457899205283850775 29195258186848807925776163)
              ·
                refine ⟨43792887280273211888664245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29195258186848807925776163 43792887280273211888664245)
                ·
                  refine ⟨4105583182525613614562273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43792887280273211888664245 4105583182525613614562273)
                  ·
                    refine ⟨3079187386894210210921705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105583182525613614562273 3079187386894210210921705)
                    ·
                      refine ⟨2309390540170657658191279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079187386894210210921705 2309390540170657658191279)
                      ·
                        rfl

theorem cell23_4497522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_4497522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497522 prefixEnd_4497522 := by exact prefixLift 4497522
  have htrace : WordTrace (prefixWord ++ tailWord_4497522) baseStart_4497522 baseEnd_4497522 := by
    simpa [prefixWord, tailWord_4497522, baseEnd_4497522] using wordTrace_append hprefix tailTrace_4497522
  have hstable : (prefixWord ++ tailWord_4497522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497522).length < 2 ^ (prefixWord ++ tailWord_4497522).sum := by decide
  have hdescent : baseEnd_4497522 < baseStart_4497522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497539 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 1, 2, 2]
def baseStart_4497539 : Nat := 118140960795 + 4497539 * 2 ^ 59
def prefixEnd_4497539 : Nat := 4983230072969 + 3 ^ 40 * 4497539 * 2
def baseEnd_4497539 : Nat := 2309399269341784091678701

theorem tailTrace_4497539 : CollatzResearch.WordTrace tailWord_4497539 prefixEnd_4497539 2309399269341784091678701 := by
  unfold tailWord_4497539
  simp only [CollatzResearch.WordTrace]
  refine ⟨164038723653191796353271671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109359149102127864235514447 164038723653191796353271671)
  ·
    refine ⟨246058085479787694529907507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164038723653191796353271671 246058085479787694529907507)
    ·
      refine ⟨369087128219681541794861261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246058085479787694529907507 369087128219681541794861261)
      ·
        refine ⟨138407673082380578173072973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369087128219681541794861261 138407673082380578173072973)
        ·
          refine ⟨51902877405892716814902365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138407673082380578173072973 51902877405892716814902365)
          ·
            refine ⟨19463579027209768805588387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51902877405892716814902365 19463579027209768805588387)
            ·
              refine ⟨29195368540814653208382581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19463579027209768805588387 29195368540814653208382581)
              ·
                refine ⟨2737065800701373738285867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29195368540814653208382581 2737065800701373738285867)
                ·
                  refine ⟨4105598701052060607428801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737065800701373738285867 4105598701052060607428801)
                  ·
                    refine ⟨3079199025789045455571601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4105598701052060607428801 3079199025789045455571601)
                    ·
                      refine ⟨2309399269341784091678701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079199025789045455571601 2309399269341784091678701)
                      ·
                        rfl

theorem cell23_4497539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_4497539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497539 prefixEnd_4497539 := by exact prefixLift 4497539
  have htrace : WordTrace (prefixWord ++ tailWord_4497539) baseStart_4497539 baseEnd_4497539 := by
    simpa [prefixWord, tailWord_4497539, baseEnd_4497539] using wordTrace_append hprefix tailTrace_4497539
  have hstable : (prefixWord ++ tailWord_4497539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497539).length < 2 ^ (prefixWord ++ tailWord_4497539).sum := by decide
  have hdescent : baseEnd_4497539 < baseStart_4497539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497566 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4497566 : Nat := 118140960795 + 4497566 * 2 ^ 59
def prefixEnd_4497566 : Nat := 4983230072969 + 3 ^ 40 * 4497566 * 2
def baseEnd_4497566 : Nat := 769804377773151828680359

theorem tailTrace_4497566 : CollatzResearch.WordTrace tailWord_4497566 prefixEnd_4497566 769804377773151828680359 := by
  unfold tailWord_4497566
  simp only [CollatzResearch.WordTrace]
  refine ⟨20504963553011747495563069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109359805616062653309669701 20504963553011747495563069)
  ·
    refine ⟨7689361332379405310836151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20504963553011747495563069 7689361332379405310836151)
    ·
      refine ⟨11534041998569107966254227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689361332379405310836151 11534041998569107966254227)
      ·
        refine ⟨17301062997853661949381341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11534041998569107966254227 17301062997853661949381341)
        ·
          refine ⟨6487898624195123231018003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17301062997853661949381341 6487898624195123231018003)
          ·
            refine ⟨9731847936292684846527005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6487898624195123231018003 9731847936292684846527005)
            ·
              refine ⟨3649442976109756817447627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9731847936292684846527005 3649442976109756817447627)
              ·
                refine ⟨5474164464164635226171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649442976109756817447627 5474164464164635226171441)
                ·
                  refine ⟨4105623348123476419628581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5474164464164635226171441 4105623348123476419628581)
                  ·
                    refine ⟨769804377773151828680359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4105623348123476419628581 769804377773151828680359)
                    ·
                      rfl

theorem cell23_4497566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4497566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497566 prefixEnd_4497566 := by exact prefixLift 4497566
  have htrace : WordTrace (prefixWord ++ tailWord_4497566) baseStart_4497566 baseEnd_4497566 := by
    simpa [prefixWord, tailWord_4497566, baseEnd_4497566] using wordTrace_append hprefix tailTrace_4497566
  have hstable : (prefixWord ++ tailWord_4497566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497566).length < 2 ^ (prefixWord ++ tailWord_4497566).sum := by decide
  have hdescent : baseEnd_4497566 < baseStart_4497566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497595 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 3, 4, 2]
def baseStart_4497595 : Nat := 118140960795 + 4497595 * 2 ^ 59
def prefixEnd_4497595 : Nat := 4983230072969 + 3 ^ 40 * 4497595 * 2
def baseEnd_4497595 : Nat := 2309428024258435872578443

theorem tailTrace_4497595 : CollatzResearch.WordTrace tailWord_4497595 prefixEnd_4497595 2309428024258435872578443 := by
  unfold tailWord_4497595
  simp only [CollatzResearch.WordTrace]
  refine ⟨164040766140988917917310239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109360510760659278611540159 164040766140988917917310239)
  ·
    refine ⟨246061149211483376875965359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164040766140988917917310239 246061149211483376875965359)
    ·
      refine ⟨369091723817225065313948039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246061149211483376875965359 369091723817225065313948039)
      ·
        refine ⟨553637585725837597970922059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369091723817225065313948039 553637585725837597970922059)
        ·
          refine ⟨830456378588756396956383089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553637585725837597970922059 830456378588756396956383089)
          ·
            refine ⟨622842283941567297717287317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830456378588756396956383089 622842283941567297717287317)
            ·
              refine ⟨29195732059760967080497843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 622842283941567297717287317 29195732059760967080497843)
              ·
                refine ⟨43793598089641450620746765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29195732059760967080497843 43793598089641450620746765)
                ·
                  refine ⟨16422599283615543982780037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43793598089641450620746765 16422599283615543982780037)
                  ·
                    refine ⟨3079237365677914496771257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16422599283615543982780037 3079237365677914496771257)
                    ·
                      refine ⟨2309428024258435872578443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079237365677914496771257 2309428024258435872578443)
                      ·
                        rfl

theorem cell23_4497595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4, 2].length) (baseStart_4497595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497595 prefixEnd_4497595 := by exact prefixLift 4497595
  have htrace : WordTrace (prefixWord ++ tailWord_4497595) baseStart_4497595 baseEnd_4497595 := by
    simpa [prefixWord, tailWord_4497595, baseEnd_4497595] using wordTrace_append hprefix tailTrace_4497595
  have hstable : (prefixWord ++ tailWord_4497595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497595).length < 2 ^ (prefixWord ++ tailWord_4497595).sum := by decide
  have hdescent : baseEnd_4497595 < baseStart_4497595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497648 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_4497648 : Nat := 118140960795 + 4497648 * 2 ^ 59
def prefixEnd_4497648 : Nat := 4983230072969 + 3 ^ 40 * 4497648 * 2
def baseEnd_4497648 : Nat := 769818412911041388405233

theorem tailTrace_4497648 : CollatzResearch.WordTrace tailWord_4497648 prefixEnd_4497648 769818412911041388405233 := by
  unfold tailWord_4497648
  simp only [CollatzResearch.WordTrace]
  refine ⟨82021349604898453984494799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109361799473197938645993065 82021349604898453984494799)
  ·
    refine ⟨123032024407347680976742199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82021349604898453984494799 123032024407347680976742199)
    ·
      refine ⟨184548036611021521465113299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123032024407347680976742199 184548036611021521465113299)
      ·
        refine ⟨276822054916532282197669949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184548036611021521465113299 276822054916532282197669949)
        ·
          refine ⟨103808270593699605824126231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276822054916532282197669949 103808270593699605824126231)
          ·
            refine ⟨155712405890549408736189347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103808270593699605824126231 155712405890549408736189347)
            ·
              refine ⟨233568608835824113104284021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155712405890549408736189347 233568608835824113104284021)
              ·
                refine ⟨21897057078358510603526627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233568608835824113104284021 21897057078358510603526627)
                ·
                  refine ⟨32845585617537765905289941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21897057078358510603526627 32845585617537765905289941)
                  ·
                    refine ⟨769818412911041388405233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32845585617537765905289941 769818412911041388405233)
                    ·
                      rfl

theorem cell23_4497648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_4497648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497648 prefixEnd_4497648 := by exact prefixLift 4497648
  have htrace : WordTrace (prefixWord ++ tailWord_4497648) baseStart_4497648 baseEnd_4497648 := by
    simpa [prefixWord, tailWord_4497648, baseEnd_4497648] using wordTrace_append hprefix tailTrace_4497648
  have hstable : (prefixWord ++ tailWord_4497648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497648).length < 2 ^ (prefixWord ++ tailWord_4497648).sum := by decide
  have hdescent : baseEnd_4497648 < baseStart_4497648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497655 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_4497655 : Nat := 118140960795 + 4497655 * 2 ^ 59
def prefixEnd_4497655 : Nat := 4983230072969 + 3 ^ 40 * 4497655 * 2
def baseEnd_4497655 : Nat := 2309458833097705637828167

theorem tailTrace_4497655 : CollatzResearch.WordTrace tailWord_4497655 prefixEnd_4497655 2309458833097705637828167 := by
  unfold tailWord_4497655
  simp only [CollatzResearch.WordTrace]
  refine ⟨164042954520771548164494419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109361969680514365442996279 164042954520771548164494419)
  ·
    refine ⟨246064431781157322246741629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164042954520771548164494419 246064431781157322246741629)
    ·
      refine ⟨92274161917933995842528111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246064431781157322246741629 92274161917933995842528111)
      ·
        refine ⟨138411242876900993763792167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92274161917933995842528111 138411242876900993763792167)
        ·
          refine ⟨207616864315351490645688251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138411242876900993763792167 207616864315351490645688251)
          ·
            refine ⟨311425296473027235968532377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207616864315351490645688251 311425296473027235968532377)
            ·
              refine ⟨233568972354770426976399283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311425296473027235968532377 233568972354770426976399283)
              ·
                refine ⟨350353458532155640464598925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233568972354770426976399283 350353458532155640464598925)
                ·
                  refine ⟨131382546949558365174224597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350353458532155640464598925 131382546949558365174224597)
                  ·
                    refine ⟨3079278444130274183770889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 131382546949558365174224597 3079278444130274183770889)
                    ·
                      refine ⟨2309458833097705637828167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079278444130274183770889 2309458833097705637828167)
                      ·
                        rfl

theorem cell23_4497655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_4497655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497655 prefixEnd_4497655 := by exact prefixLift 4497655
  have htrace : WordTrace (prefixWord ++ tailWord_4497655) baseStart_4497655 baseEnd_4497655 := by
    simpa [prefixWord, tailWord_4497655, baseEnd_4497655] using wordTrace_append hprefix tailTrace_4497655
  have hstable : (prefixWord ++ tailWord_4497655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497655).length < 2 ^ (prefixWord ++ tailWord_4497655).sum := by decide
  have hdescent : baseEnd_4497655 < baseStart_4497655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497662 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4497662 : Nat := 118140960795 + 4497662 * 2 ^ 59
def prefixEnd_4497662 : Nat := 4983230072969 + 3 ^ 40 * 4497662 * 2
def baseEnd_4497662 : Nat := 2309462427462287110440635

theorem tailTrace_4497662 : CollatzResearch.WordTrace tailWord_4497662 prefixEnd_4497662 2309462427462287110440635 := by
  unfold tailWord_4497662
  simp only [CollatzResearch.WordTrace]
  refine ⟨20505401228968273544999905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109362139887830792239999493 20505401228968273544999905)
  ·
    refine ⟨15379050921726205158749929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20505401228968273544999905 15379050921726205158749929)
    ·
      refine ⟨11534288191294653869062447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15379050921726205158749929 11534288191294653869062447)
      ·
        refine ⟨17301432286941980803593671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11534288191294653869062447 17301432286941980803593671)
        ·
          refine ⟨25952148430412971205390507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17301432286941980803593671 25952148430412971205390507)
          ·
            refine ⟨38928222645619456808085761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25952148430412971205390507 38928222645619456808085761)
            ·
              refine ⟨29196166984214592606064321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38928222645619456808085761 29196166984214592606064321)
              ·
                refine ⟨21897125238160944454548241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29196166984214592606064321 21897125238160944454548241)
                ·
                  refine ⟨16422843928620708340911181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21897125238160944454548241 16422843928620708340911181)
                  ·
                    refine ⟨6158566473232765627841693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16422843928620708340911181 6158566473232765627841693)
                    ·
                      refine ⟨2309462427462287110440635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6158566473232765627841693 2309462427462287110440635)
                      ·
                        rfl

theorem cell23_4497662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4497662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497662 prefixEnd_4497662 := by exact prefixLift 4497662
  have htrace : WordTrace (prefixWord ++ tailWord_4497662) baseStart_4497662 baseEnd_4497662 := by
    simpa [prefixWord, tailWord_4497662, baseEnd_4497662] using wordTrace_append hprefix tailTrace_4497662
  have hstable : (prefixWord ++ tailWord_4497662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497662).length < 2 ^ (prefixWord ++ tailWord_4497662).sum := by decide
  have hdescent : baseEnd_4497662 < baseStart_4497662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497665 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4497665 : Nat := 118140960795 + 4497665 * 2 ^ 59
def prefixEnd_4497665 : Nat := 4983230072969 + 3 ^ 40 * 4497665 * 2
def baseEnd_4497665 : Nat := 769821322634750199567707

theorem tailTrace_4497665 : CollatzResearch.WordTrace tailWord_4497665 prefixEnd_4497665 769821322634750199567707 := by
  unfold tailWord_4497665
  simp only [CollatzResearch.WordTrace]
  refine ⟨164043319250735319872358449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109362212833823546581572299 164043319250735319872358449)
  ·
    refine ⟨123032489438051489904268837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164043319250735319872358449 123032489438051489904268837)
    ·
      refine ⟨23068591769634654357050407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123032489438051489904268837 23068591769634654357050407)
      ·
        refine ⟨34602887654451981535575611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23068591769634654357050407 34602887654451981535575611)
        ·
          refine ⟨51904331481677972303363417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34602887654451981535575611 51904331481677972303363417)
          ·
            refine ⟨38928248611258479227522563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51904331481677972303363417 38928248611258479227522563)
            ·
              refine ⟨58392372916887718841283845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38928248611258479227522563 58392372916887718841283845)
              ·
                refine ⟨10948569921916447282740721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58392372916887718841283845 10948569921916447282740721)
                ·
                  refine ⟨8211427441437335462055541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10948569921916447282740721 8211427441437335462055541)
                  ·
                    refine ⟨769821322634750199567707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8211427441437335462055541 769821322634750199567707)
                    ·
                      rfl

theorem cell23_4497665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4497665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497665 prefixEnd_4497665 := by exact prefixLift 4497665
  have htrace : WordTrace (prefixWord ++ tailWord_4497665) baseStart_4497665 baseEnd_4497665 := by
    simpa [prefixWord, tailWord_4497665, baseEnd_4497665] using wordTrace_append hprefix tailTrace_4497665
  have hstable : (prefixWord ++ tailWord_4497665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497665).length < 2 ^ (prefixWord ++ tailWord_4497665).sum := by decide
  have hdescent : baseEnd_4497665 < baseStart_4497665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497672 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_4497672 : Nat := 118140960795 + 4497672 * 2 ^ 59
def prefixEnd_4497672 : Nat := 4983230072969 + 3 ^ 40 * 4497672 * 2
def baseEnd_4497672 : Nat := 2309467562268832071315589

theorem tailTrace_4497672 : CollatzResearch.WordTrace tailWord_4497672 prefixEnd_4497672 2309467562268832071315589 := by
  unfold tailWord_4497672
  simp only [CollatzResearch.WordTrace]
  refine ⟨82021787280854980033931635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109362383041139973378575513 82021787280854980033931635)
  ·
    refine ⟨123032680921282470050897453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82021787280854980033931635 123032680921282470050897453)
    ·
      refine ⟨46137255345480926269086545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123032680921282470050897453 46137255345480926269086545)
      ·
        refine ⟨34602941509110694701814909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46137255345480926269086545 34602941509110694701814909)
        ·
          refine ⟨12976103065916510513180591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34602941509110694701814909 12976103065916510513180591)
          ·
            refine ⟨19464154598874765769770887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12976103065916510513180591 19464154598874765769770887)
            ·
              refine ⟨29196231898312148654656331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19464154598874765769770887 29196231898312148654656331)
              ·
                refine ⟨43794347847468222981984497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29196231898312148654656331 43794347847468222981984497)
                ·
                  refine ⟨32845760885601167236488373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43794347847468222981984497 32845760885601167236488373)
                  ·
                    refine ⟨3079290083025109428420785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32845760885601167236488373 3079290083025109428420785)
                    ·
                      refine ⟨2309467562268832071315589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079290083025109428420785 2309467562268832071315589)
                      ·
                        rfl

theorem cell23_4497672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_4497672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497672 prefixEnd_4497672 := by exact prefixLift 4497672
  have htrace : WordTrace (prefixWord ++ tailWord_4497672) baseStart_4497672 baseEnd_4497672 := by
    simpa [prefixWord, tailWord_4497672, baseEnd_4497672] using wordTrace_append hprefix tailTrace_4497672
  have hstable : (prefixWord ++ tailWord_4497672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497672).length < 2 ^ (prefixWord ++ tailWord_4497672).sum := by decide
  have hdescent : baseEnd_4497672 < baseStart_4497672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497685 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4497685 : Nat := 118140960795 + 4497685 * 2 ^ 59
def prefixEnd_4497685 : Nat := 4983230072969 + 3 ^ 40 * 4497685 * 2
def baseEnd_4497685 : Nat := 2309474237517340520453029

theorem tailTrace_4497685 : CollatzResearch.WordTrace tailWord_4497685 prefixEnd_4497685 2309474237517340520453029 := by
  unfold tailWord_4497685
  simp only [CollatzResearch.WordTrace]
  refine ⟨164044048710662863288086509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109362699140441908858724339 164044048710662863288086509)
  ·
    refine ⟨61516518266498573733032441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164044048710662863288086509 61516518266498573733032441)
    ·
      refine ⟨46137388699873930299774331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61516518266498573733032441 46137388699873930299774331)
      ·
        refine ⟨69206083049810895449661497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46137388699873930299774331 69206083049810895449661497)
        ·
          refine ⟨51904562287358171587246123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69206083049810895449661497 51904562287358171587246123)
          ·
            refine ⟨77856843431037257380869185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51904562287358171587246123 77856843431037257380869185)
            ·
              refine ⟨58392632573277943035651889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77856843431037257380869185 58392632573277943035651889)
              ·
                refine ⟨43794474429958457276738917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58392632573277943035651889 43794474429958457276738917)
                ·
                  refine ⟨8211463955617210739388547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43794474429958457276738917 8211463955617210739388547)
                  ·
                    refine ⟨12317195933425816109082821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8211463955617210739388547 12317195933425816109082821)
                    ·
                      refine ⟨2309474237517340520453029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12317195933425816109082821 2309474237517340520453029)
                      ·
                        rfl

theorem cell23_4497685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4497685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497685 prefixEnd_4497685 := by exact prefixLift 4497685
  have htrace : WordTrace (prefixWord ++ tailWord_4497685) baseStart_4497685 baseEnd_4497685 := by
    simpa [prefixWord, tailWord_4497685, baseEnd_4497685] using wordTrace_append hprefix tailTrace_4497685
  have hstable : (prefixWord ++ tailWord_4497685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497685).length < 2 ^ (prefixWord ++ tailWord_4497685).sum := by decide
  have hdescent : baseEnd_4497685 < baseStart_4497685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497703 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 5]
def baseStart_4497703 : Nat := 118140960795 + 4497703 * 2 ^ 59
def prefixEnd_4497703 : Nat := 4983230072969 + 3 ^ 40 * 4497703 * 2
def baseEnd_4497703 : Nat := 256609275574346827780883

theorem tailTrace_4497703 : CollatzResearch.WordTrace tailWord_4497703 prefixEnd_4497703 256609275574346827780883 := by
  unfold tailWord_4497703
  simp only [CollatzResearch.WordTrace]
  refine ⟨164044705224597652362241763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109363136816398434908161175 164044705224597652362241763)
  ·
    refine ⟨246067057836896478543362645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164044705224597652362241763 246067057836896478543362645)
    ·
      refine ⟨2883598334026130607930031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 246067057836896478543362645 2883598334026130607930031)
      ·
        refine ⟨4325397501039195911895047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883598334026130607930031 4325397501039195911895047)
        ·
          refine ⟨6488096251558793867842571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325397501039195911895047 6488096251558793867842571)
          ·
            refine ⟨9732144377338190801763857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488096251558793867842571 9732144377338190801763857)
            ·
              refine ⟨7299108283003643101322893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9732144377338190801763857 7299108283003643101322893)
              ·
                refine ⟨2737165606126366162996085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7299108283003643101322893 2737165606126366162996085)
                ·
                  refine ⟨256609275574346827780883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2737165606126366162996085 256609275574346827780883)
                  ·
                    rfl

theorem cell23_4497703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 5].length) (baseStart_4497703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497703 prefixEnd_4497703 := by exact prefixLift 4497703
  have htrace : WordTrace (prefixWord ++ tailWord_4497703) baseStart_4497703 baseEnd_4497703 := by
    simpa [prefixWord, tailWord_4497703, baseEnd_4497703] using wordTrace_append hprefix tailTrace_4497703
  have hstable : (prefixWord ++ tailWord_4497703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497703).length < 2 ^ (prefixWord ++ tailWord_4497703).sum := by decide
  have hdescent : baseEnd_4497703 < baseStart_4497703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497752 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_4497752 : Nat := 118140960795 + 4497752 * 2 ^ 59
def prefixEnd_4497752 : Nat := 4983230072969 + 3 ^ 40 * 4497752 * 2
def baseEnd_4497752 : Nat := 2309508640721191758315221

theorem tailTrace_4497752 : CollatzResearch.WordTrace tailWord_4497752 prefixEnd_4497752 2309508640721191758315221 := by
  unfold tailWord_4497752
  simp only [CollatzResearch.WordTrace]
  refine ⟨82023246200710066865387755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109364328267613422487183673 82023246200710066865387755)
  ·
    refine ⟨123034869301065100298081633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82023246200710066865387755 123034869301065100298081633)
    ·
      refine ⟨92276151975798825223561225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123034869301065100298081633 92276151975798825223561225)
      ·
        refine ⟨69207113981849118917670919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92276151975798825223561225 69207113981849118917670919)
        ·
          refine ⟨103810670972773678376506379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69207113981849118917670919 103810670972773678376506379)
          ·
            refine ⟨155716006459160517564759569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103810670972773678376506379 155716006459160517564759569)
            ·
              refine ⟨116787004844370388173569677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155716006459160517564759569 116787004844370388173569677)
              ·
                refine ⟨43795126816638895565088629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116787004844370388173569677 43795126816638895565088629)
                ·
                  refine ⟨4105793139059896459227059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43795126816638895565088629 4105793139059896459227059)
                  ·
                    refine ⟨6158689708589844688840589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105793139059896459227059 6158689708589844688840589)
                    ·
                      refine ⟨2309508640721191758315221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6158689708589844688840589 2309508640721191758315221)
                      ·
                        rfl

theorem cell23_4497752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_4497752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497752 prefixEnd_4497752 := by exact prefixLift 4497752
  have htrace : WordTrace (prefixWord ++ tailWord_4497752) baseStart_4497752 baseEnd_4497752 := by
    simpa [prefixWord, tailWord_4497752, baseEnd_4497752] using wordTrace_append hprefix tailTrace_4497752
  have hstable : (prefixWord ++ tailWord_4497752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497752).length < 2 ^ (prefixWord ++ tailWord_4497752).sum := by decide
  have hdescent : baseEnd_4497752 < baseStart_4497752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497806 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_4497806 : Nat := 118140960795 + 4497806 * 2 ^ 59
def prefixEnd_4497806 : Nat := 4983230072969 + 3 ^ 40 * 4497806 * 2
def baseEnd_4497806 : Nat := 769845456225511515679991

theorem tailTrace_4497806 : CollatzResearch.WordTrace tailWord_4497806 prefixEnd_4497806 769845456225511515679991 := by
  unfold tailWord_4497806
  simp only [CollatzResearch.WordTrace]
  refine ⟨20506057742903062619155159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109365641295483000635494181 20506057742903062619155159)
  ·
    refine ⟨30759086614354593928732739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20506057742903062619155159 30759086614354593928732739)
    ·
      refine ⟨46138629921531890893099109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30759086614354593928732739 46138629921531890893099109)
      ·
        refine ⟨8650993110287229542456083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46138629921531890893099109 8650993110287229542456083)
        ·
          refine ⟨12976489665430844313684125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8650993110287229542456083 12976489665430844313684125)
          ·
            refine ⟨4866183624536566617631547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12976489665430844313684125 4866183624536566617631547)
            ·
              refine ⟨7299275436804849926447321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866183624536566617631547 7299275436804849926447321)
              ·
                refine ⟨5474456577603637444835491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7299275436804849926447321 5474456577603637444835491)
                ·
                  refine ⟨8211684866405456167253237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5474456577603637444835491 8211684866405456167253237)
                  ·
                    refine ⟨769845456225511515679991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8211684866405456167253237 769845456225511515679991)
                    ·
                      rfl

theorem cell23_4497806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_4497806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497806 prefixEnd_4497806 := by exact prefixLift 4497806
  have htrace : WordTrace (prefixWord ++ tailWord_4497806) baseStart_4497806 baseEnd_4497806 := by
    simpa [prefixWord, tailWord_4497806, baseEnd_4497806] using wordTrace_append hprefix tailTrace_4497806
  have hstable : (prefixWord ++ tailWord_4497806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497806).length < 2 ^ (prefixWord ++ tailWord_4497806).sum := by decide
  have hdescent : baseEnd_4497806 < baseStart_4497806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497815 : List Nat := [1, 1, 3, 3, 1, 1, 4, 9]
def baseStart_4497815 : Nat := 118140960795 + 4497815 * 2 ^ 59
def prefixEnd_4497815 : Nat := 4983230072969 + 3 ^ 40 * 4497815 * 2
def baseEnd_4497815 : Nat := 85538555185275000438053

theorem tailTrace_4497815 : CollatzResearch.WordTrace tailWord_4497815 prefixEnd_4497815 85538555185275000438053 := by
  unfold tailWord_4497815
  simp only [CollatzResearch.WordTrace]
  refine ⟨164048790200191895490318899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109365860133461263660212599 164048790200191895490318899)
  ·
    refine ⟨246073185300287843235478349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164048790200191895490318899 246073185300287843235478349)
    ·
      refine ⟨92277444487607941213304381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246073185300287843235478349 92277444487607941213304381)
      ·
        refine ⟨34604041682852977954989143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92277444487607941213304381 34604041682852977954989143)
        ·
          refine ⟨51906062524279466932483715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34604041682852977954989143 51906062524279466932483715)
          ·
            refine ⟨77859093786419200398725573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51906062524279466932483715 77859093786419200398725573)
            ·
              refine ⟨14598580084953600074761045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77859093786419200398725573 14598580084953600074761045)
              ·
                refine ⟨85538555185275000438053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14598580084953600074761045 85538555185275000438053)
                ·
                  rfl

theorem cell23_4497815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 9].length) (baseStart_4497815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497815 prefixEnd_4497815 := by exact prefixLift 4497815
  have htrace : WordTrace (prefixWord ++ tailWord_4497815) baseStart_4497815 baseEnd_4497815 := by
    simpa [prefixWord, tailWord_4497815, baseEnd_4497815] using wordTrace_append hprefix tailTrace_4497815
  have hstable : (prefixWord ++ tailWord_4497815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497815).length < 2 ^ (prefixWord ++ tailWord_4497815).sum := by decide
  have hdescent : baseEnd_4497815 < baseStart_4497815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497826 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_4497826 : Nat := 118140960795 + 4497826 * 2 ^ 59
def prefixEnd_4497826 : Nat := 4983230072969 + 3 ^ 40 * 4497826 * 2
def baseEnd_4497826 : Nat := 2309546638289624468789881

theorem tailTrace_4497826 : CollatzResearch.WordTrace tailWord_4497826 prefixEnd_4497826 2309546638289624468789881 := by
  unfold tailWord_4497826
  simp only [CollatzResearch.WordTrace]
  refine ⟨41012297850788011092242333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109366127602101362912646221 41012297850788011092242333)
  ·
    refine ⟨15379611694045504159590875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41012297850788011092242333 15379611694045504159590875)
    ·
      refine ⟨23069417541068256239386313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15379611694045504159590875 23069417541068256239386313)
      ·
        refine ⟨17302063155801192179539735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23069417541068256239386313 17302063155801192179539735)
        ·
          refine ⟨25953094733701788269309603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17302063155801192179539735 25953094733701788269309603)
          ·
            refine ⟨38929642100552682403964405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25953094733701788269309603 38929642100552682403964405)
            ·
              refine ⟨3649653946926813975371663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38929642100552682403964405 3649653946926813975371663)
              ·
                refine ⟨5474480920390220963057495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649653946926813975371663 5474480920390220963057495)
                ·
                  refine ⟨8211721380585331444586243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5474480920390220963057495 8211721380585331444586243)
                  ·
                    refine ⟨12317582070877997166879365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8211721380585331444586243 12317582070877997166879365)
                    ·
                      refine ⟨2309546638289624468789881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12317582070877997166879365 2309546638289624468789881)
                      ·
                        rfl

theorem cell23_4497826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_4497826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497826 prefixEnd_4497826 := by exact prefixLift 4497826
  have htrace : WordTrace (prefixWord ++ tailWord_4497826) baseStart_4497826 baseEnd_4497826 := by
    simpa [prefixWord, tailWord_4497826, baseEnd_4497826] using wordTrace_append hprefix tailTrace_4497826
  have hstable : (prefixWord ++ tailWord_4497826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497826).length < 2 ^ (prefixWord ++ tailWord_4497826).sum := by decide
  have hdescent : baseEnd_4497826 < baseStart_4497826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497832 : List Nat := [2, 1, 6, 1, 1, 12]
def baseStart_4497832 : Nat := 118140960795 + 4497832 * 2 ^ 59
def prefixEnd_4497832 : Nat := 4983230072969 + 3 ^ 40 * 4497832 * 2
def baseEnd_4497832 : Nat := 9504319831989923643271

theorem tailTrace_4497832 : CollatzResearch.WordTrace tailWord_4497832 prefixEnd_4497832 9504319831989923643271 := by
  unfold tailWord_4497832
  simp only [CollatzResearch.WordTrace]
  refine ⟨82024705120565153696843875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109366273494086871595791833 82024705120565153696843875)
  ·
    refine ⟨123037057680847730545265813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82024705120565153696843875 123037057680847730545265813)
    ·
      refine ⟨5767362078789737369309335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123037057680847730545265813 5767362078789737369309335)
      ·
        refine ⟨8651043118184606053964003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767362078789737369309335 8651043118184606053964003)
        ·
          refine ⟨12976564677276909080946005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8651043118184606053964003 12976564677276909080946005)
          ·
            refine ⟨9504319831989923643271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12976564677276909080946005 9504319831989923643271)
            ·
              rfl

theorem cell23_4497832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 12].length) (baseStart_4497832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497832 prefixEnd_4497832 := by exact prefixLift 4497832
  have htrace : WordTrace (prefixWord ++ tailWord_4497832) baseStart_4497832 baseEnd_4497832 := by
    simpa [prefixWord, tailWord_4497832, baseEnd_4497832] using wordTrace_append hprefix tailTrace_4497832
  have hstable : (prefixWord ++ tailWord_4497832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497832).length < 2 ^ (prefixWord ++ tailWord_4497832).sum := by decide
  have hdescent : baseEnd_4497832 < baseStart_4497832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497837 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4497837 : Nat := 118140960795 + 4497837 * 2 ^ 59
def prefixEnd_4497837 : Nat := 4983230072969 + 3 ^ 40 * 4497837 * 2
def baseEnd_4497837 : Nat := 2309552286576823925752331

theorem tailTrace_4497837 : CollatzResearch.WordTrace tailWord_4497837 prefixEnd_4497837 2309552286576823925752331 := by
  unfold tailWord_4497837
  simp only [CollatzResearch.WordTrace]
  refine ⟨164049592606112193247619765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109366395070741462165079843 164049592606112193247619765)
  ·
    refine ⟨15379649306823018116964353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164049592606112193247619765 15379649306823018116964353)
    ·
      refine ⟨11534736980117263587723265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15379649306823018116964353 11534736980117263587723265)
      ·
        refine ⟨8651052735087947690792449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11534736980117263587723265 8651052735087947690792449)
        ·
          refine ⟨6488289551315960768094337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8651052735087947690792449 6488289551315960768094337)
          ·
            refine ⟨4866217163486970576070753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6488289551315960768094337 4866217163486970576070753)
            ·
              refine ⟨3649662872615227932053065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4866217163486970576070753 3649662872615227932053065)
              ·
                refine ⟨2737247154461420949039799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3649662872615227932053065 2737247154461420949039799)
                ·
                  refine ⟨4105870731692131423559699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737247154461420949039799 4105870731692131423559699)
                  ·
                    refine ⟨6158806097538197135339549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4105870731692131423559699 6158806097538197135339549)
                    ·
                      refine ⟨2309552286576823925752331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6158806097538197135339549 2309552286576823925752331)
                      ·
                        rfl

theorem cell23_4497837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4497837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497837 prefixEnd_4497837 := by exact prefixLift 4497837
  have htrace : WordTrace (prefixWord ++ tailWord_4497837) baseStart_4497837 baseEnd_4497837 := by
    simpa [prefixWord, tailWord_4497837, baseEnd_4497837] using wordTrace_append hprefix tailTrace_4497837
  have hstable : (prefixWord ++ tailWord_4497837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497837).length < 2 ^ (prefixWord ++ tailWord_4497837).sum := by decide
  have hdescent : baseEnd_4497837 < baseStart_4497837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497842 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_4497842 : Nat := 118140960795 + 4497842 * 2 ^ 59
def prefixEnd_4497842 : Nat := 4983230072969 + 3 ^ 40 * 4497842 * 2
def baseEnd_4497842 : Nat := 2309554853980096406189807

theorem tailTrace_4497842 : CollatzResearch.WordTrace tailWord_4497842 prefixEnd_4497842 2309554853980096406189807 := by
  unfold tailWord_4497842
  simp only [CollatzResearch.WordTrace]
  refine ⟨41012443742773519775387945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109366516647396052734367853 41012443742773519775387945)
  ·
    refine ⟨30759332807080139831540959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41012443742773519775387945 30759332807080139831540959)
    ·
      refine ⟨46138999210620209747311439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30759332807080139831540959 46138999210620209747311439)
      ·
        refine ⟨69208498815930314620967159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46138999210620209747311439 69208498815930314620967159)
        ·
          refine ⟨103812748223895471931450739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69208498815930314620967159 103812748223895471931450739)
          ·
            refine ⟨155719122335843207897176109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103812748223895471931450739 155719122335843207897176109)
            ·
              refine ⟨58394670875941202961441041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155719122335843207897176109 58394670875941202961441041)
              ·
                refine ⟨43796003156955902221080781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58394670875941202961441041 43796003156955902221080781)
                ·
                  refine ⟨16423501183858463332905293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43796003156955902221080781 16423501183858463332905293)
                  ·
                    refine ⟨6158812943946923749839485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16423501183858463332905293 6158812943946923749839485)
                    ·
                      refine ⟨2309554853980096406189807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6158812943946923749839485 2309554853980096406189807)
                      ·
                        rfl

theorem cell23_4497842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_4497842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497842 prefixEnd_4497842 := by exact prefixLift 4497842
  have htrace : WordTrace (prefixWord ++ tailWord_4497842) baseStart_4497842 baseEnd_4497842 := by
    simpa [prefixWord, tailWord_4497842, baseEnd_4497842] using wordTrace_append hprefix tailTrace_4497842
  have hstable : (prefixWord ++ tailWord_4497842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497842).length < 2 ^ (prefixWord ++ tailWord_4497842).sum := by decide
  have hdescent : baseEnd_4497842 < baseStart_4497842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497855 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_4497855 : Nat := 118140960795 + 4497855 * 2 ^ 59
def prefixEnd_4497855 : Nat := 4983230072969 + 3 ^ 40 * 4497855 * 2
def baseEnd_4497855 : Nat := 2309561529228604855327247

theorem tailTrace_4497855 : CollatzResearch.WordTrace tailWord_4497855 prefixEnd_4497855 2309561529228604855327247 := by
  unfold tailWord_4497855
  simp only [CollatzResearch.WordTrace]
  refine ⟨164050249120046982321775019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109366832746697988214516679 164050249120046982321775019)
  ·
    refine ⟨246075373680070473482662529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164050249120046982321775019 246075373680070473482662529)
    ·
      refine ⟨184556530260052855111996897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246075373680070473482662529 184556530260052855111996897)
      ·
        refine ⟨138417397695039641333997673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184556530260052855111996897 138417397695039641333997673)
        ·
          refine ⟨103813048271279731000498255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138417397695039641333997673 103813048271279731000498255)
          ·
            refine ⟨155719572406919596500747383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103813048271279731000498255 155719572406919596500747383)
            ·
              refine ⟨233579358610379394751121075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155719572406919596500747383 233579358610379394751121075)
              ·
                refine ⟨350369037915569092126681613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233579358610379394751121075 350369037915569092126681613)
                ·
                  refine ⟨131388389218338409547505605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350369037915569092126681613 131388389218338409547505605)
                  ·
                    refine ⟨24635322978438451790157301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131388389218338409547505605 24635322978438451790157301)
                    ·
                      refine ⟨2309561529228604855327247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24635322978438451790157301 2309561529228604855327247)
                      ·
                        rfl

theorem cell23_4497855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_4497855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497855 prefixEnd_4497855 := by exact prefixLift 4497855
  have htrace : WordTrace (prefixWord ++ tailWord_4497855) baseStart_4497855 baseEnd_4497855 := by
    simpa [prefixWord, tailWord_4497855, baseEnd_4497855] using wordTrace_append hprefix tailTrace_4497855
  have hstable : (prefixWord ++ tailWord_4497855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497855).length < 2 ^ (prefixWord ++ tailWord_4497855).sum := by decide
  have hdescent : baseEnd_4497855 < baseStart_4497855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497912 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_4497912 : Nat := 118140960795 + 4497912 * 2 ^ 59
def prefixEnd_4497912 : Nat := 4983230072969 + 3 ^ 40 * 4497912 * 2
def baseEnd_4497912 : Nat := 2309590797625911132314485

theorem tailTrace_4497912 : CollatzResearch.WordTrace tailWord_4497912 prefixEnd_4497912 2309590797625911132314485 := by
  unfold tailWord_4497912
  simp only [CollatzResearch.WordTrace]
  refine ⟨82026164040420240528299995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109368218720560320704399993 82026164040420240528299995)
  ·
    refine ⟨123039246060630360792449993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82026164040420240528299995 123039246060630360792449993)
    ·
      refine ⟨92279434545472770594337495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123039246060630360792449993 92279434545472770594337495)
      ·
        refine ⟨138419151818209155891506243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92279434545472770594337495 138419151818209155891506243)
        ·
          refine ⟨207628727727313733837259365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138419151818209155891506243 207628727727313733837259365)
          ·
            refine ⟨38930386448871325094486131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207628727727313733837259365 38930386448871325094486131)
            ·
              refine ⟨58395579673306987641729197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38930386448871325094486131 58395579673306987641729197)
              ·
                refine ⟨21898342377490120365648449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58395579673306987641729197 21898342377490120365648449)
                ·
                  refine ⟨16423756783117590274236337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21898342377490120365648449 16423756783117590274236337)
                  ·
                    refine ⟨12317817587338192705677253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16423756783117590274236337 12317817587338192705677253)
                    ·
                      refine ⟨2309590797625911132314485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12317817587338192705677253 2309590797625911132314485)
                      ·
                        rfl

theorem cell23_4497912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_4497912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497912 prefixEnd_4497912 := by exact prefixLift 4497912
  have htrace : WordTrace (prefixWord ++ tailWord_4497912) baseStart_4497912 baseEnd_4497912 := by
    simpa [prefixWord, tailWord_4497912, baseEnd_4497912] using wordTrace_append hprefix tailTrace_4497912
  have hstable : (prefixWord ++ tailWord_4497912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497912).length < 2 ^ (prefixWord ++ tailWord_4497912).sum := by decide
  have hdescent : baseEnd_4497912 < baseStart_4497912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4497989 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_4497989 : Nat := 118140960795 + 4497989 * 2 ^ 59
def prefixEnd_4497989 : Nat := 4983230072969 + 3 ^ 40 * 4497989 * 2
def baseEnd_4497989 : Nat := 2309630335636307331051631

theorem tailTrace_4497989 : CollatzResearch.WordTrace tailWord_4497989 prefixEnd_4497989 2309630335636307331051631 := by
  unfold tailWord_4497989
  simp only [CollatzResearch.WordTrace]
  refine ⟨164055136501561523207153021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109370091001041015471435347 164055136501561523207153021)
  ·
    refine ⟨61520676188085571202682383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164055136501561523207153021 61520676188085571202682383)
    ·
      refine ⟨92281014282128356804023575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61520676188085571202682383 92281014282128356804023575)
      ·
        refine ⟨138421521423192535206035363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92281014282128356804023575 138421521423192535206035363)
        ·
          refine ⟨207632282134788802809053045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138421521423192535206035363 207632282134788802809053045)
          ·
            refine ⟨19465526450136450263348723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207632282134788802809053045 19465526450136450263348723)
            ·
              refine ⟨29198289675204675395023085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19465526450136450263348723 29198289675204675395023085)
              ·
                refine ⟨10949358628201753273133657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29198289675204675395023085 10949358628201753273133657)
                ·
                  refine ⟨8212018971151314954850243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10949358628201753273133657 8212018971151314954850243)
                  ·
                    refine ⟨12318028456726972432275365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8212018971151314954850243 12318028456726972432275365)
                    ·
                      refine ⟨2309630335636307331051631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12318028456726972432275365 2309630335636307331051631)
                      ·
                        rfl

theorem cell23_4497989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_4497989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4497989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4497989 prefixEnd_4497989 := by exact prefixLift 4497989
  have htrace : WordTrace (prefixWord ++ tailWord_4497989) baseStart_4497989 baseEnd_4497989 := by
    simpa [prefixWord, tailWord_4497989, baseEnd_4497989] using wordTrace_append hprefix tailTrace_4497989
  have hstable : (prefixWord ++ tailWord_4497989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4497989).length < 2 ^ (prefixWord ++ tailWord_4497989).sum := by decide
  have hdescent : baseEnd_4497989 < baseStart_4497989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4497989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498073 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 1, 1, 3]
def baseStart_4498073 : Nat := 118140960795 + 4498073 * 2 ^ 59
def prefixEnd_4498073 : Nat := 4983230072969 + 3 ^ 40 * 4498073 * 2
def baseEnd_4498073 : Nat := 2309673468011285002401245

theorem tailTrace_4498073 : CollatzResearch.WordTrace tailWord_4498073 prefixEnd_4498073 2309673468011285002401245 := by
  unfold tailWord_4498073
  simp only [CollatzResearch.WordTrace]
  refine ⟨164058200233257205553210873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109372133488838137035473915 164058200233257205553210873)
  ·
    refine ⟨123043650174942904164908155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164058200233257205553210873 123043650174942904164908155)
    ·
      refine ⟨184565475262414356247362233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123043650174942904164908155 184565475262414356247362233)
      ·
        refine ⟨138424106446810767185521675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184565475262414356247362233 138424106446810767185521675)
        ·
          refine ⟨207636159670216150778282513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138424106446810767185521675 207636159670216150778282513)
          ·
            refine ⟨155727119752662113083711885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207636159670216150778282513 155727119752662113083711885)
            ·
              refine ⟨58397669907248292406391957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155727119752662113083711885 58397669907248292406391957)
              ·
                refine ⟨2737390776902263706549623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58397669907248292406391957 2737390776902263706549623)
                ·
                  refine ⟨4106086165353395559824435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737390776902263706549623 4106086165353395559824435)
                  ·
                    refine ⟨6159129248030093339736653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106086165353395559824435 6159129248030093339736653)
                    ·
                      refine ⟨2309673468011285002401245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6159129248030093339736653 2309673468011285002401245)
                      ·
                        rfl

theorem cell23_4498073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_4498073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498073 prefixEnd_4498073 := by exact prefixLift 4498073
  have htrace : WordTrace (prefixWord ++ tailWord_4498073) baseStart_4498073 baseEnd_4498073 := by
    simpa [prefixWord, tailWord_4498073, baseEnd_4498073] using wordTrace_append hprefix tailTrace_4498073
  have hstable : (prefixWord ++ tailWord_4498073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498073).length < 2 ^ (prefixWord ++ tailWord_4498073).sum := by decide
  have hdescent : baseEnd_4498073 < baseStart_4498073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498089 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_4498089 : Nat := 118140960795 + 4498089 * 2 ^ 59
def prefixEnd_4498089 : Nat := 4983230072969 + 3 ^ 40 * 4498089 * 2
def baseEnd_4498089 : Nat := 769893894567252313267057

theorem tailTrace_4498089 : CollatzResearch.WordTrace tailWord_4498089 prefixEnd_4498089 769893894567252313267057 := by
  unfold tailWord_4498089
  simp only [CollatzResearch.WordTrace]
  refine ⟨164058783801199240285793321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109372522534132826857195547 164058783801199240285793321)
  ·
    refine ⟨123044087850899430214344991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164058783801199240285793321 123044087850899430214344991)
    ·
      refine ⟨184566131776349145321517487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123044087850899430214344991 184566131776349145321517487)
      ·
        refine ⟨276849197664523717982276231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184566131776349145321517487 276849197664523717982276231)
        ·
          refine ⟨415273796496785576973414347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276849197664523717982276231 415273796496785576973414347)
          ·
            refine ⟨622910694745178365460121521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415273796496785576973414347 622910694745178365460121521)
            ·
              refine ⟨467183021058883774095091141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622910694745178365460121521 467183021058883774095091141)
              ·
                refine ⟨87596816448540707642829589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467183021058883774095091141 87596816448540707642829589)
                ·
                  refine ⟨4106100771025345670757637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87596816448540707642829589 4106100771025345670757637)
                  ·
                    refine ⟨769893894567252313267057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106100771025345670757637 769893894567252313267057)
                    ·
                      rfl

theorem cell23_4498089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_4498089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498089 prefixEnd_4498089 := by exact prefixLift 4498089
  have htrace : WordTrace (prefixWord ++ tailWord_4498089) baseStart_4498089 baseEnd_4498089 := by
    simpa [prefixWord, tailWord_4498089, baseEnd_4498089] using wordTrace_append hprefix tailTrace_4498089
  have hstable : (prefixWord ++ tailWord_4498089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498089).length < 2 ^ (prefixWord ++ tailWord_4498089).sum := by decide
  have hdescent : baseEnd_4498089 < baseStart_4498089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498093 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4498093 : Nat := 118140960795 + 4498093 * 2 ^ 59
def prefixEnd_4498093 : Nat := 4983230072969 + 3 ^ 40 * 4498093 * 2
def baseEnd_4498093 : Nat := 769894579208124974717051

theorem tailTrace_4498093 : CollatzResearch.WordTrace tailWord_4498093 prefixEnd_4498093 769894579208124974717051 := by
  unfold tailWord_4498093
  simp only [CollatzResearch.WordTrace]
  refine ⟨164058929693184748968938933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109372619795456499312625955 164058929693184748968938933)
  ·
    refine ⟨15380524658736070215838025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164058929693184748968938933 15380524658736070215838025)
    ·
      refine ⟨11535393494052052661878519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15380524658736070215838025 11535393494052052661878519)
      ·
        refine ⟨17303090241078078992817779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11535393494052052661878519 17303090241078078992817779)
        ·
          refine ⟨25954635361617118489226669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303090241078078992817779 25954635361617118489226669)
          ·
            refine ⟨9732988260606419433460001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25954635361617118489226669 9732988260606419433460001)
            ·
              refine ⟨7299741195454814575095001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9732988260606419433460001 7299741195454814575095001)
              ·
                refine ⟨5474805896591110931321251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7299741195454814575095001 5474805896591110931321251)
                ·
                  refine ⟨8212208844886666396981877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5474805896591110931321251 8212208844886666396981877)
                  ·
                    refine ⟨769894579208124974717051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8212208844886666396981877 769894579208124974717051)
                    ·
                      rfl

theorem cell23_4498093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4498093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498093 prefixEnd_4498093 := by exact prefixLift 4498093
  have htrace : WordTrace (prefixWord ++ tailWord_4498093) baseStart_4498093 baseEnd_4498093 := by
    simpa [prefixWord, tailWord_4498093, baseEnd_4498093] using wordTrace_append hprefix tailTrace_4498093
  have hstable : (prefixWord ++ tailWord_4498093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498093).length < 2 ^ (prefixWord ++ tailWord_4498093).sum := by decide
  have hdescent : baseEnd_4498093 < baseStart_4498093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498116 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4498116 : Nat := 118140960795 + 4498116 * 2 ^ 59
def prefixEnd_4498116 : Nat := 4983230072969 + 3 ^ 40 * 4498116 * 2
def baseEnd_4498116 : Nat := 2309695547679428334163547

theorem tailTrace_4498116 : CollatzResearch.WordTrace tailWord_4498116 prefixEnd_4498116 2309695547679428334163547 := by
  unfold tailWord_4498116
  simp only [CollatzResearch.WordTrace]
  refine ⟨82029884286050711948513101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109373179048067615931350801 82029884286050711948513101)
  ·
    refine ⟨30761206607269016980692413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82029884286050711948513101 30761206607269016980692413)
    ·
      refine ⟨11535452477725881367759655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30761206607269016980692413 11535452477725881367759655)
      ·
        refine ⟨17303178716588822051639483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11535452477725881367759655 17303178716588822051639483)
        ·
          refine ⟨25954768074883233077459225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303178716588822051639483 25954768074883233077459225)
          ·
            refine ⟨19466076056162424808094419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25954768074883233077459225 19466076056162424808094419)
            ·
              refine ⟨29199114084243637212141629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19466076056162424808094419 29199114084243637212141629)
              ·
                refine ⟨10949667781591363954553111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29199114084243637212141629 10949667781591363954553111)
                ·
                  refine ⟨16424501672387045931829667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10949667781591363954553111 16424501672387045931829667)
                  ·
                    refine ⟨24636752508580568897744501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16424501672387045931829667 24636752508580568897744501)
                    ·
                      refine ⟨2309695547679428334163547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24636752508580568897744501 2309695547679428334163547)
                      ·
                        rfl

theorem cell23_4498116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4498116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498116 prefixEnd_4498116 := by exact prefixLift 4498116
  have htrace : WordTrace (prefixWord ++ tailWord_4498116) baseStart_4498116 baseEnd_4498116 := by
    simpa [prefixWord, tailWord_4498116, baseEnd_4498116] using wordTrace_append hprefix tailTrace_4498116
  have hstable : (prefixWord ++ tailWord_4498116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498116).length < 2 ^ (prefixWord ++ tailWord_4498116).sum := by decide
  have hdescent : baseEnd_4498116 < baseStart_4498116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498140 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4498140 : Nat := 118140960795 + 4498140 * 2 ^ 59
def prefixEnd_4498140 : Nat := 4983230072969 + 3 ^ 40 * 4498140 * 2
def baseEnd_4498140 : Nat := 769902623738378746754479

theorem tailTrace_4498140 : CollatzResearch.WordTrace tailWord_4498140 prefixEnd_4498140 769902623738378746754479 := by
  unfold tailWord_4498140
  simp only [CollatzResearch.WordTrace]
  refine ⟨82030321962007237997949937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109373762616009650663933249 82030321962007237997949937)
  ·
    refine ⟨61522741471505428498462453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82030321962007237997949937 61522741471505428498462453)
    ·
      refine ⟨5767757012953633921730855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61522741471505428498462453 5767757012953633921730855)
      ·
        refine ⟨8651635519430450882596283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767757012953633921730855 8651635519430450882596283)
        ·
          refine ⟨12977453279145676323894425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8651635519430450882596283 12977453279145676323894425)
          ·
            refine ⟨9733089959359257242920819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12977453279145676323894425 9733089959359257242920819)
            ·
              refine ⟨14599634939038885864381229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9733089959359257242920819 14599634939038885864381229)
              ·
                refine ⟨5474863102139582199142961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14599634939038885864381229 5474863102139582199142961)
                ·
                  refine ⟨4106147326604686649357221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5474863102139582199142961 4106147326604686649357221)
                  ·
                    refine ⟨769902623738378746754479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106147326604686649357221 769902623738378746754479)
                    ·
                      rfl

theorem cell23_4498140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4498140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498140 prefixEnd_4498140 := by exact prefixLift 4498140
  have htrace : WordTrace (prefixWord ++ tailWord_4498140) baseStart_4498140 baseEnd_4498140 := by
    simpa [prefixWord, tailWord_4498140, baseEnd_4498140] using wordTrace_append hprefix tailTrace_4498140
  have hstable : (prefixWord ++ tailWord_4498140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498140).length < 2 ^ (prefixWord ++ tailWord_4498140).sum := by decide
  have hdescent : baseEnd_4498140 < baseStart_4498140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498164 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4498164 : Nat := 118140960795 + 4498164 * 2 ^ 59
def prefixEnd_4498164 : Nat := 4983230072969 + 3 ^ 40 * 4498164 * 2
def baseEnd_4498164 : Nat := 2309720194750844146363327

theorem tailTrace_4498164 : CollatzResearch.WordTrace tailWord_4498164 prefixEnd_4498164 2309720194750844146363327 := by
  unfold tailWord_4498164
  simp only [CollatzResearch.WordTrace]
  refine ⟨82030759637963764047386773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109374346183951685396515697 82030759637963764047386773)
  ·
    refine ⟨3845191858029551439721255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82030759637963764047386773 3845191858029551439721255)
    ·
      refine ⟨5767787787044327159581883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3845191858029551439721255 5767787787044327159581883)
      ·
        refine ⟨8651681680566490739372825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767787787044327159581883 8651681680566490739372825)
        ·
          refine ⟨6488761260424868054529619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8651681680566490739372825 6488761260424868054529619)
          ·
            refine ⟨9733141890637302081794429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488761260424868054529619 9733141890637302081794429)
            ·
              refine ⟨3649928208988988280672911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9733141890637302081794429 3649928208988988280672911)
              ·
                refine ⟨5474892313483482421009367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649928208988988280672911 5474892313483482421009367)
                ·
                  refine ⟨8212338470225223631514051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5474892313483482421009367 8212338470225223631514051)
                  ·
                    refine ⟨12318507705337835447271077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8212338470225223631514051 12318507705337835447271077)
                    ·
                      refine ⟨2309720194750844146363327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12318507705337835447271077 2309720194750844146363327)
                      ·
                        rfl

theorem cell23_4498164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4498164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498164 prefixEnd_4498164 := by exact prefixLift 4498164
  have htrace : WordTrace (prefixWord ++ tailWord_4498164) baseStart_4498164 baseEnd_4498164 := by
    simpa [prefixWord, tailWord_4498164, baseEnd_4498164] using wordTrace_append hprefix tailTrace_4498164
  have hstable : (prefixWord ++ tailWord_4498164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498164).length < 2 ^ (prefixWord ++ tailWord_4498164).sum := by decide
  have hdescent : baseEnd_4498164 < baseStart_4498164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498169 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_4498169 : Nat := 118140960795 + 4498169 * 2 ^ 59
def prefixEnd_4498169 : Nat := 4983230072969 + 3 ^ 40 * 4498169 * 2
def baseEnd_4498169 : Nat := 2309722762154116626800803

theorem tailTrace_4498169 : CollatzResearch.WordTrace tailWord_4498169 prefixEnd_4498169 2309722762154116626800803 := by
  unfold tailWord_4498169
  simp only [CollatzResearch.WordTrace]
  refine ⟨164061701640909413948705561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109374467760606275965803707 164061701640909413948705561)
  ·
    refine ⟨123046276230682060461529171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164061701640909413948705561 123046276230682060461529171)
    ·
      refine ⟨184569414346023090692293757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123046276230682060461529171 184569414346023090692293757)
      ·
        refine ⟨69213530379758659009610159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184569414346023090692293757 69213530379758659009610159)
        ·
          refine ⟨103820295569637988514415239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69213530379758659009610159 103820295569637988514415239)
          ·
            refine ⟨155730443354456982771622859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103820295569637988514415239 155730443354456982771622859)
            ·
              refine ⟨233595665031685474157434289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155730443354456982771622859 233595665031685474157434289)
              ·
                refine ⟨175196748773764105618075717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233595665031685474157434289 175196748773764105618075717)
                ·
                  refine ⟨32849390395080769803389197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175196748773764105618075717 32849390395080769803389197)
                  ·
                    refine ⟨12318521398155288676270949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32849390395080769803389197 12318521398155288676270949)
                    ·
                      refine ⟨2309722762154116626800803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12318521398155288676270949 2309722762154116626800803)
                      ·
                        rfl

theorem cell23_4498169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_4498169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498169 prefixEnd_4498169 := by exact prefixLift 4498169
  have htrace : WordTrace (prefixWord ++ tailWord_4498169) baseStart_4498169 baseEnd_4498169 := by
    simpa [prefixWord, tailWord_4498169, baseEnd_4498169] using wordTrace_append hprefix tailTrace_4498169
  have hstable : (prefixWord ++ tailWord_4498169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498169).length < 2 ^ (prefixWord ++ tailWord_4498169).sum := by decide
  have hdescent : baseEnd_4498169 < baseStart_4498169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498179 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 2, 6]
def baseStart_4498179 : Nat := 118140960795 + 4498179 * 2 ^ 59
def prefixEnd_4498179 : Nat := 4983230072969 + 3 ^ 40 * 4498179 * 2
def baseEnd_4498179 : Nat := 769909298986887195891919

theorem tailTrace_4498179 : CollatzResearch.WordTrace tailWord_4498179 prefixEnd_4498179 769909298986887195891919 := by
  unfold tailWord_4498179
  simp only [CollatzResearch.WordTrace]
  refine ⟨164062066370873185656569591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109374710913915457104379727 164062066370873185656569591)
  ·
    refine ⟨246093099556309778484854387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164062066370873185656569591 246093099556309778484854387)
    ·
      refine ⟨369139649334464667727281581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246093099556309778484854387 369139649334464667727281581)
      ·
        refine ⟨138427368500424250397730593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369139649334464667727281581 138427368500424250397730593)
        ·
          refine ⟨103820526375318187798297945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138427368500424250397730593 103820526375318187798297945)
          ·
            refine ⟨77865394781488640848723459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103820526375318187798297945 77865394781488640848723459)
            ·
              refine ⟨116798092172232961273085189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77865394781488640848723459 116798092172232961273085189)
              ·
                refine ⟨21899642282293680238703473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116798092172232961273085189 21899642282293680238703473)
                ·
                  refine ⟨16424731711720260179027605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21899642282293680238703473 16424731711720260179027605)
                  ·
                    refine ⟨769909298986887195891919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16424731711720260179027605 769909298986887195891919)
                    ·
                      rfl

theorem cell23_4498179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_4498179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498179 prefixEnd_4498179 := by exact prefixLift 4498179
  have htrace : WordTrace (prefixWord ++ tailWord_4498179) baseStart_4498179 baseEnd_4498179 := by
    simpa [prefixWord, tailWord_4498179, baseEnd_4498179] using wordTrace_append hprefix tailTrace_4498179
  have hstable : (prefixWord ++ tailWord_4498179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498179).length < 2 ^ (prefixWord ++ tailWord_4498179).sum := by decide
  have hdescent : baseEnd_4498179 < baseStart_4498179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498180 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4498180 : Nat := 118140960795 + 4498180 * 2 ^ 59
def prefixEnd_4498180 : Nat := 4983230072969 + 3 ^ 40 * 4498180 * 2
def baseEnd_4498180 : Nat := 2309728410441316083763253

theorem tailTrace_4498180 : CollatzResearch.WordTrace tailWord_4498180 prefixEnd_4498180 2309728410441316083763253 := by
  unfold tailWord_4498180
  simp only [CollatzResearch.WordTrace]
  refine ⟨82031051421934781413677997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109374735229246375218237329 82031051421934781413677997)
  ·
    refine ⟨30761644283225543030129249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82031051421934781413677997 30761644283225543030129249)
    ·
      refine ⟨23071233212419157272596937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30761644283225543030129249 23071233212419157272596937)
      ·
        refine ⟨17303424909314367954447703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23071233212419157272596937 17303424909314367954447703)
        ·
          refine ⟨25955137363971551931671555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303424909314367954447703 25955137363971551931671555)
          ·
            refine ⟨38932706045957327897507333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25955137363971551931671555 38932706045957327897507333)
            ·
              refine ⟨7299882383616998980782625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38932706045957327897507333 7299882383616998980782625)
              ·
                refine ⟨5474911787712749235586969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7299882383616998980782625 5474911787712749235586969)
                ·
                  refine ⟨4106183840784561926690227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5474911787712749235586969 4106183840784561926690227)
                  ·
                    refine ⟨6159275761176842890035341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106183840784561926690227 6159275761176842890035341)
                    ·
                      refine ⟨2309728410441316083763253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6159275761176842890035341 2309728410441316083763253)
                      ·
                        rfl

theorem cell23_4498180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4498180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498180 prefixEnd_4498180 := by exact prefixLift 4498180
  have htrace : WordTrace (prefixWord ++ tailWord_4498180) baseStart_4498180 baseEnd_4498180 := by
    simpa [prefixWord, tailWord_4498180, baseEnd_4498180] using wordTrace_append hprefix tailTrace_4498180
  have hstable : (prefixWord ++ tailWord_4498180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498180).length < 2 ^ (prefixWord ++ tailWord_4498180).sum := by decide
  have hdescent : baseEnd_4498180 < baseStart_4498180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498216 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4498216 : Nat := 118140960795 + 4498216 * 2 ^ 59
def prefixEnd_4498216 : Nat := 4983230072969 + 3 ^ 40 * 4498216 * 2
def baseEnd_4498216 : Nat := 2309746895744877942913087

theorem tailTrace_4498216 : CollatzResearch.WordTrace tailWord_4498216 prefixEnd_4498216 2309746895744877942913087 := by
  unfold tailWord_4498216
  simp only [CollatzResearch.WordTrace]
  refine ⟨82031707935869570487833251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109375610581159427317111001 82031707935869570487833251)
  ·
    refine ⟨123047561903804355731749877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82031707935869570487833251 123047561903804355731749877)
    ·
      refine ⟨11535708928481658349851551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123047561903804355731749877 11535708928481658349851551)
      ·
        refine ⟨17303563392722487524777327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11535708928481658349851551 17303563392722487524777327)
        ·
          refine ⟨25955345089083731287165991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303563392722487524777327 25955345089083731287165991)
          ·
            refine ⟨38933017633625596930748987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25955345089083731287165991 38933017633625596930748987)
            ·
              refine ⟨58399526450438395396123481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38933017633625596930748987 58399526450438395396123481)
              ·
                refine ⟨43799644837828796547092611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58399526450438395396123481 43799644837828796547092611)
                ·
                  refine ⟨65699467256743194820638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43799644837828796547092611 65699467256743194820638917)
                  ·
                    refine ⟨12318650110639349028869797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65699467256743194820638917 12318650110639349028869797)
                    ·
                      refine ⟨2309746895744877942913087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12318650110639349028869797 2309746895744877942913087)
                      ·
                        rfl

theorem cell23_4498216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4498216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498216 prefixEnd_4498216 := by exact prefixLift 4498216
  have htrace : WordTrace (prefixWord ++ tailWord_4498216) baseStart_4498216 baseEnd_4498216 := by
    simpa [prefixWord, tailWord_4498216, baseEnd_4498216] using wordTrace_append hprefix tailTrace_4498216
  have hstable : (prefixWord ++ tailWord_4498216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498216).length < 2 ^ (prefixWord ++ tailWord_4498216).sum := by decide
  have hdescent : baseEnd_4498216 < baseStart_4498216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498237 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4498237 : Nat := 118140960795 + 4498237 * 2 ^ 59
def prefixEnd_4498237 : Nat := 4983230072969 + 3 ^ 40 * 4498237 * 2
def baseEnd_4498237 : Nat := 2309757678838622360750491

theorem tailTrace_4498237 : CollatzResearch.WordTrace tailWord_4498237 prefixEnd_4498237 2309757678838622360750491 := by
  unfold tailWord_4498237
  simp only [CollatzResearch.WordTrace]
  refine ⟨164064181804663061562180965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109376121203108707708120643 164064181804663061562180965)
  ·
    refine ⟨30762034088374324042908931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164064181804663061562180965 30762034088374324042908931)
    ·
      refine ⟨46143051132561486064363397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30762034088374324042908931 46143051132561486064363397)
      ·
        refine ⟨8651822087355278637068137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46143051132561486064363397 8651822087355278637068137)
        ·
          refine ⟨6488866565516458977801103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8651822087355278637068137 6488866565516458977801103)
          ·
            refine ⟨9733299848274688466701655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488866565516458977801103 9733299848274688466701655)
            ·
              refine ⟨14599949772412032700052483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9733299848274688466701655 14599949772412032700052483)
              ·
                refine ⟨21899924658618049050078725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14599949772412032700052483 21899924658618049050078725)
                ·
                  refine ⟨4106235873490884196889761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21899924658618049050078725 4106235873490884196889761)
                  ·
                    refine ⟨3079676905118163147667321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106235873490884196889761 3079676905118163147667321)
                    ·
                      refine ⟨2309757678838622360750491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079676905118163147667321 2309757678838622360750491)
                      ·
                        rfl

theorem cell23_4498237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4498237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498237 prefixEnd_4498237 := by exact prefixLift 4498237
  have htrace : WordTrace (prefixWord ++ tailWord_4498237) baseStart_4498237 baseEnd_4498237 := by
    simpa [prefixWord, tailWord_4498237, baseEnd_4498237] using wordTrace_append hprefix tailTrace_4498237
  have hstable : (prefixWord ++ tailWord_4498237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498237).length < 2 ^ (prefixWord ++ tailWord_4498237).sum := by decide
  have hdescent : baseEnd_4498237 < baseStart_4498237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498293 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4498293 : Nat := 118140960795 + 4498293 * 2 ^ 59
def prefixEnd_4498293 : Nat := 4983230072969 + 3 ^ 40 * 4498293 * 2
def baseEnd_4498293 : Nat := 2309786433755274141650233

theorem tailTrace_4498293 : CollatzResearch.WordTrace tailWord_4498293 prefixEnd_4498293 2309786433755274141650233 := by
  unfold tailWord_4498293
  simp only [CollatzResearch.WordTrace]
  refine ⟨164066224292460183126219533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109377482861640122084146355 164066224292460183126219533)
  ·
    refine ⟨61524834109672568672332325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164066224292460183126219533 61524834109672568672332325)
    ·
      refine ⟨11535906395563606626062311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61524834109672568672332325 11535906395563606626062311)
      ·
        refine ⟨17303859593345409939093467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11535906395563606626062311 17303859593345409939093467)
        ·
          refine ⟨25955789390018114908640201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303859593345409939093467 25955789390018114908640201)
          ·
            refine ⟨19466842042513586181480151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25955789390018114908640201 19466842042513586181480151)
            ·
              refine ⟨29200263063770379272220227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19466842042513586181480151 29200263063770379272220227)
              ·
                refine ⟨43800394595655568908330341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29200263063770379272220227 43800394595655568908330341)
                ·
                  refine ⟨8212573986685419170311939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43800394595655568908330341 8212573986685419170311939)
                  ·
                    refine ⟨12318860980028128755467909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8212573986685419170311939 12318860980028128755467909)
                    ·
                      refine ⟨2309786433755274141650233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12318860980028128755467909 2309786433755274141650233)
                      ·
                        rfl

theorem cell23_4498293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4498293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498293 prefixEnd_4498293 := by exact prefixLift 4498293
  have htrace : WordTrace (prefixWord ++ tailWord_4498293) baseStart_4498293 baseEnd_4498293 := by
    simpa [prefixWord, tailWord_4498293, baseEnd_4498293] using wordTrace_append hprefix tailTrace_4498293
  have hstable : (prefixWord ++ tailWord_4498293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498293).length < 2 ^ (prefixWord ++ tailWord_4498293).sum := by decide
  have hdescent : baseEnd_4498293 < baseStart_4498293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498296 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_4498296 : Nat := 118140960795 + 4498296 * 2 ^ 59
def prefixEnd_4498296 : Nat := 4983230072969 + 3 ^ 40 * 4498296 * 2
def baseEnd_4498296 : Nat := 2309787974197237629912719

theorem tailTrace_4498296 : CollatzResearch.WordTrace tailWord_4498296 prefixEnd_4498296 2309787974197237629912719 := by
  unfold tailWord_4498296
  simp only [CollatzResearch.WordTrace]
  refine ⟨82033166855724657319289371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109377555807632876425719161 82033166855724657319289371)
  ·
    refine ⟨123049750283586985978934057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82033166855724657319289371 123049750283586985978934057)
    ·
      refine ⟨92287312712690239484200543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123049750283586985978934057 92287312712690239484200543)
      ·
        refine ⟨138430969069035359226300815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92287312712690239484200543 138430969069035359226300815)
        ·
          refine ⟨207646453603553038839451223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138430969069035359226300815 207646453603553038839451223)
          ·
            refine ⟨311469680405329558259176835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207646453603553038839451223 311469680405329558259176835)
            ·
              refine ⟨467204520607994337388765253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311469680405329558259176835 467204520607994337388765253)
              ·
                refine ⟨87600847613998938260393485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467204520607994337388765253 87600847613998938260393485)
                ·
                  refine ⟨32850317855249601847647557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87600847613998938260393485 32850317855249601847647557)
                  ·
                    refine ⟨6159434597859300346433917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32850317855249601847647557 6159434597859300346433917)
                    ·
                      refine ⟨2309787974197237629912719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6159434597859300346433917 2309787974197237629912719)
                      ·
                        rfl

theorem cell23_4498296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_4498296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498296 prefixEnd_4498296 := by exact prefixLift 4498296
  have htrace : WordTrace (prefixWord ++ tailWord_4498296) baseStart_4498296 baseEnd_4498296 := by
    simpa [prefixWord, tailWord_4498296, baseEnd_4498296] using wordTrace_append hprefix tailTrace_4498296
  have hstable : (prefixWord ++ tailWord_4498296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498296).length < 2 ^ (prefixWord ++ tailWord_4498296).sum := by decide
  have hdescent : baseEnd_4498296 < baseStart_4498296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498303 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 3, 4]
def baseStart_4498303 : Nat := 118140960795 + 4498303 * 2 ^ 59
def prefixEnd_4498303 : Nat := 4983230072969 + 3 ^ 40 * 4498303 * 2
def baseEnd_4498303 : Nat := 769930522853939700841729

theorem tailTrace_4498303 : CollatzResearch.WordTrace tailWord_4498303 prefixEnd_4498303 769930522853939700841729 := by
  unfold tailWord_4498303
  simp only [CollatzResearch.WordTrace]
  refine ⟨164066589022423954834083563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109377726014949303222722375 164066589022423954834083563)
  ·
    refine ⟨246099883533635932251125345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164066589022423954834083563 246099883533635932251125345)
    ·
      refine ⟨184574912650226949188344009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246099883533635932251125345 184574912650226949188344009)
      ·
        refine ⟨138431184487670211891258007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184574912650226949188344009 138431184487670211891258007)
        ·
          refine ⟨207646776731505317836887011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138431184487670211891258007 207646776731505317836887011)
          ·
            refine ⟨311470165097257976755330517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207646776731505317836887011 311470165097257976755330517)
            ·
              refine ⟨7300081994466983830203059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 311470165097257976755330517 7300081994466983830203059)
              ·
                refine ⟨10950122991700475745304589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7300081994466983830203059 10950122991700475745304589)
                ·
                  refine ⟨4106296121887678404489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10950122991700475745304589 4106296121887678404489221)
                  ·
                    refine ⟨769930522853939700841729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106296121887678404489221 769930522853939700841729)
                    ·
                      rfl

theorem cell23_4498303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_4498303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498303 prefixEnd_4498303 := by exact prefixLift 4498303
  have htrace : WordTrace (prefixWord ++ tailWord_4498303) baseStart_4498303 baseEnd_4498303 := by
    simpa [prefixWord, tailWord_4498303, baseEnd_4498303] using wordTrace_append hprefix tailTrace_4498303
  have hstable : (prefixWord ++ tailWord_4498303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498303).length < 2 ^ (prefixWord ++ tailWord_4498303).sum := by decide
  have hdescent : baseEnd_4498303 < baseStart_4498303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498383 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_4498383 : Nat := 118140960795 + 4498383 * 2 ^ 59
def prefixEnd_4498383 : Nat := 4983230072969 + 3 ^ 40 * 4498383 * 2
def baseEnd_4498383 : Nat := 2309832647014178789524819

theorem tailTrace_4498383 : CollatzResearch.WordTrace tailWord_4498383 prefixEnd_4498383 2309832647014178789524819 := by
  unfold tailWord_4498383
  simp only [CollatzResearch.WordTrace]
  refine ⟨164069506862134128496995803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109379671241422752331330535 164069506862134128496995803)
  ·
    refine ⟨246104260293201192745493705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164069506862134128496995803 246104260293201192745493705)
    ·
      refine ⟨184578195219900894559120279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246104260293201192745493705 184578195219900894559120279)
      ·
        refine ⟨276867292829851341838680419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184578195219900894559120279 276867292829851341838680419)
        ·
          refine ⟨415300939244777012758020629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276867292829851341838680419 415300939244777012758020629)
          ·
            refine ⟨19467231527098922473032217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 415300939244777012758020629 19467231527098922473032217)
            ·
              refine ⟨14600423645324191854774163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19467231527098922473032217 14600423645324191854774163)
              ·
                refine ⟨21900635467986287782161245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14600423645324191854774163 21900635467986287782161245)
                ·
                  refine ⟨8212738300494857918310467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21900635467986287782161245 8212738300494857918310467)
                  ·
                    refine ⟨12319107450742286877465701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8212738300494857918310467 12319107450742286877465701)
                    ·
                      refine ⟨2309832647014178789524819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12319107450742286877465701 2309832647014178789524819)
                      ·
                        rfl

theorem cell23_4498383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_4498383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498383 prefixEnd_4498383 := by exact prefixLift 4498383
  have htrace : WordTrace (prefixWord ++ tailWord_4498383) baseStart_4498383 baseEnd_4498383 := by
    simpa [prefixWord, tailWord_4498383, baseEnd_4498383] using wordTrace_append hprefix tailTrace_4498383
  have hstable : (prefixWord ++ tailWord_4498383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498383).length < 2 ^ (prefixWord ++ tailWord_4498383).sum := by decide
  have hdescent : baseEnd_4498383 < baseStart_4498383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498393 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_4498393 : Nat := 118140960795 + 4498393 * 2 ^ 59
def prefixEnd_4498393 : Nat := 4983230072969 + 3 ^ 40 * 4498393 * 2
def baseEnd_4498393 : Nat := 769945927273574583466591

theorem tailTrace_4498393 : CollatzResearch.WordTrace tailWord_4498393 prefixEnd_4498393 769945927273574583466591 := by
  unfold tailWord_4498393
  simp only [CollatzResearch.WordTrace]
  refine ⟨164069871592097900204859833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109379914394731933469906555 164069871592097900204859833)
  ·
    refine ⟨123052403694073425153644875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164069871592097900204859833 123052403694073425153644875)
    ·
      refine ⟨184578605541110137730467313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123052403694073425153644875 184578605541110137730467313)
      ·
        refine ⟨138433954155832603297850485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184578605541110137730467313 138433954155832603297850485)
        ·
          refine ⟨12978183202109306559173483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138433954155832603297850485 12978183202109306559173483)
          ·
            refine ⟨19467274803163959838760225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12978183202109306559173483 19467274803163959838760225)
            ·
              refine ⟨14600456102372969879070169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19467274803163959838760225 14600456102372969879070169)
              ·
                refine ⟨10950342076779727409302627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14600456102372969879070169 10950342076779727409302627)
                ·
                  refine ⟨16425513115169591113953941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10950342076779727409302627 16425513115169591113953941)
                  ·
                    refine ⟨769945927273574583466591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16425513115169591113953941 769945927273574583466591)
                    ·
                      rfl

theorem cell23_4498393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_4498393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498393 prefixEnd_4498393 := by exact prefixLift 4498393
  have htrace : WordTrace (prefixWord ++ tailWord_4498393) baseStart_4498393 baseEnd_4498393 := by
    simpa [prefixWord, tailWord_4498393, baseEnd_4498393] using wordTrace_append hprefix tailTrace_4498393
  have hstable : (prefixWord ++ tailWord_4498393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498393).length < 2 ^ (prefixWord ++ tailWord_4498393).sum := by decide
  have hdescent : baseEnd_4498393 < baseStart_4498393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498394 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3]
def baseStart_4498394 : Nat := 118140960795 + 4498394 * 2 ^ 59
def prefixEnd_4498394 : Nat := 4983230072969 + 3 ^ 40 * 4498394 * 2
def baseEnd_4498394 : Nat := 2309838295301378246487269

theorem tailTrace_4498394 : CollatzResearch.WordTrace tailWord_4498394 prefixEnd_4498394 2309838295301378246487269 := by
  unfold tailWord_4498394
  simp only [CollatzResearch.WordTrace]
  refine ⟨41017477016273569343911559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109379938710062851583764157 41017477016273569343911559)
  ·
    refine ⟨61526215524410354015867339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41017477016273569343911559 61526215524410354015867339)
    ·
      refine ⟨92289323286615531023801009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61526215524410354015867339 92289323286615531023801009)
      ·
        refine ⟨69216992464961648267850757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92289323286615531023801009 69216992464961648267850757)
        ·
          refine ⟨12978186087180309050222017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69216992464961648267850757 12978186087180309050222017)
          ·
            refine ⟨9733639565385231787666513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12978186087180309050222017 9733639565385231787666513)
            ·
              refine ⟨7300229674038923840749885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9733639565385231787666513 7300229674038923840749885)
              ·
                refine ⟨2737586127764596440281207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7300229674038923840749885 2737586127764596440281207)
                ·
                  refine ⟨4106379191646894660421811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737586127764596440281207 4106379191646894660421811)
                  ·
                    refine ⟨6159568787470341990632717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106379191646894660421811 6159568787470341990632717)
                    ·
                      refine ⟨2309838295301378246487269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6159568787470341990632717 2309838295301378246487269)
                      ·
                        rfl

theorem cell23_4498394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_4498394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498394 prefixEnd_4498394 := by exact prefixLift 4498394
  have htrace : WordTrace (prefixWord ++ tailWord_4498394) baseStart_4498394 baseEnd_4498394 := by
    simpa [prefixWord, tailWord_4498394, baseEnd_4498394] using wordTrace_append hprefix tailTrace_4498394
  have hstable : (prefixWord ++ tailWord_4498394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498394).length < 2 ^ (prefixWord ++ tailWord_4498394).sum := by decide
  have hdescent : baseEnd_4498394 < baseStart_4498394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498397 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4498397 : Nat := 118140960795 + 4498397 * 2 ^ 59
def prefixEnd_4498397 : Nat := 4983230072969 + 3 ^ 40 * 4498397 * 2
def baseEnd_4498397 : Nat := 769946611914447244916585

theorem tailTrace_4498397 : CollatzResearch.WordTrace tailWord_4498397 prefixEnd_4498397 769946611914447244916585 := by
  unfold tailWord_4498397
  simp only [CollatzResearch.WordTrace]
  refine ⟨164070017484083408888005445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109380011656055605925336963 164070017484083408888005445)
  ·
    refine ⟨30763128278265639166501021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164070017484083408888005445 30763128278265639166501021)
    ·
      refine ⟨11536173104349614687437883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30763128278265639166501021 11536173104349614687437883)
      ·
        refine ⟨17304259656524422031156825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11536173104349614687437883 17304259656524422031156825)
        ·
          refine ⟨12978194742393316523367619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17304259656524422031156825 12978194742393316523367619)
          ·
            refine ⟨19467292113589974785051429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12978194742393316523367619 19467292113589974785051429)
            ·
              refine ⟨3650117271298120272197143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19467292113589974785051429 3650117271298120272197143)
              ·
                refine ⟨5475175906947180408295715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650117271298120272197143 5475175906947180408295715)
                ·
                  refine ⟨8212763860420770612443573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475175906947180408295715 8212763860420770612443573)
                  ·
                    refine ⟨769946611914447244916585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8212763860420770612443573 769946611914447244916585)
                    ·
                      rfl

theorem cell23_4498397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4498397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498397 prefixEnd_4498397 := by exact prefixLift 4498397
  have htrace : WordTrace (prefixWord ++ tailWord_4498397) baseStart_4498397 baseEnd_4498397 := by
    simpa [prefixWord, tailWord_4498397, baseEnd_4498397] using wordTrace_append hprefix tailTrace_4498397
  have hstable : (prefixWord ++ tailWord_4498397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498397).length < 2 ^ (prefixWord ++ tailWord_4498397).sum := by decide
  have hdescent : baseEnd_4498397 < baseStart_4498397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498403 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4498403 : Nat := 118140960795 + 4498403 * 2 ^ 59
def prefixEnd_4498403 : Nat := 4983230072969 + 3 ^ 40 * 4498403 * 2
def baseEnd_4498403 : Nat := 2309842916627268711274727

theorem tailTrace_4498403 : CollatzResearch.WordTrace tailWord_4498403 prefixEnd_4498403 2309842916627268711274727 := by
  unfold tailWord_4498403
  simp only [CollatzResearch.WordTrace]
  refine ⟨164070236322061671912723863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109380157548041114608482575 164070236322061671912723863)
  ·
    refine ⟨246105354483092507869085795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164070236322061671912723863 246105354483092507869085795)
    ·
      refine ⟨369158031724638761803628693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246105354483092507869085795 369158031724638761803628693)
      ·
        refine ⟨17304282737092441959545095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 369158031724638761803628693 17304282737092441959545095)
        ·
          refine ⟨25956424105638662939317643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17304282737092441959545095 25956424105638662939317643)
          ·
            refine ⟨38934636158457994408976465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25956424105638662939317643 38934636158457994408976465)
            ·
              refine ⟨29200977118843495806732349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38934636158457994408976465 29200977118843495806732349)
              ·
                refine ⟨10950366419566310927524631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29200977118843495806732349 10950366419566310927524631)
                ·
                  refine ⟨16425549629349466391286947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10950366419566310927524631 16425549629349466391286947)
                  ·
                    refine ⟨24638324444024199586930421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16425549629349466391286947 24638324444024199586930421)
                    ·
                      refine ⟨2309842916627268711274727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24638324444024199586930421 2309842916627268711274727)
                      ·
                        rfl

theorem cell23_4498403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4498403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498403 prefixEnd_4498403 := by exact prefixLift 4498403
  have htrace : WordTrace (prefixWord ++ tailWord_4498403) baseStart_4498403 baseEnd_4498403 := by
    simpa [prefixWord, tailWord_4498403, baseEnd_4498403] using wordTrace_append hprefix tailTrace_4498403
  have hstable : (prefixWord ++ tailWord_4498403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498403).length < 2 ^ (prefixWord ++ tailWord_4498403).sum := by decide
  have hdescent : baseEnd_4498403 < baseStart_4498403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498410 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_4498410 : Nat := 118140960795 + 4498410 * 2 ^ 59
def prefixEnd_4498410 : Nat := 4983230072969 + 3 ^ 40 * 4498410 * 2
def baseEnd_4498410 : Nat := 769948836997283394629065

theorem tailTrace_4498410 : CollatzResearch.WordTrace tailWord_4498410 prefixEnd_4498410 769948836997283394629065 := by
  unfold tailWord_4498410
  simp only [CollatzResearch.WordTrace]
  refine ⟨41017622908259078027057171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109380327755357541405485789 41017622908259078027057171)
  ·
    refine ⟨61526434362388617040585757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41017622908259078027057171 61526434362388617040585757)
    ·
      refine ⟨23072412885895731390219659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61526434362388617040585757 23072412885895731390219659)
      ·
        refine ⟨34608619328843597085329489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23072412885895731390219659 34608619328843597085329489)
        ·
          refine ⟨25956464496632697813997117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34608619328843597085329489 25956464496632697813997117)
          ·
            refine ⟨9733674186237261680248919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25956464496632697813997117 9733674186237261680248919)
            ·
              refine ⟨14600511279355892520373379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9733674186237261680248919 14600511279355892520373379)
              ·
                refine ⟨21900766919033838780560069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14600511279355892520373379 21900766919033838780560069)
                ·
                  refine ⟨4106393797318844771355013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21900766919033838780560069 4106393797318844771355013)
                  ·
                    refine ⟨769948836997283394629065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106393797318844771355013 769948836997283394629065)
                    ·
                      rfl

theorem cell23_4498410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_4498410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498410 prefixEnd_4498410 := by exact prefixLift 4498410
  have htrace : WordTrace (prefixWord ++ tailWord_4498410) baseStart_4498410 baseEnd_4498410 := by
    simpa [prefixWord, tailWord_4498410, baseEnd_4498410] using wordTrace_append hprefix tailTrace_4498410
  have hstable : (prefixWord ++ tailWord_4498410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498410).length < 2 ^ (prefixWord ++ tailWord_4498410).sum := by decide
  have hdescent : baseEnd_4498410 < baseStart_4498410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_4498416 : Nat := 118140960795 + 4498416 * 2 ^ 59
def prefixEnd_4498416 : Nat := 4983230072969 + 3 ^ 40 * 4498416 * 2
def baseEnd_4498416 : Nat := 2309849591875777160412167

theorem tailTrace_4498416 : CollatzResearch.WordTrace tailWord_4498416 prefixEnd_4498416 2309849591875777160412167 := by
  unfold tailWord_4498416
  simp only [CollatzResearch.WordTrace]
  refine ⟨82035355235507287566473551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109380473647343050088631401 82035355235507287566473551)
  ·
    refine ⟨123053032853260931349710327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82035355235507287566473551 123053032853260931349710327)
    ·
      refine ⟨184579549279891397024565491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123053032853260931349710327 184579549279891397024565491)
      ·
        refine ⟨276869323919837095536848237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184579549279891397024565491 276869323919837095536848237)
        ·
          refine ⟨103825996469938910826318089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276869323919837095536848237 103825996469938910826318089)
          ·
            refine ⟨77869497352454183119738567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103825996469938910826318089 77869497352454183119738567)
            ·
              refine ⟨116804246028681274679607851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77869497352454183119738567 116804246028681274679607851)
              ·
                refine ⟨175206369043021912019411777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116804246028681274679607851 175206369043021912019411777)
                ·
                  refine ⟨131404776782266434014558833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175206369043021912019411777 131404776782266434014558833)
                  ·
                    refine ⟨98553582586699825510919125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131404776782266434014558833 98553582586699825510919125)
                    ·
                      refine ⟨2309849591875777160412167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98553582586699825510919125 2309849591875777160412167)
                      ·
                        rfl

theorem cell23_4498416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_4498416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498416 prefixEnd_4498416 := by exact prefixLift 4498416
  have htrace : WordTrace (prefixWord ++ tailWord_4498416) baseStart_4498416 baseEnd_4498416 := by
    simpa [prefixWord, tailWord_4498416, baseEnd_4498416] using wordTrace_append hprefix tailTrace_4498416
  have hstable : (prefixWord ++ tailWord_4498416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498416).length < 2 ^ (prefixWord ++ tailWord_4498416).sum := by decide
  have hdescent : baseEnd_4498416 < baseStart_4498416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498417 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_4498417 : Nat := 118140960795 + 4498417 * 2 ^ 59
def prefixEnd_4498417 : Nat := 4983230072969 + 3 ^ 40 * 4498417 * 2
def baseEnd_4498417 : Nat := 2309850105356431656499663

theorem tailTrace_4498417 : CollatzResearch.WordTrace tailWord_4498417 prefixEnd_4498417 2309850105356431656499663 := by
  unfold tailWord_4498417
  simp only [CollatzResearch.WordTrace]
  refine ⟨164070746944010952303733505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109380497962673968202489003 164070746944010952303733505)
  ·
    refine ⟨123053060208008214227800129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164070746944010952303733505 123053060208008214227800129)
    ·
      refine ⟨92289795156006160670850097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123053060208008214227800129 92289795156006160670850097)
      ·
        refine ⟨69217346367004620503137573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92289795156006160670850097 69217346367004620503137573)
        ·
          refine ⟨12978252443813366344338295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69217346367004620503137573 12978252443813366344338295)
          ·
            refine ⟨19467378665720049516507443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12978252443813366344338295 19467378665720049516507443)
            ·
              refine ⟨29201067998580074274761165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19467378665720049516507443 29201067998580074274761165)
              ·
                refine ⟨10950400499467527853035437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29201067998580074274761165 10950400499467527853035437)
                ·
                  refine ⟨4106400187300322944888289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10950400499467527853035437 4106400187300322944888289)
                  ·
                    refine ⟨3079800140475242208666217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106400187300322944888289 3079800140475242208666217)
                    ·
                      refine ⟨2309850105356431656499663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079800140475242208666217 2309850105356431656499663)
                      ·
                        rfl

theorem cell23_4498417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_4498417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498417 prefixEnd_4498417 := by exact prefixLift 4498417
  have htrace : WordTrace (prefixWord ++ tailWord_4498417) baseStart_4498417 baseEnd_4498417 := by
    simpa [prefixWord, tailWord_4498417, baseEnd_4498417] using wordTrace_append hprefix tailTrace_4498417
  have hstable : (prefixWord ++ tailWord_4498417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498417).length < 2 ^ (prefixWord ++ tailWord_4498417).sum := by decide
  have hdescent : baseEnd_4498417 < baseStart_4498417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498440 : List Nat := [2, 1, 3, 2, 1, 5, 2, 7]
def baseStart_4498440 : Nat := 118140960795 + 4498440 * 2 ^ 59
def prefixEnd_4498440 : Nat := 4983230072969 + 3 ^ 40 * 4498440 * 2
def baseEnd_4498440 : Nat := 85550441311536483944891

theorem tailTrace_4498440 : CollatzResearch.WordTrace tailWord_4498440 prefixEnd_4498440 85550441311536483944891 := by
  unfold tailWord_4498440
  simp only [CollatzResearch.WordTrace]
  refine ⟨82035792911463813615910387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109381057215285084821213849 82035792911463813615910387)
  ·
    refine ⟨123053689367195720423865581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82035792911463813615910387 123053689367195720423865581)
    ·
      refine ⟨46145133512698395158949593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123053689367195720423865581 46145133512698395158949593)
      ·
        refine ⟨34608850134523796369212195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46145133512698395158949593 34608850134523796369212195)
        ·
          refine ⟨51913275201785694553818293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34608850134523796369212195 51913275201785694553818293)
          ·
            refine ⟨4866869550167408864420465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51913275201785694553818293 4866869550167408864420465)
            ·
              refine ⟨3650152162625556648315349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4866869550167408864420465 3650152162625556648315349)
              ·
                refine ⟨85550441311536483944891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3650152162625556648315349 85550441311536483944891)
                ·
                  rfl

theorem cell23_4498440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 7].length) (baseStart_4498440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498440 prefixEnd_4498440 := by exact prefixLift 4498440
  have htrace : WordTrace (prefixWord ++ tailWord_4498440) baseStart_4498440 baseEnd_4498440 := by
    simpa [prefixWord, tailWord_4498440, baseEnd_4498440] using wordTrace_append hprefix tailTrace_4498440
  have hstable : (prefixWord ++ tailWord_4498440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498440).length < 2 ^ (prefixWord ++ tailWord_4498440).sum := by decide
  have hdescent : baseEnd_4498440 < baseStart_4498440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498468 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4498468 : Nat := 118140960795 + 4498468 * 2 ^ 59
def prefixEnd_4498468 : Nat := 4983230072969 + 3 ^ 40 * 4498468 * 2
def baseEnd_4498468 : Nat := 2309876292869810956961929

theorem tailTrace_4498468 : CollatzResearch.WordTrace tailWord_4498468 prefixEnd_4498468 2309876292869810956961929 := by
  unfold tailWord_4498468
  simp only [CollatzResearch.WordTrace]
  refine ⟨82036303533413094006920029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109381738044550792009226705 82036303533413094006920029)
  ·
    refine ⟨30763613825029910252595011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82036303533413094006920029 30763613825029910252595011)
    ·
      refine ⟨46145420737544865378892517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30763613825029910252595011 46145420737544865378892517)
      ·
        refine ⟨8652266388289662258542347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46145420737544865378892517 8652266388289662258542347)
        ·
          refine ⟨12978399582434493387813521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8652266388289662258542347 12978399582434493387813521)
          ·
            refine ⟨9733799686825870040860141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12978399582434493387813521 9733799686825870040860141)
            ·
              refine ⟨3650174882559701265322553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9733799686825870040860141 3650174882559701265322553)
              ·
                refine ⟨2737631161919775948991915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3650174882559701265322553 2737631161919775948991915)
                ·
                  refine ⟨4106446742879663923487873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737631161919775948991915 4106446742879663923487873)
                  ·
                    refine ⟨3079835057159747942615905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106446742879663923487873 3079835057159747942615905)
                    ·
                      refine ⟨2309876292869810956961929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079835057159747942615905 2309876292869810956961929)
                      ·
                        rfl

theorem cell23_4498468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4498468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498468 prefixEnd_4498468 := by exact prefixLift 4498468
  have htrace : WordTrace (prefixWord ++ tailWord_4498468) baseStart_4498468 baseEnd_4498468 := by
    simpa [prefixWord, tailWord_4498468, baseEnd_4498468] using wordTrace_append hprefix tailTrace_4498468
  have hstable : (prefixWord ++ tailWord_4498468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498468).length < 2 ^ (prefixWord ++ tailWord_4498468).sum := by decide
  have hdescent : baseEnd_4498468 < baseStart_4498468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498494 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4498494 : Nat := 118140960795 + 4498494 * 2 ^ 59
def prefixEnd_4498494 : Nat := 4983230072969 + 3 ^ 40 * 4498494 * 2
def baseEnd_4498494 : Nat := 2309889643366827855236809

theorem tailTrace_4498494 : CollatzResearch.WordTrace tailWord_4498494 prefixEnd_4498494 2309889643366827855236809 := by
  unfold tailWord_4498494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20509194420591499306785817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109382370243154662969524357 20509194420591499306785817)
  ·
    refine ⟨15381895815443624480089363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20509194420591499306785817 15381895815443624480089363)
    ·
      refine ⟨23072843723165436720134045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15381895815443624480089363 23072843723165436720134045)
      ·
        refine ⟨8652316396187038770050267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23072843723165436720134045 8652316396187038770050267)
        ·
          refine ⟨12978474594280558155075401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8652316396187038770050267 12978474594280558155075401)
          ·
            refine ⟨9733855945710418616306551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12978474594280558155075401 9733855945710418616306551)
            ·
              refine ⟨14600783918565627924459827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9733855945710418616306551 14600783918565627924459827)
              ·
                refine ⟨21901175877848441886689741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14600783918565627924459827 21901175877848441886689741)
                ·
                  refine ⟨8212940954193165707508653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21901175877848441886689741 8212940954193165707508653)
                  ·
                    refine ⟨3079852857822437140315745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8212940954193165707508653 3079852857822437140315745)
                    ·
                      refine ⟨2309889643366827855236809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079852857822437140315745 2309889643366827855236809)
                      ·
                        rfl

theorem cell23_4498494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4498494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498494 prefixEnd_4498494 := by exact prefixLift 4498494
  have htrace : WordTrace (prefixWord ++ tailWord_4498494) baseStart_4498494 baseEnd_4498494 := by
    simpa [prefixWord, tailWord_4498494, baseEnd_4498494] using wordTrace_append hprefix tailTrace_4498494
  have hstable : (prefixWord ++ tailWord_4498494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498494).length < 2 ^ (prefixWord ++ tailWord_4498494).sum := by decide
  have hdescent : baseEnd_4498494 < baseStart_4498494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498518 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4498518 : Nat := 118140960795 + 4498518 * 2 ^ 59
def prefixEnd_4498518 : Nat := 4983230072969 + 3 ^ 40 * 4498518 * 2
def baseEnd_4498518 : Nat := 2309901966902535761336699

theorem tailTrace_4498518 : CollatzResearch.WordTrace tailWord_4498518 prefixEnd_4498518 2309901966902535761336699 := by
  unfold tailWord_4498518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10254651919790315409572513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109382953811096697702106805 10254651919790315409572513)
  ·
    refine ⟨7690988939842736557179385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10254651919790315409572513 7690988939842736557179385)
    ·
      refine ⟨5768241704882052417884539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7690988939842736557179385 5768241704882052417884539)
      ·
        refine ⟨8652362557323078626826809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5768241704882052417884539 8652362557323078626826809)
        ·
          refine ⟨6489271917992308970120107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8652362557323078626826809 6489271917992308970120107)
          ·
            refine ⟨9733907876988463455180161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6489271917992308970120107 9733907876988463455180161)
            ·
              refine ⟨7300430907741347591385121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9733907876988463455180161 7300430907741347591385121)
              ·
                refine ⟨5475323180806010693538841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7300430907741347591385121 5475323180806010693538841)
                ·
                  refine ⟨4106492385604508020154131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475323180806010693538841 4106492385604508020154131)
                  ·
                    refine ⟨6159738578406762030231197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106492385604508020154131 6159738578406762030231197)
                    ·
                      refine ⟨2309901966902535761336699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6159738578406762030231197 2309901966902535761336699)
                      ·
                        rfl

theorem cell23_4498518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4498518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498518 prefixEnd_4498518 := by exact prefixLift 4498518
  have htrace : WordTrace (prefixWord ++ tailWord_4498518) baseStart_4498518 baseEnd_4498518 := by
    simpa [prefixWord, tailWord_4498518, baseEnd_4498518] using wordTrace_append hprefix tailTrace_4498518
  have hstable : (prefixWord ++ tailWord_4498518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498518).length < 2 ^ (prefixWord ++ tailWord_4498518).sum := by decide
  have hdescent : baseEnd_4498518 < baseStart_4498518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498540 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_4498540 : Nat := 118140960795 + 4498540 * 2 ^ 59
def prefixEnd_4498540 : Nat := 4983230072969 + 3 ^ 40 * 4498540 * 2
def baseEnd_4498540 : Nat := 2309913263476934675261597

theorem tailTrace_4498540 : CollatzResearch.WordTrace tailWord_4498540 prefixEnd_4498540 2309913263476934675261597 := by
  unfold tailWord_4498540
  simp only [CollatzResearch.WordTrace]
  refine ⟨82037616561282672155230537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109383488748376896206974049 82037616561282672155230537)
  ·
    refine ⟨61528212420962004116422903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82037616561282672155230537 61528212420962004116422903)
    ·
      refine ⟨92292318631443006174634355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61528212420962004116422903 92292318631443006174634355)
      ·
        refine ⟨138438477947164509261951533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92292318631443006174634355 138438477947164509261951533)
        ·
          refine ⟨51914429230186690973231825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138438477947164509261951533 51914429230186690973231825)
          ·
            refine ⟨38935821922640018229923869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51914429230186690973231825 38935821922640018229923869)
            ·
              refine ⟨14600933220990006836221451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38935821922640018229923869 14600933220990006836221451)
              ·
                refine ⟨21901399831485010254332177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14600933220990006836221451 21901399831485010254332177)
                ·
                  refine ⟨16426049873613757690749133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21901399831485010254332177 16426049873613757690749133)
                  ·
                    refine ⟨6159768702605159134030925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16426049873613757690749133 6159768702605159134030925)
                    ·
                      refine ⟨2309913263476934675261597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6159768702605159134030925 2309913263476934675261597)
                      ·
                        rfl

theorem cell23_4498540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_4498540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498540 prefixEnd_4498540 := by exact prefixLift 4498540
  have htrace : WordTrace (prefixWord ++ tailWord_4498540) baseStart_4498540 baseEnd_4498540 := by
    simpa [prefixWord, tailWord_4498540, baseEnd_4498540] using wordTrace_append hprefix tailTrace_4498540
  have hstable : (prefixWord ++ tailWord_4498540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498540).length < 2 ^ (prefixWord ++ tailWord_4498540).sum := by decide
  have hdescent : baseEnd_4498540 < baseStart_4498540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498543 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 7]
def baseStart_4498543 : Nat := 118140960795 + 4498543 * 2 ^ 59
def prefixEnd_4498543 : Nat := 4983230072969 + 3 ^ 40 * 4498543 * 2
def baseEnd_4498543 : Nat := 769971601306299387841361

theorem tailTrace_4498543 : CollatzResearch.WordTrace tailWord_4498543 prefixEnd_4498543 769971601306299387841361 := by
  unfold tailWord_4498543
  simp only [CollatzResearch.WordTrace]
  refine ⟨164075342541554475822820283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109383561694369650548546855 164075342541554475822820283)
  ·
    refine ⟨246113013812331713734230425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164075342541554475822820283 246113013812331713734230425)
    ·
      refine ⟨184584760359248785300672819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246113013812331713734230425 184584760359248785300672819)
      ·
        refine ⟨276877140538873177951009229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184584760359248785300672819 276877140538873177951009229)
        ·
          refine ⟨103828927702077441731628461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276877140538873177951009229 103828927702077441731628461)
          ·
            refine ⟨38935847888279040649360673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103828927702077441731628461 38935847888279040649360673)
            ·
              refine ⟨29201885916209280487020505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38935847888279040649360673 29201885916209280487020505)
              ·
                refine ⟨21901414437156960365265379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29201885916209280487020505 21901414437156960365265379)
                ·
                  refine ⟨32852121655735440547898069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21901414437156960365265379 32852121655735440547898069)
                  ·
                    refine ⟨769971601306299387841361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32852121655735440547898069 769971601306299387841361)
                    ·
                      rfl

theorem cell23_4498543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_4498543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498543 prefixEnd_4498543 := by exact prefixLift 4498543
  have htrace : WordTrace (prefixWord ++ tailWord_4498543) baseStart_4498543 baseEnd_4498543 := by
    simpa [prefixWord, tailWord_4498543, baseEnd_4498543] using wordTrace_append hprefix tailTrace_4498543
  have hstable : (prefixWord ++ tailWord_4498543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498543).length < 2 ^ (prefixWord ++ tailWord_4498543).sum := by decide
  have hdescent : baseEnd_4498543 < baseStart_4498543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498560 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_4498560 : Nat := 118140960795 + 4498560 * 2 ^ 59
def prefixEnd_4498560 : Nat := 4983230072969 + 3 ^ 40 * 4498560 * 2
def baseEnd_4498560 : Nat := 769974511030008199003835

theorem tailTrace_4498560 : CollatzResearch.WordTrace tailWord_4498560 prefixEnd_4498560 769974511030008199003835 := by
  unfold tailWord_4498560
  simp only [CollatzResearch.WordTrace]
  refine ⟨82037981291246443863094567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109383975054995258484126089 82037981291246443863094567)
  ·
    refine ⟨123056971936869665794641851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82037981291246443863094567 123056971936869665794641851)
    ·
      refine ⟨184585457905304498691962777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123056971936869665794641851 184585457905304498691962777)
      ·
        refine ⟨138439093428978374018972083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184585457905304498691962777 138439093428978374018972083)
        ·
          refine ⟨207658640143467561028458125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138439093428978374018972083 207658640143467561028458125)
          ·
            refine ⟨77871990053800335385671797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207658640143467561028458125 77871990053800335385671797)
            ·
              refine ⟨7300499067543781442406731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77871990053800335385671797 7300499067543781442406731)
              ·
                refine ⟨10950748601315672163610097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7300499067543781442406731 10950748601315672163610097)
                ·
                  refine ⟨8213061450986754122707573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10950748601315672163610097 8213061450986754122707573)
                  ·
                    refine ⟨769974511030008199003835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8213061450986754122707573 769974511030008199003835)
                    ·
                      rfl

theorem cell23_4498560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_4498560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498560 prefixEnd_4498560 := by exact prefixLift 4498560
  have htrace : WordTrace (prefixWord ++ tailWord_4498560) baseStart_4498560 baseEnd_4498560 := by
    simpa [prefixWord, tailWord_4498560, baseEnd_4498560] using wordTrace_append hprefix tailTrace_4498560
  have hstable : (prefixWord ++ tailWord_4498560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498560).length < 2 ^ (prefixWord ++ tailWord_4498560).sum := by decide
  have hdescent : baseEnd_4498560 < baseStart_4498560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498597 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_4498597 : Nat := 118140960795 + 4498597 * 2 ^ 59
def prefixEnd_4498597 : Nat := 4983230072969 + 3 ^ 40 * 4498597 * 2
def baseEnd_4498597 : Nat := 2309942531874240952248835

theorem tailTrace_4498597 : CollatzResearch.WordTrace tailWord_4498597 prefixEnd_4498597 2309942531874240952248835 := by
  unfold tailWord_4498597
  simp only [CollatzResearch.WordTrace]
  refine ⟨164077312083358843045286045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109384874722239228696857363 164077312083358843045286045)
  ·
    refine ⟨61528992031259566141982267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164077312083358843045286045 61528992031259566141982267)
    ·
      refine ⟨92293488046889349212973401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61528992031259566141982267 92293488046889349212973401)
      ·
        refine ⟨69220116035167011909730051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92293488046889349212973401 69220116035167011909730051)
        ·
          refine ⟨103830174052750517864595077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69220116035167011909730051 103830174052750517864595077)
          ·
            refine ⟨19468157634890722099611577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103830174052750517864595077 19468157634890722099611577)
            ·
              refine ⟨14601118226168041574708683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19468157634890722099611577 14601118226168041574708683)
              ·
                refine ⟨21901677339252062362063025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14601118226168041574708683 21901677339252062362063025)
                ·
                  refine ⟨16426258004439046771547269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21901677339252062362063025 16426258004439046771547269)
                  ·
                    refine ⟨3079923375832321269665113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16426258004439046771547269 3079923375832321269665113)
                    ·
                      refine ⟨2309942531874240952248835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3079923375832321269665113 2309942531874240952248835)
                      ·
                        rfl

theorem cell23_4498597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_4498597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498597 prefixEnd_4498597 := by exact prefixLift 4498597
  have htrace : WordTrace (prefixWord ++ tailWord_4498597) baseStart_4498597 baseEnd_4498597 := by
    simpa [prefixWord, tailWord_4498597, baseEnd_4498597] using wordTrace_append hprefix tailTrace_4498597
  have hstable : (prefixWord ++ tailWord_4498597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498597).length < 2 ^ (prefixWord ++ tailWord_4498597).sum := by decide
  have hdescent : baseEnd_4498597 < baseStart_4498597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498620 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 8]
def baseStart_4498620 : Nat := 118140960795 + 4498620 * 2 ^ 59
def prefixEnd_4498620 : Nat := 4983230072969 + 3 ^ 40 * 4498620 * 2
def baseEnd_4498620 : Nat := 256661593547699373584581

theorem tailTrace_4498620 : CollatzResearch.WordTrace tailWord_4498620 prefixEnd_4498620 256661593547699373584581 := by
  unfold tailWord_4498620
  simp only [CollatzResearch.WordTrace]
  refine ⟨82039075481137758986686657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109385433974850345315582209 82039075481137758986686657)
  ·
    refine ⟨61529306610853319240014993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82039075481137758986686657 61529306610853319240014993)
    ·
      refine ⟨46146979958139989430011245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61529306610853319240014993 46146979958139989430011245)
      ·
        refine ⟨17305117484302496036254217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46146979958139989430011245 17305117484302496036254217)
        ·
          refine ⟨12978838113226872027190663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17305117484302496036254217 12978838113226872027190663)
          ·
            refine ⟨19468257169840308040785995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12978838113226872027190663 19468257169840308040785995)
            ·
              refine ⟨29202385754760462061178993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19468257169840308040785995 29202385754760462061178993)
              ·
                refine ⟨21901789316070346545884245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29202385754760462061178993 21901789316070346545884245)
                ·
                  refine ⟨256661593547699373584581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21901789316070346545884245 256661593547699373584581)
                  ·
                    rfl

theorem cell23_4498620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_4498620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498620 prefixEnd_4498620 := by exact prefixLift 4498620
  have htrace : WordTrace (prefixWord ++ tailWord_4498620) baseStart_4498620 baseEnd_4498620 := by
    simpa [prefixWord, tailWord_4498620, baseEnd_4498620] using wordTrace_append hprefix tailTrace_4498620
  have hstable : (prefixWord ++ tailWord_4498620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498620).length < 2 ^ (prefixWord ++ tailWord_4498620).sum := by decide
  have hdescent : baseEnd_4498620 < baseStart_4498620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498633 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_4498633 : Nat := 118140960795 + 4498633 * 2 ^ 59
def prefixEnd_4498633 : Nat := 4983230072969 + 3 ^ 40 * 4498633 * 2
def baseEnd_4498633 : Nat := 769987005725934270466223

theorem tailTrace_4498633 : CollatzResearch.WordTrace tailWord_4498633 prefixEnd_4498633 769987005725934270466223 := by
  unfold tailWord_4498633
  simp only [CollatzResearch.WordTrace]
  refine ⟨164078625111228421193596553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109385750074152280795731035 164078625111228421193596553)
  ·
    refine ⟨123058968833421315895197415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164078625111228421193596553 123058968833421315895197415)
    ·
      refine ⟨184588453250131973842796123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123058968833421315895197415 184588453250131973842796123)
      ·
        refine ⟨276882679875197960764194185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184588453250131973842796123 276882679875197960764194185)
        ·
          refine ⟨207662009906398470573145639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276882679875197960764194185 207662009906398470573145639)
          ·
            refine ⟨311493014859597705859718459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207662009906398470573145639 311493014859597705859718459)
            ·
              refine ⟨467239522289396558789577689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311493014859597705859718459 467239522289396558789577689)
              ·
                refine ⟨350429641717047419092183267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467239522289396558789577689 350429641717047419092183267)
                ·
                  refine ⟨525644462575571128638274901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350429641717047419092183267 525644462575571128638274901)
                  ·
                    refine ⟨769987005725934270466223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 525644462575571128638274901 769987005725934270466223)
                    ·
                      rfl

theorem cell23_4498633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_4498633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498633 prefixEnd_4498633 := by exact prefixLift 4498633
  have htrace : WordTrace (prefixWord ++ tailWord_4498633) baseStart_4498633 baseEnd_4498633 := by
    simpa [prefixWord, tailWord_4498633, baseEnd_4498633] using wordTrace_append hprefix tailTrace_4498633
  have hstable : (prefixWord ++ tailWord_4498633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498633).length < 2 ^ (prefixWord ++ tailWord_4498633).sum := by decide
  have hdescent : baseEnd_4498633 < baseStart_4498633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498650 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_4498650 : Nat := 118140960795 + 4498650 * 2 ^ 59
def prefixEnd_4498650 : Nat := 4983230072969 + 3 ^ 40 * 4498650 * 2
def baseEnd_4498650 : Nat := 769989915449643081628697

theorem tailTrace_4498650 : CollatzResearch.WordTrace tailWord_4498650 prefixEnd_4498650 769989915449643081628697 := by
  unfold tailWord_4498650
  simp only [CollatzResearch.WordTrace]
  refine ⟨41019811288041708274241351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109386163434777888731310269 41019811288041708274241351)
  ·
    refine ⟨61529716932062562411362027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41019811288041708274241351 61529716932062562411362027)
    ·
      refine ⟨92294575398093843617043041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61529716932062562411362027 92294575398093843617043041)
      ·
        refine ⟨69220931548570382712782281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92294575398093843617043041 69220931548570382712782281)
        ·
          refine ⟨51915698661427787034586711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69220931548570382712782281 51915698661427787034586711)
          ·
            refine ⟨77873547992141680551880067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51915698661427787034586711 77873547992141680551880067)
            ·
              refine ⟨116810321988212520827820101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77873547992141680551880067 116810321988212520827820101)
              ·
                refine ⟨21901935372789847655216269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116810321988212520827820101 21901935372789847655216269)
                ·
                  refine ⟨8213225764796192870706101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21901935372789847655216269 8213225764796192870706101)
                  ·
                    refine ⟨769989915449643081628697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8213225764796192870706101 769989915449643081628697)
                    ·
                      rfl

theorem cell23_4498650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_4498650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498650 prefixEnd_4498650 := by exact prefixLift 4498650
  have htrace : WordTrace (prefixWord ++ tailWord_4498650) baseStart_4498650 baseEnd_4498650 := by
    simpa [prefixWord, tailWord_4498650, baseEnd_4498650] using wordTrace_append hprefix tailTrace_4498650
  have hstable : (prefixWord ++ tailWord_4498650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498650).length < 2 ^ (prefixWord ++ tailWord_4498650).sum := by decide
  have hdescent : baseEnd_4498650 < baseStart_4498650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498667 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 1, 5]
def baseStart_4498667 : Nat := 118140960795 + 4498667 * 2 ^ 59
def prefixEnd_4498667 : Nat := 4983230072969 + 3 ^ 40 * 4498667 * 2
def baseEnd_4498667 : Nat := 769992825173351892791171

theorem tailTrace_4498667 : CollatzResearch.WordTrace tailWord_4498667 prefixEnd_4498667 769992825173351892791171 := by
  unfold tailWord_4498667
  simp only [CollatzResearch.WordTrace]
  refine ⟨164079865193105245000334255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109386576795403496666889503 164079865193105245000334255)
  ·
    refine ⟨246119797789657867500501383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164079865193105245000334255 246119797789657867500501383)
    ·
      refine ⟨369179696684486801250752075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246119797789657867500501383 369179696684486801250752075)
      ·
        refine ⟨553769545026730201876128113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369179696684486801250752075 553769545026730201876128113)
        ·
          refine ⟨415327158770047651407096085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553769545026730201876128113 415327158770047651407096085)
          ·
            refine ⟨19468460567345983659707629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 415327158770047651407096085 19468460567345983659707629)
            ·
              refine ⟨7300672712754743872390361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19468460567345983659707629 7300672712754743872390361)
              ·
                refine ⟨5475504534566057904292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7300672712754743872390361 5475504534566057904292771)
                ·
                  refine ⟨8213256801849086856439157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475504534566057904292771 8213256801849086856439157)
                  ·
                    refine ⟨769992825173351892791171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8213256801849086856439157 769992825173351892791171)
                    ·
                      rfl

theorem cell23_4498667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 5].length) (baseStart_4498667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498667 prefixEnd_4498667 := by exact prefixLift 4498667
  have htrace : WordTrace (prefixWord ++ tailWord_4498667) baseStart_4498667 baseEnd_4498667 := by
    simpa [prefixWord, tailWord_4498667, baseEnd_4498667] using wordTrace_append hprefix tailTrace_4498667
  have hstable : (prefixWord ++ tailWord_4498667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498667).length < 2 ^ (prefixWord ++ tailWord_4498667).sum := by decide
  have hdescent : baseEnd_4498667 < baseStart_4498667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498714 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_4498714 : Nat := 118140960795 + 4498714 * 2 ^ 59
def prefixEnd_4498714 : Nat := 4983230072969 + 3 ^ 40 * 4498714 * 2
def baseEnd_4498714 : Nat := 770000869703605664828599

theorem tailTrace_4498714 : CollatzResearch.WordTrace tailWord_4498714 prefixEnd_4498714 770000869703605664828599 := by
  unfold tailWord_4498714
  simp only [CollatzResearch.WordTrace]
  refine ⟨41020394855983743006823799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109387719615956648018196797 41020394855983743006823799)
  ·
    refine ⟨61530592283975614510235699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41020394855983743006823799 61530592283975614510235699)
    ·
      refine ⟨92295888425963421765353549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61530592283975614510235699 92295888425963421765353549)
      ·
        refine ⟨34610958159736283162007581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92295888425963421765353549 34610958159736283162007581)
        ·
          refine ⟨12979109309901106185752843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34610958159736283162007581 12979109309901106185752843)
          ·
            refine ⟨19468663964851659278629265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12979109309901106185752843 19468663964851659278629265)
            ·
              refine ⟨14601497973638744458971949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19468663964851659278629265 14601497973638744458971949)
              ·
                refine ⟨5475561740114529172114481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14601497973638744458971949 5475561740114529172114481)
                ·
                  refine ⟨4106671305085896879085861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475561740114529172114481 4106671305085896879085861)
                  ·
                    refine ⟨770000869703605664828599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106671305085896879085861 770000869703605664828599)
                    ·
                      rfl

theorem cell23_4498714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_4498714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498714 prefixEnd_4498714 := by exact prefixLift 4498714
  have htrace : WordTrace (prefixWord ++ tailWord_4498714) baseStart_4498714 baseEnd_4498714 := by
    simpa [prefixWord, tailWord_4498714, baseEnd_4498714] using wordTrace_append hprefix tailTrace_4498714
  have hstable : (prefixWord ++ tailWord_4498714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498714).length < 2 ^ (prefixWord ++ tailWord_4498714).sum := by decide
  have hdescent : baseEnd_4498714 < baseStart_4498714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498724 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_4498724 : Nat := 118140960795 + 4498724 * 2 ^ 59
def prefixEnd_4498724 : Nat := 4983230072969 + 3 ^ 40 * 4498724 * 2
def baseEnd_4498724 : Nat := 2310007743917361955360751

theorem tailTrace_4498724 : CollatzResearch.WordTrace tailWord_4498724 prefixEnd_4498724 2310007743917361955360751 := by
  unfold tailWord_4498724
  simp only [CollatzResearch.WordTrace]
  refine ⟨82040972076949371867579613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109387962769265829156772817 82040972076949371867579613)
  ·
    refine ⟨30765364528856014450342355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82040972076949371867579613 30765364528856014450342355)
    ·
      refine ⟨46148046793284021675513533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30765364528856014450342355 46148046793284021675513533)
      ·
        refine ⟨17305517547481508128317575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46148046793284021675513533 17305517547481508128317575)
        ·
          refine ⟨25958276321222262192476363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17305517547481508128317575 25958276321222262192476363)
          ·
            refine ⟨38937414481833393288714545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25958276321222262192476363 38937414481833393288714545)
            ·
              refine ⟨29203060861375044966535909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38937414481833393288714545 29203060861375044966535909)
              ·
                refine ⟨5475573911507820931225483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29203060861375044966535909 5475573911507820931225483)
                ·
                  refine ⟨8213360867261731396838225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475573911507820931225483 8213360867261731396838225)
                  ·
                    refine ⟨6160020650446298547628669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8213360867261731396838225 6160020650446298547628669)
                    ·
                      refine ⟨2310007743917361955360751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160020650446298547628669 2310007743917361955360751)
                      ·
                        rfl

theorem cell23_4498724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_4498724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498724 prefixEnd_4498724 := by exact prefixLift 4498724
  have htrace : WordTrace (prefixWord ++ tailWord_4498724) baseStart_4498724 baseEnd_4498724 := by
    simpa [prefixWord, tailWord_4498724, baseEnd_4498724] using wordTrace_append hprefix tailTrace_4498724
  have hstable : (prefixWord ++ tailWord_4498724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498724).length < 2 ^ (prefixWord ++ tailWord_4498724).sum := by decide
  have hdescent : baseEnd_4498724 < baseStart_4498724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498738 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_4498738 : Nat := 118140960795 + 4498738 * 2 ^ 59
def prefixEnd_4498738 : Nat := 4983230072969 + 3 ^ 40 * 4498738 * 2
def baseEnd_4498738 : Nat := 2310014932646524900585687

theorem tailTrace_4498738 : CollatzResearch.WordTrace tailWord_4498738 prefixEnd_4498738 2310014932646524900585687 := by
  unfold tailWord_4498738
  simp only [CollatzResearch.WordTrace]
  refine ⟨41020613693962006031542217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109388303183898682750779245 41020613693962006031542217)
  ·
    refine ⟨30765460270471504523656663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41020613693962006031542217 30765460270471504523656663)
    ·
      refine ⟨46148190405707256785484995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30765460270471504523656663 46148190405707256785484995)
      ·
        refine ⟨69222285608560885178227493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46148190405707256785484995 69222285608560885178227493)
        ·
          refine ⟨12979178551605165970917655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69222285608560885178227493 12979178551605165970917655)
          ·
            refine ⟨19468767827407748956376483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12979178551605165970917655 19468767827407748956376483)
            ·
              refine ⟨29203151741111623434564725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19468767827407748956376483 29203151741111623434564725)
              ·
                refine ⟨2737795475729214696990443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29203151741111623434564725 2737795475729214696990443)
                ·
                  refine ⟨4106693213593822045485665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737795475729214696990443 4106693213593822045485665)
                  ·
                    refine ⟨3080019910195366534114249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106693213593822045485665 3080019910195366534114249)
                    ·
                      refine ⟨2310014932646524900585687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080019910195366534114249 2310014932646524900585687)
                      ·
                        rfl

theorem cell23_4498738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_4498738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498738 prefixEnd_4498738 := by exact prefixLift 4498738
  have htrace : WordTrace (prefixWord ++ tailWord_4498738) baseStart_4498738 baseEnd_4498738 := by
    simpa [prefixWord, tailWord_4498738, baseEnd_4498738] using wordTrace_append hprefix tailTrace_4498738
  have hstable : (prefixWord ++ tailWord_4498738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498738).length < 2 ^ (prefixWord ++ tailWord_4498738).sum := by decide
  have hdescent : baseEnd_4498738 < baseStart_4498738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498741 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_4498741 : Nat := 118140960795 + 4498741 * 2 ^ 59
def prefixEnd_4498741 : Nat := 4983230072969 + 3 ^ 40 * 4498741 * 2
def baseEnd_4498741 : Nat := 2310016473088488388848173

theorem tailTrace_4498741 : CollatzResearch.WordTrace tailWord_4498741 prefixEnd_4498741 2310016473088488388848173 := by
  unfold tailWord_4498741
  simp only [CollatzResearch.WordTrace]
  refine ⟨164082564194837155638528077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109388376129891437092352051 164082564194837155638528077)
  ·
    refine ⟨61530961573063933364448029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164082564194837155638528077 61530961573063933364448029)
    ·
      refine ⟨23074110589898975011668011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61530961573063933364448029 23074110589898975011668011)
      ·
        refine ⟨34611165884848462517502017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23074110589898975011668011 34611165884848462517502017)
        ·
          refine ⟨25958374413636346888126513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34611165884848462517502017 25958374413636346888126513)
          ·
            refine ⟨19468780810227260166094885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25958374413636346888126513 19468780810227260166094885)
            ·
              refine ⟨3650396401917611281142791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19468780810227260166094885 3650396401917611281142791)
              ·
                refine ⟨5475594602876416921714187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650396401917611281142791 5475594602876416921714187)
                ·
                  refine ⟨8213391904314625382571281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475594602876416921714187 8213391904314625382571281)
                  ·
                    refine ⟨6160043928235969036928461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8213391904314625382571281 6160043928235969036928461)
                    ·
                      refine ⟨2310016473088488388848173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160043928235969036928461 2310016473088488388848173)
                      ·
                        rfl

theorem cell23_4498741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_4498741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498741 prefixEnd_4498741 := by exact prefixLift 4498741
  have htrace : WordTrace (prefixWord ++ tailWord_4498741) baseStart_4498741 baseEnd_4498741 := by
    simpa [prefixWord, tailWord_4498741, baseEnd_4498741] using wordTrace_append hprefix tailTrace_4498741
  have hstable : (prefixWord ++ tailWord_4498741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498741).length < 2 ^ (prefixWord ++ tailWord_4498741).sum := by decide
  have hdescent : baseEnd_4498741 < baseStart_4498741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498758 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4498758 : Nat := 118140960795 + 4498758 * 2 ^ 59
def prefixEnd_4498758 : Nat := 4983230072969 + 3 ^ 40 * 4498758 * 2
def baseEnd_4498758 : Nat := 2310025202259614822335595

theorem tailTrace_4498758 : CollatzResearch.WordTrace tailWord_4498758 prefixEnd_4498758 2310025202259614822335595 := by
  unfold tailWord_4498758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127599507367986485684279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109388789490517045027931285 5127599507367986485684279)
  ·
    refine ⟨7691399261051979728526419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5127599507367986485684279 7691399261051979728526419)
    ·
      refine ⟨11537098891577969592789629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7691399261051979728526419 11537098891577969592789629)
      ·
        refine ⟨4326412084341738597296111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11537098891577969592789629 4326412084341738597296111)
        ·
          refine ⟨6489618126512607895944167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326412084341738597296111 6489618126512607895944167)
          ·
            refine ⟨9734427189768911843916251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6489618126512607895944167 9734427189768911843916251)
            ·
              refine ⟨14601640784653367765874377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9734427189768911843916251 14601640784653367765874377)
              ·
                refine ⟨10951230588490025824405783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14601640784653367765874377 10951230588490025824405783)
                ·
                  refine ⟨16426845882735038736608675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10951230588490025824405783 16426845882735038736608675)
                  ·
                    refine ⟨24640268824102558104913013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16426845882735038736608675 24640268824102558104913013)
                    ·
                      refine ⟨2310025202259614822335595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24640268824102558104913013 2310025202259614822335595)
                      ·
                        rfl

theorem cell23_4498758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4498758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498758 prefixEnd_4498758 := by exact prefixLift 4498758
  have htrace : WordTrace (prefixWord ++ tailWord_4498758) baseStart_4498758 baseEnd_4498758 := by
    simpa [prefixWord, tailWord_4498758, baseEnd_4498758] using wordTrace_append hprefix tailTrace_4498758
  have hstable : (prefixWord ++ tailWord_4498758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498758).length < 2 ^ (prefixWord ++ tailWord_4498758).sum := by decide
  have hdescent : baseEnd_4498758 < baseStart_4498758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498765 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_4498765 : Nat := 118140960795 + 4498765 * 2 ^ 59
def prefixEnd_4498765 : Nat := 4983230072969 + 3 ^ 40 * 4498765 * 2
def baseEnd_4498765 : Nat := 770009598874732098316021

theorem tailTrace_4498765 : CollatzResearch.WordTrace tailWord_4498765 prefixEnd_4498765 770009598874732098316021 := by
  unfold tailWord_4498765
  simp only [CollatzResearch.WordTrace]
  refine ⟨164083439546750207737401749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109388959697833471824934499 164083439546750207737401749)
  ·
    refine ⟨7691411228753915987690707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164083439546750207737401749 7691411228753915987690707)
    ·
      refine ⟨11537116843130873981536061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7691411228753915987690707 11537116843130873981536061)
      ·
        refine ⟨4326418816174077743076023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11537116843130873981536061 4326418816174077743076023)
        ·
          refine ⟨6489628224261116614614035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326418816174077743076023 6489628224261116614614035)
          ·
            refine ⟨9734442336391674921921053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6489628224261116614614035 9734442336391674921921053)
            ·
              refine ⟨3650415876146878095720395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9734442336391674921921053 3650415876146878095720395)
              ·
                refine ⟨5475623814220317143580593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650415876146878095720395 5475623814220317143580593)
                ·
                  refine ⟨4106717860665237857685445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475623814220317143580593 4106717860665237857685445)
                  ·
                    refine ⟨770009598874732098316021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106717860665237857685445 770009598874732098316021)
                    ·
                      rfl

theorem cell23_4498765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_4498765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498765 prefixEnd_4498765 := by exact prefixLift 4498765
  have htrace : WordTrace (prefixWord ++ tailWord_4498765) baseStart_4498765 baseEnd_4498765 := by
    simpa [prefixWord, tailWord_4498765, baseEnd_4498765] using wordTrace_append hprefix tailTrace_4498765
  have hstable : (prefixWord ++ tailWord_4498765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498765).length < 2 ^ (prefixWord ++ tailWord_4498765).sum := by decide
  have hdescent : baseEnd_4498765 < baseStart_4498765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498771 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 2, 1, 3]
def baseStart_4498771 : Nat := 118140960795 + 4498771 * 2 ^ 59
def prefixEnd_4498771 : Nat := 4983230072969 + 3 ^ 40 * 4498771 * 2
def baseEnd_4498771 : Nat := 2310031877508123271473035

theorem tailTrace_4498771 : CollatzResearch.WordTrace tailWord_4498771 prefixEnd_4498771 2310031877508123271473035 := by
  unfold tailWord_4498771
  simp only [CollatzResearch.WordTrace]
  refine ⟨164083658384728470762120167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109389105589818980508080111 164083658384728470762120167)
  ·
    refine ⟨246125487577092706143180251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164083658384728470762120167 246125487577092706143180251)
    ·
      refine ⟨369188231365639059214770377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246125487577092706143180251 369188231365639059214770377)
      ·
        refine ⟨276891173524229294411077783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369188231365639059214770377 276891173524229294411077783)
        ·
          refine ⟨415336760286343941616616675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276891173524229294411077783 415336760286343941616616675)
          ·
            refine ⟨623005140429515912424925013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415336760286343941616616675 623005140429515912424925013)
            ·
              refine ⟨3650420744704194799364795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 623005140429515912424925013 3650420744704194799364795)
              ·
                refine ⟨5475631117056292199047193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650420744704194799364795 5475631117056292199047193)
                ·
                  refine ⟨4106723337792219149285395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475631117056292199047193 4106723337792219149285395)
                  ·
                    refine ⟨6160085006688328723928093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4106723337792219149285395 6160085006688328723928093)
                    ·
                      refine ⟨2310031877508123271473035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160085006688328723928093 2310031877508123271473035)
                      ·
                        rfl

theorem cell23_4498771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 1, 3].length) (baseStart_4498771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498771 prefixEnd_4498771 := by exact prefixLift 4498771
  have htrace : WordTrace (prefixWord ++ tailWord_4498771) baseStart_4498771 baseEnd_4498771 := by
    simpa [prefixWord, tailWord_4498771, baseEnd_4498771] using wordTrace_append hprefix tailTrace_4498771
  have hstable : (prefixWord ++ tailWord_4498771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498771).length < 2 ^ (prefixWord ++ tailWord_4498771).sum := by decide
  have hdescent : baseEnd_4498771 < baseStart_4498771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498797 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4498797 : Nat := 118140960795 + 4498797 * 2 ^ 59
def prefixEnd_4498797 : Nat := 4983230072969 + 3 ^ 40 * 4498797 * 2
def baseEnd_4498797 : Nat := 2310045228005140169747915

theorem tailTrace_4498797 : CollatzResearch.WordTrace tailWord_4498797 prefixEnd_4498797 2310045228005140169747915 := by
  unfold tailWord_4498797
  simp only [CollatzResearch.WordTrace]
  refine ⟨164084606682634277202566645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109389737788422851468377763 164084606682634277202566645)
  ·
    refine ⟨15382931876496963487740623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164084606682634277202566645 15382931876496963487740623)
    ·
      refine ⟨23074397814745445231610935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15382931876496963487740623 23074397814745445231610935)
      ·
        refine ⟨34611596722118167847416403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23074397814745445231610935 34611596722118167847416403)
        ·
          refine ⟨51917395083177251771124605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34611596722118167847416403 51917395083177251771124605)
          ·
            refine ⟨19469023156191469414171727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51917395083177251771124605 19469023156191469414171727)
            ·
              refine ⟨29203534734287204121257591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19469023156191469414171727 29203534734287204121257591)
              ·
                refine ⟨43805302101430806181886387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29203534734287204121257591 43805302101430806181886387)
                ·
                  refine ⟨65707953152146209272829581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43805302101430806181886387 65707953152146209272829581)
                  ·
                    refine ⟨24640482432054828477311093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65707953152146209272829581 24640482432054828477311093)
                    ·
                      refine ⟨2310045228005140169747915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24640482432054828477311093 2310045228005140169747915)
                      ·
                        rfl

theorem cell23_4498797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4498797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498797 prefixEnd_4498797 := by exact prefixLift 4498797
  have htrace : WordTrace (prefixWord ++ tailWord_4498797) baseStart_4498797 baseEnd_4498797 := by
    simpa [prefixWord, tailWord_4498797, baseEnd_4498797] using wordTrace_append hprefix tailTrace_4498797
  have hstable : (prefixWord ++ tailWord_4498797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498797).length < 2 ^ (prefixWord ++ tailWord_4498797).sum := by decide
  have hdescent : baseEnd_4498797 < baseStart_4498797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498811 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 2, 2, 2]
def baseStart_4498811 : Nat := 118140960795 + 4498811 * 2 ^ 59
def prefixEnd_4498811 : Nat := 4983230072969 + 3 ^ 40 * 4498811 * 2
def baseEnd_4498811 : Nat := 2310052416734303114972851

theorem tailTrace_4498811 : CollatzResearch.WordTrace tailWord_4498811 prefixEnd_4498811 2310052416734303114972851 := by
  unfold tailWord_4498811
  simp only [CollatzResearch.WordTrace]
  refine ⟨164085117304583557593576287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109390078203055705062384191 164085117304583557593576287)
  ·
    refine ⟨246127675956875336390364431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164085117304583557593576287 246127675956875336390364431)
    ·
      refine ⟨369191513935313004585546647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246127675956875336390364431 369191513935313004585546647)
      ·
        refine ⟨553787270902969506878319971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369191513935313004585546647 553787270902969506878319971)
        ·
          refine ⟨830680906354454260317479957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553787270902969506878319971 830680906354454260317479957)
          ·
            refine ⟨38938167485365043452381873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 830680906354454260317479957 38938167485365043452381873)
            ·
              refine ⟨29203625614023782589286405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38938167485365043452381873 29203625614023782589286405)
              ·
                refine ⟨5475679802629459235491201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29203625614023782589286405 5475679802629459235491201)
                ·
                  refine ⟨4106759851972094426618401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475679802629459235491201 4106759851972094426618401)
                  ·
                    refine ⟨3080069888979070819963801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106759851972094426618401 3080069888979070819963801)
                    ·
                      refine ⟨2310052416734303114972851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080069888979070819963801 2310052416734303114972851)
                      ·
                        rfl

theorem cell23_4498811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2, 2].length) (baseStart_4498811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498811 prefixEnd_4498811 := by exact prefixLift 4498811
  have htrace : WordTrace (prefixWord ++ tailWord_4498811) baseStart_4498811 baseEnd_4498811 := by
    simpa [prefixWord, tailWord_4498811, baseEnd_4498811] using wordTrace_append hprefix tailTrace_4498811
  have hstable : (prefixWord ++ tailWord_4498811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498811).length < 2 ^ (prefixWord ++ tailWord_4498811).sum := by decide
  have hdescent : baseEnd_4498811 < baseStart_4498811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498827 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3]
def baseStart_4498827 : Nat := 118140960795 + 4498827 * 2 ^ 59
def prefixEnd_4498827 : Nat := 4983230072969 + 3 ^ 40 * 4498827 * 2
def baseEnd_4498827 : Nat := 2310060632424775052372777

theorem tailTrace_4498827 : CollatzResearch.WordTrace tailWord_4498827 prefixEnd_4498827 2310060632424775052372777 := by
  unfold tailWord_4498827
  simp only [CollatzResearch.WordTrace]
  refine ⟨164085700872525592326158735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109390467248350394884105823 164085700872525592326158735)
  ·
    refine ⟨246128551308788388489238103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164085700872525592326158735 246128551308788388489238103)
    ·
      refine ⟨369192826963182582733857155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246128551308788388489238103 369192826963182582733857155)
      ·
        refine ⟨553789240444773874100785733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369192826963182582733857155 553789240444773874100785733)
        ·
          refine ⟨103835482583395101393897325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 553789240444773874100785733 103835482583395101393897325)
          ·
            refine ⟨38938305968773163022711497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103835482583395101393897325 38938305968773163022711497)
            ·
              refine ⟨29203729476579872267033623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38938305968773163022711497 29203729476579872267033623)
              ·
                refine ⟨43805594214869808400550435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29203729476579872267033623 43805594214869808400550435)
                ·
                  refine ⟨65708391322304712600825653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43805594214869808400550435 65708391322304712600825653)
                  ·
                    refine ⟨6160161686466066806327405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65708391322304712600825653 6160161686466066806327405)
                    ·
                      refine ⟨2310060632424775052372777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160161686466066806327405 2310060632424775052372777)
                      ·
                        rfl

theorem cell23_4498827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 3].length) (baseStart_4498827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498827 prefixEnd_4498827 := by exact prefixLift 4498827
  have htrace : WordTrace (prefixWord ++ tailWord_4498827) baseStart_4498827 baseEnd_4498827 := by
    simpa [prefixWord, tailWord_4498827, baseEnd_4498827] using wordTrace_append hprefix tailTrace_4498827
  have hstable : (prefixWord ++ tailWord_4498827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498827).length < 2 ^ (prefixWord ++ tailWord_4498827).sum := by decide
  have hdescent : baseEnd_4498827 < baseStart_4498827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498894 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_4498894 : Nat := 118140960795 + 4498894 * 2 ^ 59
def prefixEnd_4498894 : Nat := 4983230072969 + 3 ^ 40 * 4498894 * 2
def baseEnd_4498894 : Nat := 770031678542875430078323

theorem tailTrace_4498894 : CollatzResearch.WordTrace tailWord_4498894 prefixEnd_4498894 770031678542875430078323 := by
  unfold tailWord_4498894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20511018070410357846105967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109392096375521908512565157 20511018070410357846105967)
  ·
    refine ⟨30766527105615536769158951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20511018070410357846105967 30766527105615536769158951)
    ·
      refine ⟨46149790658423305153738427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30766527105615536769158951 46149790658423305153738427)
      ·
        refine ⟨69224685987634957730607641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46149790658423305153738427 69224685987634957730607641)
        ·
          refine ⟨51918514490726218297955731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69224685987634957730607641 51918514490726218297955731)
          ·
            refine ⟨77877771736089327446933597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51918514490726218297955731 77877771736089327446933597)
            ·
              refine ⟨29204164401033497792600099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77877771736089327446933597 29204164401033497792600099)
              ·
                refine ⟨43806246601550246688900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29204164401033497792600099 43806246601550246688900149)
                ·
                  refine ⟨4106835618895335627084389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43806246601550246688900149 4106835618895335627084389)
                  ·
                    refine ⟨770031678542875430078323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4106835618895335627084389 770031678542875430078323)
                    ·
                      rfl

theorem cell23_4498894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_4498894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498894 prefixEnd_4498894 := by exact prefixLift 4498894
  have htrace : WordTrace (prefixWord ++ tailWord_4498894) baseStart_4498894 baseEnd_4498894 := by
    simpa [prefixWord, tailWord_4498894, baseEnd_4498894] using wordTrace_append hprefix tailTrace_4498894
  have hstable : (prefixWord ++ tailWord_4498894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498894).length < 2 ^ (prefixWord ++ tailWord_4498894).sum := by decide
  have hdescent : baseEnd_4498894 < baseStart_4498894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498927 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_4498927 : Nat := 118140960795 + 4498927 * 2 ^ 59
def prefixEnd_4498927 : Nat := 4983230072969 + 3 ^ 40 * 4498927 * 2
def baseEnd_4498927 : Nat := 2310111980490224661122317

theorem tailTrace_4498927 : CollatzResearch.WordTrace tailWord_4498927 prefixEnd_4498927 2310111980490224661122317 := by
  unfold tailWord_4498927
  simp only [CollatzResearch.WordTrace]
  refine ⟨164089348172163309404799035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109392898781442206269866023 164089348172163309404799035)
  ·
    refine ⟨246134022258244964107198553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164089348172163309404799035 246134022258244964107198553)
    ·
      refine ⟨184600516693683723080398915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246134022258244964107198553 184600516693683723080398915)
      ·
        refine ⟨276900775040525584620598373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184600516693683723080398915 276900775040525584620598373)
        ·
          refine ⟨51918895320098547116362195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276900775040525584620598373 51918895320098547116362195)
          ·
            refine ⟨77878342980147820674543293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51918895320098547116362195 77878342980147820674543293)
            ·
              refine ⟨29204378617555432752953735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77878342980147820674543293 29204378617555432752953735)
              ·
                refine ⟨43806567926333149129430603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29204378617555432752953735 43806567926333149129430603)
                ·
                  refine ⟨65709851889499723694145905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43806567926333149129430603 65709851889499723694145905)
                  ·
                    refine ⟨49282388917124792770609429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65709851889499723694145905 49282388917124792770609429)
                    ·
                      refine ⟨2310111980490224661122317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49282388917124792770609429 2310111980490224661122317)
                      ·
                        rfl

theorem cell23_4498927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_4498927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498927 prefixEnd_4498927 := by exact prefixLift 4498927
  have htrace : WordTrace (prefixWord ++ tailWord_4498927) baseStart_4498927 baseEnd_4498927 := by
    simpa [prefixWord, tailWord_4498927, baseEnd_4498927] using wordTrace_append hprefix tailTrace_4498927
  have hstable : (prefixWord ++ tailWord_4498927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498927).length < 2 ^ (prefixWord ++ tailWord_4498927).sum := by decide
  have hdescent : baseEnd_4498927 < baseStart_4498927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498941 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 6]
def baseStart_4498941 : Nat := 118140960795 + 4498941 * 2 ^ 59
def prefixEnd_4498941 : Nat := 4983230072969 + 3 ^ 40 * 4498941 * 2
def baseEnd_4498941 : Nat := 256679907691043067371917

theorem tailTrace_4498941 : CollatzResearch.WordTrace tailWord_4498941 prefixEnd_4498941 256679907691043067371917 := by
  unfold tailWord_4498941
  simp only [CollatzResearch.WordTrace]
  refine ⟨164089858794112589795808677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109393239196075059863872451 164089858794112589795808677)
  ·
    refine ⟨30766848523896110586714127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164089858794112589795808677 30766848523896110586714127)
    ·
      refine ⟨46150272785844165880071191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30766848523896110586714127 46150272785844165880071191)
      ·
        refine ⟨69225409178766248820106787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46150272785844165880071191 69225409178766248820106787)
        ·
          refine ⟨103838113768149373230160181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69225409178766248820106787 103838113768149373230160181)
          ·
            refine ⟨9734823165764003740327517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103838113768149373230160181 9734823165764003740327517)
            ·
              refine ⟨3650558687161501402622819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9734823165764003740327517 3650558687161501402622819)
              ·
                refine ⟨5475838030742252103934229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650558687161501402622819 5475838030742252103934229)
                ·
                  refine ⟨256679907691043067371917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5475838030742252103934229 256679907691043067371917)
                  ·
                    rfl

theorem cell23_4498941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_4498941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498941 prefixEnd_4498941 := by exact prefixLift 4498941
  have htrace : WordTrace (prefixWord ++ tailWord_4498941) baseStart_4498941 baseEnd_4498941 := by
    simpa [prefixWord, tailWord_4498941, baseEnd_4498941] using wordTrace_append hprefix tailTrace_4498941
  have hstable : (prefixWord ++ tailWord_4498941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498941).length < 2 ^ (prefixWord ++ tailWord_4498941).sum := by decide
  have hdescent : baseEnd_4498941 < baseStart_4498941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498961 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_4498961 : Nat := 118140960795 + 4498961 * 2 ^ 59
def prefixEnd_4498961 : Nat := 4983230072969 + 3 ^ 40 * 4498961 * 2
def baseEnd_4498961 : Nat := 2310129438832477528097161

theorem tailTrace_4498961 : CollatzResearch.WordTrace tailWord_4498961 prefixEnd_4498961 2310129438832477528097161 := by
  unfold tailWord_4498961
  simp only [CollatzResearch.WordTrace]
  refine ⟨164090588254040133211536737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109393725502693422141024491 164090588254040133211536737)
  ·
    refine ⟨123067941190530099908652553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164090588254040133211536737 123067941190530099908652553)
    ·
      refine ⟨92300955892897574931489415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123067941190530099908652553 92300955892897574931489415)
      ·
        refine ⟨138451433839346362397234123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92300955892897574931489415 138451433839346362397234123)
        ·
          refine ⟨207677150759019543595851185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138451433839346362397234123 207677150759019543595851185)
          ·
            refine ⟨155757863069264657696888389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207677150759019543595851185 155757863069264657696888389)
            ·
              refine ⟨29204599325487123318166573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155757863069264657696888389 29204599325487123318166573)
              ·
                refine ⟨10951724747057671244312465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29204599325487123318166573 10951724747057671244312465)
                ·
                  refine ⟨8213793560293253433234349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10951724747057671244312465 8213793560293253433234349)
                  ·
                    refine ⟨3080172585109970037462881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8213793560293253433234349 3080172585109970037462881)
                    ·
                      refine ⟨2310129438832477528097161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080172585109970037462881 2310129438832477528097161)
                      ·
                        rfl

theorem cell23_4498961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_4498961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498961 prefixEnd_4498961 := by exact prefixLift 4498961
  have htrace : WordTrace (prefixWord ++ tailWord_4498961) baseStart_4498961 baseEnd_4498961 := by
    simpa [prefixWord, tailWord_4498961, baseEnd_4498961] using wordTrace_append hprefix tailTrace_4498961
  have hstable : (prefixWord ++ tailWord_4498961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498961).length < 2 ^ (prefixWord ++ tailWord_4498961).sum := by decide
  have hdescent : baseEnd_4498961 < baseStart_4498961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4498994 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_4498994 : Nat := 118140960795 + 4498994 * 2 ^ 59
def prefixEnd_4498994 : Nat := 4983230072969 + 3 ^ 40 * 4498994 * 2
def baseEnd_4498994 : Nat := 2310146383694075898984509

theorem tailTrace_4498994 : CollatzResearch.WordTrace tailWord_4498994 prefixEnd_4498994 2310146383694075898984509 := by
  unfold tailWord_4498994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41022947965730144961872009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109394527908613719898325357 41022947965730144961872009)
  ·
    refine ⟨30767210974297608721404007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41022947965730144961872009 30767210974297608721404007)
    ·
      refine ⟨46150816461446413082106011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30767210974297608721404007 46150816461446413082106011)
      ·
        refine ⟨69226224692169619623159017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46150816461446413082106011 69226224692169619623159017)
        ·
          refine ⟨51919668519127214717369263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69226224692169619623159017 51919668519127214717369263)
          ·
            refine ⟨77879502778690822076053895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51919668519127214717369263 77879502778690822076053895)
            ·
              refine ⟨116819254168036233114080843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77879502778690822076053895 116819254168036233114080843)
              ·
                refine ⟨175228881252054349671121265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116819254168036233114080843 175228881252054349671121265)
                ·
                  refine ⟨131421660939040762253340949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175228881252054349671121265 131421660939040762253340949)
                  ·
                    refine ⟨6160390356517535730625357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131421660939040762253340949 6160390356517535730625357)
                    ·
                      refine ⟨2310146383694075898984509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160390356517535730625357 2310146383694075898984509)
                      ·
                        rfl

theorem cell23_4498994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_4498994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4498994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4498994 prefixEnd_4498994 := by exact prefixLift 4498994
  have htrace : WordTrace (prefixWord ++ tailWord_4498994) baseStart_4498994 baseEnd_4498994 := by
    simpa [prefixWord, tailWord_4498994, baseEnd_4498994] using wordTrace_append hprefix tailTrace_4498994
  have hstable : (prefixWord ++ tailWord_4498994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4498994).length < 2 ^ (prefixWord ++ tailWord_4498994).sum := by decide
  have hdescent : baseEnd_4498994 < baseStart_4498994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4498994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499005 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_4499005 : Nat := 118140960795 + 4499005 * 2 ^ 59
def prefixEnd_4499005 : Nat := 4983230072969 + 3 ^ 40 * 4499005 * 2
def baseEnd_4499005 : Nat := 770050677327091785315653

theorem tailTrace_4499005 : CollatzResearch.WordTrace tailWord_4499005 prefixEnd_4499005 770050677327091785315653 := by
  unfold tailWord_4499005
  simp only [CollatzResearch.WordTrace]
  refine ⟨164092193065880728726138469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109394795377253819150758979 164092193065880728726138469)
  ·
    refine ⟨30767286199852636636150963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164092193065880728726138469 30767286199852636636150963)
    ·
      refine ⟨46150929299778954954226445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30767286199852636636150963 46150929299778954954226445)
      ·
        refine ⟨17306598487417108107834917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46150929299778954954226445 17306598487417108107834917)
        ·
          refine ⟨3244987216390707770219047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17306598487417108107834917 3244987216390707770219047)
          ·
            refine ⟨4867480824586061655328571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244987216390707770219047 4867480824586061655328571)
            ·
              refine ⟨7301221236879092482992857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867480824586061655328571 7301221236879092482992857)
              ·
                refine ⟨5475915927659319362244643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7301221236879092482992857 5475915927659319362244643)
                ·
                  refine ⟨8213873891488979043366965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475915927659319362244643 8213873891488979043366965)
                  ·
                    refine ⟨770050677327091785315653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8213873891488979043366965 770050677327091785315653)
                    ·
                      rfl

theorem cell23_4499005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_4499005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499005 prefixEnd_4499005 := by exact prefixLift 4499005
  have htrace : WordTrace (prefixWord ++ tailWord_4499005) baseStart_4499005 baseEnd_4499005 := by
    simpa [prefixWord, tailWord_4499005, baseEnd_4499005] using wordTrace_append hprefix tailTrace_4499005
  have hstable : (prefixWord ++ tailWord_4499005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499005).length < 2 ^ (prefixWord ++ tailWord_4499005).sum := by decide
  have hdescent : baseEnd_4499005 < baseStart_4499005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499025 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 1, 2, 2]
def baseStart_4499025 : Nat := 118140960795 + 4499025 * 2 ^ 59
def prefixEnd_4499025 : Nat := 4983230072969 + 3 ^ 40 * 4499025 * 2
def baseEnd_4499025 : Nat := 2310162301594365277696867

theorem tailTrace_4499025 : CollatzResearch.WordTrace tailWord_4499025 prefixEnd_4499025 2310162301594365277696867 := by
  unfold tailWord_4499025
  simp only [CollatzResearch.WordTrace]
  refine ⟨164092922525808272141866529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109395281683872181427911019 164092922525808272141866529)
  ·
    refine ⟨123069691894356204106399897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164092922525808272141866529 123069691894356204106399897)
    ·
      refine ⟨92302268920767153079799923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123069691894356204106399897 92302268920767153079799923)
      ·
        refine ⟨138453403381150729619699885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92302268920767153079799923 138453403381150729619699885)
        ·
          refine ⟨51920026267931523607387457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138453403381150729619699885 51920026267931523607387457)
          ·
            refine ⟨38940019700948642705540593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51920026267931523607387457 38940019700948642705540593)
            ·
              refine ⟨29205014775711482029155445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38940019700948642705540593 29205014775711482029155445)
              ·
                refine ⟨2737970135222951440233323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29205014775711482029155445 2737970135222951440233323)
                ·
                  refine ⟨4106955202834427160349985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2737970135222951440233323 4106955202834427160349985)
                  ·
                    refine ⟨3080216402125820370262489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4106955202834427160349985 3080216402125820370262489)
                    ·
                      refine ⟨2310162301594365277696867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080216402125820370262489 2310162301594365277696867)
                      ·
                        rfl

theorem cell23_4499025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_4499025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499025 prefixEnd_4499025 := by exact prefixLift 4499025
  have htrace : WordTrace (prefixWord ++ tailWord_4499025) baseStart_4499025 baseEnd_4499025 := by
    simpa [prefixWord, tailWord_4499025, baseEnd_4499025] using wordTrace_append hprefix tailTrace_4499025
  have hstable : (prefixWord ++ tailWord_4499025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499025).length < 2 ^ (prefixWord ++ tailWord_4499025).sum := by decide
  have hdescent : baseEnd_4499025 < baseStart_4499025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499044 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_4499044 : Nat := 118140960795 + 4499044 * 2 ^ 59
def prefixEnd_4499044 : Nat := 4983230072969 + 3 ^ 40 * 4499044 * 2
def baseEnd_4499044 : Nat := 770057352575600234453093

theorem tailTrace_4499044 : CollatzResearch.WordTrace tailWord_4499044 prefixEnd_4499044 770057352575600234453093 := by
  unfold tailWord_4499044
  simp only [CollatzResearch.WordTrace]
  refine ⟨82046807756369719193404093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109395743675159625591205457 82046807756369719193404093)
  ·
    refine ⟨30767552908638644697526535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82046807756369719193404093 30767552908638644697526535)
    ·
      refine ⟨46151329362957967046289803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30767552908638644697526535 46151329362957967046289803)
      ·
        refine ⟨69226994044436950569434705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46151329362957967046289803 69226994044436950569434705)
        ·
          refine ⟨51920245533327712927076029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69226994044436950569434705 51920245533327712927076029)
          ·
            refine ⟨19470092074997892347653511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51920245533327712927076029 19470092074997892347653511)
            ·
              refine ⟨29205138112496838521480267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19470092074997892347653511 29205138112496838521480267)
              ·
                refine ⟨43807707168745257782220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29205138112496838521480267 43807707168745257782220401)
                ·
                  refine ⟨32855780376558943336665301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43807707168745257782220401 32855780376558943336665301)
                  ·
                    refine ⟨770057352575600234453093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32855780376558943336665301 770057352575600234453093)
                    ·
                      rfl

theorem cell23_4499044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_4499044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499044 prefixEnd_4499044 := by exact prefixLift 4499044
  have htrace : WordTrace (prefixWord ++ tailWord_4499044) baseStart_4499044 baseEnd_4499044 := by
    simpa [prefixWord, tailWord_4499044, baseEnd_4499044] using wordTrace_append hprefix tailTrace_4499044
  have hstable : (prefixWord ++ tailWord_4499044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499044).length < 2 ^ (prefixWord ++ tailWord_4499044).sum := by decide
  have hdescent : baseEnd_4499044 < baseStart_4499044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499058 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_4499058 : Nat := 118140960795 + 4499058 * 2 ^ 59
def prefixEnd_4499058 : Nat := 4983230072969 + 3 ^ 40 * 4499058 * 2
def baseEnd_4499058 : Nat := 2310179246455963648584215

theorem tailTrace_4499058 : CollatzResearch.WordTrace tailWord_4499058 prefixEnd_4499058 2310179246455963648584215 := by
  unfold tailWord_4499058
  simp only [CollatzResearch.WordTrace]
  refine ⟨41023531533672179694454457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109396084089792479185211885 41023531533672179694454457)
  ·
    refine ⟨30767648650254134770840843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41023531533672179694454457 30767648650254134770840843)
    ·
      refine ⟨46151472975381202156261265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30767648650254134770840843 46151472975381202156261265)
      ·
        refine ⟨34613604731535901617195949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46151472975381202156261265 34613604731535901617195949)
        ·
          refine ⟨12980101774325963106448481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34613604731535901617195949 12980101774325963106448481)
          ·
            refine ⟨9735076330744472329836361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12980101774325963106448481 9735076330744472329836361)
            ·
              refine ⟨7301307248058354247377271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735076330744472329836361 7301307248058354247377271)
              ·
                refine ⟨10951960872087531371065907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7301307248058354247377271 10951960872087531371065907)
                ·
                  refine ⟨16427941308131297056598861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10951960872087531371065907 16427941308131297056598861)
                  ·
                    refine ⟨6160477990549236396224573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16427941308131297056598861 6160477990549236396224573)
                    ·
                      refine ⟨2310179246455963648584215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160477990549236396224573 2310179246455963648584215)
                      ·
                        rfl

theorem cell23_4499058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_4499058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499058 prefixEnd_4499058 := by exact prefixLift 4499058
  have htrace : WordTrace (prefixWord ++ tailWord_4499058) baseStart_4499058 baseEnd_4499058 := by
    simpa [prefixWord, tailWord_4499058, baseEnd_4499058] using wordTrace_append hprefix tailTrace_4499058
  have hstable : (prefixWord ++ tailWord_4499058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499058).length < 2 ^ (prefixWord ++ tailWord_4499058).sum := by decide
  have hdescent : baseEnd_4499058 < baseStart_4499058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499068 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_4499068 : Nat := 118140960795 + 4499068 * 2 ^ 59
def prefixEnd_4499068 : Nat := 4983230072969 + 3 ^ 40 * 4499068 * 2
def baseEnd_4499068 : Nat := 2310184381262508609459169

theorem tailTrace_4499068 : CollatzResearch.WordTrace tailWord_4499068 prefixEnd_4499068 2310184381262508609459169 := by
  unfold tailWord_4499068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82047245432326245242840929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109396327243101660323787905 82047245432326245242840929)
  ·
    refine ⟨61535434074244683932130697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82047245432326245242840929 61535434074244683932130697)
    ·
      refine ⟨46151575555683512949098023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61535434074244683932130697 46151575555683512949098023)
      ·
        refine ⟨69227363333525269423647035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46151575555683512949098023 69227363333525269423647035)
        ·
          refine ⟨103841045000287904135470553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69227363333525269423647035 103841045000287904135470553)
          ·
            refine ⟨77880783750215928101602915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103841045000287904135470553 77880783750215928101602915)
            ·
              refine ⟨116821175625323892152404373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77880783750215928101602915 116821175625323892152404373)
              ·
                refine ⟨5475992607437057444643955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116821175625323892152404373 5475992607437057444643955)
                ·
                  refine ⟨8213988911155586166965933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475992607437057444643955 8213988911155586166965933)
                  ·
                    refine ⟨3080245841683344812612225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8213988911155586166965933 3080245841683344812612225)
                    ·
                      refine ⟨2310184381262508609459169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080245841683344812612225 2310184381262508609459169)
                      ·
                        rfl

theorem cell23_4499068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_4499068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499068 prefixEnd_4499068 := by exact prefixLift 4499068
  have htrace : WordTrace (prefixWord ++ tailWord_4499068) baseStart_4499068 baseEnd_4499068 := by
    simpa [prefixWord, tailWord_4499068, baseEnd_4499068] using wordTrace_append hprefix tailTrace_4499068
  have hstable : (prefixWord ++ tailWord_4499068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499068).length < 2 ^ (prefixWord ++ tailWord_4499068).sum := by decide
  have hdescent : baseEnd_4499068 < baseStart_4499068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499084 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4499084 : Nat := 118140960795 + 4499084 * 2 ^ 59
def prefixEnd_4499084 : Nat := 4983230072969 + 3 ^ 40 * 4499084 * 2
def baseEnd_4499084 : Nat := 2310192596952980546859095

theorem tailTrace_4499084 : CollatzResearch.WordTrace tailWord_4499084 prefixEnd_4499084 2310192596952980546859095 := by
  unfold tailWord_4499084
  simp only [CollatzResearch.WordTrace]
  refine ⟨82047537216297262609132153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109396716288396350145509537 82047537216297262609132153)
  ·
    refine ⟨61535652912222946956849115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82047537216297262609132153 61535652912222946956849115)
    ·
      refine ⟨92303479368334420435273673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61535652912222946956849115 92303479368334420435273673)
      ·
        refine ⟨69227609526250815326455255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92303479368334420435273673 69227609526250815326455255)
        ·
          refine ⟨103841414289376222989682883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69227609526250815326455255 103841414289376222989682883)
          ·
            refine ⟨155762121434064334484524325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103841414289376222989682883 155762121434064334484524325)
            ·
              refine ⟨29205397768887062715848311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155762121434064334484524325 29205397768887062715848311)
              ·
                refine ⟨43808096653330594073772467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29205397768887062715848311 43808096653330594073772467)
                ·
                  refine ⟨65712144979995891110658701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43808096653330594073772467 65712144979995891110658701)
                  ·
                    refine ⟨24642054367498459166497013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65712144979995891110658701 24642054367498459166497013)
                    ·
                      refine ⟨2310192596952980546859095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24642054367498459166497013 2310192596952980546859095)
                      ·
                        rfl

theorem cell23_4499084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4499084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499084 prefixEnd_4499084 := by exact prefixLift 4499084
  have htrace : WordTrace (prefixWord ++ tailWord_4499084) baseStart_4499084 baseEnd_4499084 := by
    simpa [prefixWord, tailWord_4499084, baseEnd_4499084] using wordTrace_append hprefix tailTrace_4499084
  have hstable : (prefixWord ++ tailWord_4499084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499084).length < 2 ^ (prefixWord ++ tailWord_4499084).sum := by decide
  have hdescent : baseEnd_4499084 < baseStart_4499084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499161 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_4499161 : Nat := 118140960795 + 4499161 * 2 ^ 59
def prefixEnd_4499161 : Nat := 4983230072969 + 3 ^ 40 * 4499161 * 2
def baseEnd_4499161 : Nat := 2310232134963376745596241

theorem tailTrace_4499161 : CollatzResearch.WordTrace tailWord_4499161 prefixEnd_4499161 2310232134963376745596241 := by
  unfold tailWord_4499161
  simp only [CollatzResearch.WordTrace]
  refine ⟨164097882853315567368817337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109398588568877044912544891 164097882853315567368817337)
  ·
    refine ⟨123073412139986675526613003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164097882853315567368817337 123073412139986675526613003)
    ·
      refine ⟨184610118209980013289919505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123073412139986675526613003 184610118209980013289919505)
      ·
        refine ⟨138457588657485009967439629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184610118209980013289919505 138457588657485009967439629)
        ·
          refine ⟨51921595746556878737789861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138457588657485009967439629 51921595746556878737789861)
          ·
            refine ⟨9735299202479414763335599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51921595746556878737789861 9735299202479414763335599)
            ·
              refine ⟨14602948803719122145003399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9735299202479414763335599 14602948803719122145003399)
              ·
                refine ⟨21904423205578683217505099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14602948803719122145003399 21904423205578683217505099)
                ·
                  refine ⟨32856634808368024826257649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21904423205578683217505099 32856634808368024826257649)
                  ·
                    refine ⟨24642476106276018619693237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32856634808368024826257649 24642476106276018619693237)
                    ·
                      refine ⟨2310232134963376745596241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24642476106276018619693237 2310232134963376745596241)
                      ·
                        rfl

theorem cell23_4499161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_4499161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499161 prefixEnd_4499161 := by exact prefixLift 4499161
  have htrace : WordTrace (prefixWord ++ tailWord_4499161) baseStart_4499161 baseEnd_4499161 := by
    simpa [prefixWord, tailWord_4499161, baseEnd_4499161] using wordTrace_append hprefix tailTrace_4499161
  have hstable : (prefixWord ++ tailWord_4499161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499161).length < 2 ^ (prefixWord ++ tailWord_4499161).sum := by decide
  have hdescent : baseEnd_4499161 < baseStart_4499161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499191 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_4499191 : Nat := 118140960795 + 4499191 * 2 ^ 59
def prefixEnd_4499191 : Nat := 4983230072969 + 3 ^ 40 * 4499191 * 2
def baseEnd_4499191 : Nat := 2310247539383011628221103

theorem tailTrace_4499191 : CollatzResearch.WordTrace tailWord_4499191 prefixEnd_4499191 2310247539383011628221103 := by
  unfold tailWord_4499191
  simp only [CollatzResearch.WordTrace]
  refine ⟨164098977043206882492409427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109399318028804588328272951 164098977043206882492409427)
  ·
    refine ⟨246148465564810323738614141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164098977043206882492409427 246148465564810323738614141)
    ·
      refine ⟨92305674586803871401980303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246148465564810323738614141 92305674586803871401980303)
      ·
        refine ⟨138458511880205807102970455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92305674586803871401980303 138458511880205807102970455)
        ·
          refine ⟨207687767820308710654455683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138458511880205807102970455 207687767820308710654455683)
          ·
            refine ⟨311531651730463065981683525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207687767820308710654455683 311531651730463065981683525)
            ·
              refine ⟨58412184699461824871565661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 311531651730463065981683525 58412184699461824871565661)
              ·
                refine ⟨21904569262298184326837123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58412184699461824871565661 21904569262298184326837123)
                ·
                  refine ⟨32856853893447276490255685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21904569262298184326837123 32856853893447276490255685)
                  ·
                    refine ⟨6160660105021364341922941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32856853893447276490255685 6160660105021364341922941)
                    ·
                      refine ⟨2310247539383011628221103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160660105021364341922941 2310247539383011628221103)
                      ·
                        rfl

theorem cell23_4499191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_4499191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499191 prefixEnd_4499191 := by exact prefixLift 4499191
  have htrace : WordTrace (prefixWord ++ tailWord_4499191) baseStart_4499191 baseEnd_4499191 := by
    simpa [prefixWord, tailWord_4499191, baseEnd_4499191] using wordTrace_append hprefix tailTrace_4499191
  have hstable : (prefixWord ++ tailWord_4499191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499191).length < 2 ^ (prefixWord ++ tailWord_4499191).sum := by decide
  have hdescent : baseEnd_4499191 < baseStart_4499191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499208 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_4499208 : Nat := 118140960795 + 4499208 * 2 ^ 59
def prefixEnd_4499208 : Nat := 4983230072969 + 3 ^ 40 * 4499208 * 2
def baseEnd_4499208 : Nat := 2310256268554138061708525

theorem tailTrace_4499208 : CollatzResearch.WordTrace tailWord_4499208 prefixEnd_4499208 2310256268554138061708525 := by
  unfold tailWord_4499208
  simp only [CollatzResearch.WordTrace]
  refine ⟨82049798542072647197889139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109399731389430196263852185 82049798542072647197889139)
  ·
    refine ⟨123074697813108970796833709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82049798542072647197889139 123074697813108970796833709)
    ·
      refine ⟨46153011679915864048812641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123074697813108970796833709 46153011679915864048812641)
      ·
        refine ⟨34614758759936898036609481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46153011679915864048812641 34614758759936898036609481)
        ·
          refine ⟨25961069069952673527457111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34614758759936898036609481 25961069069952673527457111)
          ·
            refine ⟨38941603604929010291185667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25961069069952673527457111 38941603604929010291185667)
            ·
              refine ⟨58412405407393515436778501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38941603604929010291185667 58412405407393515436778501)
              ·
                refine ⟨10952326013886284144395969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58412405407393515436778501 10952326013886284144395969)
                ·
                  refine ⟨8214244510414713108296977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10952326013886284144395969 8214244510414713108296977)
                  ·
                    refine ⟨6160683382811034831222733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8214244510414713108296977 6160683382811034831222733)
                    ·
                      refine ⟨2310256268554138061708525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160683382811034831222733 2310256268554138061708525)
                      ·
                        rfl

theorem cell23_4499208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_4499208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499208 prefixEnd_4499208 := by exact prefixLift 4499208
  have htrace : WordTrace (prefixWord ++ tailWord_4499208) baseStart_4499208 baseEnd_4499208 := by
    simpa [prefixWord, tailWord_4499208, baseEnd_4499208] using wordTrace_append hprefix tailTrace_4499208
  have hstable : (prefixWord ++ tailWord_4499208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499208).length < 2 ^ (prefixWord ++ tailWord_4499208).sum := by decide
  have hdescent : baseEnd_4499208 < baseStart_4499208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499211 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 6]
def baseStart_4499211 : Nat := 118140960795 + 4499211 * 2 ^ 59
def prefixEnd_4499211 : Nat := 4983230072969 + 3 ^ 40 * 4499211 * 2
def baseEnd_4499211 : Nat := 256695312110677949996779

theorem tailTrace_4499211 : CollatzResearch.WordTrace tailWord_4499211 prefixEnd_4499211 256695312110677949996779 := by
  unfold tailWord_4499211
  simp only [CollatzResearch.WordTrace]
  refine ⟨164099706503134425908137487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109399804335422950605424991 164099706503134425908137487)
  ·
    refine ⟨246149559754701638862206231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164099706503134425908137487 246149559754701638862206231)
    ·
      refine ⟨369224339632052458293309347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246149559754701638862206231 369224339632052458293309347)
      ·
        refine ⟨553836509448078687439964021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369224339632052458293309347 553836509448078687439964021)
        ·
          refine ⟨51922172760757376947496627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 553836509448078687439964021 51922172760757376947496627)
          ·
            refine ⟨77883259141136065421244941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51922172760757376947496627 77883259141136065421244941)
            ·
              refine ⟨29206222177926024532966853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77883259141136065421244941 29206222177926024532966853)
              ·
                refine ⟨5476166658361129599931285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29206222177926024532966853 5476166658361129599931285)
                ·
                  refine ⟨256695312110677949996779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5476166658361129599931285 256695312110677949996779)
                  ·
                    rfl

theorem cell23_4499211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 6].length) (baseStart_4499211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499211 prefixEnd_4499211 := by exact prefixLift 4499211
  have htrace : WordTrace (prefixWord ++ tailWord_4499211) baseStart_4499211 baseEnd_4499211 := by
    simpa [prefixWord, tailWord_4499211, baseEnd_4499211] using wordTrace_append hprefix tailTrace_4499211
  have hstable : (prefixWord ++ tailWord_4499211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499211).length < 2 ^ (prefixWord ++ tailWord_4499211).sum := by decide
  have hdescent : baseEnd_4499211 < baseStart_4499211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499271 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 3, 6]
def baseStart_4499271 : Nat := 118140960795 + 4499271 * 2 ^ 59
def prefixEnd_4499271 : Nat := 4983230072969 + 3 ^ 40 * 4499271 * 2
def baseEnd_4499271 : Nat := 770096205945123771740245

theorem tailTrace_4499271 : CollatzResearch.WordTrace tailWord_4499271 prefixEnd_4499271 770096205945123771740245 := by
  unfold tailWord_4499271
  simp only [CollatzResearch.WordTrace]
  refine ⟨164101894882917056155321667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109401263255278037436881111 164101894882917056155321667)
  ·
    refine ⟨246152842324375584232982501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164101894882917056155321667 246152842324375584232982501)
    ·
      refine ⟨46153657935820422043684219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246152842324375584232982501 46153657935820422043684219)
      ·
        refine ⟨69230486903730633065526329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46153657935820422043684219 69230486903730633065526329)
        ·
          refine ⟨51922865177797974799144747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69230486903730633065526329 51922865177797974799144747)
          ·
            refine ⟨77884297766696962198717121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51922865177797974799144747 77884297766696962198717121)
            ·
              refine ⟨58413223325022721649037841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77884297766696962198717121 58413223325022721649037841)
              ·
                refine ⟨43809917493767041236778381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58413223325022721649037841 43809917493767041236778381)
                ·
                  refine ⟨16428719060162640463791893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43809917493767041236778381 16428719060162640463791893)
                  ·
                    refine ⟨770096205945123771740245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16428719060162640463791893 770096205945123771740245)
                    ·
                      rfl

theorem cell23_4499271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_4499271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499271 prefixEnd_4499271 := by exact prefixLift 4499271
  have htrace : WordTrace (prefixWord ++ tailWord_4499271) baseStart_4499271 baseEnd_4499271 := by
    simpa [prefixWord, tailWord_4499271, baseEnd_4499271] using wordTrace_append hprefix tailTrace_4499271
  have hstable : (prefixWord ++ tailWord_4499271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499271).length < 2 ^ (prefixWord ++ tailWord_4499271).sum := by decide
  have hdescent : baseEnd_4499271 < baseStart_4499271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499272 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_4499272 : Nat := 118140960795 + 4499272 * 2 ^ 59
def prefixEnd_4499272 : Nat := 4983230072969 + 3 ^ 40 * 4499272 * 2
def baseEnd_4499272 : Nat := 2310289131316025811308231

theorem tailTrace_4499272 : CollatzResearch.WordTrace tailWord_4499272 prefixEnd_4499272 2310289131316025811308231 := by
  unfold tailWord_4499272
  simp only [CollatzResearch.WordTrace]
  refine ⟨82050965677956716663054035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109401287570608955550738713 82050965677956716663054035)
  ·
    refine ⟨123076448516935074994581053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82050965677956716663054035 123076448516935074994581053)
    ·
      refine ⟨46153668193850653122967895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123076448516935074994581053 46153668193850653122967895)
      ·
        refine ⟨69230502290775979684451843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46153668193850653122967895 69230502290775979684451843)
        ·
          refine ⟨103845753436163969526677765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69230502290775979684451843 103845753436163969526677765)
          ·
            refine ⟨19471078769280744286252081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103845753436163969526677765 19471078769280744286252081)
            ·
              refine ⟨14603309076960558214689061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19471078769280744286252081 14603309076960558214689061)
              ·
                refine ⟨2738120451930104665254199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14603309076960558214689061 2738120451930104665254199)
                ·
                  refine ⟨4107180677895156997881299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738120451930104665254199 4107180677895156997881299)
                  ·
                    refine ⟨6160771016842735496821949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107180677895156997881299 6160771016842735496821949)
                    ·
                      refine ⟨2310289131316025811308231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160771016842735496821949 2310289131316025811308231)
                      ·
                        rfl

theorem cell23_4499272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_4499272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499272 prefixEnd_4499272 := by exact prefixLift 4499272
  have htrace : WordTrace (prefixWord ++ tailWord_4499272) baseStart_4499272 baseEnd_4499272 := by
    simpa [prefixWord, tailWord_4499272, baseEnd_4499272] using wordTrace_append hprefix tailTrace_4499272
  have hstable : (prefixWord ++ tailWord_4499272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499272).length < 2 ^ (prefixWord ++ tailWord_4499272).sum := by decide
  have hdescent : baseEnd_4499272 < baseStart_4499272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499292 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4499292 : Nat := 118140960795 + 4499292 * 2 ^ 59
def prefixEnd_4499292 : Nat := 4983230072969 + 3 ^ 40 * 4499292 * 2
def baseEnd_4499292 : Nat := 770099800309705244352713

theorem tailTrace_4499292 : CollatzResearch.WordTrace tailWord_4499292 prefixEnd_4499292 770099800309705244352713 := by
  unfold tailWord_4499292
  simp only [CollatzResearch.WordTrace]
  refine ⟨82051330407920488370918065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109401773877227317827890753 82051330407920488370918065)
  ·
    refine ⟨61538497805940366278188549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82051330407920488370918065 61538497805940366278188549)
    ·
      refine ⟨11538468338613818677160353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61538497805940366278188549 11538468338613818677160353)
      ·
        refine ⟨8653851253960364007870265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11538468338613818677160353 8653851253960364007870265)
        ·
          refine ⟨6490388440470273005902699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8653851253960364007870265 6490388440470273005902699)
          ·
            refine ⟨9735582660705409508854049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490388440470273005902699 9735582660705409508854049)
            ·
              refine ⟨7301686995529057131640537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735582660705409508854049 7301686995529057131640537)
              ·
                refine ⟨5476265246646792848730403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7301686995529057131640537 5476265246646792848730403)
                ·
                  refine ⟨8214397869970189273095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5476265246646792848730403 8214397869970189273095605)
                  ·
                    refine ⟨770099800309705244352713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8214397869970189273095605 770099800309705244352713)
                    ·
                      rfl

theorem cell23_4499292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4499292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499292 prefixEnd_4499292 := by exact prefixLift 4499292
  have htrace : WordTrace (prefixWord ++ tailWord_4499292) baseStart_4499292 baseEnd_4499292 := by
    simpa [prefixWord, tailWord_4499292, baseEnd_4499292] using wordTrace_append hprefix tailTrace_4499292
  have hstable : (prefixWord ++ tailWord_4499292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499292).length < 2 ^ (prefixWord ++ tailWord_4499292).sum := by decide
  have hdescent : baseEnd_4499292 < baseStart_4499292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499295 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_4499295 : Nat := 118140960795 + 4499295 * 2 ^ 59
def prefixEnd_4499295 : Nat := 4983230072969 + 3 ^ 40 * 4499295 * 2
def baseEnd_4499295 : Nat := 2310300941371079221320625

theorem tailTrace_4499295 : CollatzResearch.WordTrace tailWord_4499295 prefixEnd_4499295 2310300941371079221320625 := by
  unfold tailWord_4499295
  simp only [CollatzResearch.WordTrace]
  refine ⟨164102770234830108254195339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109401846823220072169463559 164102770234830108254195339)
  ·
    refine ⟨246154155352245162381293009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164102770234830108254195339 246154155352245162381293009)
    ·
      refine ⟨184615616514183871785969757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246154155352245162381293009 184615616514183871785969757)
      ·
        refine ⟨69230856192818951919738659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184615616514183871785969757 69230856192818951919738659)
        ·
          refine ⟨103846284289228427879607989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69230856192818951919738659 103846284289228427879607989)
          ·
            refine ⟨9735589152115165113713249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103846284289228427879607989 9735589152115165113713249)
            ·
              refine ⟨7301691864086373835284937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735589152115165113713249 7301691864086373835284937)
              ·
                refine ⟨5476268898064780376463703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7301691864086373835284937 5476268898064780376463703)
                ·
                  refine ⟨8214403347097170564695555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5476268898064780376463703 8214403347097170564695555)
                  ·
                    refine ⟨12321605020645755847043333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8214403347097170564695555 12321605020645755847043333)
                    ·
                      refine ⟨2310300941371079221320625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12321605020645755847043333 2310300941371079221320625)
                      ·
                        rfl

theorem cell23_4499295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_4499295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499295 prefixEnd_4499295 := by exact prefixLift 4499295
  have htrace : WordTrace (prefixWord ++ tailWord_4499295) baseStart_4499295 baseEnd_4499295 := by
    simpa [prefixWord, tailWord_4499295, baseEnd_4499295] using wordTrace_append hprefix tailTrace_4499295
  have hstable : (prefixWord ++ tailWord_4499295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499295).length < 2 ^ (prefixWord ++ tailWord_4499295).sum := by decide
  have hdescent : baseEnd_4499295 < baseStart_4499295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499362 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_4499362 : Nat := 118140960795 + 4499362 * 2 ^ 59
def prefixEnd_4499362 : Nat := 4983230072969 + 3 ^ 40 * 4499362 * 2
def baseEnd_4499362 : Nat := 2310335344574930459182817

theorem tailTrace_4499362 : CollatzResearch.WordTrace tailWord_4499362 prefixEnd_4499362 2310335344574930459182817 := by
  unfold tailWord_4499362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41026303481396844674221085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109403475950391585797922893 41026303481396844674221085)
  ·
    refine ⟨15384863805523816752832907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41026303481396844674221085 15384863805523816752832907)
    ·
      refine ⟨23077295708285725129249361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15384863805523816752832907 23077295708285725129249361)
      ·
        refine ⟨17307971781214293846937021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23077295708285725129249361 17307971781214293846937021)
        ·
          refine ⟨6490489417955360192601383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17307971781214293846937021 6490489417955360192601383)
          ·
            refine ⟨9735734126933040288902075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490489417955360192601383 9735734126933040288902075)
            ·
              refine ⟨14603601190399560433353113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9735734126933040288902075 14603601190399560433353113)
              ·
                refine ⟨10952700892799670325014835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14603601190399560433353113 10952700892799670325014835)
                ·
                  refine ⟨16429051339199505487522253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10952700892799670325014835 16429051339199505487522253)
                  ·
                    refine ⟨6160894252199814557820845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16429051339199505487522253 6160894252199814557820845)
                    ·
                      refine ⟨2310335344574930459182817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6160894252199814557820845 2310335344574930459182817)
                      ·
                        rfl

theorem cell23_4499362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_4499362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499362 prefixEnd_4499362 := by exact prefixLift 4499362
  have htrace : WordTrace (prefixWord ++ tailWord_4499362) baseStart_4499362 baseEnd_4499362 := by
    simpa [prefixWord, tailWord_4499362, baseEnd_4499362] using wordTrace_append hprefix tailTrace_4499362
  have hstable : (prefixWord ++ tailWord_4499362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499362).length < 2 ^ (prefixWord ++ tailWord_4499362).sum := by decide
  have hdescent : baseEnd_4499362 < baseStart_4499362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499385 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4499385 : Nat := 118140960795 + 4499385 * 2 ^ 59
def prefixEnd_4499385 : Nat := 4983230072969 + 3 ^ 40 * 4499385 * 2
def baseEnd_4499385 : Nat := 2310347154629983869195211

theorem tailTrace_4499385 : CollatzResearch.WordTrace tailWord_4499385 prefixEnd_4499385 2310347154629983869195211 := by
  unfold tailWord_4499385
  simp only [CollatzResearch.WordTrace]
  refine ⟨164106052804504053624971609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109404035203002702416647739 164106052804504053624971609)
  ·
    refine ⟨123079539603378040218728707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164106052804504053624971609 123079539603378040218728707)
    ·
      refine ⟨184619309405067060328093061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123079539603378040218728707 184619309405067060328093061)
      ·
        refine ⟨34616120513450073811517449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184619309405067060328093061 34616120513450073811517449)
        ·
          refine ⟨25962090385087555358638087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34616120513450073811517449 25962090385087555358638087)
          ·
            refine ⟨38943135577631333037957131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25962090385087555358638087 38943135577631333037957131)
            ·
              refine ⟨58414703366446999556935697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38943135577631333037957131 58414703366446999556935697)
              ·
                refine ⟨43811027524835249667701773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58414703366446999556935697 43811027524835249667701773)
                ·
                  refine ⟨16429135321813218625388165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43811027524835249667701773 16429135321813218625388165)
                  ·
                    refine ⟨3080462872839978492260281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16429135321813218625388165 3080462872839978492260281)
                    ·
                      refine ⟨2310347154629983869195211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080462872839978492260281 2310347154629983869195211)
                      ·
                        rfl

theorem cell23_4499385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4499385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499385 prefixEnd_4499385 := by exact prefixLift 4499385
  have htrace : WordTrace (prefixWord ++ tailWord_4499385) baseStart_4499385 baseEnd_4499385 := by
    simpa [prefixWord, tailWord_4499385, baseEnd_4499385] using wordTrace_append hprefix tailTrace_4499385
  have hstable : (prefixWord ++ tailWord_4499385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499385).length < 2 ^ (prefixWord ++ tailWord_4499385).sum := by decide
  have hdescent : baseEnd_4499385 < baseStart_4499385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499425 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 5]
def baseStart_4499425 : Nat := 118140960795 + 4499425 * 2 ^ 59
def prefixEnd_4499425 : Nat := 4983230072969 + 3 ^ 40 * 4499425 * 2
def baseEnd_4499425 : Nat := 256707521539573745855003

theorem tailTrace_4499425 : CollatzResearch.WordTrace tailWord_4499425 prefixEnd_4499425 256707521539573745855003 := by
  unfold tailWord_4499425
  simp only [CollatzResearch.WordTrace]
  refine ⟨164107511724359140456427729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109405007816239426970951819 164107511724359140456427729)
  ·
    refine ⟨123080633793269355342320797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164107511724359140456427729 123080633793269355342320797)
    ·
      refine ⟨46155237672476008253370299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123080633793269355342320797 46155237672476008253370299)
      ·
        refine ⟨69232856508714012380055449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46155237672476008253370299 69232856508714012380055449)
        ·
          refine ⟨51924642381535509285041587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69232856508714012380055449 51924642381535509285041587)
          ·
            refine ⟨77886963572303263927562381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51924642381535509285041587 77886963572303263927562381)
            ·
              refine ⟨29207611339613723972835893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77886963572303263927562381 29207611339613723972835893)
              ·
                refine ⟨2738213563088786622453365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29207611339613723972835893 2738213563088786622453365)
                ·
                  refine ⟨256707521539573745855003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2738213563088786622453365 256707521539573745855003)
                  ·
                    rfl

theorem cell23_4499425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 5].length) (baseStart_4499425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499425 prefixEnd_4499425 := by exact prefixLift 4499425
  have htrace : WordTrace (prefixWord ++ tailWord_4499425) baseStart_4499425 baseEnd_4499425 := by
    simpa [prefixWord, tailWord_4499425, baseEnd_4499425] using wordTrace_append hprefix tailTrace_4499425
  have hstable : (prefixWord ++ tailWord_4499425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499425).length < 2 ^ (prefixWord ++ tailWord_4499425).sum := by decide
  have hdescent : baseEnd_4499425 < baseStart_4499425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499448 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_4499448 : Nat := 118140960795 + 4499448 * 2 ^ 59
def prefixEnd_4499448 : Nat := 4983230072969 + 3 ^ 40 * 4499448 * 2
def baseEnd_4499448 : Nat := 2310379503911217122707421

theorem tailTrace_4499448 : CollatzResearch.WordTrace tailWord_4499448 prefixEnd_4499448 2310379503911217122707421 := by
  unfold tailWord_4499448
  simp only [CollatzResearch.WordTrace]
  refine ⟨82054175301637907692257499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109405567068850543589676665 82054175301637907692257499)
  ·
    refine ⟨123081262952456861538386249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82054175301637907692257499 123081262952456861538386249)
    ·
      refine ⟨92310947214342646153789687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123081262952456861538386249 92310947214342646153789687)
      ·
        refine ⟨138466420821513969230684531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92310947214342646153789687 138466420821513969230684531)
        ·
          refine ⟨207699631232270953846026797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138466420821513969230684531 207699631232270953846026797)
          ·
            refine ⟨77887361712101607692260049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207699631232270953846026797 77887361712101607692260049)
            ·
              refine ⟨58415521284076205769195037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77887361712101607692260049 58415521284076205769195037)
              ·
                refine ⟨21905820481528577163448139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58415521284076205769195037 21905820481528577163448139)
                ·
                  refine ⟨32858730722292865745172209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21905820481528577163448139 32858730722292865745172209)
                  ·
                    refine ⟨24644048041719649308879157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32858730722292865745172209 24644048041719649308879157)
                    ·
                      refine ⟨2310379503911217122707421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24644048041719649308879157 2310379503911217122707421)
                      ·
                        rfl

theorem cell23_4499448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_4499448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499448 prefixEnd_4499448 := by exact prefixLift 4499448
  have htrace : WordTrace (prefixWord ++ tailWord_4499448) baseStart_4499448 baseEnd_4499448 := by
    simpa [prefixWord, tailWord_4499448, baseEnd_4499448] using wordTrace_append hprefix tailTrace_4499448
  have hstable : (prefixWord ++ tailWord_4499448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499448).length < 2 ^ (prefixWord ++ tailWord_4499448).sum := by decide
  have hdescent : baseEnd_4499448 < baseStart_4499448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499468 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_4499468 : Nat := 118140960795 + 4499468 * 2 ^ 59
def prefixEnd_4499468 : Nat := 4983230072969 + 3 ^ 40 * 4499468 * 2
def baseEnd_4499468 : Nat := 770129924508102348152443

theorem tailTrace_4499468 : CollatzResearch.WordTrace tailWord_4499468 prefixEnd_4499468 770129924508102348152443 := by
  unfold tailWord_4499468
  simp only [CollatzResearch.WordTrace]
  refine ⟨82054540031601679400121529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109406053375468905866828705 82054540031601679400121529)
  ·
    refine ⟨61540905023701259550091147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82054540031601679400121529 61540905023701259550091147)
    ·
      refine ⟨92311357535551889325136721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61540905023701259550091147 92311357535551889325136721)
      ·
        refine ⟨69233518151663916993852541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92311357535551889325136721 69233518151663916993852541)
        ·
          refine ⟨25962569306873968872694703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69233518151663916993852541 25962569306873968872694703)
          ·
            refine ⟨38943853960310953309042055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25962569306873968872694703 38943853960310953309042055)
            ·
              refine ⟨58415780940466429963563083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38943853960310953309042055 58415780940466429963563083)
              ·
                refine ⟨87623671410699644945344625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58415780940466429963563083 87623671410699644945344625)
                ·
                  refine ⟨65717753558024733709008469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87623671410699644945344625 65717753558024733709008469)
                  ·
                    refine ⟨770129924508102348152443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65717753558024733709008469 770129924508102348152443)
                    ·
                      rfl

theorem cell23_4499468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_4499468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499468 prefixEnd_4499468 := by exact prefixLift 4499468
  have htrace : WordTrace (prefixWord ++ tailWord_4499468) baseStart_4499468 baseEnd_4499468 := by
    simpa [prefixWord, tailWord_4499468, baseEnd_4499468] using wordTrace_append hprefix tailTrace_4499468
  have hstable : (prefixWord ++ tailWord_4499468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499468).length < 2 ^ (prefixWord ++ tailWord_4499468).sum := by decide
  have hdescent : baseEnd_4499468 < baseStart_4499468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499475 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 6, 2]
def baseStart_4499475 : Nat := 118140960795 + 4499475 * 2 ^ 59
def prefixEnd_4499475 : Nat := 4983230072969 + 3 ^ 40 * 4499475 * 2
def baseEnd_4499475 : Nat := 2310393367888888517069797

theorem tailTrace_4499475 : CollatzResearch.WordTrace tailWord_4499475 prefixEnd_4499475 2310393367888888517069797 := by
  unfold tailWord_4499475
  simp only [CollatzResearch.WordTrace]
  refine ⟨164109335374177998995747879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109406223582785332663831919 164109335374177998995747879)
  ·
    refine ⟨246164003061266998493621819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164109335374177998995747879 246164003061266998493621819)
    ·
      refine ⟨369246004591900497740432729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246164003061266998493621819 369246004591900497740432729)
      ·
        refine ⟨276934503443925373305324547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369246004591900497740432729 276934503443925373305324547)
        ·
          refine ⟨415401755165888059957986821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276934503443925373305324547 415401755165888059957986821)
          ·
            refine ⟨77887829093604011242122529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 415401755165888059957986821 77887829093604011242122529)
            ·
              refine ⟨58415871820203008431591897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77887829093604011242122529 58415871820203008431591897)
              ·
                refine ⟨43811903865152256323693923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58415871820203008431591897 43811903865152256323693923)
                ·
                  refine ⟨65717855797728384485540885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43811903865152256323693923 65717855797728384485540885)
                  ·
                    refine ⟨3080524490518518022759729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65717855797728384485540885 3080524490518518022759729)
                    ·
                      refine ⟨2310393367888888517069797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080524490518518022759729 2310393367888888517069797)
                      ·
                        rfl

theorem cell23_4499475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 6, 2].length) (baseStart_4499475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499475 prefixEnd_4499475 := by exact prefixLift 4499475
  have htrace : WordTrace (prefixWord ++ tailWord_4499475) baseStart_4499475 baseEnd_4499475 := by
    simpa [prefixWord, tailWord_4499475, baseEnd_4499475] using wordTrace_append hprefix tailTrace_4499475
  have hstable : (prefixWord ++ tailWord_4499475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499475).length < 2 ^ (prefixWord ++ tailWord_4499475).sum := by decide
  have hdescent : baseEnd_4499475 < baseStart_4499475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499549 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 6]
def baseStart_4499549 : Nat := 118140960795 + 4499549 * 2 ^ 59
def prefixEnd_4499549 : Nat := 4983230072969 + 3 ^ 40 * 4499549 * 2
def baseEnd_4499549 : Nat := 256714596161924580838273

theorem tailTrace_4499549 : CollatzResearch.WordTrace tailWord_4499549 prefixEnd_4499549 256714596161924580838273 := by
  unfold tailWord_4499549
  simp only [CollatzResearch.WordTrace]
  refine ⟨164112034375909909633941701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109408022917273273089294467 164112034375909909633941701)
  ·
    refine ⟨30771006445483108056364069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164112034375909909633941701 30771006445483108056364069)
    ·
      refine ⟨5769563708528082760568263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30771006445483108056364069 5769563708528082760568263)
      ·
        refine ⟨8654345562792124140852395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769563708528082760568263 8654345562792124140852395)
        ·
          refine ⟨12981518344188186211278593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654345562792124140852395 12981518344188186211278593)
          ·
            refine ⟨9736138758141139658458945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12981518344188186211278593 9736138758141139658458945)
            ·
              refine ⟨7302104068605854743844209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9736138758141139658458945 7302104068605854743844209)
              ·
                refine ⟨5476578051454391057883157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302104068605854743844209 5476578051454391057883157)
                ·
                  refine ⟨256714596161924580838273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5476578051454391057883157 256714596161924580838273)
                  ·
                    rfl

theorem cell23_4499549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_4499549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499549 prefixEnd_4499549 := by exact prefixLift 4499549
  have htrace : WordTrace (prefixWord ++ tailWord_4499549) baseStart_4499549 baseEnd_4499549 := by
    simpa [prefixWord, tailWord_4499549, baseEnd_4499549] using wordTrace_append hprefix tailTrace_4499549
  have hstable : (prefixWord ++ tailWord_4499549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499549).length < 2 ^ (prefixWord ++ tailWord_4499549).sum := by decide
  have hdescent : baseEnd_4499549 < baseStart_4499549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499575 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 1, 6]
def baseStart_4499575 : Nat := 118140960795 + 4499575 * 2 ^ 59
def prefixEnd_4499575 : Nat := 4983230072969 + 3 ^ 40 * 4499575 * 2
def baseEnd_4499575 : Nat := 770148238651446041939779

theorem tailTrace_4499575 : CollatzResearch.WordTrace tailWord_4499575 prefixEnd_4499575 770148238651446041939779 := by
  unfold tailWord_4499575
  simp only [CollatzResearch.WordTrace]
  refine ⟨164112982673815716074388179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109408655115877144049592119 164112982673815716074388179)
  ·
    refine ⟨246169474010723574111582269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164112982673815716074388179 246169474010723574111582269)
    ·
      refine ⟨92313552754021340291843351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246169474010723574111582269 92313552754021340291843351)
      ·
        refine ⟨138470329131032010437765027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92313552754021340291843351 138470329131032010437765027)
        ·
          refine ⟨207705493696548015656647541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138470329131032010437765027 207705493696548015656647541)
          ·
            refine ⟨19472390034051376467810707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207705493696548015656647541 19472390034051376467810707)
            ·
              refine ⟨29208585051077064701716061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19472390034051376467810707 29208585051077064701716061)
              ·
                refine ⟨10953219394153899263143523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29208585051077064701716061 10953219394153899263143523)
                ·
                  refine ⟨16429829091230848894715285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10953219394153899263143523 16429829091230848894715285)
                  ·
                    refine ⟨770148238651446041939779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16429829091230848894715285 770148238651446041939779)
                    ·
                      rfl

theorem cell23_4499575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_4499575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499575 prefixEnd_4499575 := by exact prefixLift 4499575
  have htrace : WordTrace (prefixWord ++ tailWord_4499575) baseStart_4499575 baseEnd_4499575 := by
    simpa [prefixWord, tailWord_4499575, baseEnd_4499575] using wordTrace_append hprefix tailTrace_4499575
  have hstable : (prefixWord ++ tailWord_4499575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499575).length < 2 ^ (prefixWord ++ tailWord_4499575).sum := by decide
  have hdescent : baseEnd_4499575 < baseStart_4499575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499592 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_4499592 : Nat := 118140960795 + 4499592 * 2 ^ 59
def prefixEnd_4499592 : Nat := 4983230072969 + 3 ^ 40 * 4499592 * 2
def baseEnd_4499592 : Nat := 770151148375154853102253

theorem tailTrace_4499592 : CollatzResearch.WordTrace tailWord_4499592 prefixEnd_4499592 770151148375154853102253 := by
  unfold tailWord_4499592
  simp only [CollatzResearch.WordTrace]
  refine ⟨82056801357377063988878515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109409068476502751985171353 82056801357377063988878515)
  ·
    refine ⟨123085202036065595983317773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82056801357377063988878515 123085202036065595983317773)
    ·
      refine ⟨46156950763524598493744165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123085202036065595983317773 46156950763524598493744165)
      ·
        refine ⟨8654428268160862217577031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46156950763524598493744165 8654428268160862217577031)
        ·
          refine ⟨12981642402241293326365547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654428268160862217577031 12981642402241293326365547)
          ·
            refine ⟨19472463603361939989548321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12981642402241293326365547 19472463603361939989548321)
            ·
              refine ⟨14604347702521454992161241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19472463603361939989548321 14604347702521454992161241)
              ·
                refine ⟨10953260776891091244120931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14604347702521454992161241 10953260776891091244120931)
                ·
                  refine ⟨16429891165336636866181397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10953260776891091244120931 16429891165336636866181397)
                  ·
                    refine ⟨770151148375154853102253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16429891165336636866181397 770151148375154853102253)
                    ·
                      rfl

theorem cell23_4499592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_4499592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499592 prefixEnd_4499592 := by exact prefixLift 4499592
  have htrace : WordTrace (prefixWord ++ tailWord_4499592) baseStart_4499592 baseEnd_4499592 := by
    simpa [prefixWord, tailWord_4499592, baseEnd_4499592] using wordTrace_append hprefix tailTrace_4499592
  have hstable : (prefixWord ++ tailWord_4499592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499592).length < 2 ^ (prefixWord ++ tailWord_4499592).sum := by decide
  have hdescent : baseEnd_4499592 < baseStart_4499592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499602 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4499602 : Nat := 118140960795 + 4499602 * 2 ^ 59
def prefixEnd_4499602 : Nat := 4983230072969 + 3 ^ 40 * 4499602 * 2
def baseEnd_4499602 : Nat := 2310458579932009520181713

theorem tailTrace_4499602 : CollatzResearch.WordTrace tailWord_4499602 prefixEnd_4499602 2310458579932009520181713 := by
  unfold tailWord_4499602
  simp only [CollatzResearch.WordTrace]
  refine ⟨41028491861179474921405265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109409311629811933123747373 41028491861179474921405265)
  ·
    refine ⟨30771368895884606191053949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41028491861179474921405265 30771368895884606191053949)
    ·
      refine ⟨11539263335956727321645231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30771368895884606191053949 11539263335956727321645231)
      ·
        refine ⟨17308895003935090982467847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539263335956727321645231 17308895003935090982467847)
        ·
          refine ⟨25963342505902636473701771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17308895003935090982467847 25963342505902636473701771)
          ·
            refine ⟨38945013758853954710552657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25963342505902636473701771 38945013758853954710552657)
            ·
              refine ⟨29208760319140466032914493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38945013758853954710552657 29208760319140466032914493)
              ·
                refine ⟨10953285119677674762342935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29208760319140466032914493 10953285119677674762342935)
                ·
                  refine ⟨16429927679516512143514403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10953285119677674762342935 16429927679516512143514403)
                  ·
                    refine ⟨24644891519274768215271605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16429927679516512143514403 24644891519274768215271605)
                    ·
                      refine ⟨2310458579932009520181713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24644891519274768215271605 2310458579932009520181713)
                      ·
                        rfl

theorem cell23_4499602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4499602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499602 prefixEnd_4499602 := by exact prefixLift 4499602
  have htrace : WordTrace (prefixWord ++ tailWord_4499602) baseStart_4499602 baseEnd_4499602 := by
    simpa [prefixWord, tailWord_4499602, baseEnd_4499602] using wordTrace_append hprefix tailTrace_4499602
  have hstable : (prefixWord ++ tailWord_4499602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499602).length < 2 ^ (prefixWord ++ tailWord_4499602).sum := by decide
  have hdescent : baseEnd_4499602 < baseStart_4499602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499616 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2]
def baseStart_4499616 : Nat := 118140960795 + 4499616 * 2 ^ 59
def prefixEnd_4499616 : Nat := 4983230072969 + 3 ^ 40 * 4499616 * 2
def baseEnd_4499616 : Nat := 2310465768661172465406649

theorem tailTrace_4499616 : CollatzResearch.WordTrace tailWord_4499616 prefixEnd_4499616 2310465768661172465406649 := by
  unfold tailWord_4499616
  simp only [CollatzResearch.WordTrace]
  refine ⟨82057239033333590038315351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109409652044444786717753801 82057239033333590038315351)
  ·
    refine ⟨123085858550000385057473027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82057239033333590038315351 123085858550000385057473027)
    ·
      refine ⟨184628787825000577586209541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123085858550000385057473027 184628787825000577586209541)
      ·
        refine ⟨34617897717187608297414289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184628787825000577586209541 34617897717187608297414289)
        ·
          refine ⟨25963423287890706223060717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34617897717187608297414289 25963423287890706223060717)
          ·
            refine ⟨9736283732959014833647769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25963423287890706223060717 9736283732959014833647769)
            ·
              refine ⟨7302212799719261125235827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9736283732959014833647769 7302212799719261125235827)
              ·
                refine ⟨10953319199578891687853741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7302212799719261125235827 10953319199578891687853741)
                ·
                  refine ⟨4107494699842084382945153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10953319199578891687853741 4107494699842084382945153)
                  ·
                    refine ⟨3080621024881563287208865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4107494699842084382945153 3080621024881563287208865)
                    ·
                      refine ⟨2310465768661172465406649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080621024881563287208865 2310465768661172465406649)
                      ·
                        rfl

theorem cell23_4499616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_4499616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499616 prefixEnd_4499616 := by exact prefixLift 4499616
  have htrace : WordTrace (prefixWord ++ tailWord_4499616) baseStart_4499616 baseEnd_4499616 := by
    simpa [prefixWord, tailWord_4499616, baseEnd_4499616] using wordTrace_append hprefix tailTrace_4499616
  have hstable : (prefixWord ++ tailWord_4499616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499616).length < 2 ^ (prefixWord ++ tailWord_4499616).sum := by decide
  have hdescent : baseEnd_4499616 < baseStart_4499616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499626 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4499626 : Nat := 118140960795 + 4499626 * 2 ^ 59
def prefixEnd_4499626 : Nat := 4983230072969 + 3 ^ 40 * 4499626 * 2
def baseEnd_4499626 : Nat := 770156967822572475427201

theorem tailTrace_4499626 : CollatzResearch.WordTrace tailWord_4499626 prefixEnd_4499626 770156967822572475427201 := by
  unfold tailWord_4499626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41028710699157737946123683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109409895197753967856329821 41028710699157737946123683)
  ·
    refine ⟨61543066048736606919185525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41028710699157737946123683 61543066048736606919185525)
    ·
      refine ⟨5769662442069056898673643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61543066048736606919185525 5769662442069056898673643)
      ·
        refine ⟨8654493663103585348010465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769662442069056898673643 8654493663103585348010465)
        ·
          refine ⟨6490870247327689011007849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8654493663103585348010465 6490870247327689011007849)
          ·
            refine ⟨4868152685495766758255887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6490870247327689011007849 4868152685495766758255887)
            ·
              refine ⟨7302229028243650137383831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868152685495766758255887 7302229028243650137383831)
              ·
                refine ⟨10953343542365475206075747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7302229028243650137383831 10953343542365475206075747)
                ·
                  refine ⟨16430015313548212809113621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10953343542365475206075747 16430015313548212809113621)
                  ·
                    refine ⟨770156967822572475427201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16430015313548212809113621 770156967822572475427201)
                    ·
                      rfl

theorem cell23_4499626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4499626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499626 prefixEnd_4499626 := by exact prefixLift 4499626
  have htrace : WordTrace (prefixWord ++ tailWord_4499626) baseStart_4499626 baseEnd_4499626 := by
    simpa [prefixWord, tailWord_4499626, baseEnd_4499626] using wordTrace_append hprefix tailTrace_4499626
  have hstable : (prefixWord ++ tailWord_4499626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499626).length < 2 ^ (prefixWord ++ tailWord_4499626).sum := by decide
  have hdescent : baseEnd_4499626 < baseStart_4499626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499629 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_4499629 : Nat := 118140960795 + 4499629 * 2 ^ 59
def prefixEnd_4499629 : Nat := 4983230072969 + 3 ^ 40 * 4499629 * 2
def baseEnd_4499629 : Nat := 2310472443909680914544089

theorem tailTrace_4499629 : CollatzResearch.WordTrace tailWord_4499629 prefixEnd_4499629 2310472443909680914544089 := by
  unfold tailWord_4499629
  simp only [CollatzResearch.WordTrace]
  refine ⟨164114952215620083296853941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109409968143746722197902627 164114952215620083296853941)
  ·
    refine ⟨15385776770214382809080057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164114952215620083296853941 15385776770214382809080057)
    ·
      refine ⟨11539332577660787106810043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15385776770214382809080057 11539332577660787106810043)
      ·
        refine ⟨17308998866491180660215065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539332577660787106810043 17308998866491180660215065)
        ·
          refine ⟨12981749149868385495161299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17308998866491180660215065 12981749149868385495161299)
          ·
            refine ⟨19472623724802578242741949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12981749149868385495161299 19472623724802578242741949)
            ·
              refine ⟨7302233896800966841028231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19472623724802578242741949 7302233896800966841028231)
              ·
                refine ⟨10953350845201450261542347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7302233896800966841028231 10953350845201450261542347)
                ·
                  refine ⟨16430026267802175392313521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10953350845201450261542347 16430026267802175392313521)
                  ·
                    refine ⟨12322519700851631544235141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16430026267802175392313521 12322519700851631544235141)
                    ·
                      refine ⟨2310472443909680914544089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12322519700851631544235141 2310472443909680914544089)
                      ·
                        rfl

theorem cell23_4499629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_4499629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499629 prefixEnd_4499629 := by exact prefixLift 4499629
  have htrace : WordTrace (prefixWord ++ tailWord_4499629) baseStart_4499629 baseEnd_4499629 := by
    simpa [prefixWord, tailWord_4499629, baseEnd_4499629] using wordTrace_append hprefix tailTrace_4499629
  have hstable : (prefixWord ++ tailWord_4499629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499629).length < 2 ^ (prefixWord ++ tailWord_4499629).sum := by decide
  have hdescent : baseEnd_4499629 < baseStart_4499629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499632 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3]
def baseStart_4499632 : Nat := 118140960795 + 4499632 * 2 ^ 59
def prefixEnd_4499632 : Nat := 4983230072969 + 3 ^ 40 * 4499632 * 2
def baseEnd_4499632 : Nat := 2310473984351644402806575

theorem tailTrace_4499632 : CollatzResearch.WordTrace tailWord_4499632 prefixEnd_4499632 2310473984351644402806575 := by
  unfold tailWord_4499632
  simp only [CollatzResearch.WordTrace]
  refine ⟨82057530817304607404606575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109410041089739476539475433 82057530817304607404606575)
  ·
    refine ⟨123086296225956911106909863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82057530817304607404606575 123086296225956911106909863)
    ·
      refine ⟨184629444338935366660364795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123086296225956911106909863 184629444338935366660364795)
      ·
        refine ⟨276944166508403049990547193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184629444338935366660364795 276944166508403049990547193)
        ·
          refine ⟨207708124881302287492910395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276944166508403049990547193 207708124881302287492910395)
          ·
            refine ⟨311562187321953431239365593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207708124881302287492910395 311562187321953431239365593)
            ·
              refine ⟨233671640491465073429524195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311562187321953431239365593 233671640491465073429524195)
              ·
                refine ⟨350507460737197610144286293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233671640491465073429524195 350507460737197610144286293)
                ·
                  refine ⟨4107509305514034493878355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 350507460737197610144286293 4107509305514034493878355)
                  ·
                    refine ⟨6161263958271051740817533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107509305514034493878355 6161263958271051740817533)
                    ·
                      refine ⟨2310473984351644402806575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6161263958271051740817533 2310473984351644402806575)
                      ·
                        rfl

theorem cell23_4499632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_4499632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499632 prefixEnd_4499632 := by exact prefixLift 4499632
  have htrace : WordTrace (prefixWord ++ tailWord_4499632) baseStart_4499632 baseEnd_4499632 := by
    simpa [prefixWord, tailWord_4499632, baseEnd_4499632] using wordTrace_append hprefix tailTrace_4499632
  have hstable : (prefixWord ++ tailWord_4499632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499632).length < 2 ^ (prefixWord ++ tailWord_4499632).sum := by decide
  have hdescent : baseEnd_4499632 < baseStart_4499632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499655 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_4499655 : Nat := 118140960795 + 4499655 * 2 ^ 59
def prefixEnd_4499655 : Nat := 4983230072969 + 3 ^ 40 * 4499655 * 2
def baseEnd_4499655 : Nat := 2310485794406697812818969

theorem tailTrace_4499655 : CollatzResearch.WordTrace tailWord_4499655 prefixEnd_4499655 2310485794406697812818969 := by
  unfold tailWord_4499655
  simp only [CollatzResearch.WordTrace]
  refine ⟨164115900513525889737300419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109410600342350593158200279 164115900513525889737300419)
  ·
    refine ⟨246173850770288834605950629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164115900513525889737300419 246173850770288834605950629)
    ·
      refine ⟨46157597019429156488615743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246173850770288834605950629 46157597019429156488615743)
      ·
        refine ⟨69236395529143734732923615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46157597019429156488615743 69236395529143734732923615)
        ·
          refine ⟨103854593293715602099385423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69236395529143734732923615 103854593293715602099385423)
          ·
            refine ⟨155781889940573403149078135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103854593293715602099385423 155781889940573403149078135)
            ·
              refine ⟨233672834910860104723617203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155781889940573403149078135 233672834910860104723617203)
              ·
                refine ⟨350509252366290157085425805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233672834910860104723617203 350509252366290157085425805)
                ·
                  refine ⟨131440969637358808907034677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350509252366290157085425805 131440969637358808907034677)
                  ·
                    refine ⟨12322590903502388335034501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131440969637358808907034677 12322590903502388335034501)
                    ·
                      refine ⟨2310485794406697812818969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12322590903502388335034501 2310485794406697812818969)
                      ·
                        rfl

theorem cell23_4499655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_4499655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499655 prefixEnd_4499655 := by exact prefixLift 4499655
  have htrace : WordTrace (prefixWord ++ tailWord_4499655) baseStart_4499655 baseEnd_4499655 := by
    simpa [prefixWord, tailWord_4499655, baseEnd_4499655] using wordTrace_append hprefix tailTrace_4499655
  have hstable : (prefixWord ++ tailWord_4499655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499655).length < 2 ^ (prefixWord ++ tailWord_4499655).sum := by decide
  have hdescent : baseEnd_4499655 < baseStart_4499655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499659 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 1, 3, 2]
def baseStart_4499659 : Nat := 118140960795 + 4499659 * 2 ^ 59
def prefixEnd_4499659 : Nat := 4983230072969 + 3 ^ 40 * 4499659 * 2
def baseEnd_4499659 : Nat := 2310487848329315797168951

theorem tailTrace_4499659 : CollatzResearch.WordTrace tailWord_4499659 prefixEnd_4499659 2310487848329315797168951 := by
  unfold tailWord_4499659
  simp only [CollatzResearch.WordTrace]
  refine ⟨164116046405511398420446031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109410697603674265613630687 164116046405511398420446031)
  ·
    refine ⟨246174069608267097630669047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164116046405511398420446031 246174069608267097630669047)
    ·
      refine ⟨369261104412400646446003571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246174069608267097630669047 369261104412400646446003571)
      ·
        refine ⟨553891656618600969669005357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369261104412400646446003571 553891656618600969669005357)
        ·
          refine ⟨207709371231975363625877009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 553891656618600969669005357 207709371231975363625877009)
          ·
            refine ⟨155782028423981522719407757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207709371231975363625877009 155782028423981522719407757)
            ·
              refine ⟨58418260658993071019777909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155782028423981522719407757 58418260658993071019777909)
              ·
                refine ⟨5476711936780600408104179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58418260658993071019777909 5476711936780600408104179)
                ·
                  refine ⟨8215067905170900612156269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5476711936780600408104179 8215067905170900612156269)
                  ·
                    refine ⟨3080650464439087729558601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8215067905170900612156269 3080650464439087729558601)
                    ·
                      refine ⟨2310487848329315797168951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080650464439087729558601 2310487848329315797168951)
                      ·
                        rfl

theorem cell23_4499659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3, 2].length) (baseStart_4499659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499659 prefixEnd_4499659 := by exact prefixLift 4499659
  have htrace : WordTrace (prefixWord ++ tailWord_4499659) baseStart_4499659 baseEnd_4499659 := by
    simpa [prefixWord, tailWord_4499659, baseEnd_4499659] using wordTrace_append hprefix tailTrace_4499659
  have hstable : (prefixWord ++ tailWord_4499659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499659).length < 2 ^ (prefixWord ++ tailWord_4499659).sum := by decide
  have hdescent : baseEnd_4499659 < baseStart_4499659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499665 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_4499665 : Nat := 118140960795 + 4499665 * 2 ^ 59
def prefixEnd_4499665 : Nat := 4983230072969 + 3 ^ 40 * 4499665 * 2
def baseEnd_4499665 : Nat := 770163643071080924564641

theorem tailTrace_4499665 : CollatzResearch.WordTrace tailWord_4499665 prefixEnd_4499665 770163643071080924564641 := by
  unfold tailWord_4499665
  simp only [CollatzResearch.WordTrace]
  refine ⟨164116265243489661445164449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109410843495659774296776299 164116265243489661445164449)
  ·
    refine ⟨123087198932617246083873337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164116265243489661445164449 123087198932617246083873337)
    ·
      refine ⟨92315399199462934562905003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123087198932617246083873337 92315399199462934562905003)
      ·
        refine ⟨138473098799194401844357505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92315399199462934562905003 138473098799194401844357505)
        ·
          refine ⟨103854824099395801383268129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138473098799194401844357505 103854824099395801383268129)
          ·
            refine ⟨77891118074546851037451097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103854824099395801383268129 77891118074546851037451097)
            ·
              refine ⟨58418338555910138278088323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77891118074546851037451097 58418338555910138278088323)
              ·
                refine ⟨87627507833865207417132485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58418338555910138278088323 87627507833865207417132485)
                ·
                  refine ⟨16430157718849726390712341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87627507833865207417132485 16430157718849726390712341)
                  ·
                    refine ⟨770163643071080924564641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16430157718849726390712341 770163643071080924564641)
                    ·
                      rfl

theorem cell23_4499665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_4499665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499665 prefixEnd_4499665 := by exact prefixLift 4499665
  have htrace : WordTrace (prefixWord ++ tailWord_4499665) baseStart_4499665 baseEnd_4499665 := by
    simpa [prefixWord, tailWord_4499665, baseEnd_4499665] using wordTrace_append hprefix tailTrace_4499665
  have hstable : (prefixWord ++ tailWord_4499665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499665).length < 2 ^ (prefixWord ++ tailWord_4499665).sum := by decide
  have hdescent : baseEnd_4499665 < baseStart_4499665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_4499675 : Nat := 118140960795 + 4499675 * 2 ^ 59
def prefixEnd_4499675 : Nat := 4983230072969 + 3 ^ 40 * 4499675 * 2
def baseEnd_4499675 : Nat := 2310496064019787734568877

theorem tailTrace_4499675 : CollatzResearch.WordTrace tailWord_4499675 prefixEnd_4499675 2310496064019787734568877 := by
  unfold tailWord_4499675
  simp only [CollatzResearch.WordTrace]
  refine ⟨164116629973453433153028479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109411086648968955435352319 164116629973453433153028479)
  ·
    refine ⟨246174944960180149729542719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164116629973453433153028479 246174944960180149729542719)
    ·
      refine ⟨369262417440270224594314079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246174944960180149729542719 369262417440270224594314079)
      ·
        refine ⟨553893626160405336891471119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369262417440270224594314079 553893626160405336891471119)
        ·
          refine ⟨830840439240608005337206679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553893626160405336891471119 830840439240608005337206679)
          ·
            refine ⟨1246260658860912008005810019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830840439240608005337206679 1246260658860912008005810019)
            ·
              refine ⟨1869390988291368012008715029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246260658860912008005810019 1869390988291368012008715029)
              ·
                refine ⟨87627702576157875562908517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1869390988291368012008715029 87627702576157875562908517)
                ·
                  refine ⟨16430194233029601668045347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87627702576157875562908517 16430194233029601668045347)
                  ·
                    refine ⟨24645291349544402502068021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16430194233029601668045347 24645291349544402502068021)
                    ·
                      refine ⟨2310496064019787734568877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24645291349544402502068021 2310496064019787734568877)
                      ·
                        rfl

theorem cell23_4499675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_4499675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499675 prefixEnd_4499675 := by exact prefixLift 4499675
  have htrace : WordTrace (prefixWord ++ tailWord_4499675) baseStart_4499675 baseEnd_4499675 := by
    simpa [prefixWord, tailWord_4499675, baseEnd_4499675] using wordTrace_append hprefix tailTrace_4499675
  have hstable : (prefixWord ++ tailWord_4499675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499675).length < 2 ^ (prefixWord ++ tailWord_4499675).sum := by decide
  have hdescent : baseEnd_4499675 < baseStart_4499675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499683 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4499683 : Nat := 118140960795 + 4499683 * 2 ^ 59
def prefixEnd_4499683 : Nat := 4983230072969 + 3 ^ 40 * 4499683 * 2
def baseEnd_4499683 : Nat := 2310500171865023703268841

theorem tailTrace_4499683 : CollatzResearch.WordTrace tailWord_4499683 prefixEnd_4499683 2310500171865023703268841 := by
  unfold tailWord_4499683
  simp only [CollatzResearch.WordTrace]
  refine ⟨164116921757424450519319703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109411281171616300346213135 164116921757424450519319703)
  ·
    refine ⟨246175382636136675778979555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164116921757424450519319703 246175382636136675778979555)
    ·
      refine ⟨369263073954205013668469333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246175382636136675778979555 369263073954205013668469333)
      ·
        refine ⟨4327301647900840003927375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 369263073954205013668469333 4327301647900840003927375)
        ·
          refine ⟨6490952471851260005891063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327301647900840003927375 6490952471851260005891063)
          ·
            refine ⟨9736428707776890008836595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490952471851260005891063 9736428707776890008836595)
            ·
              refine ⟨14604643061665335013254893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9736428707776890008836595 14604643061665335013254893)
              ·
                refine ⟨5476741148124500629970585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14604643061665335013254893 5476741148124500629970585)
                ·
                  refine ⟨4107555861093375472477939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5476741148124500629970585 4107555861093375472477939)
                  ·
                    refine ⟨6161333791640063208716909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107555861093375472477939 6161333791640063208716909)
                    ·
                      refine ⟨2310500171865023703268841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6161333791640063208716909 2310500171865023703268841)
                      ·
                        rfl

theorem cell23_4499683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4499683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499683 prefixEnd_4499683 := by exact prefixLift 4499683
  have htrace : WordTrace (prefixWord ++ tailWord_4499683) baseStart_4499683 baseEnd_4499683 := by
    simpa [prefixWord, tailWord_4499683, baseEnd_4499683] using wordTrace_append hprefix tailTrace_4499683
  have hstable : (prefixWord ++ tailWord_4499683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499683).length < 2 ^ (prefixWord ++ tailWord_4499683).sum := by decide
  have hdescent : baseEnd_4499683 < baseStart_4499683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499705 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_4499705 : Nat := 118140960795 + 4499705 * 2 ^ 59
def prefixEnd_4499705 : Nat := 4983230072969 + 3 ^ 40 * 4499705 * 2
def baseEnd_4499705 : Nat := 2310511468439422617193739

theorem tailTrace_4499705 : CollatzResearch.WordTrace tailWord_4499705 prefixEnd_4499705 2310511468439422617193739 := by
  unfold tailWord_4499705
  simp only [CollatzResearch.WordTrace]
  refine ⟨164117724163344748276620569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109411816108896498851080379 164117724163344748276620569)
  ·
    refine ⟨123088293122508561207465427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164117724163344748276620569 123088293122508561207465427)
    ·
      refine ⟨184632439683762841811198141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123088293122508561207465427 184632439683762841811198141)
      ·
        refine ⟨69237164881411065679199303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184632439683762841811198141 69237164881411065679199303)
        ·
          refine ⟨103855747322116598518798955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69237164881411065679199303 103855747322116598518798955)
          ·
            refine ⟨155783620983174897778198433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103855747322116598518798955 155783620983174897778198433)
            ·
              refine ⟨116837715737381173333648825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155783620983174897778198433 116837715737381173333648825)
              ·
                refine ⟨87628286803035880000236619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116837715737381173333648825 87628286803035880000236619)
                ·
                  refine ⟨131442430204553820000354929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87628286803035880000236619 131442430204553820000354929)
                  ·
                    refine ⟨98581822653415365000266197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131442430204553820000354929 98581822653415365000266197)
                    ·
                      refine ⟨2310511468439422617193739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98581822653415365000266197 2310511468439422617193739)
                      ·
                        rfl

theorem cell23_4499705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_4499705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499705 prefixEnd_4499705 := by exact prefixLift 4499705
  have htrace : WordTrace (prefixWord ++ tailWord_4499705) baseStart_4499705 baseEnd_4499705 := by
    simpa [prefixWord, tailWord_4499705, baseEnd_4499705] using wordTrace_append hprefix tailTrace_4499705
  have hstable : (prefixWord ++ tailWord_4499705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499705).length < 2 ^ (prefixWord ++ tailWord_4499705).sum := by decide
  have hdescent : baseEnd_4499705 < baseStart_4499705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499729 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 5]
def baseStart_4499729 : Nat := 118140960795 + 4499729 * 2 ^ 59
def prefixEnd_4499729 : Nat := 4983230072969 + 3 ^ 40 * 4499729 * 2
def baseEnd_4499729 : Nat := 256724865775014502588181

theorem tailTrace_4499729 : CollatzResearch.WordTrace tailWord_4499729 prefixEnd_4499729 256724865775014502588181 := by
  unfold tailWord_4499729
  simp only [CollatzResearch.WordTrace]
  refine ⟨164118599515257800375494241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109412399676838533583662827 164118599515257800375494241)
  ·
    refine ⟨123088949636443350281620681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164118599515257800375494241 123088949636443350281620681)
    ·
      refine ⟨92316712227332512711215511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123088949636443350281620681 92316712227332512711215511)
      ·
        refine ⟨138475068340998769066823267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92316712227332512711215511 138475068340998769066823267)
        ·
          refine ⟨207712602511498153600234901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138475068340998769066823267 207712602511498153600234901)
          ·
            refine ⟨9736528242726475950011011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 207712602511498153600234901 9736528242726475950011011)
            ·
              refine ⟨14604792364089713925016517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9736528242726475950011011 14604792364089713925016517)
              ·
                refine ⟨2738398568266821360940597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14604792364089713925016517 2738398568266821360940597)
                ·
                  refine ⟨256724865775014502588181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2738398568266821360940597 256724865775014502588181)
                  ·
                    rfl

theorem cell23_4499729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 5].length) (baseStart_4499729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499729 prefixEnd_4499729 := by exact prefixLift 4499729
  have htrace : WordTrace (prefixWord ++ tailWord_4499729) baseStart_4499729 baseEnd_4499729 := by
    simpa [prefixWord, tailWord_4499729, baseEnd_4499729] using wordTrace_append hprefix tailTrace_4499729
  have hstable : (prefixWord ++ tailWord_4499729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499729).length < 2 ^ (prefixWord ++ tailWord_4499729).sum := by decide
  have hdescent : baseEnd_4499729 < baseStart_4499729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499779 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 2, 4, 2]
def baseStart_4499779 : Nat := 118140960795 + 4499779 * 2 ^ 59
def prefixEnd_4499779 : Nat := 4983230072969 + 3 ^ 40 * 4499779 * 2
def baseEnd_4499779 : Nat := 2310549466007855327668399

theorem tailTrace_4499779 : CollatzResearch.WordTrace tailWord_4499779 prefixEnd_4499779 2310549466007855327668399 := by
  unfold tailWord_4499779
  simp only [CollatzResearch.WordTrace]
  refine ⟨164120423165076658914814391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109413615443384439276542927 164120423165076658914814391)
  ·
    refine ⟨246180634747614988372221587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164120423165076658914814391 246180634747614988372221587)
    ·
      refine ⟨369270952121422482558332381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246180634747614988372221587 369270952121422482558332381)
      ·
        refine ⟨138476607045533430959374643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369270952121422482558332381 138476607045533430959374643)
        ·
          refine ⟨207714910568300146439061965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138476607045533430959374643 207714910568300146439061965)
          ·
            refine ⟨77893091463112554914648237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207714910568300146439061965 77893091463112554914648237)
            ·
              refine ⟨29209909298667208092993089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77893091463112554914648237 29209909298667208092993089)
              ·
                refine ⟨21907431974000406069744817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29209909298667208092993089 21907431974000406069744817)
                ·
                  refine ⟨16430573980500304552308613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21907431974000406069744817 16430573980500304552308613)
                  ·
                    refine ⟨3080732621343807103557865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16430573980500304552308613 3080732621343807103557865)
                    ·
                      refine ⟨2310549466007855327668399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080732621343807103557865 2310549466007855327668399)
                      ·
                        rfl

theorem cell23_4499779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_4499779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499779 prefixEnd_4499779 := by exact prefixLift 4499779
  have htrace : WordTrace (prefixWord ++ tailWord_4499779) baseStart_4499779 baseEnd_4499779 := by
    simpa [prefixWord, tailWord_4499779, baseEnd_4499779] using wordTrace_append hprefix tailTrace_4499779
  have hstable : (prefixWord ++ tailWord_4499779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499779).length < 2 ^ (prefixWord ++ tailWord_4499779).sum := by decide
  have hdescent : baseEnd_4499779 < baseStart_4499779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499796 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_4499796 : Nat := 118140960795 + 4499796 * 2 ^ 59
def prefixEnd_4499796 : Nat := 4983230072969 + 3 ^ 40 * 4499796 * 2
def baseEnd_4499796 : Nat := 2310558195178981761155821

theorem tailTrace_4499796 : CollatzResearch.WordTrace tailWord_4499796 prefixEnd_4499796 2310558195178981761155821 := by
  unfold tailWord_4499796
  simp only [CollatzResearch.WordTrace]
  refine ⟨82060521603007535409091621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109414028804010047212122161 82060521603007535409091621)
  ·
    refine ⟨15386347800563912889204679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82060521603007535409091621 15386347800563912889204679)
    ·
      refine ⟨23079521700845869333807019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15386347800563912889204679 23079521700845869333807019)
      ·
        refine ⟨34619282551268804000710529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23079521700845869333807019 34619282551268804000710529)
        ·
          refine ⟨25964461913451603000532897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34619282551268804000710529 25964461913451603000532897)
          ·
            refine ⟨19473346435088702250399673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25964461913451603000532897 19473346435088702250399673)
            ·
              refine ⟨14605009826316526687799755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19473346435088702250399673 14605009826316526687799755)
              ·
                refine ⟨21907514739474790031699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14605009826316526687799755 21907514739474790031699633)
                ·
                  refine ⟨16430636054606092523774725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21907514739474790031699633 16430636054606092523774725)
                  ·
                    refine ⟨3080744260238642348207761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16430636054606092523774725 3080744260238642348207761)
                    ·
                      refine ⟨2310558195178981761155821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080744260238642348207761 2310558195178981761155821)
                      ·
                        rfl

theorem cell23_4499796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_4499796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499796 prefixEnd_4499796 := by exact prefixLift 4499796
  have htrace : WordTrace (prefixWord ++ tailWord_4499796) baseStart_4499796 baseEnd_4499796 := by
    simpa [prefixWord, tailWord_4499796, baseEnd_4499796] using wordTrace_append hprefix tailTrace_4499796
  have hstable : (prefixWord ++ tailWord_4499796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499796).length < 2 ^ (prefixWord ++ tailWord_4499796).sum := by decide
  have hdescent : baseEnd_4499796 < baseStart_4499796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499866 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_4499866 : Nat := 118140960795 + 4499866 * 2 ^ 59
def prefixEnd_4499866 : Nat := 4983230072969 + 3 ^ 40 * 4499866 * 2
def baseEnd_4499866 : Nat := 770198046274932162426833

theorem tailTrace_4499866 : CollatzResearch.WordTrace tailWord_4499866 prefixEnd_4499866 770198046274932162426833 := by
  unfold tailWord_4499866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41030899078940368193307863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109415730877174315182154301 41030899078940368193307863)
  ·
    refine ⟨61546348618410552289961795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41030899078940368193307863 61546348618410552289961795)
    ·
      refine ⟨92319522927615828434942693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61546348618410552289961795 92319522927615828434942693)
      ·
        refine ⟨17309910548927967831551755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92319522927615828434942693 17309910548927967831551755)
        ·
          refine ⟨25964865823391951747327633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17309910548927967831551755 25964865823391951747327633)
          ·
            refine ⟨19473649367543963810495725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25964865823391951747327633 19473649367543963810495725)
            ·
              refine ⟨7302618512828986428935897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19473649367543963810495725 7302618512828986428935897)
              ·
                refine ⟨5476963884621739821701923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302618512828986428935897 5476963884621739821701923)
                ·
                  refine ⟨8215445826932609732552885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5476963884621739821701923 8215445826932609732552885)
                  ·
                    refine ⟨770198046274932162426833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8215445826932609732552885 770198046274932162426833)
                    ·
                      rfl

theorem cell23_4499866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_4499866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499866 prefixEnd_4499866 := by exact prefixLift 4499866
  have htrace : WordTrace (prefixWord ++ tailWord_4499866) baseStart_4499866 baseEnd_4499866 := by
    simpa [prefixWord, tailWord_4499866, baseEnd_4499866] using wordTrace_append hprefix tailTrace_4499866
  have hstable : (prefixWord ++ tailWord_4499866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499866).length < 2 ^ (prefixWord ++ tailWord_4499866).sum := by decide
  have hdescent : baseEnd_4499866 < baseStart_4499866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499879 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4499879 : Nat := 118140960795 + 4499879 * 2 ^ 59
def prefixEnd_4499879 : Nat := 4983230072969 + 3 ^ 40 * 4499879 * 2
def baseEnd_4499879 : Nat := 770200271357768312139313

theorem tailTrace_4499879 : CollatzResearch.WordTrace tailWord_4499879 prefixEnd_4499879 770200271357768312139313 := by
  unfold tailWord_4499879
  simp only [CollatzResearch.WordTrace]
  refine ⟨164124070464714375993454691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109416046976476250662303127 164124070464714375993454691)
  ·
    refine ⟨246186105697071563990182037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164124070464714375993454691 246186105697071563990182037)
    ·
      refine ⟨11539973704550229562039783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246186105697071563990182037 11539973704550229562039783)
      ·
        refine ⟨17309960556825344343059675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539973704550229562039783 17309960556825344343059675)
        ·
          refine ⟨25964940835238016514589513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17309960556825344343059675 25964940835238016514589513)
          ·
            refine ⟨19473705626428512385942135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25964940835238016514589513 19473705626428512385942135)
            ·
              refine ⟨29210558439642768578913203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19473705626428512385942135 29210558439642768578913203)
              ·
                refine ⟨43815837659464152868369805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29210558439642768578913203 43815837659464152868369805)
                ·
                  refine ⟨16430939122299057325638677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43815837659464152868369805 16430939122299057325638677)
                  ·
                    refine ⟨770200271357768312139313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16430939122299057325638677 770200271357768312139313)
                    ·
                      rfl

theorem cell23_4499879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4499879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499879 prefixEnd_4499879 := by exact prefixLift 4499879
  have htrace : WordTrace (prefixWord ++ tailWord_4499879) baseStart_4499879 baseEnd_4499879 := by
    simpa [prefixWord, tailWord_4499879, baseEnd_4499879] using wordTrace_append hprefix tailTrace_4499879
  have hstable : (prefixWord ++ tailWord_4499879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499879).length < 2 ^ (prefixWord ++ tailWord_4499879).sum := by decide
  have hdescent : baseEnd_4499879 < baseStart_4499879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499897 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4499897 : Nat := 118140960795 + 4499897 * 2 ^ 59
def prefixEnd_4499897 : Nat := 4983230072969 + 3 ^ 40 * 4499897 * 2
def baseEnd_4499897 : Nat := 2310610056725085865992857

theorem tailTrace_4499897 : CollatzResearch.WordTrace tailWord_4499897 prefixEnd_4499897 2310610056725085865992857 := by
  unfold tailWord_4499897
  simp only [CollatzResearch.WordTrace]
  refine ⟨164124726978649165067609945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109416484652432776711739963 164124726978649165067609945)
  ·
    refine ⟨123093545233986873800707459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164124726978649165067609945 123093545233986873800707459)
    ·
      refine ⟨184640317850980310701061189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123093545233986873800707459 184640317850980310701061189)
      ·
        refine ⟨34620059597058808256448973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184640317850980310701061189 34620059597058808256448973)
        ·
          refine ⟨12982522348897053096168365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34620059597058808256448973 12982522348897053096168365)
          ·
            refine ⟨4868445880836394911063137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12982522348897053096168365 4868445880836394911063137)
            ·
              refine ⟨3651334410627296183297353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4868445880836394911063137 3651334410627296183297353)
              ·
                refine ⟨2738500807970472137473015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3651334410627296183297353 2738500807970472137473015)
                ·
                  refine ⟨4107751211955708206209523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738500807970472137473015 4107751211955708206209523)
                  ·
                    refine ⟨6161626817933562309314285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107751211955708206209523 6161626817933562309314285)
                    ·
                      refine ⟨2310610056725085865992857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6161626817933562309314285 2310610056725085865992857)
                      ·
                        rfl

theorem cell23_4499897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4499897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499897 prefixEnd_4499897 := by exact prefixLift 4499897
  have htrace : WordTrace (prefixWord ++ tailWord_4499897) baseStart_4499897 baseEnd_4499897 := by
    simpa [prefixWord, tailWord_4499897, baseEnd_4499897] using wordTrace_append hprefix tailTrace_4499897
  have hstable : (prefixWord ++ tailWord_4499897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499897).length < 2 ^ (prefixWord ++ tailWord_4499897).sum := by decide
  have hdescent : baseEnd_4499897 < baseStart_4499897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499936 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3]
def baseStart_4499936 : Nat := 118140960795 + 4499936 * 2 ^ 59
def prefixEnd_4499936 : Nat := 4983230072969 + 3 ^ 40 * 4499936 * 2
def baseEnd_4499936 : Nat := 2310630082470611213405177

theorem tailTrace_4499936 : CollatzResearch.WordTrace tailWord_4499936 prefixEnd_4499936 2310630082470611213405177 := by
  unfold tailWord_4499936
  simp only [CollatzResearch.WordTrace]
  refine ⟨82063074712753937364139831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109417432950338583152186441 82063074712753937364139831)
  ·
    refine ⟨123094612069130906046209747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82063074712753937364139831 123094612069130906046209747)
    ·
      refine ⟨184641918103696359069314621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123094612069130906046209747 184641918103696359069314621)
      ·
        refine ⟨69240719288886134650992983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184641918103696359069314621 69240719288886134650992983)
        ·
          refine ⟨103861078933329201976489475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69240719288886134650992983 103861078933329201976489475)
          ·
            refine ⟨155791618399993802964734213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103861078933329201976489475 155791618399993802964734213)
            ·
              refine ⟨29210928449998838055887665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155791618399993802964734213 29210928449998838055887665)
              ·
                refine ⟨21908196337499128541915749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29210928449998838055887665 21908196337499128541915749)
                ·
                  refine ⟨4107786813281086601609203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21908196337499128541915749 4107786813281086601609203)
                  ·
                    refine ⟨6161680219921629902413805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4107786813281086601609203 6161680219921629902413805)
                    ·
                      refine ⟨2310630082470611213405177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6161680219921629902413805 2310630082470611213405177)
                      ·
                        rfl

theorem cell23_4499936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_4499936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499936 prefixEnd_4499936 := by exact prefixLift 4499936
  have htrace : WordTrace (prefixWord ++ tailWord_4499936) baseStart_4499936 baseEnd_4499936 := by
    simpa [prefixWord, tailWord_4499936, baseEnd_4499936] using wordTrace_append hprefix tailTrace_4499936
  have hstable : (prefixWord ++ tailWord_4499936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499936).length < 2 ^ (prefixWord ++ tailWord_4499936).sum := by decide
  have hdescent : baseEnd_4499936 < baseStart_4499936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499974 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4499974 : Nat := 118140960795 + 4499974 * 2 ^ 59
def prefixEnd_4499974 : Nat := 4983230072969 + 3 ^ 40 * 4499974 * 2
def baseEnd_4499974 : Nat := 2310649594735482064730003

theorem tailTrace_4499974 : CollatzResearch.WordTrace tailWord_4499974 prefixEnd_4499974 2310649594735482064730003 := by
  unfold tailWord_4499974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128985481230318975567593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109418356932913471478775317 5128985481230318975567593)
  ·
    refine ⟨3846739110922739231675695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5128985481230318975567593 3846739110922739231675695)
    ·
      refine ⟨5770108666384108847513543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846739110922739231675695 5770108666384108847513543)
      ·
        refine ⟨8655162999576163271270315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5770108666384108847513543 8655162999576163271270315)
        ·
          refine ⟨12982744499364244906905473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8655162999576163271270315 12982744499364244906905473)
          ·
            refine ⟨9737058374523183680179105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12982744499364244906905473 9737058374523183680179105)
            ·
              refine ⟨7302793780892387760134329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9737058374523183680179105 7302793780892387760134329)
              ·
                refine ⟨5477095335669290820100747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302793780892387760134329 5477095335669290820100747)
                ·
                  refine ⟨8215643003503936230151121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477095335669290820100747 8215643003503936230151121)
                  ·
                    refine ⟨6161732252627952172613341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8215643003503936230151121 6161732252627952172613341)
                    ·
                      refine ⟨2310649594735482064730003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6161732252627952172613341 2310649594735482064730003)
                      ·
                        rfl

theorem cell23_4499974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4499974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499974 prefixEnd_4499974 := by exact prefixLift 4499974
  have htrace : WordTrace (prefixWord ++ tailWord_4499974) baseStart_4499974 baseEnd_4499974 := by
    simpa [prefixWord, tailWord_4499974, baseEnd_4499974] using wordTrace_append hprefix tailTrace_4499974
  have hstable : (prefixWord ++ tailWord_4499974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499974).length < 2 ^ (prefixWord ++ tailWord_4499974).sum := by decide
  have hdescent : baseEnd_4499974 < baseStart_4499974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499980 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_4499980 : Nat := 118140960795 + 4499980 * 2 ^ 59
def prefixEnd_4499980 : Nat := 4983230072969 + 3 ^ 40 * 4499980 * 2
def baseEnd_4499980 : Nat := 2310652675619409041254975

theorem tailTrace_4499980 : CollatzResearch.WordTrace tailWord_4499980 prefixEnd_4499980 2310652675619409041254975 := by
  unfold tailWord_4499980
  simp only [CollatzResearch.WordTrace]
  refine ⟨82063877118674235121440697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109418502824898980161920929 82063877118674235121440697)
  ·
    refine ⟨61547907839005676341080523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82063877118674235121440697 61547907839005676341080523)
    ·
      refine ⟨92321861758508514511620785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61547907839005676341080523 92321861758508514511620785)
      ·
        refine ⟨69241396318881385883715589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92321861758508514511620785 69241396318881385883715589)
        ·
          refine ⟨12982761809790259853196673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69241396318881385883715589 12982761809790259853196673)
          ·
            refine ⟨9737071357342694889897505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12982761809790259853196673 9737071357342694889897505)
            ·
              refine ⟨7302803518007021167423129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9737071357342694889897505 7302803518007021167423129)
              ·
                refine ⟨5477102638505265875567347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7302803518007021167423129 5477102638505265875567347)
                ·
                  refine ⟨8215653957757898813351021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477102638505265875567347 8215653957757898813351021)
                  ·
                    refine ⟨3080870234159212055006633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8215653957757898813351021 3080870234159212055006633)
                    ·
                      refine ⟨2310652675619409041254975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080870234159212055006633 2310652675619409041254975)
                      ·
                        rfl

theorem cell23_4499980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_4499980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499980 prefixEnd_4499980 := by exact prefixLift 4499980
  have htrace : WordTrace (prefixWord ++ tailWord_4499980) baseStart_4499980 baseEnd_4499980 := by
    simpa [prefixWord, tailWord_4499980, baseEnd_4499980] using wordTrace_append hprefix tailTrace_4499980
  have hstable : (prefixWord ++ tailWord_4499980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499980).length < 2 ^ (prefixWord ++ tailWord_4499980).sum := by decide
  have hdescent : baseEnd_4499980 < baseStart_4499980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4499996 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4499996 : Nat := 118140960795 + 4499996 * 2 ^ 59
def prefixEnd_4499996 : Nat := 4983230072969 + 3 ^ 40 * 4499996 * 2
def baseEnd_4499996 : Nat := 2310660891309880978654901

theorem tailTrace_4499996 : CollatzResearch.WordTrace tailWord_4499996 prefixEnd_4499996 2310660891309880978654901 := by
  unfold tailWord_4499996
  simp only [CollatzResearch.WordTrace]
  refine ⟨82064168902645252487731921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109418891870193669983642561 82064168902645252487731921)
  ·
    refine ⟨61548126676983939365798941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82064168902645252487731921 61548126676983939365798941)
    ·
      refine ⟨23080547503868977262174603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61548126676983939365798941 23080547503868977262174603)
      ·
        refine ⟨34620821255803465893261905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23080547503868977262174603 34620821255803465893261905)
        ·
          refine ⟨25965615941852599419946429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34620821255803465893261905 25965615941852599419946429)
          ·
            refine ⟨9737105978194724782479911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25965615941852599419946429 9737105978194724782479911)
            ·
              refine ⟨14605658967292087173719867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9737105978194724782479911 14605658967292087173719867)
              ·
                refine ⟨21908488450938130760579801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14605658967292087173719867 21908488450938130760579801)
                ·
                  refine ⟨16431366338203598070434851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21908488450938130760579801 16431366338203598070434851)
                  ·
                    refine ⟨24647049507305397105652277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16431366338203598070434851 24647049507305397105652277)
                    ·
                      refine ⟨2310660891309880978654901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24647049507305397105652277 2310660891309880978654901)
                      ·
                        rfl

theorem cell23_4499996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4499996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4499996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4499996 prefixEnd_4499996 := by exact prefixLift 4499996
  have htrace : WordTrace (prefixWord ++ tailWord_4499996) baseStart_4499996 baseEnd_4499996 := by
    simpa [prefixWord, tailWord_4499996, baseEnd_4499996] using wordTrace_append hprefix tailTrace_4499996
  have hstable : (prefixWord ++ tailWord_4499996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4499996).length < 2 ^ (prefixWord ++ tailWord_4499996).sum := by decide
  have hdescent : baseEnd_4499996 < baseStart_4499996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4499996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500010 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4500010 : Nat := 118140960795 + 4500010 * 2 ^ 59
def prefixEnd_4500010 : Nat := 4983230072969 + 3 ^ 40 * 4500010 * 2
def baseEnd_4500010 : Nat := 2310668080039043923879837

theorem tailTrace_4500010 : CollatzResearch.WordTrace tailWord_4500010 prefixEnd_4500010 2310668080039043923879837 := by
  unfold tailWord_4500010
  simp only [CollatzResearch.WordTrace]
  refine ⟨41032212106809946341618371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109419232284826523577648989 41032212106809946341618371)
  ·
    refine ⟨61548318160214919512427557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41032212106809946341618371 61548318160214919512427557)
    ·
      refine ⟨11540309655040297408580167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61548318160214919512427557 11540309655040297408580167)
      ·
        refine ⟨17310464482560446112870251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11540309655040297408580167 17310464482560446112870251)
        ·
          refine ⟨25965696723840669169305377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17310464482560446112870251 25965696723840669169305377)
          ·
            refine ⟨19474272542880501876979033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25965696723840669169305377 19474272542880501876979033)
            ·
              refine ⟨14605704407160376407734275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19474272542880501876979033 14605704407160376407734275)
              ·
                refine ⟨21908556610740564611601413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14605704407160376407734275 21908556610740564611601413)
                ·
                  refine ⟨4107854364513855864675265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21908556610740564611601413 4107854364513855864675265)
                  ·
                    refine ⟨3080890773385391898506449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4107854364513855864675265 3080890773385391898506449)
                    ·
                      refine ⟨2310668080039043923879837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080890773385391898506449 2310668080039043923879837)
                      ·
                        rfl

theorem cell23_4500010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4500010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500010 prefixEnd_4500010 := by exact prefixLift 4500010
  have htrace : WordTrace (prefixWord ++ tailWord_4500010) baseStart_4500010 baseEnd_4500010 := by
    simpa [prefixWord, tailWord_4500010, baseEnd_4500010] using wordTrace_append hprefix tailTrace_4500010
  have hstable : (prefixWord ++ tailWord_4500010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500010).length < 2 ^ (prefixWord ++ tailWord_4500010).sum := by decide
  have hdescent : baseEnd_4500010 < baseStart_4500010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500016 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 5]
def baseStart_4500016 : Nat := 118140960795 + 4500016 * 2 ^ 59
def prefixEnd_4500016 : Nat := 4983230072969 + 3 ^ 40 * 4500016 * 2
def baseEnd_4500016 : Nat := 256741240102552322267201

theorem tailTrace_4500016 : CollatzResearch.WordTrace tailWord_4500016 prefixEnd_4500016 256741240102552322267201 := by
  unfold tailWord_4500016
  simp only [CollatzResearch.WordTrace]
  refine ⟨82064533632609024195595951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109419378176812032260794601 82064533632609024195595951)
  ·
    refine ⟨123096800448913536293393927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82064533632609024195595951 123096800448913536293393927)
    ·
      refine ⟨184645200673370304440090891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123096800448913536293393927 184645200673370304440090891)
      ·
        refine ⟨276967801010055456660136337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184645200673370304440090891 276967801010055456660136337)
        ·
          refine ⟨207725850757541592495102253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276967801010055456660136337 207725850757541592495102253)
          ·
            refine ⟨77897194034078097185663345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207725850757541592495102253 77897194034078097185663345)
            ·
              refine ⟨58422895525558572889247509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77897194034078097185663345 58422895525558572889247509)
              ·
                refine ⟨2738573227760558104183477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58422895525558572889247509 2738573227760558104183477)
                ·
                  refine ⟨256741240102552322267201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2738573227760558104183477 256741240102552322267201)
                  ·
                    rfl

theorem cell23_4500016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 5].length) (baseStart_4500016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500016 prefixEnd_4500016 := by exact prefixLift 4500016
  have htrace : WordTrace (prefixWord ++ tailWord_4500016) baseStart_4500016 baseEnd_4500016 := by
    simpa [prefixWord, tailWord_4500016, baseEnd_4500016] using wordTrace_append hprefix tailTrace_4500016
  have hstable : (prefixWord ++ tailWord_4500016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500016).length < 2 ^ (prefixWord ++ tailWord_4500016).sum := by decide
  have hdescent : baseEnd_4500016 < baseStart_4500016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500046 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_4500046 : Nat := 118140960795 + 4500046 * 2 ^ 59
def prefixEnd_4500046 : Nat := 4983230072969 + 3 ^ 40 * 4500046 * 2
def baseEnd_4500046 : Nat := 770228855114201927676557

theorem tailTrace_4500046 : CollatzResearch.WordTrace tailWord_4500046 prefixEnd_4500046 770228855114201927676557 := by
  unfold tailWord_4500046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20516270181888670439347999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109420107636739575676522661 20516270181888670439347999)
  ·
    refine ⟨30774405272833005659021999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20516270181888670439347999 30774405272833005659021999)
    ·
      refine ⟨46161607909249508488532999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30774405272833005659021999 46161607909249508488532999)
      ·
        refine ⟨69242411863874262732799499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46161607909249508488532999 69242411863874262732799499)
        ·
          refine ⟨103863617795811394099199249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69242411863874262732799499 103863617795811394099199249)
          ·
            refine ⟨77897713346858545574399437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103863617795811394099199249 77897713346858545574399437)
            ·
              refine ⟨29211642505071954590399789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77897713346858545574399437 29211642505071954590399789)
              ·
                refine ⟨10954365939401982971399921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29211642505071954590399789 10954365939401982971399921)
                ·
                  refine ⟨8215774454551487228549941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10954365939401982971399921 8215774454551487228549941)
                  ·
                    refine ⟨770228855114201927676557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8215774454551487228549941 770228855114201927676557)
                    ·
                      rfl

theorem cell23_4500046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_4500046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500046 prefixEnd_4500046 := by exact prefixLift 4500046
  have htrace : WordTrace (prefixWord ++ tailWord_4500046) baseStart_4500046 baseEnd_4500046 := by
    simpa [prefixWord, tailWord_4500046, baseEnd_4500046] using wordTrace_append hprefix tailTrace_4500046
  have hstable : (prefixWord ++ tailWord_4500046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500046).length < 2 ^ (prefixWord ++ tailWord_4500046).sum := by decide
  have hdescent : baseEnd_4500046 < baseStart_4500046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500100 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4500100 : Nat := 118140960795 + 4500100 * 2 ^ 59
def prefixEnd_4500100 : Nat := 4983230072969 + 3 ^ 40 * 4500100 * 2
def baseEnd_4500100 : Nat := 2310714293297948571754423

theorem tailTrace_4500100 : CollatzResearch.WordTrace tailWord_4500100 prefixEnd_4500100 2310714293297948571754423 := by
  unfold tailWord_4500100
  simp only [CollatzResearch.WordTrace]
  refine ⟨82066065498456865368624877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109421420664609153824833169 82066065498456865368624877)
  ·
    refine ⟨30774774561921324513234329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82066065498456865368624877 30774774561921324513234329)
    ·
      refine ⟨23081080921440993384925747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30774774561921324513234329 23081080921440993384925747)
      ·
        refine ⟨34621621382161490077388621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23081080921440993384925747 34621621382161490077388621)
        ·
          refine ⟨12983108018310558779020733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34621621382161490077388621 12983108018310558779020733)
          ·
            refine ⟨4868665506866459542132775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12983108018310558779020733 4868665506866459542132775)
            ·
              refine ⟨7302998260299689313199163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868665506866459542132775 7302998260299689313199163)
              ·
                refine ⟨10954497390449533969798745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7302998260299689313199163 10954497390449533969798745)
                ·
                  refine ⟨8215873042837150477349059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10954497390449533969798745 8215873042837150477349059)
                  ·
                    refine ⟨12323809564255725716023589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8215873042837150477349059 12323809564255725716023589)
                    ·
                      refine ⟨2310714293297948571754423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12323809564255725716023589 2310714293297948571754423)
                      ·
                        rfl

theorem cell23_4500100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4500100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500100 prefixEnd_4500100 := by exact prefixLift 4500100
  have htrace : WordTrace (prefixWord ++ tailWord_4500100) baseStart_4500100 baseEnd_4500100 := by
    simpa [prefixWord, tailWord_4500100, baseEnd_4500100] using wordTrace_append hprefix tailTrace_4500100
  have hstable : (prefixWord ++ tailWord_4500100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500100).length < 2 ^ (prefixWord ++ tailWord_4500100).sum := by decide
  have hdescent : baseEnd_4500100 < baseStart_4500100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500143 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 5, 2]
def baseStart_4500143 : Nat := 118140960795 + 4500143 * 2 ^ 59
def prefixEnd_4500143 : Nat := 4983230072969 + 3 ^ 40 * 4500143 * 2
def baseEnd_4500143 : Nat := 2310736372966091903516725

theorem tailTrace_4500143 : CollatzResearch.WordTrace tailWord_4500143 prefixEnd_4500143 2310736372966091903516725 := by
  unfold tailWord_4500143
  simp only [CollatzResearch.WordTrace]
  refine ⟨164133699335757949081065083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109422466223838632720710055 164133699335757949081065083)
  ·
    refine ⟨246200549003636923621597625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164133699335757949081065083 246200549003636923621597625)
    ·
      refine ⟨184650411752727692716198219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246200549003636923621597625 184650411752727692716198219)
      ·
        refine ⟨276975617629091539074297329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184650411752727692716198219 276975617629091539074297329)
        ·
          refine ⟨207731713221818654305722997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276975617629091539074297329 207731713221818654305722997)
          ·
            refine ⟨19474848114545498841161531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207731713221818654305722997 19474848114545498841161531)
            ·
              refine ⟨29212272171818248261742297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19474848114545498841161531 29212272171818248261742297)
              ·
                refine ⟨21909204128863686196306723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29212272171818248261742297 21909204128863686196306723)
                ·
                  refine ⟨32863806193295529294460085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21909204128863686196306723 32863806193295529294460085)
                  ·
                    refine ⟨3080981830621455871355633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32863806193295529294460085 3080981830621455871355633)
                    ·
                      refine ⟨2310736372966091903516725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3080981830621455871355633 2310736372966091903516725)
                      ·
                        rfl

theorem cell23_4500143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5, 2].length) (baseStart_4500143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500143 prefixEnd_4500143 := by exact prefixLift 4500143
  have htrace : WordTrace (prefixWord ++ tailWord_4500143) baseStart_4500143 baseEnd_4500143 := by
    simpa [prefixWord, tailWord_4500143, baseEnd_4500143] using wordTrace_append hprefix tailTrace_4500143
  have hstable : (prefixWord ++ tailWord_4500143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500143).length < 2 ^ (prefixWord ++ tailWord_4500143).sum := by decide
  have hdescent : baseEnd_4500143 < baseStart_4500143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500161 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4500161 : Nat := 118140960795 + 4500161 * 2 ^ 59
def prefixEnd_4500161 : Nat := 4983230072969 + 3 ^ 40 * 4500161 * 2
def baseEnd_4500161 : Nat := 770248538539290944363881

theorem tailTrace_4500161 : CollatzResearch.WordTrace tailWord_4500161 prefixEnd_4500161 770248538539290944363881 := by
  unfold tailWord_4500161
  simp only [CollatzResearch.WordTrace]
  refine ⟨164134355849692738155220337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109422903899795158770146891 164134355849692738155220337)
  ·
    refine ⟨123100766887269553616415253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164134355849692738155220337 123100766887269553616415253)
    ·
      refine ⟨5770348447840760325769465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123100766887269553616415253 5770348447840760325769465)
      ·
        refine ⟨4327761335880570244327099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5770348447840760325769465 4327761335880570244327099)
        ·
          refine ⟨6491642003820855366490649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327761335880570244327099 6491642003820855366490649)
          ·
            refine ⟨4868731502865641524867987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6491642003820855366490649 4868731502865641524867987)
            ·
              refine ⟨7303097254298462287301981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868731502865641524867987 7303097254298462287301981)
              ·
                refine ⟨2738661470361923357738243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7303097254298462287301981 2738661470361923357738243)
                ·
                  refine ⟨4107992205542885036607365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738661470361923357738243 4107992205542885036607365)
                  ·
                    refine ⟨770248538539290944363881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4107992205542885036607365 770248538539290944363881)
                    ·
                      rfl

theorem cell23_4500161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4500161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500161 prefixEnd_4500161 := by exact prefixLift 4500161
  have htrace : WordTrace (prefixWord ++ tailWord_4500161) baseStart_4500161 baseEnd_4500161 := by
    simpa [prefixWord, tailWord_4500161, baseEnd_4500161] using wordTrace_append hprefix tailTrace_4500161
  have hstable : (prefixWord ++ tailWord_4500161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500161).length < 2 ^ (prefixWord ++ tailWord_4500161).sum := by decide
  have hdescent : baseEnd_4500161 < baseStart_4500161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500176 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_4500176 : Nat := 118140960795 + 4500176 * 2 ^ 59
def prefixEnd_4500176 : Nat := 4983230072969 + 3 ^ 40 * 4500176 * 2
def baseEnd_4500176 : Nat := 2310753317827690274404073

theorem tailTrace_4500176 : CollatzResearch.WordTrace tailWord_4500176 prefixEnd_4500176 2310753317827690274404073 := by
  unfold tailWord_4500176
  simp only [CollatzResearch.WordTrace]
  refine ⟨82067451472319197858508191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109423268629758930478010921 82067451472319197858508191)
  ·
    refine ⟨123101177208478796787762287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82067451472319197858508191 123101177208478796787762287)
    ·
      refine ⟨184651765812718195181643431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123101177208478796787762287 184651765812718195181643431)
      ·
        refine ⟨276977648719077292772465147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184651765812718195181643431 276977648719077292772465147)
        ·
          refine ⟨415466473078615939158697721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276977648719077292772465147 415466473078615939158697721)
          ·
            refine ⟨311599854808961954369023291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415466473078615939158697721 311599854808961954369023291)
            ·
              refine ⟨467399782213442931553534937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311599854808961954369023291 467399782213442931553534937)
              ·
                refine ⟨350549836660082198665151203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467399782213442931553534937 350549836660082198665151203)
                ·
                  refine ⟨525824754990123297997726805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350549836660082198665151203 525824754990123297997726805)
                  ·
                    refine ⟨6162008847540507398410861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 525824754990123297997726805 6162008847540507398410861)
                    ·
                      refine ⟨2310753317827690274404073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162008847540507398410861 2310753317827690274404073)
                      ·
                        rfl

theorem cell23_4500176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_4500176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500176 prefixEnd_4500176 := by exact prefixLift 4500176
  have htrace : WordTrace (prefixWord ++ tailWord_4500176) baseStart_4500176 baseEnd_4500176 := by
    simpa [prefixWord, tailWord_4500176, baseEnd_4500176] using wordTrace_append hprefix tailTrace_4500176
  have hstable : (prefixWord ++ tailWord_4500176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500176).length < 2 ^ (prefixWord ++ tailWord_4500176).sum := by decide
  have hdescent : baseEnd_4500176 < baseStart_4500176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500183 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 4, 4]
def baseStart_4500183 : Nat := 118140960795 + 4500183 * 2 ^ 59
def prefixEnd_4500183 : Nat := 4983230072969 + 3 ^ 40 * 4500183 * 2
def baseEnd_4500183 : Nat := 770252304064090582338847

theorem tailTrace_4500183 : CollatzResearch.WordTrace tailWord_4500183 prefixEnd_4500183 770252304064090582338847 := by
  unfold tailWord_4500183
  simp only [CollatzResearch.WordTrace]
  refine ⟨164135158255613035912521203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109423438837075357275014135 164135158255613035912521203)
  ·
    refine ⟨246202737383419553868781805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164135158255613035912521203 246202737383419553868781805)
    ·
      refine ⟨92326026518782332700793177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246202737383419553868781805 92326026518782332700793177)
      ·
        refine ⟨69244519889086749525594883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92326026518782332700793177 69244519889086749525594883)
        ·
          refine ⟨103866779833630124288392325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69244519889086749525594883 103866779833630124288392325)
          ·
            refine ⟨19475021218805648304073561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103866779833630124288392325 19475021218805648304073561)
            ·
              refine ⟨14606265914104236228055171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19475021218805648304073561 14606265914104236228055171)
              ·
                refine ⟨21909398871156354342082757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14606265914104236228055171 21909398871156354342082757)
                ·
                  refine ⟨4108012288341816439140517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21909398871156354342082757 4108012288341816439140517)
                  ·
                    refine ⟨770252304064090582338847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108012288341816439140517 770252304064090582338847)
                    ·
                      rfl

theorem cell23_4500183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_4500183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500183 prefixEnd_4500183 := by exact prefixLift 4500183
  have htrace : WordTrace (prefixWord ++ tailWord_4500183) baseStart_4500183 baseEnd_4500183 := by
    simpa [prefixWord, tailWord_4500183, baseEnd_4500183] using wordTrace_append hprefix tailTrace_4500183
  have hstable : (prefixWord ++ tailWord_4500183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500183).length < 2 ^ (prefixWord ++ tailWord_4500183).sum := by decide
  have hdescent : baseEnd_4500183 < baseStart_4500183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500184 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 1, 1, 3]
def baseStart_4500184 : Nat := 118140960795 + 4500184 * 2 ^ 59
def prefixEnd_4500184 : Nat := 4983230072969 + 3 ^ 40 * 4500184 * 2
def baseEnd_4500184 : Nat := 2310757425672926243104037

theorem tailTrace_4500184 : CollatzResearch.WordTrace tailWord_4500184 prefixEnd_4500184 2310757425672926243104037 := by
  unfold tailWord_4500184
  simp only [CollatzResearch.WordTrace]
  refine ⟨82067597364304706541653803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109423463152406275388871737 82067597364304706541653803)
  ·
    refine ⟨123101396046457059812480705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82067597364304706541653803 123101396046457059812480705)
    ·
      refine ⟨92326047034842794859360529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123101396046457059812480705 92326047034842794859360529)
      ·
        refine ⟨69244535276132096144520397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92326047034842794859360529 69244535276132096144520397)
        ·
          refine ⟨25966700728549536054195149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69244535276132096144520397 25966700728549536054195149)
          ·
            refine ⟨9737512773206076020323181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25966700728549536054195149 9737512773206076020323181)
            ·
              refine ⟨3651567289952278507621193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9737512773206076020323181 3651567289952278507621193)
              ·
                refine ⟨2738675467464208880715895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3651567289952278507621193 2738675467464208880715895)
                ·
                  refine ⟨4108013201196313321073843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738675467464208880715895 4108013201196313321073843)
                  ·
                    refine ⟨6162019801794469981610765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108013201196313321073843 6162019801794469981610765)
                    ·
                      refine ⟨2310757425672926243104037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162019801794469981610765 2310757425672926243104037)
                      ·
                        rfl

theorem cell23_4500184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_4500184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500184 prefixEnd_4500184 := by exact prefixLift 4500184
  have htrace : WordTrace (prefixWord ++ tailWord_4500184) baseStart_4500184 baseEnd_4500184 := by
    simpa [prefixWord, tailWord_4500184, baseEnd_4500184] using wordTrace_append hprefix tailTrace_4500184
  have hstable : (prefixWord ++ tailWord_4500184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500184).length < 2 ^ (prefixWord ++ tailWord_4500184).sum := by decide
  have hdescent : baseEnd_4500184 < baseStart_4500184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500186 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4500186 : Nat := 118140960795 + 4500186 * 2 ^ 59
def prefixEnd_4500186 : Nat := 4983230072969 + 3 ^ 40 * 4500186 * 2
def baseEnd_4500186 : Nat := 2310758452634235235279027

theorem tailTrace_4500186 : CollatzResearch.WordTrace tailWord_4500186 prefixEnd_4500186 2310758452634235235279027 := by
  unfold tailWord_4500186
  simp only [CollatzResearch.WordTrace]
  refine ⟨41033816918650541856220103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109423511783068111616586941 41033816918650541856220103)
  ·
    refine ⟨61550725377975812784330155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41033816918650541856220103 61550725377975812784330155)
    ·
      refine ⟨92326088066963719176495233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61550725377975812784330155 92326088066963719176495233)
      ·
        refine ⟨69244566050222789382371425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92326088066963719176495233 69244566050222789382371425)
        ·
          refine ⟨51933424537667092036778569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69244566050222789382371425 51933424537667092036778569)
          ·
            refine ⟨38950068403250319027583927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51933424537667092036778569 38950068403250319027583927)
            ·
              refine ⟨58425102604875478541375891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38950068403250319027583927 58425102604875478541375891)
              ·
                refine ⟨87637653907313217812063837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58425102604875478541375891 87637653907313217812063837)
                ·
                  refine ⟨32864120215242456679523939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87637653907313217812063837 32864120215242456679523939)
                  ·
                    refine ⟨49296180322863685019285909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32864120215242456679523939 49296180322863685019285909)
                    ·
                      refine ⟨2310758452634235235279027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49296180322863685019285909 2310758452634235235279027)
                      ·
                        rfl

theorem cell23_4500186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4500186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500186 prefixEnd_4500186 := by exact prefixLift 4500186
  have htrace : WordTrace (prefixWord ++ tailWord_4500186) baseStart_4500186 baseEnd_4500186 := by
    simpa [prefixWord, tailWord_4500186, baseEnd_4500186] using wordTrace_append hprefix tailTrace_4500186
  have hstable : (prefixWord ++ tailWord_4500186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500186).length < 2 ^ (prefixWord ++ tailWord_4500186).sum := by decide
  have hdescent : baseEnd_4500186 < baseStart_4500186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500193 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_4500193 : Nat := 118140960795 + 4500193 * 2 ^ 59
def prefixEnd_4500193 : Nat := 4983230072969 + 3 ^ 40 * 4500193 * 2
def baseEnd_4500193 : Nat := 2310762046998816707891495

theorem tailTrace_4500193 : CollatzResearch.WordTrace tailWord_4500193 prefixEnd_4500193 2310762046998816707891495 := by
  unfold tailWord_4500193
  simp only [CollatzResearch.WordTrace]
  refine ⟨164135522985576807620385233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109423681990384538413590155 164135522985576807620385233)
  ·
    refine ⟨123101642239182605715288925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164135522985576807620385233 123101642239182605715288925)
    ·
      refine ⟨46163115839693477143233347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123101642239182605715288925 46163115839693477143233347)
      ·
        refine ⟨69244673759540215714850021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46163115839693477143233347 69244673759540215714850021)
        ·
          refine ⟨12983376329913790446534379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69244673759540215714850021 12983376329913790446534379)
          ·
            refine ⟨19475064494870685669801569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12983376329913790446534379 19475064494870685669801569)
            ·
              refine ⟨14606298371153014252351177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19475064494870685669801569 14606298371153014252351177)
              ·
                refine ⟨10954723778364760689263383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14606298371153014252351177 10954723778364760689263383)
                ·
                  refine ⟨16432085667547141033895075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10954723778364760689263383 16432085667547141033895075)
                  ·
                    refine ⟨24648128501320711550842613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16432085667547141033895075 24648128501320711550842613)
                    ·
                      refine ⟨2310762046998816707891495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24648128501320711550842613 2310762046998816707891495)
                      ·
                        rfl

theorem cell23_4500193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_4500193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500193 prefixEnd_4500193 := by exact prefixLift 4500193
  have htrace : WordTrace (prefixWord ++ tailWord_4500193) baseStart_4500193 baseEnd_4500193 := by
    simpa [prefixWord, tailWord_4500193, baseEnd_4500193] using wordTrace_append hprefix tailTrace_4500193
  have hstable : (prefixWord ++ tailWord_4500193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500193).length < 2 ^ (prefixWord ++ tailWord_4500193).sum := by decide
  have hdescent : baseEnd_4500193 < baseStart_4500193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500196 : List Nat := [2, 3, 1, 1, 1, 4, 1, 10]
def baseStart_4500196 : Nat := 118140960795 + 4500196 * 2 ^ 59
def prefixEnd_4500196 : Nat := 4983230072969 + 3 ^ 40 * 4500196 * 2
def baseEnd_4500196 : Nat := 85583836571880748005703

theorem tailTrace_4500196 : CollatzResearch.WordTrace tailWord_4500196 prefixEnd_4500196 85583836571880748005703 := by
  unfold tailWord_4500196
  simp only [CollatzResearch.WordTrace]
  refine ⟨82067816202282969566372221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109423754936377292755162961 82067816202282969566372221)
  ·
    refine ⟨30775431075856113587389583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82067816202282969566372221 30775431075856113587389583)
    ·
      refine ⟨46163146613784170381084375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30775431075856113587389583 46163146613784170381084375)
      ·
        refine ⟨69244719920676255571626563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46163146613784170381084375 69244719920676255571626563)
        ·
          refine ⟨103867079881014383357439845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69244719920676255571626563 103867079881014383357439845)
          ·
            refine ⟨19475077477690196879519971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103867079881014383357439845 19475077477690196879519971)
            ·
              refine ⟨29212616216535295319279957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19475077477690196879519971 29212616216535295319279957)
              ·
                refine ⟨85583836571880748005703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29212616216535295319279957 85583836571880748005703)
                ·
                  rfl

theorem cell23_4500196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 10].length) (baseStart_4500196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500196 prefixEnd_4500196 := by exact prefixLift 4500196
  have htrace : WordTrace (prefixWord ++ tailWord_4500196) baseStart_4500196 baseEnd_4500196 := by
    simpa [prefixWord, tailWord_4500196, baseEnd_4500196] using wordTrace_append hprefix tailTrace_4500196
  have hstable : (prefixWord ++ tailWord_4500196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500196).length < 2 ^ (prefixWord ++ tailWord_4500196).sum := by decide
  have hdescent : baseEnd_4500196 < baseStart_4500196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500210 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4500210 : Nat := 118140960795 + 4500210 * 2 ^ 59
def prefixEnd_4500210 : Nat := 4983230072969 + 3 ^ 40 * 4500210 * 2
def baseEnd_4500210 : Nat := 2310770776169943141378917

theorem tailTrace_4500210 : CollatzResearch.WordTrace tailWord_4500210 prefixEnd_4500210 2310770776169943141378917 := by
  unfold tailWord_4500210
  simp only [CollatzResearch.WordTrace]
  refine ⟨41034035756628804880938521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109424095351010146349169389 41034035756628804880938521)
  ·
    refine ⟨30775526817471603660703891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41034035756628804880938521 30775526817471603660703891)
    ·
      refine ⟨46163290226207405491055837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30775526817471603660703891 46163290226207405491055837)
      ·
        refine ⟨17311233834827777059145939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46163290226207405491055837 17311233834827777059145939)
        ·
          refine ⟨25966850752241665588718909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17311233834827777059145939 25966850752241665588718909)
          ·
            refine ⟨9737569032090624595769591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25966850752241665588718909 9737569032090624595769591)
            ·
              refine ⟨14606353548135936893654387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9737569032090624595769591 14606353548135936893654387)
              ·
                refine ⟨21909530322203905340481581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14606353548135936893654387 21909530322203905340481581)
                ·
                  refine ⟨8216073870826464502680593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21909530322203905340481581 8216073870826464502680593)
                  ·
                    refine ⟨6162055403119848377010445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8216073870826464502680593 6162055403119848377010445)
                    ·
                      refine ⟨2310770776169943141378917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162055403119848377010445 2310770776169943141378917)
                      ·
                        rfl

theorem cell23_4500210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4500210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500210 prefixEnd_4500210 := by exact prefixLift 4500210
  have htrace : WordTrace (prefixWord ++ tailWord_4500210) baseStart_4500210 baseEnd_4500210 := by
    simpa [prefixWord, tailWord_4500210, baseEnd_4500210] using wordTrace_append hprefix tailTrace_4500210
  have hstable : (prefixWord ++ tailWord_4500210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500210).length < 2 ^ (prefixWord ++ tailWord_4500210).sum := by decide
  have hdescent : baseEnd_4500210 < baseStart_4500210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500250 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_4500250 : Nat := 118140960795 + 4500250 * 2 ^ 59
def prefixEnd_4500250 : Nat := 4983230072969 + 3 ^ 40 * 4500250 * 2
def baseEnd_4500250 : Nat := 2310791315396122984878733

theorem tailTrace_4500250 : CollatzResearch.WordTrace tailWord_4500250 prefixEnd_4500250 2310791315396122984878733 := by
  unfold tailWord_4500250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41034400486592576588802551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109425067964246870903473469 41034400486592576588802551)
  ·
    refine ⟨61551600729888864883203827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41034400486592576588802551 61551600729888864883203827)
    ·
      refine ⟨92327401094833297324805741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61551600729888864883203827 92327401094833297324805741)
      ·
        refine ⟨34622775410562486496802153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92327401094833297324805741 34622775410562486496802153)
        ·
          refine ⟨25967081557921864872601615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34622775410562486496802153 25967081557921864872601615)
          ·
            refine ⟨38950622336882797308902423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25967081557921864872601615 38950622336882797308902423)
            ·
              refine ⟨58425933505324195963353635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38950622336882797308902423 58425933505324195963353635)
              ·
                refine ⟨87638900257986293945030453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58425933505324195963353635 87638900257986293945030453)
                ·
                  refine ⟨8216146899186215057346605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87638900257986293945030453 8216146899186215057346605)
                  ·
                    refine ⟨3081055087194830646504977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8216146899186215057346605 3081055087194830646504977)
                    ·
                      refine ⟨2310791315396122984878733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081055087194830646504977 2310791315396122984878733)
                      ·
                        rfl

theorem cell23_4500250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_4500250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500250 prefixEnd_4500250 := by exact prefixLift 4500250
  have htrace : WordTrace (prefixWord ++ tailWord_4500250) baseStart_4500250 baseEnd_4500250 := by
    simpa [prefixWord, tailWord_4500250, baseEnd_4500250] using wordTrace_append hprefix tailTrace_4500250
  have hstable : (prefixWord ++ tailWord_4500250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500250).length < 2 ^ (prefixWord ++ tailWord_4500250).sum := by decide
  have hdescent : baseEnd_4500250 < baseStart_4500250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500278 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4500278 : Nat := 118140960795 + 4500278 * 2 ^ 59
def prefixEnd_4500278 : Nat := 4983230072969 + 3 ^ 40 * 4500278 * 2
def baseEnd_4500278 : Nat := 2310805692854448875328605

theorem tailTrace_4500278 : CollatzResearch.WordTrace tailWord_4500278 prefixEnd_4500278 2310805692854448875328605 := by
  unfold tailWord_4500278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258663949391804196076843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109425748793512578091486325 10258663949391804196076843)
  ·
    refine ⟨15387995924087706294115265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258663949391804196076843 15387995924087706294115265)
    ·
      refine ⟨11540996943065779720586449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15387995924087706294115265 11540996943065779720586449)
      ·
        refine ⟨8655747707299334790439837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11540996943065779720586449 8655747707299334790439837)
        ·
          refine ⟨3245905390237250546414939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8655747707299334790439837 3245905390237250546414939)
          ·
            refine ⟨4868858085355875819622409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245905390237250546414939 4868858085355875819622409)
            ·
              refine ⟨3651643564016906864716807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4868858085355875819622409 3651643564016906864716807)
              ·
                refine ⟨5477465346025360297075211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3651643564016906864716807 5477465346025360297075211)
                ·
                  refine ⟨8216198019038040445612817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477465346025360297075211 8216198019038040445612817)
                  ·
                    refine ⟨6162148514278530334209613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8216198019038040445612817 6162148514278530334209613)
                    ·
                      refine ⟨2310805692854448875328605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162148514278530334209613 2310805692854448875328605)
                      ·
                        rfl

theorem cell23_4500278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4500278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500278 prefixEnd_4500278 := by exact prefixLift 4500278
  have htrace : WordTrace (prefixWord ++ tailWord_4500278) baseStart_4500278 baseEnd_4500278 := by
    simpa [prefixWord, tailWord_4500278, baseEnd_4500278] using wordTrace_append hprefix tailTrace_4500278
  have hstable : (prefixWord ++ tailWord_4500278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500278).length < 2 ^ (prefixWord ++ tailWord_4500278).sum := by decide
  have hdescent : baseEnd_4500278 < baseStart_4500278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500280 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_4500280 : Nat := 118140960795 + 4500280 * 2 ^ 59
def prefixEnd_4500280 : Nat := 4983230072969 + 3 ^ 40 * 4500280 * 2
def baseEnd_4500280 : Nat := 2310806719815757867503595

theorem tailTrace_4500280 : CollatzResearch.WordTrace tailWord_4500280 prefixEnd_4500280 2310806719815757867503595 := by
  unfold tailWord_4500280
  simp only [CollatzResearch.WordTrace]
  refine ⟨82069348068130810739401147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109425797424174414319201529 82069348068130810739401147)
  ·
    refine ⟨123104022102196216109101721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82069348068130810739401147 123104022102196216109101721)
    ·
      refine ⟨92328016576647162081826291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123104022102196216109101721 92328016576647162081826291)
      ·
        refine ⟨138492024864970743122739437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92328016576647162081826291 138492024864970743122739437)
        ·
          refine ⟨51934509324364028671027289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138492024864970743122739437 51934509324364028671027289)
          ·
            refine ⟨38950881993273021503270467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51934509324364028671027289 38950881993273021503270467)
            ·
              refine ⟨58426322989909532254905701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38950881993273021503270467 58426322989909532254905701)
              ·
                refine ⟨10954935560608037297794819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58426322989909532254905701 10954935560608037297794819)
                ·
                  refine ⟨16432403340912055946692229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10954935560608037297794819 16432403340912055946692229)
                  ·
                    refine ⟨3081075626421010490004793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16432403340912055946692229 3081075626421010490004793)
                    ·
                      refine ⟨2310806719815757867503595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081075626421010490004793 2310806719815757867503595)
                      ·
                        rfl

theorem cell23_4500280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_4500280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500280 prefixEnd_4500280 := by exact prefixLift 4500280
  have htrace : WordTrace (prefixWord ++ tailWord_4500280) baseStart_4500280 baseEnd_4500280 := by
    simpa [prefixWord, tailWord_4500280, baseEnd_4500280] using wordTrace_append hprefix tailTrace_4500280
  have hstable : (prefixWord ++ tailWord_4500280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500280).length < 2 ^ (prefixWord ++ tailWord_4500280).sum := by decide
  have hdescent : baseEnd_4500280 < baseStart_4500280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500297 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 4, 2, 2]
def baseStart_4500297 : Nat := 118140960795 + 4500297 * 2 ^ 59
def prefixEnd_4500297 : Nat := 4983230072969 + 3 ^ 40 * 4500297 * 2
def baseEnd_4500297 : Nat := 2310815448986884300991017

theorem tailTrace_4500297 : CollatzResearch.WordTrace tailWord_4500297 prefixEnd_4500297 2310815448986884300991017 := by
  unfold tailWord_4500297
  simp only [CollatzResearch.WordTrace]
  refine ⟨164139316177200033382171145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109426210784800022254780763 164139316177200033382171145)
  ·
    refine ⟨123104487132900025036628359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164139316177200033382171145 123104487132900025036628359)
    ·
      refine ⟨184656730699350037554942539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123104487132900025036628359 184656730699350037554942539)
      ·
        refine ⟨276985096049025056332413809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184656730699350037554942539 276985096049025056332413809)
        ·
          refine ⟨207738822036768792249310357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276985096049025056332413809 207738822036768792249310357)
          ·
            refine ⟨9737757282973537136686423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 207738822036768792249310357 9737757282973537136686423)
            ·
              refine ⟨14606635924460305705029635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9737757282973537136686423 14606635924460305705029635)
              ·
                refine ⟨21909953886690458557544453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14606635924460305705029635 21909953886690458557544453)
                ·
                  refine ⟨4108116353754460979539585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21909953886690458557544453 4108116353754460979539585)
                  ·
                    refine ⟨3081087265315845734654689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108116353754460979539585 3081087265315845734654689)
                    ·
                      refine ⟨2310815448986884300991017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081087265315845734654689 2310815448986884300991017)
                      ·
                        rfl

theorem cell23_4500297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 2, 2].length) (baseStart_4500297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500297 prefixEnd_4500297 := by exact prefixLift 4500297
  have htrace : WordTrace (prefixWord ++ tailWord_4500297) baseStart_4500297 baseEnd_4500297 := by
    simpa [prefixWord, tailWord_4500297, baseEnd_4500297] using wordTrace_append hprefix tailTrace_4500297
  have hstable : (prefixWord ++ tailWord_4500297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500297).length < 2 ^ (prefixWord ++ tailWord_4500297).sum := by decide
  have hdescent : baseEnd_4500297 < baseStart_4500297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500337 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 5]
def baseStart_4500337 : Nat := 118140960795 + 4500337 * 2 ^ 59
def prefixEnd_4500337 : Nat := 4983230072969 + 3 ^ 40 * 4500337 * 2
def baseEnd_4500337 : Nat := 256759554245896016054537

theorem tailTrace_4500337 : CollatzResearch.WordTrace tailWord_4500337 prefixEnd_4500337 256759554245896016054537 := by
  unfold tailWord_4500337
  simp only [CollatzResearch.WordTrace]
  refine ⟨164140775097055120213627265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109427183398036746809084843 164140775097055120213627265)
  ·
    refine ⟨123105581322791340160220449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164140775097055120213627265 123105581322791340160220449)
    ·
      refine ⟨92329185992093505120165337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123105581322791340160220449 92329185992093505120165337)
      ·
        refine ⟨69246889494070128840124003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92329185992093505120165337 69246889494070128840124003)
        ·
          refine ⟨103870334241105193260186005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69246889494070128840124003 103870334241105193260186005)
          ·
            refine ⟨4868921917551805934071219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103870334241105193260186005 4868921917551805934071219)
            ·
              refine ⟨7303382876327708901106829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868921917551805934071219 7303382876327708901106829)
              ·
                refine ⟨2738768578622890837915061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7303382876327708901106829 2738768578622890837915061)
                ·
                  refine ⟨256759554245896016054537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2738768578622890837915061 256759554245896016054537)
                  ·
                    rfl

theorem cell23_4500337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 5].length) (baseStart_4500337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500337 prefixEnd_4500337 := by exact prefixLift 4500337
  have htrace : WordTrace (prefixWord ++ tailWord_4500337) baseStart_4500337 baseEnd_4500337 := by
    simpa [prefixWord, tailWord_4500337, baseEnd_4500337] using wordTrace_append hprefix tailTrace_4500337
  have hstable : (prefixWord ++ tailWord_4500337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500337).length < 2 ^ (prefixWord ++ tailWord_4500337).sum := by decide
  have hdescent : baseEnd_4500337 < baseStart_4500337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500360 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4500360 : Nat := 118140960795 + 4500360 * 2 ^ 59
def prefixEnd_4500360 : Nat := 4983230072969 + 3 ^ 40 * 4500360 * 2
def baseEnd_4500360 : Nat := 2310847798268117554503227

theorem tailTrace_4500360 : CollatzResearch.WordTrace tailWord_4500360 prefixEnd_4500360 2310847798268117554503227 := by
  unfold tailWord_4500360
  simp only [CollatzResearch.WordTrace]
  refine ⟨82070806987985897570857267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109427742650647863427809689 82070806987985897570857267)
  ·
    refine ⟨123106210481978846356285901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82070806987985897570857267 123106210481978846356285901)
    ·
      refine ⟨46164828930742067383607213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123106210481978846356285901 46164828930742067383607213)
      ·
        refine ⟨17311810849028275268852705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46164828930742067383607213 17311810849028275268852705)
        ·
          refine ⟨12983858136771206451639529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17311810849028275268852705 12983858136771206451639529)
          ·
            refine ⟨9737893602578404838729647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12983858136771206451639529 9737893602578404838729647)
            ·
              refine ⟨14606840403867607258094471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9737893602578404838729647 14606840403867607258094471)
              ·
                refine ⟨21910260605801410887141707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14606840403867607258094471 21910260605801410887141707)
                ·
                  refine ⟨32865390908702116330712561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21910260605801410887141707 32865390908702116330712561)
                  ·
                    refine ⟨24649043181526587248034421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32865390908702116330712561 24649043181526587248034421)
                    ·
                      refine ⟨2310847798268117554503227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24649043181526587248034421 2310847798268117554503227)
                      ·
                        rfl

theorem cell23_4500360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4500360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500360 prefixEnd_4500360 := by exact prefixLift 4500360
  have htrace : WordTrace (prefixWord ++ tailWord_4500360) baseStart_4500360 baseEnd_4500360 := by
    simpa [prefixWord, tailWord_4500360, baseEnd_4500360] using wordTrace_append hprefix tailTrace_4500360
  have hstable : (prefixWord ++ tailWord_4500360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500360).length < 2 ^ (prefixWord ++ tailWord_4500360).sum := by decide
  have hdescent : baseEnd_4500360 < baseStart_4500360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500404 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4500404 : Nat := 118140960795 + 4500404 * 2 ^ 59
def prefixEnd_4500404 : Nat := 4983230072969 + 3 ^ 40 * 4500404 * 2
def baseEnd_4500404 : Nat := 2310870391416915382353025

theorem tailTrace_4500404 : CollatzResearch.WordTrace tailWord_4500404 prefixEnd_4500404 2310870391416915382353025 := by
  unfold tailWord_4500404
  simp only [CollatzResearch.WordTrace]
  refine ⟨82071609393906195328158133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109428812525208260437544177 82071609393906195328158133)
  ·
    refine ⟨7694213380678705812014825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82071609393906195328158133 7694213380678705812014825)
    ·
      refine ⟨5770660035509029359011119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7694213380678705812014825 5770660035509029359011119)
      ·
        refine ⟨8655990053263544038516679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5770660035509029359011119 8655990053263544038516679)
        ·
          refine ⟨12983985079895316057775019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8655990053263544038516679 12983985079895316057775019)
          ·
            refine ⟨19475977619842974086662529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12983985079895316057775019 19475977619842974086662529)
            ·
              refine ⟨14606983214882230564996897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19475977619842974086662529 14606983214882230564996897)
              ·
                refine ⟨10955237411161672923747673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14606983214882230564996897 10955237411161672923747673)
                ·
                  refine ⟨8216428058371254692810755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10955237411161672923747673 8216428058371254692810755)
                  ·
                    refine ⟨12324642087556882039216133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8216428058371254692810755 12324642087556882039216133)
                    ·
                      refine ⟨2310870391416915382353025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12324642087556882039216133 2310870391416915382353025)
                      ·
                        rfl

theorem cell23_4500404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4500404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500404 prefixEnd_4500404 := by exact prefixLift 4500404
  have htrace : WordTrace (prefixWord ++ tailWord_4500404) baseStart_4500404 baseEnd_4500404 := by
    simpa [prefixWord, tailWord_4500404, baseEnd_4500404] using wordTrace_append hprefix tailTrace_4500404
  have hstable : (prefixWord ++ tailWord_4500404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500404).length < 2 ^ (prefixWord ++ tailWord_4500404).sum := by decide
  have hdescent : baseEnd_4500404 < baseStart_4500404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500410 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_4500410 : Nat := 118140960795 + 4500410 * 2 ^ 59
def prefixEnd_4500410 : Nat := 4983230072969 + 3 ^ 40 * 4500410 * 2
def baseEnd_4500410 : Nat := 256763719144538039875333

theorem tailTrace_4500410 : CollatzResearch.WordTrace tailWord_4500410 prefixEnd_4500410 256763719144538039875333 := by
  unfold tailWord_4500410
  simp only [CollatzResearch.WordTrace]
  refine ⟨41035859406447663420258671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109428958417193769120689789 41035859406447663420258671)
  ·
    refine ⟨61553789109671495130388007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41035859406447663420258671 61553789109671495130388007)
    ·
      refine ⟨92330683664507242695582011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61553789109671495130388007 92330683664507242695582011)
      ·
        refine ⟨138496025496760864043373017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92330683664507242695582011 138496025496760864043373017)
        ·
          refine ⟨103872019122570648032529763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138496025496760864043373017 103872019122570648032529763)
          ·
            refine ⟨155808028683855972048794645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103872019122570648032529763 155808028683855972048794645)
            ·
              refine ⟨7303501344555748689787249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155808028683855972048794645 7303501344555748689787249)
              ·
                refine ⟨5477626008416811517340437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7303501344555748689787249 5477626008416811517340437)
                ·
                  refine ⟨256763719144538039875333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5477626008416811517340437 256763719144538039875333)
                  ·
                    rfl

theorem cell23_4500410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_4500410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500410 prefixEnd_4500410 := by exact prefixLift 4500410
  have htrace : WordTrace (prefixWord ++ tailWord_4500410) baseStart_4500410 baseEnd_4500410 := by
    simpa [prefixWord, tailWord_4500410, baseEnd_4500410] using wordTrace_append hprefix tailTrace_4500410
  have hstable : (prefixWord ++ tailWord_4500410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500410).length < 2 ^ (prefixWord ++ tailWord_4500410).sum := by decide
  have hdescent : baseEnd_4500410 < baseStart_4500410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500414 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_4500414 : Nat := 118140960795 + 4500414 * 2 ^ 59
def prefixEnd_4500414 : Nat := 4983230072969 + 3 ^ 40 * 4500414 * 2
def baseEnd_4500414 : Nat := 770291842074486781075993

theorem tailTrace_4500414 : CollatzResearch.WordTrace tailWord_4500414 prefixEnd_4500414 770291842074486781075993 := by
  unfold tailWord_4500414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20517947939722020295522537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109429055678517441576120197 20517947939722020295522537)
  ·
    refine ⟨15388460954791515221641903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20517947939722020295522537 15388460954791515221641903)
    ·
      refine ⟨23082691432187272832462855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388460954791515221641903 23082691432187272832462855)
      ·
        refine ⟨34624037148280909248694283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23082691432187272832462855 34624037148280909248694283)
        ·
          refine ⟨51936055722421363873041425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34624037148280909248694283 51936055722421363873041425)
          ·
            refine ⟨38952041791816022904781069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51936055722421363873041425 38952041791816022904781069)
            ·
              refine ⟨14607015671931008589292901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38952041791816022904781069 14607015671931008589292901)
              ·
                refine ⟨2738815438487064110492419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14607015671931008589292901 2738815438487064110492419)
                ·
                  refine ⟨4108223157730596165738629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738815438487064110492419 4108223157730596165738629)
                  ·
                    refine ⟨770291842074486781075993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108223157730596165738629 770291842074486781075993)
                    ·
                      rfl

theorem cell23_4500414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_4500414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500414 prefixEnd_4500414 := by exact prefixLift 4500414
  have htrace : WordTrace (prefixWord ++ tailWord_4500414) baseStart_4500414 baseEnd_4500414 := by
    simpa [prefixWord, tailWord_4500414, baseEnd_4500414] using wordTrace_append hprefix tailTrace_4500414
  have hstable : (prefixWord ++ tailWord_4500414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500414).length < 2 ^ (prefixWord ++ tailWord_4500414).sum := by decide
  have hdescent : baseEnd_4500414 < baseStart_4500414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500433 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_4500433 : Nat := 118140960795 + 4500433 * 2 ^ 59
def prefixEnd_4500433 : Nat := 4983230072969 + 3 ^ 40 * 4500433 * 2
def baseEnd_4500433 : Nat := 2310885282355895768890391

theorem tailTrace_4500433 : CollatzResearch.WordTrace tailWord_4500433 prefixEnd_4500433 2310885282355895768890391 := by
  unfold tailWord_4500433
  simp only [CollatzResearch.WordTrace]
  refine ⟨164144276504707328609121953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109429517669804885739414635 164144276504707328609121953)
  ·
    refine ⟨123108207378530496456841465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164144276504707328609121953 123108207378530496456841465)
    ·
      refine ⟨92331155533897872342631099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123108207378530496456841465 92331155533897872342631099)
      ·
        refine ⟨138496733300846808513946649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92331155533897872342631099 138496733300846808513946649)
        ·
          refine ⟨103872549975635106385459987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138496733300846808513946649 103872549975635106385459987)
          ·
            refine ⟨155808824963452659578189981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103872549975635106385459987 155808824963452659578189981)
            ·
              refine ⟨58428309361294747341821243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155808824963452659578189981 58428309361294747341821243)
              ·
                refine ⟨87642464041942121012731865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58428309361294747341821243 87642464041942121012731865)
                ·
                  refine ⟨65731848031456590759548899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87642464041942121012731865 65731848031456590759548899)
                  ·
                    refine ⟨98597772047184886139323349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65731848031456590759548899 98597772047184886139323349)
                    ·
                      refine ⟨2310885282355895768890391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98597772047184886139323349 2310885282355895768890391)
                      ·
                        rfl

theorem cell23_4500433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_4500433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500433 prefixEnd_4500433 := by exact prefixLift 4500433
  have htrace : WordTrace (prefixWord ++ tailWord_4500433) baseStart_4500433 baseEnd_4500433 := by
    simpa [prefixWord, tailWord_4500433, baseEnd_4500433] using wordTrace_append hprefix tailTrace_4500433
  have hstable : (prefixWord ++ tailWord_4500433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500433).length < 2 ^ (prefixWord ++ tailWord_4500433).sum := by decide
  have hdescent : baseEnd_4500433 < baseStart_4500433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500440 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_4500440 : Nat := 118140960795 + 4500440 * 2 ^ 59
def prefixEnd_4500440 : Nat := 4983230072969 + 3 ^ 40 * 4500440 * 2
def baseEnd_4500440 : Nat := 770296292240159080500953

theorem tailTrace_4500440 : CollatzResearch.WordTrace tailWord_4500440 prefixEnd_4500440 770296292240159080500953 := by
  unfold tailWord_4500440
  simp only [CollatzResearch.WordTrace]
  refine ⟨82072265907840984402313387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109429687877121312536417849 82072265907840984402313387)
  ·
    refine ⟨123108398861761476603470081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82072265907840984402313387 123108398861761476603470081)
    ·
      refine ⟨92331299146321107452602561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123108398861761476603470081 92331299146321107452602561)
      ·
        refine ⟨69248474359740830589451921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92331299146321107452602561 69248474359740830589451921)
        ·
          refine ⟨51936355769805622942088941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69248474359740830589451921 51936355769805622942088941)
          ·
            refine ⟨19476133413677108603283353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51936355769805622942088941 19476133413677108603283353)
            ·
              refine ⟨14607100060257831452462515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19476133413677108603283353 14607100060257831452462515)
              ·
                refine ⟨21910650090386747178693773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14607100060257831452462515 21910650090386747178693773)
                ·
                  refine ⟨8216493783895030192010165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21910650090386747178693773 8216493783895030192010165)
                  ·
                    refine ⟨770296292240159080500953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8216493783895030192010165 770296292240159080500953)
                    ·
                      rfl

theorem cell23_4500440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_4500440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500440 prefixEnd_4500440 := by exact prefixLift 4500440
  have htrace : WordTrace (prefixWord ++ tailWord_4500440) baseStart_4500440 baseEnd_4500440 := by
    simpa [prefixWord, tailWord_4500440, baseEnd_4500440] using wordTrace_append hprefix tailTrace_4500440
  have hstable : (prefixWord ++ tailWord_4500440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500440).length < 2 ^ (prefixWord ++ tailWord_4500440).sum := by decide
  have hdescent : baseEnd_4500440 < baseStart_4500440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500494 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4500494 : Nat := 118140960795 + 4500494 * 2 ^ 59
def prefixEnd_4500494 : Nat := 4983230072969 + 3 ^ 40 * 4500494 * 2
def baseEnd_4500494 : Nat := 2310916604675820030227611

theorem tailTrace_4500494 : CollatzResearch.WordTrace tailWord_4500494 prefixEnd_4500494 2310916604675820030227611 := by
  unfold tailWord_4500494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20518312669685792003386567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109431000904990890684728357 20518312669685792003386567)
  ·
    refine ⟨30777469004528688005079851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20518312669685792003386567 30777469004528688005079851)
    ·
      refine ⟨46166203506793032007619777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30777469004528688005079851 46166203506793032007619777)
      ·
        refine ⟨34624652630094774005714833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46166203506793032007619777 34624652630094774005714833)
        ·
          refine ⟨25968489472571080504286125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34624652630094774005714833 25968489472571080504286125)
          ·
            refine ⟨9738183552214155189107297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25968489472571080504286125 9738183552214155189107297)
            ·
              refine ⟨7303637664160616391830473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738183552214155189107297 7303637664160616391830473)
              ·
                refine ⟨5477728248120462293872855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7303637664160616391830473 5477728248120462293872855)
                ·
                  refine ⟨8216592372180693440809283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477728248120462293872855 8216592372180693440809283)
                  ·
                    refine ⟨12324888558271040161213925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8216592372180693440809283 12324888558271040161213925)
                    ·
                      refine ⟨2310916604675820030227611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12324888558271040161213925 2310916604675820030227611)
                      ·
                        rfl

theorem cell23_4500494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4500494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500494 prefixEnd_4500494 := by exact prefixLift 4500494
  have htrace : WordTrace (prefixWord ++ tailWord_4500494) baseStart_4500494 baseEnd_4500494 := by
    simpa [prefixWord, tailWord_4500494, baseEnd_4500494] using wordTrace_append hprefix tailTrace_4500494
  have hstable : (prefixWord ++ tailWord_4500494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500494).length < 2 ^ (prefixWord ++ tailWord_4500494).sum := by decide
  have hdescent : baseEnd_4500494 < baseStart_4500494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500514 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_4500514 : Nat := 118140960795 + 4500514 * 2 ^ 59
def prefixEnd_4500514 : Nat := 4983230072969 + 3 ^ 40 * 4500514 * 2
def baseEnd_4500514 : Nat := 2310926874288909951977519

theorem tailTrace_4500514 : CollatzResearch.WordTrace tailWord_4500514 prefixEnd_4500514 2310926874288909951977519 := by
  unfold tailWord_4500514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41036807704353469860705149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109431487211609252961880397 41036807704353469860705149)
  ·
    refine ⟨15388802889132551197764431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41036807704353469860705149 15388802889132551197764431)
    ·
      refine ⟨23083204333698826796646647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15388802889132551197764431 23083204333698826796646647)
      ·
        refine ⟨34624806500548240194969971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23083204333698826796646647 34624806500548240194969971)
        ·
          refine ⟨51937209750822360292454957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34624806500548240194969971 51937209750822360292454957)
          ·
            refine ⟨19476453656558385109670609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51937209750822360292454957 19476453656558385109670609)
            ·
              refine ⟨14607340242418788832252957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19476453656558385109670609 14607340242418788832252957)
              ·
                refine ⟨5477752590907045812094859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14607340242418788832252957 5477752590907045812094859)
                ·
                  refine ⟨8216628886360568718142289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5477752590907045812094859 8216628886360568718142289)
                  ·
                    refine ⟨6162471664770426538606717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8216628886360568718142289 6162471664770426538606717)
                    ·
                      refine ⟨2310926874288909951977519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162471664770426538606717 2310926874288909951977519)
                      ·
                        rfl

theorem cell23_4500514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_4500514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500514 prefixEnd_4500514 := by exact prefixLift 4500514
  have htrace : WordTrace (prefixWord ++ tailWord_4500514) baseStart_4500514 baseEnd_4500514 := by
    simpa [prefixWord, tailWord_4500514, baseEnd_4500514] using wordTrace_append hprefix tailTrace_4500514
  have hstable : (prefixWord ++ tailWord_4500514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500514).length < 2 ^ (prefixWord ++ tailWord_4500514).sum := by decide
  have hdescent : baseEnd_4500514 < baseStart_4500514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500528 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 1, 2, 2]
def baseStart_4500528 : Nat := 118140960795 + 4500528 * 2 ^ 59
def prefixEnd_4500528 : Nat := 4983230072969 + 3 ^ 40 * 4500528 * 2
def baseEnd_4500528 : Nat := 2310934063018072897202455

theorem tailTrace_4500528 : CollatzResearch.WordTrace tailWord_4500528 prefixEnd_4500528 2310934063018072897202455 := by
  unfold tailWord_4500528
  simp only [CollatzResearch.WordTrace]
  refine ⟨82073870719681579916915119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109431827626242106555886825 82073870719681579916915119)
  ·
    refine ⟨123110806079522369875372679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82073870719681579916915119 123110806079522369875372679)
    ·
      refine ⟨184666209119283554813059019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123110806079522369875372679 184666209119283554813059019)
      ·
        refine ⟨276999313678925332219588529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184666209119283554813059019 276999313678925332219588529)
        ·
          refine ⟨207749485259193999164691397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276999313678925332219588529 207749485259193999164691397)
          ·
            refine ⟨38953028486098874843379637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207749485259193999164691397 38953028486098874843379637)
            ·
              refine ⟨3651846420571769516566841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38953028486098874843379637 3651846420571769516566841)
              ·
                refine ⟨2738884815428827137425131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3651846420571769516566841 2738884815428827137425131)
                ·
                  refine ⟨4108327223143240706137697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738884815428827137425131 4108327223143240706137697)
                  ·
                    refine ⟨3081245417357430529603273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108327223143240706137697 3081245417357430529603273)
                    ·
                      refine ⟨2310934063018072897202455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081245417357430529603273 2310934063018072897202455)
                      ·
                        rfl

theorem cell23_4500528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 2, 2].length) (baseStart_4500528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500528 prefixEnd_4500528 := by exact prefixLift 4500528
  have htrace : WordTrace (prefixWord ++ tailWord_4500528) baseStart_4500528 baseEnd_4500528 := by
    simpa [prefixWord, tailWord_4500528, baseEnd_4500528] using wordTrace_append hprefix tailTrace_4500528
  have hstable : (prefixWord ++ tailWord_4500528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500528).length < 2 ^ (prefixWord ++ tailWord_4500528).sum := by decide
  have hdescent : baseEnd_4500528 < baseStart_4500528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500530 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_4500530 : Nat := 118140960795 + 4500530 * 2 ^ 59
def prefixEnd_4500530 : Nat := 4983230072969 + 3 ^ 40 * 4500530 * 2
def baseEnd_4500530 : Nat := 770311696659793963125815

theorem tailTrace_4500530 : CollatzResearch.WordTrace tailWord_4500530 prefixEnd_4500530 770311696659793963125815 := by
  unfold tailWord_4500530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41036953596338978543850761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109431876256903942783602029 41036953596338978543850761)
  ·
    refine ⟨30777715197254233907888071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41036953596338978543850761 30777715197254233907888071)
    ·
      refine ⟨46166572795881350861832107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30777715197254233907888071 46166572795881350861832107)
      ·
        refine ⟨69249859193822026292748161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46166572795881350861832107 69249859193822026292748161)
        ·
          refine ⟨51937394395366519719561121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69249859193822026292748161 51937394395366519719561121)
          ·
            refine ⟨38953045796524889789670841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51937394395366519719561121 38953045796524889789670841)
            ·
              refine ⟨29214784347393667342253131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38953045796524889789670841 29214784347393667342253131)
              ·
                refine ⟨43822176521090501013379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29214784347393667342253131 43822176521090501013379697)
                ·
                  refine ⟨32866632390817875760034773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43822176521090501013379697 32866632390817875760034773)
                  ·
                    refine ⟨770311696659793963125815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32866632390817875760034773 770311696659793963125815)
                    ·
                      rfl

theorem cell23_4500530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_4500530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500530 prefixEnd_4500530 := by exact prefixLift 4500530
  have htrace : WordTrace (prefixWord ++ tailWord_4500530) baseStart_4500530 baseEnd_4500530 := by
    simpa [prefixWord, tailWord_4500530, baseEnd_4500530] using wordTrace_append hprefix tailTrace_4500530
  have hstable : (prefixWord ++ tailWord_4500530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500530).length < 2 ^ (prefixWord ++ tailWord_4500530).sum := by decide
  have hdescent : baseEnd_4500530 < baseStart_4500530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500544 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3]
def baseStart_4500544 : Nat := 118140960795 + 4500544 * 2 ^ 59
def prefixEnd_4500544 : Nat := 4983230072969 + 3 ^ 40 * 4500544 * 2
def baseEnd_4500544 : Nat := 2310942278708544834602381

theorem tailTrace_4500544 : CollatzResearch.WordTrace tailWord_4500544 prefixEnd_4500544 2310942278708544834602381 := by
  unfold tailWord_4500544
  simp only [CollatzResearch.WordTrace]
  refine ⟨82074162503652597283206343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109432216671536796377608457 82074162503652597283206343)
  ·
    refine ⟨123111243755478895924809515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82074162503652597283206343 123111243755478895924809515)
    ·
      refine ⟨184666865633218343887214273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123111243755478895924809515 184666865633218343887214273)
      ·
        refine ⟨138500149224913757915410705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184666865633218343887214273 138500149224913757915410705)
        ·
          refine ⟨103875111918685318436558029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138500149224913757915410705 103875111918685318436558029)
          ·
            refine ⟨38953166969506994413709261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103875111918685318436558029 38953166969506994413709261)
            ·
              refine ⟨14607437613565122905140973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38953166969506994413709261 14607437613565122905140973)
              ·
                refine ⟨5477789105086921089427865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14607437613565122905140973 5477789105086921089427865)
                ·
                  refine ⟨4108341828815190817070899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477789105086921089427865 4108341828815190817070899)
                  ·
                    refine ⟨6162512743222786225606349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108341828815190817070899 6162512743222786225606349)
                    ·
                      refine ⟨2310942278708544834602381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162512743222786225606349 2310942278708544834602381)
                      ·
                        rfl

theorem cell23_4500544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_4500544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500544 prefixEnd_4500544 := by exact prefixLift 4500544
  have htrace : WordTrace (prefixWord ++ tailWord_4500544) baseStart_4500544 baseEnd_4500544 := by
    simpa [prefixWord, tailWord_4500544, baseEnd_4500544] using wordTrace_append hprefix tailTrace_4500544
  have hstable : (prefixWord ++ tailWord_4500544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500544).length < 2 ^ (prefixWord ++ tailWord_4500544).sum := by decide
  have hdescent : baseEnd_4500544 < baseStart_4500544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500570 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4500570 : Nat := 118140960795 + 4500570 * 2 ^ 59
def prefixEnd_4500570 : Nat := 4983230072969 + 3 ^ 40 * 4500570 * 2
def baseEnd_4500570 : Nat := 2310955629205561732877261

theorem tailTrace_4500570 : CollatzResearch.WordTrace tailWord_4500570 prefixEnd_4500570 2310955629205561732877261 := by
  unfold tailWord_4500570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41037318326302750251714791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109432848870140667337906109 41037318326302750251714791)
  ·
    refine ⟨61555977489454125377572187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41037318326302750251714791 61555977489454125377572187)
    ·
      refine ⟨92333966234181188066358281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61555977489454125377572187 92333966234181188066358281)
      ·
        refine ⟨69250474675635891049768711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92333966234181188066358281 69250474675635891049768711)
        ·
          refine ⟨103875712013453836574653067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69250474675635891049768711 103875712013453836574653067)
          ·
            refine ⟨155813568020180754861979601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103875712013453836574653067 155813568020180754861979601)
            ·
              refine ⟨116860176015135566146484701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155813568020180754861979601 116860176015135566146484701)
              ·
                refine ⟨43822566005675837304931763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116860176015135566146484701 43822566005675837304931763)
                ·
                  refine ⟨65733849008513755957397645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43822566005675837304931763 65733849008513755957397645)
                  ·
                    refine ⟨24650193378192658484024117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65733849008513755957397645 24650193378192658484024117)
                    ·
                      refine ⟨2310955629205561732877261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24650193378192658484024117 2310955629205561732877261)
                      ·
                        rfl

theorem cell23_4500570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4500570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500570 prefixEnd_4500570 := by exact prefixLift 4500570
  have htrace : WordTrace (prefixWord ++ tailWord_4500570) baseStart_4500570 baseEnd_4500570 := by
    simpa [prefixWord, tailWord_4500570, baseEnd_4500570] using wordTrace_append hprefix tailTrace_4500570
  have hstable : (prefixWord ++ tailWord_4500570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500570).length < 2 ^ (prefixWord ++ tailWord_4500570).sum := by decide
  have hdescent : baseEnd_4500570 < baseStart_4500570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500578 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4500578 : Nat := 118140960795 + 4500578 * 2 ^ 59
def prefixEnd_4500578 : Nat := 4983230072969 + 3 ^ 40 * 4500578 * 2
def baseEnd_4500578 : Nat := 2310959737050797701577225

theorem tailTrace_4500578 : CollatzResearch.WordTrace tailWord_4500578 prefixEnd_4500578 2310959737050797701577225 := by
  unfold tailWord_4500578
  simp only [CollatzResearch.WordTrace]
  refine ⟨41037391272295504593287597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109433043392788012248766925 41037391272295504593287597)
  ·
    refine ⟨15389021727110814222482849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41037391272295504593287597 15389021727110814222482849)
    ·
      refine ⟨11541766295333110666862137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15389021727110814222482849 11541766295333110666862137)
      ·
        refine ⟨8656324721499833000146603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11541766295333110666862137 8656324721499833000146603)
        ·
          refine ⟨12984487082249749500219905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656324721499833000146603 12984487082249749500219905)
          ·
            refine ⟨9738365311687312125164929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12984487082249749500219905 9738365311687312125164929)
            ·
              refine ⟨7303773983765484093873697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738365311687312125164929 7303773983765484093873697)
              ·
                refine ⟨5477830487824113070405273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7303773983765484093873697 5477830487824113070405273)
                ·
                  refine ⟨4108372865868084802803955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5477830487824113070405273 4108372865868084802803955)
                  ·
                    refine ⟨6162559298802127204205933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108372865868084802803955 6162559298802127204205933)
                    ·
                      refine ⟨2310959737050797701577225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162559298802127204205933 2310959737050797701577225)
                      ·
                        rfl

theorem cell23_4500578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4500578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500578 prefixEnd_4500578 := by exact prefixLift 4500578
  have htrace : WordTrace (prefixWord ++ tailWord_4500578) baseStart_4500578 baseEnd_4500578 := by
    simpa [prefixWord, tailWord_4500578, baseEnd_4500578] using wordTrace_append hprefix tailTrace_4500578
  have hstable : (prefixWord ++ tailWord_4500578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500578).length < 2 ^ (prefixWord ++ tailWord_4500578).sum := by decide
  have hdescent : baseEnd_4500578 < baseStart_4500578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
