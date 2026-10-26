import V185TrunkScan23Chunk0014

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_88117 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_88117 : Nat := 118140960795 + 88117 * 2 ^ 59
def prefixEnd_88117 : Nat := 4983230072969 + 3 ^ 40 * 88117 * 2
def baseEnd_88117 : Nat := 15082124944112325177421

theorem tailTrace_88117 : CollatzResearch.WordTrace tailWord_88117 prefixEnd_88117 15082124944112325177421 := by
  unfold tailWord_88117
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213891021774633030582605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2142594014516422020388403 3213891021774633030582605)
  ·
    refine ⟨1205209133165487386468477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3213891021774633030582605 1205209133165487386468477)
    ·
      refine ⟨451953424937057769925679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1205209133165487386468477 451953424937057769925679)
      ·
        refine ⟨677930137405586654888519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451953424937057769925679 677930137405586654888519)
        ·
          refine ⟨1016895206108379982332779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677930137405586654888519 1016895206108379982332779)
          ·
            refine ⟨1525342809162569973499169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016895206108379982332779 1525342809162569973499169)
            ·
              refine ⟨1144007106871927480124377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525342809162569973499169 1144007106871927480124377)
              ·
                refine ⟨858005330153945610093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144007106871927480124377 858005330153945610093283)
                ·
                  refine ⟨1287007995230918415139925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858005330153945610093283 1287007995230918415139925)
                  ·
                    refine ⟨15082124944112325177421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1287007995230918415139925 15082124944112325177421)
                    ·
                      rfl

theorem cell23_88117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_88117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88117 prefixEnd_88117 := by exact prefixLift 88117
  have htrace : WordTrace (prefixWord ++ tailWord_88117) baseStart_88117 baseEnd_88117 := by
    simpa [prefixWord, tailWord_88117, baseEnd_88117] using wordTrace_append hprefix tailTrace_88117
  have hstable : (prefixWord ++ tailWord_88117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88117).length < 2 ^ (prefixWord ++ tailWord_88117).sum := by decide
  have hdescent : baseEnd_88117 < baseStart_88117 := by decide
  rcases family_descends (prefixWord ++ tailWord_88117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88127 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_88127 : Nat := 118140960795 + 88127 * 2 ^ 59
def prefixEnd_88127 : Nat := 4983230072969 + 3 ^ 40 * 88127 * 2
def baseEnd_88127 : Nat := 45251509638881936407217

theorem tailTrace_88127 : CollatzResearch.WordTrace tailWord_88127 prefixEnd_88127 45251509638881936407217 := by
  unfold tailWord_88127
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214255751738404738446635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2142837167825603158964423 3214255751738404738446635)
  ·
    refine ⟨4821383627607607107669953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3214255751738404738446635 4821383627607607107669953)
    ·
      refine ⟨3616037720705705330752465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4821383627607607107669953 3616037720705705330752465)
      ·
        refine ⟨2712028290529278998064349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3616037720705705330752465 2712028290529278998064349)
        ·
          refine ⟨1017010608948479624274131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2712028290529278998064349 1017010608948479624274131)
          ·
            refine ⟨1525515913422719436411197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017010608948479624274131 1525515913422719436411197)
            ·
              refine ⟨572068467533519788654199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525515913422719436411197 572068467533519788654199)
              ·
                refine ⟨858102701300279682981299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572068467533519788654199 858102701300279682981299)
                ·
                  refine ⟨1287154051950419524471949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858102701300279682981299 1287154051950419524471949)
                  ·
                    refine ⟨482682769481407321676981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287154051950419524471949 482682769481407321676981)
                    ·
                      refine ⟨45251509638881936407217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 482682769481407321676981 45251509638881936407217)
                      ·
                        rfl

theorem cell23_88127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_88127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88127 prefixEnd_88127 := by exact prefixLift 88127
  have htrace : WordTrace (prefixWord ++ tailWord_88127) baseStart_88127 baseEnd_88127 := by
    simpa [prefixWord, tailWord_88127, baseEnd_88127] using wordTrace_append hprefix tailTrace_88127
  have hstable : (prefixWord ++ tailWord_88127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88127).length < 2 ^ (prefixWord ++ tailWord_88127).sum := by decide
  have hdescent : baseEnd_88127 < baseStart_88127 := by decide
  rcases family_descends (prefixWord ++ tailWord_88127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88162 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_88162 : Nat := 118140960795 + 88162 * 2 ^ 59
def prefixEnd_88162 : Nat := 4983230072969 + 3 ^ 40 * 88162 * 2
def baseEnd_88162 : Nat := 45269481461789299469557

theorem tailTrace_88162 : CollatzResearch.WordTrace tailWord_88162 prefixEnd_88162 45269481461789299469557 := by
  unfold tailWord_88162
  simp only [CollatzResearch.WordTrace]
  refine ⟨803883076652901428992685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2143688204407737143980493 803883076652901428992685)
  ·
    refine ⟨301456153744838035872257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 803883076652901428992685 301456153744838035872257)
    ·
      refine ⟨226092115308628526904193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301456153744838035872257 226092115308628526904193)
      ·
        refine ⟨169569086481471395178145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226092115308628526904193 169569086481471395178145)
        ·
          refine ⟨127176814861103546383609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169569086481471395178145 127176814861103546383609)
          ·
            refine ⟨95382611145827659787707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127176814861103546383609 95382611145827659787707)
            ·
              refine ⟨143073916718741489681561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95382611145827659787707 143073916718741489681561)
              ·
                refine ⟨107305437539056117261171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143073916718741489681561 107305437539056117261171)
                ·
                  refine ⟨160958156308584175891757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107305437539056117261171 160958156308584175891757)
                  ·
                    refine ⟨60359308615719065959409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160958156308584175891757 60359308615719065959409)
                    ·
                      refine ⟨45269481461789299469557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60359308615719065959409 45269481461789299469557)
                      ·
                        rfl

theorem cell23_88162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_88162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88162 prefixEnd_88162 := by exact prefixLift 88162
  have htrace : WordTrace (prefixWord ++ tailWord_88162) baseStart_88162 baseEnd_88162 := by
    simpa [prefixWord, tailWord_88162, baseEnd_88162] using wordTrace_append hprefix tailTrace_88162
  have hstable : (prefixWord ++ tailWord_88162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88162).length < 2 ^ (prefixWord ++ tailWord_88162).sum := by decide
  have hdescent : baseEnd_88162 < baseStart_88162 := by decide
  rcases family_descends (prefixWord ++ tailWord_88162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88228 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_88228 : Nat := 118140960795 + 88228 * 2 ^ 59
def prefixEnd_88228 : Nat := 4983230072969 + 3 ^ 40 * 88228 * 2
def baseEnd_88228 : Nat := 15101123728328680414751

theorem tailTrace_88228 : CollatzResearch.WordTrace tailWord_88228 prefixEnd_88228 15101123728328680414751 := by
  unfold tailWord_88228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608969762186249493936669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2145293016248332658582225 1608969762186249493936669)
  ·
    refine ⟨603363660819843560226251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1608969762186249493936669 603363660819843560226251)
    ·
      refine ⟨905045491229765340339377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603363660819843560226251 905045491229765340339377)
      ·
        refine ⟨678784118422324005254533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 905045491229765340339377 678784118422324005254533)
        ·
          refine ⟨127272022204185750985225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 678784118422324005254533 127272022204185750985225)
          ·
            refine ⟨95454016653139313238919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127272022204185750985225 95454016653139313238919)
            ·
              refine ⟨143181024979708969858379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95454016653139313238919 143181024979708969858379)
              ·
                refine ⟨214771537469563454787569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143181024979708969858379 214771537469563454787569)
                ·
                  refine ⟨161078653102172591090677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214771537469563454787569 161078653102172591090677)
                  ·
                    refine ⟨15101123728328680414751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161078653102172591090677 15101123728328680414751)
                    ·
                      rfl

theorem cell23_88228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_88228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88228 prefixEnd_88228 := by exact prefixLift 88228
  have htrace : WordTrace (prefixWord ++ tailWord_88228) baseStart_88228 baseEnd_88228 := by
    simpa [prefixWord, tailWord_88228, baseEnd_88228] using wordTrace_append hprefix tailTrace_88228
  have hstable : (prefixWord ++ tailWord_88228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88228).length < 2 ^ (prefixWord ++ tailWord_88228).sum := by decide
  have hdescent : baseEnd_88228 < baseStart_88228 := by decide
  rcases family_descends (prefixWord ++ tailWord_88228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88271 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 6]
def baseStart_88271 : Nat := 118140960795 + 88271 * 2 ^ 59
def prefixEnd_88271 : Nat := 4983230072969 + 3 ^ 40 * 88271 * 2
def baseEnd_88271 : Nat := 5036161205903263667395

theorem tailTrace_88271 : CollatzResearch.WordTrace tailWord_88271 prefixEnd_88271 5036161205903263667395 := by
  unfold tailWord_88271
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219507863216717331688667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2146338575477811554459111 3219507863216717331688667)
  ·
    refine ⟨4829261794825075997533001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219507863216717331688667 4829261794825075997533001)
    ·
      refine ⟨3621946346118806998149751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4829261794825075997533001 3621946346118806998149751)
      ·
        refine ⟨5432919519178210497224627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621946346118806998149751 5432919519178210497224627)
        ·
          refine ⟨8149379278767315745836941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432919519178210497224627 8149379278767315745836941)
          ·
            refine ⟨3056017229537743404688853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8149379278767315745836941 3056017229537743404688853)
            ·
              refine ⟨71625403817290861047395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3056017229537743404688853 71625403817290861047395)
              ·
                refine ⟨107438105725936291571093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71625403817290861047395 107438105725936291571093)
                ·
                  refine ⟨5036161205903263667395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107438105725936291571093 5036161205903263667395)
                  ·
                    rfl

theorem cell23_88271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 6].length) (baseStart_88271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88271 prefixEnd_88271 := by exact prefixLift 88271
  have htrace : WordTrace (prefixWord ++ tailWord_88271) baseStart_88271 baseEnd_88271 := by
    simpa [prefixWord, tailWord_88271, baseEnd_88271] using wordTrace_append hprefix tailTrace_88271
  have hstable : (prefixWord ++ tailWord_88271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88271).length < 2 ^ (prefixWord ++ tailWord_88271).sum := by decide
  have hdescent : baseEnd_88271 < baseStart_88271 := by decide
  rcases family_descends (prefixWord ++ tailWord_88271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88321 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_88321 : Nat := 118140960795 + 88321 * 2 ^ 59
def prefixEnd_88321 : Nat := 4983230072969 + 3 ^ 40 * 88321 * 2
def baseEnd_88321 : Nat := 45351124885854177381325

theorem tailTrace_88321 : CollatzResearch.WordTrace tailWord_88321 prefixEnd_88321 45351124885854177381325 := by
  unfold tailWord_88321
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221331513035575871008817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2147554342023717247339211 3221331513035575871008817)
  ·
    refine ⟨2415998634776681903256613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3221331513035575871008817 2415998634776681903256613)
    ·
      refine ⟨452999744020627856860615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2415998634776681903256613 452999744020627856860615)
      ·
        refine ⟨679499616030941785290923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452999744020627856860615 679499616030941785290923)
        ·
          refine ⟨1019249424046412677936385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679499616030941785290923 1019249424046412677936385)
          ·
            refine ⟨764437068034809508452289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019249424046412677936385 764437068034809508452289)
            ·
              refine ⟨573327801026107131339217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764437068034809508452289 573327801026107131339217)
              ·
                refine ⟨429995850769580348504413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573327801026107131339217 429995850769580348504413)
                ·
                  refine ⟨161248444038592630689155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429995850769580348504413 161248444038592630689155)
                  ·
                    refine ⟨241872666057888946033733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161248444038592630689155 241872666057888946033733)
                    ·
                      refine ⟨45351124885854177381325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 241872666057888946033733 45351124885854177381325)
                      ·
                        rfl

theorem cell23_88321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_88321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88321 prefixEnd_88321 := by exact prefixLift 88321
  have htrace : WordTrace (prefixWord ++ tailWord_88321) baseStart_88321 baseEnd_88321 := by
    simpa [prefixWord, tailWord_88321, baseEnd_88321] using wordTrace_append hprefix tailTrace_88321
  have hstable : (prefixWord ++ tailWord_88321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88321).length < 2 ^ (prefixWord ++ tailWord_88321).sum := by decide
  have hdescent : baseEnd_88321 < baseStart_88321 := by decide
  rcases family_descends (prefixWord ++ tailWord_88321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88344 : List Nat := [2, 1, 2, 3, 1, 2, 1, 11]
def baseStart_88344 : Nat := 118140960795 + 88344 * 2 ^ 59
def prefixEnd_88344 : Nat := 4983230072969 + 3 ^ 40 * 88344 * 2
def baseEnd_88344 : Nat := 1680108701515095829397

theorem tailTrace_88344 : CollatzResearch.WordTrace tailWord_88344 prefixEnd_88344 1680108701515095829397 := by
  unfold tailWord_88344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611085195976125399548043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2148113594634833866064057 1611085195976125399548043)
  ·
    refine ⟨2416627793964188099322065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1611085195976125399548043 2416627793964188099322065)
    ·
      refine ⟨1812470845473141074491549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2416627793964188099322065 1812470845473141074491549)
      ·
        refine ⟨679676567052427902934331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1812470845473141074491549 679676567052427902934331)
        ·
          refine ⟨1019514850578641854401497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679676567052427902934331 1019514850578641854401497)
          ·
            refine ⟨764636137933981390801123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019514850578641854401497 764636137933981390801123)
            ·
              refine ⟨1146954206900972086201685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764636137933981390801123 1146954206900972086201685)
              ·
                refine ⟨1680108701515095829397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1146954206900972086201685 1680108701515095829397)
                ·
                  rfl

theorem cell23_88344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 11].length) (baseStart_88344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88344 prefixEnd_88344 := by exact prefixLift 88344
  have htrace : WordTrace (prefixWord ++ tailWord_88344) baseStart_88344 baseEnd_88344 := by
    simpa [prefixWord, tailWord_88344, baseEnd_88344] using wordTrace_append hprefix tailTrace_88344
  have hstable : (prefixWord ++ tailWord_88344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88344).length < 2 ^ (prefixWord ++ tailWord_88344).sum := by decide
  have hdescent : baseEnd_88344 < baseStart_88344 := by decide
  rcases family_descends (prefixWord ++ tailWord_88344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88351 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_88351 : Nat := 118140960795 + 88351 * 2 ^ 59
def prefixEnd_88351 : Nat := 4983230072969 + 3 ^ 40 * 88351 * 2
def baseEnd_88351 : Nat := 45366529305489060006187

theorem tailTrace_88351 : CollatzResearch.WordTrace tailWord_88351 prefixEnd_88351 45366529305489060006187 := by
  unfold tailWord_88351
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222425702926890994600907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2148283801951260663067271 3222425702926890994600907)
  ·
    refine ⟨4833638554390336491901361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222425702926890994600907 4833638554390336491901361)
    ·
      refine ⟨3625228915792752368926021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4833638554390336491901361 3625228915792752368926021)
      ·
        refine ⟨679730421711141069173629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3625228915792752368926021 679730421711141069173629)
        ·
          refine ⟨254898908141677900940111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679730421711141069173629 254898908141677900940111)
          ·
            refine ⟨382348362212516851410167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254898908141677900940111 382348362212516851410167)
            ·
              refine ⟨573522543318775277115251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382348362212516851410167 573522543318775277115251)
              ·
                refine ⟨860283814978162915672877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573522543318775277115251 860283814978162915672877)
                ·
                  refine ⟨322606430616811093377329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860283814978162915672877 322606430616811093377329)
                  ·
                    refine ⟨241954822962608320032997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322606430616811093377329 241954822962608320032997)
                    ·
                      refine ⟨45366529305489060006187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 241954822962608320032997 45366529305489060006187)
                      ·
                        rfl

theorem cell23_88351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_88351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88351 prefixEnd_88351 := by exact prefixLift 88351
  have htrace : WordTrace (prefixWord ++ tailWord_88351) baseStart_88351 baseEnd_88351 := by
    simpa [prefixWord, tailWord_88351, baseEnd_88351] using wordTrace_append hprefix tailTrace_88351
  have hstable : (prefixWord ++ tailWord_88351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88351).length < 2 ^ (prefixWord ++ tailWord_88351).sum := by decide
  have hdescent : baseEnd_88351 < baseStart_88351 := by decide
  rcases family_descends (prefixWord ++ tailWord_88351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88371 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3]
def baseStart_88371 : Nat := 118140960795 + 88371 * 2 ^ 59
def prefixEnd_88371 : Nat := 4983230072969 + 3 ^ 40 * 88371 * 2
def baseEnd_88371 : Nat := 45376798918578981756095

theorem tailTrace_88371 : CollatzResearch.WordTrace tailWord_88371 prefixEnd_88371 45376798918578981756095 := by
  unfold tailWord_88371
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223155162854434410328967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2148770108569622940219311 3223155162854434410328967)
  ·
    refine ⟨4834732744281651615493451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223155162854434410328967 4834732744281651615493451)
    ·
      refine ⟨7252099116422477423240177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834732744281651615493451 7252099116422477423240177)
      ·
        refine ⟨5439074337316858067430133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7252099116422477423240177 5439074337316858067430133)
        ·
          refine ⟨509913219123455443821575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5439074337316858067430133 509913219123455443821575)
          ·
            refine ⟨764869828685183165732363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509913219123455443821575 764869828685183165732363)
            ·
              refine ⟨1147304743027774748598545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764869828685183165732363 1147304743027774748598545)
              ·
                refine ⟨860478557270831061448909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147304743027774748598545 860478557270831061448909)
                ·
                  refine ⟨322679458976561648043341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860478557270831061448909 322679458976561648043341)
                  ·
                    refine ⟨121004797116210618016253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322679458976561648043341 121004797116210618016253)
                    ·
                      refine ⟨45376798918578981756095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121004797116210618016253 45376798918578981756095)
                      ·
                        rfl

theorem cell23_88371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_88371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88371 prefixEnd_88371 := by exact prefixLift 88371
  have htrace : WordTrace (prefixWord ++ tailWord_88371) baseStart_88371 baseEnd_88371 := by
    simpa [prefixWord, tailWord_88371, baseEnd_88371] using wordTrace_append hprefix tailTrace_88371
  have hstable : (prefixWord ++ tailWord_88371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88371).length < 2 ^ (prefixWord ++ tailWord_88371).sum := by decide
  have hdescent : baseEnd_88371 < baseStart_88371 := by decide
  rcases family_descends (prefixWord ++ tailWord_88371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88385 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_88385 : Nat := 118140960795 + 88385 * 2 ^ 59
def prefixEnd_88385 : Nat := 4983230072969 + 3 ^ 40 * 88385 * 2
def baseEnd_88385 : Nat := 45383987647741926981031

theorem tailTrace_88385 : CollatzResearch.WordTrace tailWord_88385 prefixEnd_88385 45383987647741926981031 := by
  unfold tailWord_88385
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223665784803714801338609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2149110523202476534225739 3223665784803714801338609)
  ·
    refine ⟨2417749338602786101003957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3223665784803714801338609 2417749338602786101003957)
    ·
      refine ⟨226664000494011196969121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2417749338602786101003957 226664000494011196969121)
      ·
        refine ⟨169998000370508397726841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226664000494011196969121 169998000370508397726841)
        ·
          refine ⟨127498500277881298295131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169998000370508397726841 127498500277881298295131)
          ·
            refine ⟨191247750416821947442697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127498500277881298295131 191247750416821947442697)
            ·
              refine ⟨143435812812616460582023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191247750416821947442697 143435812812616460582023)
              ·
                refine ⟨215153719218924690873035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143435812812616460582023 215153719218924690873035)
                ·
                  refine ⟨322730578828387036309553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215153719218924690873035 322730578828387036309553)
                  ·
                    refine ⟨242047934121290277232165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 322730578828387036309553 242047934121290277232165)
                    ·
                      refine ⟨45383987647741926981031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 242047934121290277232165 45383987647741926981031)
                      ·
                        rfl

theorem cell23_88385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_88385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88385 prefixEnd_88385 := by exact prefixLift 88385
  have htrace : WordTrace (prefixWord ++ tailWord_88385) baseStart_88385 baseEnd_88385 := by
    simpa [prefixWord, tailWord_88385, baseEnd_88385] using wordTrace_append hprefix tailTrace_88385
  have hstable : (prefixWord ++ tailWord_88385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88385).length < 2 ^ (prefixWord ++ tailWord_88385).sum := by decide
  have hdescent : baseEnd_88385 < baseStart_88385 := by decide
  rcases family_descends (prefixWord ++ tailWord_88385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88421 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_88421 : Nat := 118140960795 + 88421 * 2 ^ 59
def prefixEnd_88421 : Nat := 4983230072969 + 3 ^ 40 * 88421 * 2
def baseEnd_88421 : Nat := 15134157650434595376955

theorem tailTrace_88421 : CollatzResearch.WordTrace tailWord_88421 prefixEnd_88421 15134157650434595376955 := by
  unfold tailWord_88421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224978812673292949649117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2149985875115528633099411 3224978812673292949649117)
  ·
    refine ⟨1209367054752484856118419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3224978812673292949649117 1209367054752484856118419)
    ·
      refine ⟨1814050582128727284177629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209367054752484856118419 1814050582128727284177629)
      ·
        refine ⟨680268968298272731566611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1814050582128727284177629 680268968298272731566611)
        ·
          refine ⟨1020403452447409097349917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680268968298272731566611 1020403452447409097349917)
          ·
            refine ⟨382651294667778411506219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1020403452447409097349917 382651294667778411506219)
            ·
              refine ⟨573976942001667617259329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382651294667778411506219 573976942001667617259329)
              ·
                refine ⟨430482706501250712944497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573976942001667617259329 430482706501250712944497)
                ·
                  refine ⟨322862029875938034708373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430482706501250712944497 322862029875938034708373)
                  ·
                    refine ⟨15134157650434595376955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 322862029875938034708373 15134157650434595376955)
                    ·
                      rfl

theorem cell23_88421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_88421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88421 prefixEnd_88421 := by exact prefixLift 88421
  have htrace : WordTrace (prefixWord ++ tailWord_88421) baseStart_88421 baseEnd_88421 := by
    simpa [prefixWord, tailWord_88421, baseEnd_88421] using wordTrace_append hprefix tailTrace_88421
  have hstable : (prefixWord ++ tailWord_88421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88421).length < 2 ^ (prefixWord ++ tailWord_88421).sum := by decide
  have hdescent : baseEnd_88421 < baseStart_88421 := by decide
  rcases family_descends (prefixWord ++ tailWord_88421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88431 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_88431 : Nat := 118140960795 + 88431 * 2 ^ 59
def prefixEnd_88431 : Nat := 4983230072969 + 3 ^ 40 * 88431 * 2
def baseEnd_88431 : Nat := 45407607757848747005819

theorem tailTrace_88431 : CollatzResearch.WordTrace tailWord_88431 prefixEnd_88431 45407607757848747005819 := by
  unfold tailWord_88431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225343542637064657513147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2150229028424709771675431 3225343542637064657513147)
  ·
    refine ⟨4838015313955596986269721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225343542637064657513147 4838015313955596986269721)
    ·
      refine ⟨3628511485466697739702291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4838015313955596986269721 3628511485466697739702291)
      ·
        refine ⟨5442767228200046609553437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628511485466697739702291 5442767228200046609553437)
        ·
          refine ⟨2041037710575017478582539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5442767228200046609553437 2041037710575017478582539)
          ·
            refine ⟨3061556565862526217873809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041037710575017478582539 3061556565862526217873809)
            ·
              refine ⟨2296167424396894663405357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061556565862526217873809 2296167424396894663405357)
              ·
                refine ⟨861062784148835498777009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2296167424396894663405357 861062784148835498777009)
                ·
                  refine ⟨645797088111626624082757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 861062784148835498777009 645797088111626624082757)
                  ·
                    refine ⟨121086954020929992015517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 645797088111626624082757 121086954020929992015517)
                    ·
                      refine ⟨45407607757848747005819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121086954020929992015517 45407607757848747005819)
                      ·
                        rfl

theorem cell23_88431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_88431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88431 prefixEnd_88431 := by exact prefixLift 88431
  have htrace : WordTrace (prefixWord ++ tailWord_88431) baseStart_88431 baseEnd_88431 := by
    simpa [prefixWord, tailWord_88431, baseEnd_88431] using wordTrace_append hprefix tailTrace_88431
  have hstable : (prefixWord ++ tailWord_88431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88431).length < 2 ^ (prefixWord ++ tailWord_88431).sum := by decide
  have hdescent : baseEnd_88431 < baseStart_88431 := by decide
  rcases family_descends (prefixWord ++ tailWord_88431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88445 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_88445 : Nat := 118140960795 + 88445 * 2 ^ 59
def prefixEnd_88445 : Nat := 4983230072969 + 3 ^ 40 * 88445 * 2
def baseEnd_88445 : Nat := 45414796487011692230755

theorem tailTrace_88445 : CollatzResearch.WordTrace tailWord_88445 prefixEnd_88445 45414796487011692230755 := by
  unfold tailWord_88445
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225854164586345048522789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2150569443057563365681859 3225854164586345048522789)
  ·
    refine ⟨604847655859939696598023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3225854164586345048522789 604847655859939696598023)
    ·
      refine ⟨907271483789909544897035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604847655859939696598023 907271483789909544897035)
      ·
        refine ⟨1360907225684864317345553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907271483789909544897035 1360907225684864317345553)
        ·
          refine ⟨1020680419263648238009165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360907225684864317345553 1020680419263648238009165)
          ·
            refine ⟨382755157223868089253437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1020680419263648238009165 382755157223868089253437)
            ·
              refine ⟨143533183958950533470039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382755157223868089253437 143533183958950533470039)
              ·
                refine ⟨215299775938425800205059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143533183958950533470039 215299775938425800205059)
                ·
                  refine ⟨322949663907638700307589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215299775938425800205059 322949663907638700307589)
                  ·
                    refine ⟨60553061982682256307673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322949663907638700307589 60553061982682256307673)
                    ·
                      refine ⟨45414796487011692230755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60553061982682256307673 45414796487011692230755)
                      ·
                        rfl

theorem cell23_88445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_88445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88445 prefixEnd_88445 := by exact prefixLift 88445
  have htrace : WordTrace (prefixWord ++ tailWord_88445) baseStart_88445 baseEnd_88445 := by
    simpa [prefixWord, tailWord_88445, baseEnd_88445] using wordTrace_append hprefix tailTrace_88445
  have hstable : (prefixWord ++ tailWord_88445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88445).length < 2 ^ (prefixWord ++ tailWord_88445).sum := by decide
  have hdescent : baseEnd_88445 < baseStart_88445 := by decide
  rcases family_descends (prefixWord ++ tailWord_88445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88462 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_88462 : Nat := 118140960795 + 88462 * 2 ^ 59
def prefixEnd_88462 : Nat := 4983230072969 + 3 ^ 40 * 88462 * 2
def baseEnd_88462 : Nat := 45423525658138125718177

theorem tailTrace_88462 : CollatzResearch.WordTrace tailWord_88462 prefixEnd_88462 45423525658138125718177 := by
  unfold tailWord_88462
  simp only [CollatzResearch.WordTrace]
  refine ⟨403309275690594618986455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2150982803683171301261093 403309275690594618986455)
  ·
    refine ⟨604963913535891928479683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403309275690594618986455 604963913535891928479683)
    ·
      refine ⟨907445870303837892719525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604963913535891928479683 907445870303837892719525)
      ·
        refine ⟨170146100681969604884911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 907445870303837892719525 170146100681969604884911)
        ·
          refine ⟨255219151022954407327367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170146100681969604884911 255219151022954407327367)
          ·
            refine ⟨382828726534431610991051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255219151022954407327367 382828726534431610991051)
            ·
              refine ⟨574243089801647416486577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382828726534431610991051 574243089801647416486577)
              ·
                refine ⟨430682317351235562364933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574243089801647416486577 430682317351235562364933)
                ·
                  refine ⟨80752934503356667943425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430682317351235562364933 80752934503356667943425)
                  ·
                    refine ⟨60564700877517500957569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80752934503356667943425 60564700877517500957569)
                    ·
                      refine ⟨45423525658138125718177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60564700877517500957569 45423525658138125718177)
                      ·
                        rfl

theorem cell23_88462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_88462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88462 prefixEnd_88462 := by exact prefixLift 88462
  have htrace : WordTrace (prefixWord ++ tailWord_88462) baseStart_88462 baseEnd_88462 := by
    simpa [prefixWord, tailWord_88462, baseEnd_88462] using wordTrace_append hprefix tailTrace_88462
  have hstable : (prefixWord ++ tailWord_88462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88462).length < 2 ^ (prefixWord ++ tailWord_88462).sum := by decide
  have hdescent : baseEnd_88462 < baseStart_88462 := by decide
  rcases family_descends (prefixWord ++ tailWord_88462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88485 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 5]
def baseStart_88485 : Nat := 118140960795 + 88485 * 2 ^ 59
def prefixEnd_88485 : Nat := 4983230072969 + 3 ^ 40 * 88485 * 2
def baseEnd_88485 : Nat := 5048370634799059525619

theorem tailTrace_88485 : CollatzResearch.WordTrace tailWord_88485 prefixEnd_88485 5048370634799059525619 := by
  unfold tailWord_88485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227313084441431879978909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2151542056294287919985939 3227313084441431879978909)
  ·
    refine ⟨1210242406665536954992091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3227313084441431879978909 1210242406665536954992091)
    ·
      refine ⟨1815363609998305432488137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210242406665536954992091 1815363609998305432488137)
      ·
        refine ⟨1361522707498729074366103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815363609998305432488137 1361522707498729074366103)
        ·
          refine ⟨2042284061248093611549155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361522707498729074366103 2042284061248093611549155)
          ·
            refine ⟨3063426091872140417323733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042284061248093611549155 3063426091872140417323733)
            ·
              refine ⟨71799049028253291031025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3063426091872140417323733 71799049028253291031025)
              ·
                refine ⟨53849286771189968273269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71799049028253291031025 53849286771189968273269)
                ·
                  refine ⟨5048370634799059525619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53849286771189968273269 5048370634799059525619)
                  ·
                    rfl

theorem cell23_88485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_88485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88485 prefixEnd_88485 := by exact prefixLift 88485
  have htrace : WordTrace (prefixWord ++ tailWord_88485) baseStart_88485 baseEnd_88485 := by
    simpa [prefixWord, tailWord_88485, baseEnd_88485] using wordTrace_append hprefix tailTrace_88485
  have hstable : (prefixWord ++ tailWord_88485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88485).length < 2 ^ (prefixWord ++ tailWord_88485).sum := by decide
  have hdescent : baseEnd_88485 < baseStart_88485 := by decide
  rcases family_descends (prefixWord ++ tailWord_88485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88490 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_88490 : Nat := 118140960795 + 88490 * 2 ^ 59
def prefixEnd_88490 : Nat := 4983230072969 + 3 ^ 40 * 88490 * 2
def baseEnd_88490 : Nat := 45437903116464016168049

theorem tailTrace_88490 : CollatzResearch.WordTrace tailWord_88490 prefixEnd_88490 45437903116464016168049 := by
  unfold tailWord_88490
  simp only [CollatzResearch.WordTrace]
  refine ⟨806873862355829433477731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2151663632948878489273949 806873862355829433477731)
  ·
    refine ⟨1210310793533744150216597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806873862355829433477731 1210310793533744150216597)
    ·
      refine ⟨56733318446894257041403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1210310793533744150216597 56733318446894257041403)
      ·
        refine ⟨85099977670341385562105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56733318446894257041403 85099977670341385562105)
        ·
          refine ⟨63824983252756039171579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85099977670341385562105 63824983252756039171579)
          ·
            refine ⟨95737474879134058757369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63824983252756039171579 95737474879134058757369)
            ·
              refine ⟨71803106159350544068027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95737474879134058757369 71803106159350544068027)
              ·
                refine ⟨107704659239025816102041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71803106159350544068027 107704659239025816102041)
                ·
                  refine ⟨80778494429269362076531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107704659239025816102041 80778494429269362076531)
                  ·
                    refine ⟨121167741643904043114797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80778494429269362076531 121167741643904043114797)
                    ·
                      refine ⟨45437903116464016168049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121167741643904043114797 45437903116464016168049)
                      ·
                        rfl

theorem cell23_88490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_88490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88490 prefixEnd_88490 := by exact prefixLift 88490
  have htrace : WordTrace (prefixWord ++ tailWord_88490) baseStart_88490 baseEnd_88490 := by
    simpa [prefixWord, tailWord_88490, baseEnd_88490] using wordTrace_append hprefix tailTrace_88490
  have hstable : (prefixWord ++ tailWord_88490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88490).length < 2 ^ (prefixWord ++ tailWord_88490).sum := by decide
  have hdescent : baseEnd_88490 < baseStart_88490 := by decide
  rcases family_descends (prefixWord ++ tailWord_88490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88531 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_88531 : Nat := 118140960795 + 88531 * 2 ^ 59
def prefixEnd_88531 : Nat := 4983230072969 + 3 ^ 40 * 88531 * 2
def baseEnd_88531 : Nat := 45458955823298355755359

theorem tailTrace_88531 : CollatzResearch.WordTrace tailWord_88531 prefixEnd_88531 45458955823298355755359 := by
  unfold tailWord_88531
  simp only [CollatzResearch.WordTrace]
  refine ⟨3228990842274781736153447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2152660561516521157435631 3228990842274781736153447)
  ·
    refine ⟨4843486263412172604230171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3228990842274781736153447 4843486263412172604230171)
    ·
      refine ⟨7265229395118258906345257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843486263412172604230171 7265229395118258906345257)
      ·
        refine ⟨5448922046338694179758943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7265229395118258906345257 5448922046338694179758943)
        ·
          refine ⟨8173383069508041269638415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5448922046338694179758943 8173383069508041269638415)
          ·
            refine ⟨12260074604262061904457623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173383069508041269638415 12260074604262061904457623)
            ·
              refine ⟨18390111906393092856686435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12260074604262061904457623 18390111906393092856686435)
              ·
                refine ⟨27585167859589639285029653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18390111906393092856686435 27585167859589639285029653)
                ·
                  refine ⟨1293054743418264341485765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27585167859589639285029653 1293054743418264341485765)
                  ·
                    refine ⟨242447764390924564028581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293054743418264341485765 242447764390924564028581)
                    ·
                      refine ⟨45458955823298355755359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 242447764390924564028581 45458955823298355755359)
                      ·
                        rfl

theorem cell23_88531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_88531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88531 prefixEnd_88531 := by exact prefixLift 88531
  have htrace : WordTrace (prefixWord ++ tailWord_88531) baseStart_88531 baseEnd_88531 := by
    simpa [prefixWord, tailWord_88531, baseEnd_88531] using wordTrace_append hprefix tailTrace_88531
  have hstable : (prefixWord ++ tailWord_88531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88531).length < 2 ^ (prefixWord ++ tailWord_88531).sum := by decide
  have hdescent : baseEnd_88531 < baseStart_88531 := by decide
  rcases family_descends (prefixWord ++ tailWord_88531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88562 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_88562 : Nat := 118140960795 + 88562 * 2 ^ 59
def prefixEnd_88562 : Nat := 4983230072969 + 3 ^ 40 * 88562 * 2
def baseEnd_88562 : Nat := 15158291241195911489239

theorem tailTrace_88562 : CollatzResearch.WordTrace tailWord_88562 prefixEnd_88562 15158291241195911489239 := by
  unfold tailWord_88562
  simp only [CollatzResearch.WordTrace]
  refine ⟨807530376290618507632985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2153414336774982687021293 807530376290618507632985)
  ·
    refine ⟨605647782217963880724739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 807530376290618507632985 605647782217963880724739)
    ·
      refine ⟨908471673326945821087109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605647782217963880724739 908471673326945821087109)
      ·
        refine ⟨170338438748802341453833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 908471673326945821087109 170338438748802341453833)
        ·
          refine ⟨127753829061601756090375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170338438748802341453833 127753829061601756090375)
          ·
            refine ⟨191630743592402634135563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127753829061601756090375 191630743592402634135563)
            ·
              refine ⟨287446115388603951203345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191630743592402634135563 287446115388603951203345)
              ·
                refine ⟨215584586541452963402509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287446115388603951203345 215584586541452963402509)
                ·
                  refine ⟨80844219953044861275941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215584586541452963402509 80844219953044861275941)
                  ·
                    refine ⟨15158291241195911489239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80844219953044861275941 15158291241195911489239)
                    ·
                      rfl

theorem cell23_88562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_88562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88562 prefixEnd_88562 := by exact prefixLift 88562
  have htrace : WordTrace (prefixWord ++ tailWord_88562) baseStart_88562 baseEnd_88562 := by
    simpa [prefixWord, tailWord_88562, baseEnd_88562] using wordTrace_append hprefix tailTrace_88562
  have hstable : (prefixWord ++ tailWord_88562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88562).length < 2 ^ (prefixWord ++ tailWord_88562).sum := by decide
  have hdescent : baseEnd_88562 < baseStart_88562 := by decide
  rcases family_descends (prefixWord ++ tailWord_88562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88595 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 4, 3, 2]
def baseStart_88595 : Nat := 118140960795 + 88595 * 2 ^ 59
def prefixEnd_88595 : Nat := 4983230072969 + 3 ^ 40 * 88595 * 2
def baseEnd_88595 : Nat := 45491818585186105355065

theorem tailTrace_88595 : CollatzResearch.WordTrace tailWord_88595 prefixEnd_88595 45491818585186105355065 := by
  unfold tailWord_88595
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231325114042920666483239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2154216742695280444322159 3231325114042920666483239)
  ·
    refine ⟨4846987671064380999724859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231325114042920666483239 4846987671064380999724859)
    ·
      refine ⟨7270481506596571499587289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846987671064380999724859 7270481506596571499587289)
      ·
        refine ⟨5452861129947428624690467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7270481506596571499587289 5452861129947428624690467)
        ·
          refine ⟨8179291694921142937035701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452861129947428624690467 8179291694921142937035701)
          ·
            refine ⟨766808596398857150347097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8179291694921142937035701 766808596398857150347097)
            ·
              refine ⟨575106447299142862760323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766808596398857150347097 575106447299142862760323)
              ·
                refine ⟨862659670948714294140485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575106447299142862760323 862659670948714294140485)
                ·
                  refine ⟨161748688302883930151341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862659670948714294140485 161748688302883930151341)
                  ·
                    refine ⟨60655758113581473806753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161748688302883930151341 60655758113581473806753)
                    ·
                      refine ⟨45491818585186105355065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60655758113581473806753 45491818585186105355065)
                      ·
                        rfl

theorem cell23_88595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 3, 2].length) (baseStart_88595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88595 prefixEnd_88595 := by exact prefixLift 88595
  have htrace : WordTrace (prefixWord ++ tailWord_88595) baseStart_88595 baseEnd_88595 := by
    simpa [prefixWord, tailWord_88595, baseEnd_88595] using wordTrace_append hprefix tailTrace_88595
  have hstable : (prefixWord ++ tailWord_88595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88595).length < 2 ^ (prefixWord ++ tailWord_88595).sum := by decide
  have hdescent : baseEnd_88595 < baseStart_88595 := by decide
  rcases family_descends (prefixWord ++ tailWord_88595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88625 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_88625 : Nat := 118140960795 + 88625 * 2 ^ 59
def prefixEnd_88625 : Nat := 4983230072969 + 3 ^ 40 * 88625 * 2
def baseEnd_88625 : Nat := 45507223004820987979927

theorem tailTrace_88625 : CollatzResearch.WordTrace tailWord_88625 prefixEnd_88625 45507223004820987979927 := by
  unfold tailWord_88625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232419303934235790075329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2154946202622823860050219 3232419303934235790075329)
  ·
    refine ⟨2424314477950676842556497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3232419303934235790075329 2424314477950676842556497)
    ·
      refine ⟨1818235858463007631917373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2424314477950676842556497 1818235858463007631917373)
      ·
        refine ⟨681838446923627861969015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1818235858463007631917373 681838446923627861969015)
        ·
          refine ⟨1022757670385441792953523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681838446923627861969015 1022757670385441792953523)
          ·
            refine ⟨1534136505578162689430285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022757670385441792953523 1534136505578162689430285)
            ·
              refine ⟨575301189591811008536357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1534136505578162689430285 575301189591811008536357)
              ·
                refine ⟨107868973048464564100567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575301189591811008536357 107868973048464564100567)
                ·
                  refine ⟨161803459572696846150851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107868973048464564100567 161803459572696846150851)
                  ·
                    refine ⟨242705189359045269226277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161803459572696846150851 242705189359045269226277)
                    ·
                      refine ⟨45507223004820987979927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 242705189359045269226277 45507223004820987979927)
                      ·
                        rfl

theorem cell23_88625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_88625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88625 prefixEnd_88625 := by exact prefixLift 88625
  have htrace : WordTrace (prefixWord ++ tailWord_88625) baseStart_88625 baseEnd_88625 := by
    simpa [prefixWord, tailWord_88625, baseEnd_88625] using wordTrace_append hprefix tailTrace_88625
  have hstable : (prefixWord ++ tailWord_88625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88625).length < 2 ^ (prefixWord ++ tailWord_88625).sum := by decide
  have hdescent : baseEnd_88625 < baseStart_88625 := by decide
  rcases family_descends (prefixWord ++ tailWord_88625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88636 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_88636 : Nat := 118140960795 + 88636 * 2 ^ 59
def prefixEnd_88636 : Nat := 4983230072969 + 3 ^ 40 * 88636 * 2
def baseEnd_88636 : Nat := 45512871292020444942377

theorem tailTrace_88636 : CollatzResearch.WordTrace tailWord_88636 prefixEnd_88636 45512871292020444942377 := by
  unfold tailWord_88636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616410253447192334362881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2155213671262923112483841 1616410253447192334362881)
  ·
    refine ⟨1212307690085394250772161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1616410253447192334362881 1212307690085394250772161)
    ·
      refine ⟨909230767564045688079121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1212307690085394250772161 909230767564045688079121)
      ·
        refine ⟨681923075673034266059341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909230767564045688079121 681923075673034266059341)
        ·
          refine ⟨255721153377387849772253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681923075673034266059341 255721153377387849772253)
          ·
            refine ⟨95895432516520443664595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255721153377387849772253 95895432516520443664595)
            ·
              refine ⟨143843148774780665496893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95895432516520443664595 143843148774780665496893)
              ·
                refine ⟨53941180790542749561335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143843148774780665496893 53941180790542749561335)
                ·
                  refine ⟨80911771185814124342003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53941180790542749561335 80911771185814124342003)
                  ·
                    refine ⟨121367656778721186513005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80911771185814124342003 121367656778721186513005)
                    ·
                      refine ⟨45512871292020444942377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121367656778721186513005 45512871292020444942377)
                      ·
                        rfl

theorem cell23_88636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_88636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88636 prefixEnd_88636 := by exact prefixLift 88636
  have htrace : WordTrace (prefixWord ++ tailWord_88636) baseStart_88636 baseEnd_88636 := by
    simpa [prefixWord, tailWord_88636, baseEnd_88636] using wordTrace_append hprefix tailTrace_88636
  have hstable : (prefixWord ++ tailWord_88636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88636).length < 2 ^ (prefixWord ++ tailWord_88636).sum := by decide
  have hdescent : baseEnd_88636 < baseStart_88636 := by decide
  rcases family_descends (prefixWord ++ tailWord_88636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88645 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_88645 : Nat := 118140960795 + 88645 * 2 ^ 59
def prefixEnd_88645 : Nat := 4983230072969 + 3 ^ 40 * 88645 * 2
def baseEnd_88645 : Nat := 45517492617910909729835

theorem tailTrace_88645 : CollatzResearch.WordTrace tailWord_88645 prefixEnd_88645 45517492617910909729835 := by
  unfold tailWord_88645
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233148763861779205803389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2155432509241186137202259 3233148763861779205803389)
  ·
    refine ⟨1212430786448167202176271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3233148763861779205803389 1212430786448167202176271)
    ·
      refine ⟨1818646179672250803264407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212430786448167202176271 1818646179672250803264407)
      ·
        refine ⟨2727969269508376204896611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818646179672250803264407 2727969269508376204896611)
        ·
          refine ⟨4091953904262564307344917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727969269508376204896611 4091953904262564307344917)
          ·
            refine ⟨191810339262307701906793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4091953904262564307344917 191810339262307701906793)
            ·
              refine ⟨143857754446730776430095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191810339262307701906793 143857754446730776430095)
              ·
                refine ⟨215786631670096164645143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143857754446730776430095 215786631670096164645143)
                ·
                  refine ⟨323679947505144246967715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215786631670096164645143 323679947505144246967715)
                  ·
                    refine ⟨485519921257716370451573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323679947505144246967715 485519921257716370451573)
                    ·
                      refine ⟨45517492617910909729835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 485519921257716370451573 45517492617910909729835)
                      ·
                        rfl

theorem cell23_88645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_88645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88645 prefixEnd_88645 := by exact prefixLift 88645
  have htrace : WordTrace (prefixWord ++ tailWord_88645) baseStart_88645 baseEnd_88645 := by
    simpa [prefixWord, tailWord_88645, baseEnd_88645] using wordTrace_append hprefix tailTrace_88645
  have hstable : (prefixWord ++ tailWord_88645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88645).length < 2 ^ (prefixWord ++ tailWord_88645).sum := by decide
  have hdescent : baseEnd_88645 < baseStart_88645 := by decide
  rcases family_descends (prefixWord ++ tailWord_88645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88646 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_88646 : Nat := 118140960795 + 88646 * 2 ^ 59
def prefixEnd_88646 : Nat := 4983230072969 + 3 ^ 40 * 88646 * 2
def baseEnd_88646 : Nat := 45518006098565405817331

theorem tailTrace_88646 : CollatzResearch.WordTrace tailWord_88646 prefixEnd_88646 45518006098565405817331 := by
  unfold tailWord_88646
  simp only [CollatzResearch.WordTrace]
  refine ⟨101037038651817386768431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2155456824572104251059861 101037038651817386768431)
  ·
    refine ⟨151555557977726080152647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101037038651817386768431 151555557977726080152647)
    ·
      refine ⟨227333336966589120228971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151555557977726080152647 227333336966589120228971)
      ·
        refine ⟨341000005449883680343457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227333336966589120228971 341000005449883680343457)
        ·
          refine ⟨255750004087412760257593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341000005449883680343457 255750004087412760257593)
          ·
            refine ⟨191812503065559570193195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255750004087412760257593 191812503065559570193195)
            ·
              refine ⟨287718754598339355289793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191812503065559570193195 287718754598339355289793)
              ·
                refine ⟨215789065948754516467345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287718754598339355289793 215789065948754516467345)
                ·
                  refine ⟨161841799461565887350509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215789065948754516467345 161841799461565887350509)
                  ·
                    refine ⟨60690674798087207756441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161841799461565887350509 60690674798087207756441)
                    ·
                      refine ⟨45518006098565405817331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60690674798087207756441 45518006098565405817331)
                      ·
                        rfl

theorem cell23_88646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_88646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88646 prefixEnd_88646 := by exact prefixLift 88646
  have htrace : WordTrace (prefixWord ++ tailWord_88646) baseStart_88646 baseEnd_88646 := by
    simpa [prefixWord, tailWord_88646, baseEnd_88646] using wordTrace_append hprefix tailTrace_88646
  have hstable : (prefixWord ++ tailWord_88646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88646).length < 2 ^ (prefixWord ++ tailWord_88646).sum := by decide
  have hdescent : baseEnd_88646 < baseStart_88646 := by decide
  rcases family_descends (prefixWord ++ tailWord_88646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88653 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_88653 : Nat := 118140960795 + 88653 * 2 ^ 59
def prefixEnd_88653 : Nat := 4983230072969 + 3 ^ 40 * 88653 * 2
def baseEnd_88653 : Nat := 45521600463146878429799

theorem tailTrace_88653 : CollatzResearch.WordTrace tailWord_88653 prefixEnd_88653 45521600463146878429799 := by
  unfold tailWord_88653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233440547832796572094613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2155627031888531048063075 3233440547832796572094613)
  ·
    refine ⟨151567525679662339316935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3233440547832796572094613 151567525679662339316935)
    ·
      refine ⟨227351288519493508975403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151567525679662339316935 227351288519493508975403)
      ·
        refine ⟨341026932779240263463105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227351288519493508975403 341026932779240263463105)
        ·
          refine ⟨255770199584430197597329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341026932779240263463105 255770199584430197597329)
          ·
            refine ⟨191827649688322648197997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255770199584430197597329 191827649688322648197997)
            ·
              refine ⟨71935368633120993074249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191827649688322648197997 71935368633120993074249)
              ·
                refine ⟨53951526474840744805687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71935368633120993074249 53951526474840744805687)
                ·
                  refine ⟨80927289712261117208531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53951526474840744805687 80927289712261117208531)
                  ·
                    refine ⟨121390934568391675812797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80927289712261117208531 121390934568391675812797)
                    ·
                      refine ⟨45521600463146878429799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121390934568391675812797 45521600463146878429799)
                      ·
                        rfl

theorem cell23_88653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_88653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88653 prefixEnd_88653 := by exact prefixLift 88653
  have htrace : WordTrace (prefixWord ++ tailWord_88653) baseStart_88653 baseEnd_88653 := by
    simpa [prefixWord, tailWord_88653, baseEnd_88653] using wordTrace_append hprefix tailTrace_88653
  have hstable : (prefixWord ++ tailWord_88653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88653).length < 2 ^ (prefixWord ++ tailWord_88653).sum := by decide
  have hdescent : baseEnd_88653 < baseStart_88653 := by decide
  rcases family_descends (prefixWord ++ tailWord_88653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88675 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3]
def baseStart_88675 : Nat := 118140960795 + 88675 * 2 ^ 59
def prefixEnd_88675 : Nat := 4983230072969 + 3 ^ 40 * 88675 * 2
def baseEnd_88675 : Nat := 45532897037545792354697

theorem tailTrace_88675 : CollatzResearch.WordTrace tailWord_88675 prefixEnd_88675 45532897037545792354697 := by
  unfold tailWord_88675
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234242953753094329395479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2156161969168729552930319 3234242953753094329395479)
  ·
    refine ⟨4851364430629641494093219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234242953753094329395479 4851364430629641494093219)
    ·
      refine ⟨7277046645944462241139829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4851364430629641494093219 7277046645944462241139829)
      ·
        refine ⟨682223123057293335106859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7277046645944462241139829 682223123057293335106859)
        ·
          refine ⟨1023334684585940002660289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682223123057293335106859 1023334684585940002660289)
          ·
            refine ⟨767501013439455001995217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023334684585940002660289 767501013439455001995217)
            ·
              refine ⟨575625760079591251496413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767501013439455001995217 575625760079591251496413)
              ·
                refine ⟨215859660029846719311155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575625760079591251496413 215859660029846719311155)
                ·
                  refine ⟨323789490044770078966733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215859660029846719311155 323789490044770078966733)
                  ·
                    refine ⟨121421058766788779612525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323789490044770078966733 121421058766788779612525)
                    ·
                      refine ⟨45532897037545792354697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121421058766788779612525 45532897037545792354697)
                      ·
                        rfl

theorem cell23_88675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_88675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88675 prefixEnd_88675 := by exact prefixLift 88675
  have htrace : WordTrace (prefixWord ++ tailWord_88675) baseStart_88675 baseEnd_88675 := by
    simpa [prefixWord, tailWord_88675, baseEnd_88675] using wordTrace_append hprefix tailTrace_88675
  have hstable : (prefixWord ++ tailWord_88675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88675).length < 2 ^ (prefixWord ++ tailWord_88675).sum := by decide
  have hdescent : baseEnd_88675 < baseStart_88675 := by decide
  rcases family_descends (prefixWord ++ tailWord_88675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88709 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_88709 : Nat := 118140960795 + 88709 * 2 ^ 59
def prefixEnd_88709 : Nat := 4983230072969 + 3 ^ 40 * 88709 * 2
def baseEnd_88709 : Nat := 45550355379798659329541

theorem tailTrace_88709 : CollatzResearch.WordTrace tailWord_88709 prefixEnd_88709 45550355379798659329541 := by
  unfold tailWord_88709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235483035629918136133181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2156988690419945424088787 3235483035629918136133181)
  ·
    refine ⟨1213306138361219301049943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3235483035629918136133181 1213306138361219301049943)
    ·
      refine ⟨1819959207541828951574915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213306138361219301049943 1819959207541828951574915)
      ·
        refine ⟨2729938811312743427362373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819959207541828951574915 2729938811312743427362373)
        ·
          refine ⟨511863527121139392630445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2729938811312743427362373 511863527121139392630445)
          ·
            refine ⟨191948822670427272236417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511863527121139392630445 191948822670427272236417)
            ·
              refine ⟨143961617002820454177313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191948822670427272236417 143961617002820454177313)
              ·
                refine ⟨107971212752115340632985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143961617002820454177313 107971212752115340632985)
                ·
                  refine ⟨80978409564086505474739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107971212752115340632985 80978409564086505474739)
                  ·
                    refine ⟨121467614346129758212109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80978409564086505474739 121467614346129758212109)
                    ·
                      refine ⟨45550355379798659329541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121467614346129758212109 45550355379798659329541)
                      ·
                        rfl

theorem cell23_88709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_88709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88709 prefixEnd_88709 := by exact prefixLift 88709
  have htrace : WordTrace (prefixWord ++ tailWord_88709) baseStart_88709 baseEnd_88709 := by
    simpa [prefixWord, tailWord_88709, baseEnd_88709] using wordTrace_append hprefix tailTrace_88709
  have hstable : (prefixWord ++ tailWord_88709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88709).length < 2 ^ (prefixWord ++ tailWord_88709).sum := by decide
  have hdescent : baseEnd_88709 < baseStart_88709 := by decide
  rcases family_descends (prefixWord ++ tailWord_88709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88749 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_88749 : Nat := 118140960795 + 88749 * 2 ^ 59
def prefixEnd_88749 : Nat := 4983230072969 + 3 ^ 40 * 88749 * 2
def baseEnd_88749 : Nat := 45570894605978502829357

theorem tailTrace_88749 : CollatzResearch.WordTrace tailWord_88749 prefixEnd_88749 45570894605978502829357 := by
  unfold tailWord_88749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236941955485004967589301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2157961303656669978392867 3236941955485004967589301)
  ·
    refine ⟨303463308326719215711497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3236941955485004967589301 303463308326719215711497)
    ·
      refine ⟨227597481245039411783623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303463308326719215711497 227597481245039411783623)
      ·
        refine ⟨341396221867559117675435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227597481245039411783623 341396221867559117675435)
        ·
          refine ⟨512094332801338676513153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341396221867559117675435 512094332801338676513153)
          ·
            refine ⟨384070749601004007384865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512094332801338676513153 384070749601004007384865)
            ·
              refine ⟨288053062200753005538649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384070749601004007384865 288053062200753005538649)
              ·
                refine ⟨216039796650564754153987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288053062200753005538649 216039796650564754153987)
                ·
                  refine ⟨324059694975847131230981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216039796650564754153987 324059694975847131230981)
                  ·
                    refine ⟨60761192807971337105809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324059694975847131230981 60761192807971337105809)
                    ·
                      refine ⟨45570894605978502829357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60761192807971337105809 45570894605978502829357)
                      ·
                        rfl

theorem cell23_88749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_88749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88749 prefixEnd_88749 := by exact prefixLift 88749
  have htrace : WordTrace (prefixWord ++ tailWord_88749) baseStart_88749 baseEnd_88749 := by
    simpa [prefixWord, tailWord_88749, baseEnd_88749] using wordTrace_append hprefix tailTrace_88749
  have hstable : (prefixWord ++ tailWord_88749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88749).length < 2 ^ (prefixWord ++ tailWord_88749).sum := by decide
  have hdescent : baseEnd_88749 < baseStart_88749 := by decide
  rcases family_descends (prefixWord ++ tailWord_88749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88772 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 7]
def baseStart_88772 : Nat := 118140960795 + 88772 * 2 ^ 59
def prefixEnd_88772 : Nat := 4983230072969 + 3 ^ 40 * 88772 * 2
def baseEnd_88772 : Nat := 5064744962336879204639

theorem tailTrace_88772 : CollatzResearch.WordTrace tailWord_88772 prefixEnd_88772 5064744962336879204639 := by
  unfold tailWord_88772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618890417200839947838285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2158520556267786597117713 1618890417200839947838285)
  ·
    refine ⟨607083906450314980439357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1618890417200839947838285 607083906450314980439357)
    ·
      refine ⟨227656464918868117664759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 607083906450314980439357 227656464918868117664759)
      ·
        refine ⟨341484697378302176497139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227656464918868117664759 341484697378302176497139)
        ·
          refine ⟨512227046067453264745709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341484697378302176497139 512227046067453264745709)
          ·
            refine ⟨192085142275294974279641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512227046067453264745709 192085142275294974279641)
            ·
              refine ⟨144063856706471230709731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192085142275294974279641 144063856706471230709731)
              ·
                refine ⟨216095785059706846064597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144063856706471230709731 216095785059706846064597)
                ·
                  refine ⟨5064744962336879204639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 216095785059706846064597 5064744962336879204639)
                  ·
                    rfl

theorem cell23_88772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_88772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88772 prefixEnd_88772 := by exact prefixLift 88772
  have htrace : WordTrace (prefixWord ++ tailWord_88772) baseStart_88772 baseEnd_88772 := by
    simpa [prefixWord, tailWord_88772, baseEnd_88772] using wordTrace_append hprefix tailTrace_88772
  have hstable : (prefixWord ++ tailWord_88772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88772).length < 2 ^ (prefixWord ++ tailWord_88772).sum := by decide
  have hdescent : baseEnd_88772 < baseStart_88772 := by decide
  rcases family_descends (prefixWord ++ tailWord_88772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88782 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_88782 : Nat := 118140960795 + 88782 * 2 ^ 59
def prefixEnd_88782 : Nat := 4983230072969 + 3 ^ 40 * 88782 * 2
def baseEnd_88782 : Nat := 45587839467576873716705

theorem tailTrace_88782 : CollatzResearch.WordTrace tailWord_88782 prefixEnd_88782 45587839467576873716705 := by
  unfold tailWord_88782
  simp only [CollatzResearch.WordTrace]
  refine ⟨404768195545681450442575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2158763709576967735693733 404768195545681450442575)
  ·
    refine ⟨607152293318522175663863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 404768195545681450442575 607152293318522175663863)
    ·
      refine ⟨910728439977783263495795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607152293318522175663863 910728439977783263495795)
      ·
        refine ⟨1366092659966674895243693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910728439977783263495795 1366092659966674895243693)
        ·
          refine ⟨512284747487503085716385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1366092659966674895243693 512284747487503085716385)
          ·
            refine ⟨384213560615627314287289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512284747487503085716385 384213560615627314287289)
            ·
              refine ⟨288160170461720485715467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384213560615627314287289 288160170461720485715467)
              ·
                refine ⟨432240255692580728573201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288160170461720485715467 432240255692580728573201)
                ·
                  refine ⟨324180191769435546429901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432240255692580728573201 324180191769435546429901)
                  ·
                    refine ⟨121567571913538329911213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324180191769435546429901 121567571913538329911213)
                    ·
                      refine ⟨45587839467576873716705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121567571913538329911213 45587839467576873716705)
                      ·
                        rfl

theorem cell23_88782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_88782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88782 prefixEnd_88782 := by exact prefixLift 88782
  have htrace : WordTrace (prefixWord ++ tailWord_88782) baseStart_88782 baseEnd_88782 := by
    simpa [prefixWord, tailWord_88782, baseEnd_88782] using wordTrace_append hprefix tailTrace_88782
  have hstable : (prefixWord ++ tailWord_88782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88782).length < 2 ^ (prefixWord ++ tailWord_88782).sum := by decide
  have hdescent : baseEnd_88782 < baseStart_88782 := by decide
  rcases family_descends (prefixWord ++ tailWord_88782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88842 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_88842 : Nat := 118140960795 + 88842 * 2 ^ 59
def prefixEnd_88842 : Nat := 4983230072969 + 3 ^ 40 * 88842 * 2
def baseEnd_88842 : Nat := 45618648306846638966429

theorem tailTrace_88842 : CollatzResearch.WordTrace tailWord_88842 prefixEnd_88842 45618648306846638966429 := by
  unfold tailWord_88842
  simp only [CollatzResearch.WordTrace]
  refine ⟨810083486037020462681195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2160222629432054567149853 810083486037020462681195)
  ·
    refine ⟨1215125229055530694021793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810083486037020462681195 1215125229055530694021793)
    ·
      refine ⟨911343921791648020516345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1215125229055530694021793 911343921791648020516345)
      ·
        refine ⟨683507941343736015387259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911343921791648020516345 683507941343736015387259)
        ·
          refine ⟨1025261912015604023080889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683507941343736015387259 1025261912015604023080889)
          ·
            refine ⟨768946434011703017310667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025261912015604023080889 768946434011703017310667)
            ·
              refine ⟨1153419651017554525966001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768946434011703017310667 1153419651017554525966001)
              ·
                refine ⟨865064738263165894474501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153419651017554525966001 865064738263165894474501)
                ·
                  refine ⟨162199638424343605213969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865064738263165894474501 162199638424343605213969)
                  ·
                    refine ⟨121649728818257703910477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162199638424343605213969 121649728818257703910477)
                    ·
                      refine ⟨45618648306846638966429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121649728818257703910477 45618648306846638966429)
                      ·
                        rfl

theorem cell23_88842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_88842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88842 prefixEnd_88842 := by exact prefixLift 88842
  have htrace : WordTrace (prefixWord ++ tailWord_88842) baseStart_88842 baseEnd_88842 := by
    simpa [prefixWord, tailWord_88842, baseEnd_88842] using wordTrace_append hprefix tailTrace_88842
  have hstable : (prefixWord ++ tailWord_88842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88842).length < 2 ^ (prefixWord ++ tailWord_88842).sum := by decide
  have hdescent : baseEnd_88842 < baseStart_88842 := by decide
  rcases family_descends (prefixWord ++ tailWord_88842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88875 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 5, 5]
def baseStart_88875 : Nat := 118140960795 + 88875 * 2 ^ 59
def prefixEnd_88875 : Nat := 4983230072969 + 3 ^ 40 * 88875 * 2
def baseEnd_88875 : Nat := 15211864389481669951259

theorem tailTrace_88875 : CollatzResearch.WordTrace tailWord_88875 prefixEnd_88875 15211864389481669951259 := by
  unfold tailWord_88875
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241537553028528486676079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2161025035352352324450719 3241537553028528486676079)
  ·
    refine ⟨4862306329542792730014119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3241537553028528486676079 4862306329542792730014119)
    ·
      refine ⟨7293459494314189095021179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862306329542792730014119 7293459494314189095021179)
      ·
        refine ⟨10940189241471283642531769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293459494314189095021179 10940189241471283642531769)
        ·
          refine ⟨8205141931103462731898827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10940189241471283642531769 8205141931103462731898827)
          ·
            refine ⟨12307712896655194097848241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8205141931103462731898827 12307712896655194097848241)
            ·
              refine ⟨9230784672491395573386181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12307712896655194097848241 9230784672491395573386181)
              ·
                refine ⟨1730772126092136670009909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9230784672491395573386181 1730772126092136670009909)
                ·
                  refine ⟨162259886821137812813429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1730772126092136670009909 162259886821137812813429)
                  ·
                    refine ⟨15211864389481669951259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162259886821137812813429 15211864389481669951259)
                    ·
                      rfl

theorem cell23_88875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 5].length) (baseStart_88875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88875 prefixEnd_88875 := by exact prefixLift 88875
  have htrace : WordTrace (prefixWord ++ tailWord_88875) baseStart_88875 baseEnd_88875 := by
    simpa [prefixWord, tailWord_88875, baseEnd_88875] using wordTrace_append hprefix tailTrace_88875
  have hstable : (prefixWord ++ tailWord_88875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88875).length < 2 ^ (prefixWord ++ tailWord_88875).sum := by decide
  have hdescent : baseEnd_88875 < baseStart_88875 := by decide
  rcases family_descends (prefixWord ++ tailWord_88875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88883 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 1, 4]
def baseStart_88883 : Nat := 118140960795 + 88883 * 2 ^ 59
def prefixEnd_88883 : Nat := 4983230072969 + 3 ^ 40 * 88883 * 2
def baseEnd_88883 : Nat := 15213233671226992851247

theorem tailTrace_88883 : CollatzResearch.WordTrace tailWord_88883 prefixEnd_88883 15213233671226992851247 := by
  unfold tailWord_88883
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241829336999545852967303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2161219557999697235311535 3241829336999545852967303)
  ·
    refine ⟨4862744005499318779450955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3241829336999545852967303 4862744005499318779450955)
    ·
      refine ⟨7294116008248978169176433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862744005499318779450955 7294116008248978169176433)
      ·
        refine ⟨5470587006186733626882325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7294116008248978169176433 5470587006186733626882325)
        ·
          refine ⟨256433765915003138760109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5470587006186733626882325 256433765915003138760109)
          ·
            refine ⟨96162662218126177035041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256433765915003138760109 96162662218126177035041)
            ·
              refine ⟨72121996663594632776281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96162662218126177035041 72121996663594632776281)
              ·
                refine ⟨54091497497695974582211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72121996663594632776281 54091497497695974582211)
                ·
                  refine ⟨81137246246543961873317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54091497497695974582211 81137246246543961873317)
                  ·
                    refine ⟨15213233671226992851247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81137246246543961873317 15213233671226992851247)
                    ·
                      rfl

theorem cell23_88883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 4].length) (baseStart_88883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88883 prefixEnd_88883 := by exact prefixLift 88883
  have htrace : WordTrace (prefixWord ++ tailWord_88883) baseStart_88883 baseEnd_88883 := by
    simpa [prefixWord, tailWord_88883, baseEnd_88883] using wordTrace_append hprefix tailTrace_88883
  have hstable : (prefixWord ++ tailWord_88883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88883).length < 2 ^ (prefixWord ++ tailWord_88883).sum := by decide
  have hdescent : baseEnd_88883 < baseStart_88883 := by decide
  rcases family_descends (prefixWord ++ tailWord_88883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88912 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_88912 : Nat := 118140960795 + 88912 * 2 ^ 59
def prefixEnd_88912 : Nat := 4983230072969 + 3 ^ 40 * 88912 * 2
def baseEnd_88912 : Nat := 45654591952661365091107

theorem tailTrace_88912 : CollatzResearch.WordTrace tailWord_88912 prefixEnd_88912 45654591952661365091107 := by
  unfold tailWord_88912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621443526947241902886495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2161924702596322537181993 1621443526947241902886495)
  ·
    refine ⟨2432165290420862854329743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621443526947241902886495 2432165290420862854329743)
    ·
      refine ⟨3648247935631294281494615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432165290420862854329743 3648247935631294281494615)
      ·
        refine ⟨5472371903446941422241923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648247935631294281494615 5472371903446941422241923)
        ·
          refine ⟨8208557855170412133362885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472371903446941422241923 8208557855170412133362885)
          ·
            refine ⟨1539104597844452275005541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8208557855170412133362885 1539104597844452275005541)
            ·
              refine ⟨288582112095834801563539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1539104597844452275005541 288582112095834801563539)
              ·
                refine ⟨432873168143752202345309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288582112095834801563539 432873168143752202345309)
                ·
                  refine ⟨162327438053907075879491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432873168143752202345309 162327438053907075879491)
                  ·
                    refine ⟨243491157080860613819237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162327438053907075879491 243491157080860613819237)
                    ·
                      refine ⟨45654591952661365091107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 243491157080860613819237 45654591952661365091107)
                      ·
                        rfl

theorem cell23_88912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_88912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88912 prefixEnd_88912 := by exact prefixLift 88912
  have htrace : WordTrace (prefixWord ++ tailWord_88912) baseStart_88912 baseEnd_88912 := by
    simpa [prefixWord, tailWord_88912, baseEnd_88912] using wordTrace_append hprefix tailTrace_88912
  have hstable : (prefixWord ++ tailWord_88912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88912).length < 2 ^ (prefixWord ++ tailWord_88912).sum := by decide
  have hdescent : baseEnd_88912 < baseStart_88912 := by decide
  rcases family_descends (prefixWord ++ tailWord_88912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88916 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_88916 : Nat := 118140960795 + 88916 * 2 ^ 59
def prefixEnd_88916 : Nat := 4983230072969 + 3 ^ 40 * 88916 * 2
def baseEnd_88916 : Nat := 45656645875279349441089

theorem tailTrace_88916 : CollatzResearch.WordTrace tailWord_88916 prefixEnd_88916 45656645875279349441089 := by
  unfold tailWord_88916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621516472939996244459301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2162021963919994992612401 1621516472939996244459301)
  ·
    refine ⟨304034338676249295836119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1621516472939996244459301 304034338676249295836119)
    ·
      refine ⟨456051508014373943754179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304034338676249295836119 456051508014373943754179)
      ·
        refine ⟨684077262021560915631269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456051508014373943754179 684077262021560915631269)
        ·
          refine ⟨128264486629042671680863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 684077262021560915631269 128264486629042671680863)
          ·
            refine ⟨192396729943564007521295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128264486629042671680863 192396729943564007521295)
            ·
              refine ⟨288595094915346011281943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192396729943564007521295 288595094915346011281943)
              ·
                refine ⟨432892642373019016922915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288595094915346011281943 432892642373019016922915)
                ·
                  refine ⟨649338963559528525384373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432892642373019016922915 649338963559528525384373)
                  ·
                    refine ⟨60875527833705799254785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 649338963559528525384373 60875527833705799254785)
                    ·
                      refine ⟨45656645875279349441089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60875527833705799254785 45656645875279349441089)
                      ·
                        rfl

theorem cell23_88916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_88916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88916 prefixEnd_88916 := by exact prefixLift 88916
  have htrace : WordTrace (prefixWord ++ tailWord_88916) baseStart_88916 baseEnd_88916 := by
    simpa [prefixWord, tailWord_88916, baseEnd_88916] using wordTrace_append hprefix tailTrace_88916
  have hstable : (prefixWord ++ tailWord_88916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88916).length < 2 ^ (prefixWord ++ tailWord_88916).sum := by decide
  have hdescent : baseEnd_88916 < baseStart_88916 := by decide
  rcases family_descends (prefixWord ++ tailWord_88916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88922 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_88922 : Nat := 118140960795 + 88922 * 2 ^ 59
def prefixEnd_88922 : Nat := 4983230072969 + 3 ^ 40 * 88922 * 2
def baseEnd_88922 : Nat := 15219908919735441988687

theorem tailTrace_88922 : CollatzResearch.WordTrace tailWord_88922 prefixEnd_88922 15219908919735441988687 := by
  unfold tailWord_88922
  simp only [CollatzResearch.WordTrace]
  refine ⟨810812945964563878409255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2162167855905503675758013 810812945964563878409255)
  ·
    refine ⟨1216219418946845817613883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810812945964563878409255 1216219418946845817613883)
    ·
      refine ⟨1824329128420268726420825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216219418946845817613883 1824329128420268726420825)
      ·
        refine ⟨1368246846315201544815619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1824329128420268726420825 1368246846315201544815619)
        ·
          refine ⟨2052370269472802317223429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368246846315201544815619 2052370269472802317223429)
          ·
            refine ⟨384819425526150434479393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2052370269472802317223429 384819425526150434479393)
            ·
              refine ⟨288614569144612825859545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384819425526150434479393 288614569144612825859545)
              ·
                refine ⟨216460926858459619394659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288614569144612825859545 216460926858459619394659)
                ·
                  refine ⟨324691390287689429091989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216460926858459619394659 324691390287689429091989)
                  ·
                    refine ⟨15219908919735441988687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 324691390287689429091989 15219908919735441988687)
                    ·
                      rfl

theorem cell23_88922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_88922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88922 prefixEnd_88922 := by exact prefixLift 88922
  have htrace : WordTrace (prefixWord ++ tailWord_88922) baseStart_88922 baseEnd_88922 := by
    simpa [prefixWord, tailWord_88922, baseEnd_88922] using wordTrace_append hprefix tailTrace_88922
  have hstable : (prefixWord ++ tailWord_88922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88922).length < 2 ^ (prefixWord ++ tailWord_88922).sum := by decide
  have hdescent : baseEnd_88922 < baseStart_88922 := by decide
  rcases family_descends (prefixWord ++ tailWord_88922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88939 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 2, 4]
def baseStart_88939 : Nat := 118140960795 + 88939 * 2 ^ 59
def prefixEnd_88939 : Nat := 4983230072969 + 3 ^ 40 * 88939 * 2
def baseEnd_88939 : Nat := 15222818643444253151161

theorem tailTrace_88939 : CollatzResearch.WordTrace tailWord_88939 prefixEnd_88939 15222818643444253151161 := by
  unfold tailWord_88939
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243871824796667417005871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2162581216531111611337247 3243871824796667417005871)
  ·
    refine ⟨4865807737195001125508807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243871824796667417005871 4865807737195001125508807)
    ·
      refine ⟨7298711605792501688263211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865807737195001125508807 7298711605792501688263211)
      ·
        refine ⟨10948067408688752532394817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7298711605792501688263211 10948067408688752532394817)
        ·
          refine ⟨8211050556516564399296113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10948067408688752532394817 8211050556516564399296113)
          ·
            refine ⟨6158287917387423299472085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8211050556516564399296113 6158287917387423299472085)
            ·
              refine ⟨144334873063767733581377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6158287917387423299472085 144334873063767733581377)
              ·
                refine ⟨108251154797825800186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144334873063767733581377 108251154797825800186033)
                ·
                  refine ⟨81188366098369350139525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108251154797825800186033 81188366098369350139525)
                  ·
                    refine ⟨15222818643444253151161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81188366098369350139525 15222818643444253151161)
                    ·
                      rfl

theorem cell23_88939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 4].length) (baseStart_88939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88939 prefixEnd_88939 := by exact prefixLift 88939
  have htrace : WordTrace (prefixWord ++ tailWord_88939) baseStart_88939 baseEnd_88939 := by
    simpa [prefixWord, tailWord_88939, baseEnd_88939] using wordTrace_append hprefix tailTrace_88939
  have hstable : (prefixWord ++ tailWord_88939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88939).length < 2 ^ (prefixWord ++ tailWord_88939).sum := by decide
  have hdescent : baseEnd_88939 < baseStart_88939 := by decide
  rcases family_descends (prefixWord ++ tailWord_88939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88946 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_88946 : Nat := 118140960795 + 88946 * 2 ^ 59
def prefixEnd_88946 : Nat := 4983230072969 + 3 ^ 40 * 88946 * 2
def baseEnd_88946 : Nat := 45672050294914232065951

theorem tailTrace_88946 : CollatzResearch.WordTrace tailWord_88946 prefixEnd_88946 45672050294914232065951 := by
  unfold tailWord_88946
  simp only [CollatzResearch.WordTrace]
  refine ⟨811031783942826903127673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2162751423847538408340461 811031783942826903127673)
  ·
    refine ⟨608273837957120177345755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 811031783942826903127673 608273837957120177345755)
    ·
      refine ⟨912410756935680266018633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608273837957120177345755 912410756935680266018633)
      ·
        refine ⟨684308067701760199513975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912410756935680266018633 684308067701760199513975)
        ·
          refine ⟨1026462101552640299270963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684308067701760199513975 1026462101552640299270963)
          ·
            refine ⟨1539693152328960448906445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026462101552640299270963 1539693152328960448906445)
            ·
              refine ⟨577384932123360168339917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1539693152328960448906445 577384932123360168339917)
              ·
                refine ⟨216519349546260063127469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577384932123360168339917 216519349546260063127469)
                ·
                  refine ⟨81194756079847523672801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216519349546260063127469 81194756079847523672801)
                  ·
                    refine ⟨60896067059885642754601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81194756079847523672801 60896067059885642754601)
                    ·
                      refine ⟨45672050294914232065951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60896067059885642754601 45672050294914232065951)
                      ·
                        rfl

theorem cell23_88946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_88946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88946 prefixEnd_88946 := by exact prefixLift 88946
  have htrace : WordTrace (prefixWord ++ tailWord_88946) baseStart_88946 baseEnd_88946 := by
    simpa [prefixWord, tailWord_88946, baseEnd_88946] using wordTrace_append hprefix tailTrace_88946
  have hstable : (prefixWord ++ tailWord_88946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88946).length < 2 ^ (prefixWord ++ tailWord_88946).sum := by decide
  have hdescent : baseEnd_88946 < baseStart_88946 := by decide
  rcases family_descends (prefixWord ++ tailWord_88946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88949 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_88949 : Nat := 118140960795 + 88949 * 2 ^ 59
def prefixEnd_88949 : Nat := 4983230072969 + 3 ^ 40 * 88949 * 2
def baseEnd_88949 : Nat := 45673590736877720328437

theorem tailTrace_88949 : CollatzResearch.WordTrace tailWord_88949 prefixEnd_88949 45673590736877720328437 := by
  unfold tailWord_88949
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244236554760439124869901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2162824369840292749913267 3244236554760439124869901)
  ·
    refine ⟨1216588708035164671826213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3244236554760439124869901 1216588708035164671826213)
    ·
      refine ⟨228110382756593375967415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1216588708035164671826213 228110382756593375967415)
      ·
        refine ⟨342165574134890063951123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228110382756593375967415 342165574134890063951123)
        ·
          refine ⟨513248361202335095926685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342165574134890063951123 513248361202335095926685)
          ·
            refine ⟨192468135450875660972507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513248361202335095926685 192468135450875660972507)
            ·
              refine ⟨288702203176313491458761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192468135450875660972507 288702203176313491458761)
              ·
                refine ⟨216526652382235118594071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288702203176313491458761 216526652382235118594071)
                ·
                  refine ⟨324789978573352677891107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216526652382235118594071 324789978573352677891107)
                  ·
                    refine ⟨487184967860029016836661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324789978573352677891107 487184967860029016836661)
                    ·
                      refine ⟨45673590736877720328437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 487184967860029016836661 45673590736877720328437)
                      ·
                        rfl

theorem cell23_88949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_88949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88949 prefixEnd_88949 := by exact prefixLift 88949
  have htrace : WordTrace (prefixWord ++ tailWord_88949) baseStart_88949 baseEnd_88949 := by
    simpa [prefixWord, tailWord_88949, baseEnd_88949] using wordTrace_append hprefix tailTrace_88949
  have hstable : (prefixWord ++ tailWord_88949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88949).length < 2 ^ (prefixWord ++ tailWord_88949).sum := by decide
  have hdescent : baseEnd_88949 < baseStart_88949 := by decide
  rcases family_descends (prefixWord ++ tailWord_88949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88969 : List Nat := [1, 2, 1, 1, 5, 4, 2, 7]
def baseStart_88969 : Nat := 118140960795 + 88969 * 2 ^ 59
def prefixEnd_88969 : Nat := 4983230072969 + 3 ^ 40 * 88969 * 2
def baseEnd_88969 : Nat := 1691994827776579336235

theorem tailTrace_88969 : CollatzResearch.WordTrace tailWord_88969 prefixEnd_88969 1691994827776579336235 := by
  unfold tailWord_88969
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244966014687982540597961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2163310676458655027065307 3244966014687982540597961)
  ·
    refine ⟨2433724511015986905448471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3244966014687982540597961 2433724511015986905448471)
    ·
      refine ⟨3650586766523980358172707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2433724511015986905448471 3650586766523980358172707)
      ·
        refine ⟨5475880149785970537259061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650586766523980358172707 5475880149785970537259061)
        ·
          refine ⟨513363764042434737868037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5475880149785970537259061 513363764042434737868037)
          ·
            refine ⟨96255705757956513350257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 513363764042434737868037 96255705757956513350257)
            ·
              refine ⟨72191779318467385012693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96255705757956513350257 72191779318467385012693)
              ·
                refine ⟨1691994827776579336235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72191779318467385012693 1691994827776579336235)
                ·
                  rfl

theorem cell23_88969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 7].length) (baseStart_88969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88969 prefixEnd_88969 := by exact prefixLift 88969
  have htrace : WordTrace (prefixWord ++ tailWord_88969) baseStart_88969 baseEnd_88969 := by
    simpa [prefixWord, tailWord_88969, baseEnd_88969] using wordTrace_append hprefix tailTrace_88969
  have hstable : (prefixWord ++ tailWord_88969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88969).length < 2 ^ (prefixWord ++ tailWord_88969).sum := by decide
  have hdescent : baseEnd_88969 < baseStart_88969 := by decide
  rcases family_descends (prefixWord ++ tailWord_88969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88996 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_88996 : Nat := 118140960795 + 88996 * 2 ^ 59
def prefixEnd_88996 : Nat := 4983230072969 + 3 ^ 40 * 88996 * 2
def baseEnd_88996 : Nat := 45697724327639036440721

theorem tailTrace_88996 : CollatzResearch.WordTrace tailWord_88996 prefixEnd_88996 45697724327639036440721 := by
  unfold tailWord_88996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622975392795083075915421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2163967190393444101220561 1622975392795083075915421)
  ·
    refine ⟨608615772298156153468283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1622975392795083075915421 608615772298156153468283)
    ·
      refine ⟨912923658447234230202425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608615772298156153468283 912923658447234230202425)
      ·
        refine ⟨684692743835425672651819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912923658447234230202425 684692743835425672651819)
        ·
          refine ⟨1027039115753138508977729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684692743835425672651819 1027039115753138508977729)
          ·
            refine ⟨770279336814853881733297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027039115753138508977729 770279336814853881733297)
            ·
              refine ⟨577709502611140411299973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770279336814853881733297 577709502611140411299973)
              ·
                refine ⟨108320531739588827118745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577709502611140411299973 108320531739588827118745)
                ·
                  refine ⟨81240398804691620339059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108320531739588827118745 81240398804691620339059)
                  ·
                    refine ⟨121860598207037430508589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81240398804691620339059 121860598207037430508589)
                    ·
                      refine ⟨45697724327639036440721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 121860598207037430508589 45697724327639036440721)
                      ·
                        rfl

theorem cell23_88996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_88996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88996 prefixEnd_88996 := by exact prefixLift 88996
  have htrace : WordTrace (prefixWord ++ tailWord_88996) baseStart_88996 baseEnd_88996 := by
    simpa [prefixWord, tailWord_88996, baseEnd_88996] using wordTrace_append hprefix tailTrace_88996
  have hstable : (prefixWord ++ tailWord_88996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88996).length < 2 ^ (prefixWord ++ tailWord_88996).sum := by decide
  have hdescent : baseEnd_88996 < baseStart_88996 := by decide
  rcases family_descends (prefixWord ++ tailWord_88996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89014 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_89014 : Nat := 118140960795 + 89014 * 2 ^ 59
def prefixEnd_89014 : Nat := 4983230072969 + 3 ^ 40 * 89014 * 2
def baseEnd_89014 : Nat := 45706966979419966015639

theorem tailTrace_89014 : CollatzResearch.WordTrace tailWord_89014 prefixEnd_89014 45706966979419966015639 := by
  unfold tailWord_89014
  simp only [CollatzResearch.WordTrace]
  refine ⟨202912956220309701624131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2164404866349970150657397 202912956220309701624131)
  ·
    refine ⟨304369434330464552436197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202912956220309701624131 304369434330464552436197)
    ·
      refine ⟨57069268936962103581787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304369434330464552436197 57069268936962103581787)
      ·
        refine ⟨85603903405443155372681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57069268936962103581787 85603903405443155372681)
        ·
          refine ⟨64202927554082366529511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85603903405443155372681 64202927554082366529511)
          ·
            refine ⟨96304391331123549794267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64202927554082366529511 96304391331123549794267)
            ·
              refine ⟨144456586996685324691401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96304391331123549794267 144456586996685324691401)
              ·
                refine ⟨108342440247513993518551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144456586996685324691401 108342440247513993518551)
                ·
                  refine ⟨162513660371270990277827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108342440247513993518551 162513660371270990277827)
                  ·
                    refine ⟨243770490556906485416741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162513660371270990277827 243770490556906485416741)
                    ·
                      refine ⟨45706966979419966015639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 243770490556906485416741 45706966979419966015639)
                      ·
                        rfl

theorem cell23_89014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_89014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89014 prefixEnd_89014 := by exact prefixLift 89014
  have htrace : WordTrace (prefixWord ++ tailWord_89014) baseStart_89014 baseEnd_89014 := by
    simpa [prefixWord, tailWord_89014, baseEnd_89014] using wordTrace_append hprefix tailTrace_89014
  have hstable : (prefixWord ++ tailWord_89014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89014).length < 2 ^ (prefixWord ++ tailWord_89014).sum := by decide
  have hdescent : baseEnd_89014 < baseStart_89014 := by decide
  rcases family_descends (prefixWord ++ tailWord_89014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89036 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_89036 : Nat := 118140960795 + 89036 * 2 ^ 59
def prefixEnd_89036 : Nat := 4983230072969 + 3 ^ 40 * 89036 * 2
def baseEnd_89036 : Nat := 45718263553818879940537

theorem tailTrace_89036 : CollatzResearch.WordTrace tailWord_89036 prefixEnd_89036 45718263553818879940537 := by
  unfold tailWord_89036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623704852722626491643481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2164939803630168655524641 1623704852722626491643481)
  ·
    refine ⟨1217778639541969868732611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1623704852722626491643481 1217778639541969868732611)
    ·
      refine ⟨1826667959312954803098917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217778639541969868732611 1826667959312954803098917)
      ·
        refine ⟨342500242371179025581047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1826667959312954803098917 342500242371179025581047)
        ·
          refine ⟨513750363556768538371571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342500242371179025581047 513750363556768538371571)
          ·
            refine ⟨770625545335152807557357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513750363556768538371571 770625545335152807557357)
            ·
              refine ⟨288984579500682302834009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770625545335152807557357 288984579500682302834009)
              ·
                refine ⟨216738434625511727125507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288984579500682302834009 216738434625511727125507)
                ·
                  refine ⟨325107651938267590688261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216738434625511727125507 325107651938267590688261)
                  ·
                    refine ⟨60957684738425173254049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325107651938267590688261 60957684738425173254049)
                    ·
                      refine ⟨45718263553818879940537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60957684738425173254049 45718263553818879940537)
                      ·
                        rfl

theorem cell23_89036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_89036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89036 prefixEnd_89036 := by exact prefixLift 89036
  have htrace : WordTrace (prefixWord ++ tailWord_89036) baseStart_89036 baseEnd_89036 := by
    simpa [prefixWord, tailWord_89036, baseEnd_89036] using wordTrace_append hprefix tailTrace_89036
  have hstable : (prefixWord ++ tailWord_89036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89036).length < 2 ^ (prefixWord ++ tailWord_89036).sum := by decide
  have hdescent : baseEnd_89036 < baseStart_89036 := by decide
  rcases family_descends (prefixWord ++ tailWord_89036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89072 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_89072 : Nat := 118140960795 + 89072 * 2 ^ 59
def prefixEnd_89072 : Nat := 4983230072969 + 3 ^ 40 * 89072 * 2
def baseEnd_89072 : Nat := 15245582952460246363457

theorem tailTrace_89072 : CollatzResearch.WordTrace tailWord_89072 prefixEnd_89072 15245582952460246363457 := by
  unfold tailWord_89072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624361366657415565798735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2165815155543220754398313 1624361366657415565798735)
  ·
    refine ⟨2436542049986123348698103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1624361366657415565798735 2436542049986123348698103)
    ·
      refine ⟨3654813074979185023047155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436542049986123348698103 3654813074979185023047155)
      ·
        refine ⟨5482219612468777534570733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654813074979185023047155 5482219612468777534570733)
        ·
          refine ⟨2055832354675791575464025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5482219612468777534570733 2055832354675791575464025)
          ·
            refine ⟨1541874266006843681598019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2055832354675791575464025 1541874266006843681598019)
            ·
              refine ⟨2312811399010265522397029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541874266006843681598019 2312811399010265522397029)
              ·
                refine ⟨433652137314424785449443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2312811399010265522397029 433652137314424785449443)
                ·
                  refine ⟨650478205971637178174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433652137314424785449443 650478205971637178174165)
                  ·
                    refine ⟨15245582952460246363457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 650478205971637178174165 15245582952460246363457)
                    ·
                      rfl

theorem cell23_89072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_89072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89072 prefixEnd_89072 := by exact prefixLift 89072
  have htrace : WordTrace (prefixWord ++ tailWord_89072) baseStart_89072 baseEnd_89072 := by
    simpa [prefixWord, tailWord_89072, baseEnd_89072] using wordTrace_append hprefix tailTrace_89072
  have hstable : (prefixWord ++ tailWord_89072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89072).length < 2 ^ (prefixWord ++ tailWord_89072).sum := by decide
  have hdescent : baseEnd_89072 < baseStart_89072 := by decide
  rcases family_descends (prefixWord ++ tailWord_89072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89082 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_89082 : Nat := 118140960795 + 89082 * 2 ^ 59
def prefixEnd_89082 : Nat := 4983230072969 + 3 ^ 40 * 89082 * 2
def baseEnd_89082 : Nat := 45741883663925699965325

theorem tailTrace_89082 : CollatzResearch.WordTrace tailWord_89082 prefixEnd_89082 45741883663925699965325 := by
  unfold tailWord_89082
  simp only [CollatzResearch.WordTrace]
  refine ⟨812271865819650709865375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2166058308852401892974333 812271865819650709865375)
  ·
    refine ⟨1218407798729476064798063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 812271865819650709865375 1218407798729476064798063)
    ·
      refine ⟨1827611698094214097197095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218407798729476064798063 1827611698094214097197095)
      ·
        refine ⟨2741417547141321145795643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827611698094214097197095 2741417547141321145795643)
        ·
          refine ⟨4112126320711981718693465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741417547141321145795643 4112126320711981718693465)
          ·
            refine ⟨3084094740533986289020099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112126320711981718693465 3084094740533986289020099)
            ·
              refine ⟨4626142110800979433530149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084094740533986289020099 4626142110800979433530149)
              ·
                refine ⟨867401645775183643786903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4626142110800979433530149 867401645775183643786903)
                ·
                  refine ⟨1301102468662775465680355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867401645775183643786903 1301102468662775465680355)
                  ·
                    refine ⟨1951653702994163198520533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1301102468662775465680355 1951653702994163198520533)
                    ·
                      refine ⟨45741883663925699965325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1951653702994163198520533 45741883663925699965325)
                      ·
                        rfl

theorem cell23_89082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_89082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89082 prefixEnd_89082 := by exact prefixLift 89082
  have htrace : WordTrace (prefixWord ++ tailWord_89082) baseStart_89082 baseEnd_89082 := by
    simpa [prefixWord, tailWord_89082, baseEnd_89082] using wordTrace_append hprefix tailTrace_89082
  have hstable : (prefixWord ++ tailWord_89082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89082).length < 2 ^ (prefixWord ++ tailWord_89082).sum := by decide
  have hdescent : baseEnd_89082 < baseStart_89082 := by decide
  rcases family_descends (prefixWord ++ tailWord_89082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89089 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_89089 : Nat := 118140960795 + 89089 * 2 ^ 59
def prefixEnd_89089 : Nat := 4983230072969 + 3 ^ 40 * 89089 * 2
def baseEnd_89089 : Nat := 15248492676169057525931

theorem tailTrace_89089 : CollatzResearch.WordTrace tailWord_89089 prefixEnd_89089 15248492676169057525931 := by
  unfold tailWord_89089
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249342774253243034966321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2166228516168828689977547 3249342774253243034966321)
  ·
    refine ⟨2437007080689932276224741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3249342774253243034966321 2437007080689932276224741)
    ·
      refine ⟨456938827629362301792139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2437007080689932276224741 456938827629362301792139)
      ·
        refine ⟨685408241444043452688209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456938827629362301792139 685408241444043452688209)
        ·
          refine ⟨514056181083032589516157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685408241444043452688209 514056181083032589516157)
          ·
            refine ⟨192771067906137221068559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514056181083032589516157 192771067906137221068559)
            ·
              refine ⟨289156601859205831602839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192771067906137221068559 289156601859205831602839)
              ·
                refine ⟨433734902788808747404259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289156601859205831602839 433734902788808747404259)
                ·
                  refine ⟨650602354183213121106389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433734902788808747404259 650602354183213121106389)
                  ·
                    refine ⟨15248492676169057525931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 650602354183213121106389 15248492676169057525931)
                    ·
                      rfl

theorem cell23_89089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_89089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89089 prefixEnd_89089 := by exact prefixLift 89089
  have htrace : WordTrace (prefixWord ++ tailWord_89089) baseStart_89089 baseEnd_89089 := by
    simpa [prefixWord, tailWord_89089, baseEnd_89089] using wordTrace_append hprefix tailTrace_89089
  have hstable : (prefixWord ++ tailWord_89089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89089).length < 2 ^ (prefixWord ++ tailWord_89089).sum := by decide
  have hdescent : baseEnd_89089 < baseStart_89089 := by decide
  rcases family_descends (prefixWord ++ tailWord_89089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89149 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 8]
def baseStart_89149 : Nat := 118140960795 + 89149 * 2 ^ 59
def prefixEnd_89149 : Nat := 4983230072969 + 3 ^ 40 * 89149 * 2
def baseEnd_89149 : Nat := 5086254096419659758613

theorem tailTrace_89149 : CollatzResearch.WordTrace tailWord_89149 prefixEnd_89149 5086254096419659758613 := by
  unfold tailWord_89149
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251531154035873282150501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2167687436023915521433667 3251531154035873282150501)
  ·
    refine ⟨609662091381726240403219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3251531154035873282150501 609662091381726240403219)
    ·
      refine ⟨914493137072589360604829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609662091381726240403219 914493137072589360604829)
      ·
        refine ⟨342934926402221010226811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 914493137072589360604829 342934926402221010226811)
        ·
          refine ⟨514402389603331515340217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342934926402221010226811 514402389603331515340217)
          ·
            refine ⟨385801792202498636505163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514402389603331515340217 385801792202498636505163)
            ·
              refine ⟨578702688303747954757745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385801792202498636505163 578702688303747954757745)
              ·
                refine ⟨434027016227810966068309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578702688303747954757745 434027016227810966068309)
                ·
                  refine ⟨5086254096419659758613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 434027016227810966068309 5086254096419659758613)
                  ·
                    rfl

theorem cell23_89149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_89149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89149 prefixEnd_89149 := by exact prefixLift 89149
  have htrace : WordTrace (prefixWord ++ tailWord_89149) baseStart_89149 baseEnd_89149 := by
    simpa [prefixWord, tailWord_89149, baseEnd_89149] using wordTrace_append hprefix tailTrace_89149
  have hstable : (prefixWord ++ tailWord_89149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89149).length < 2 ^ (prefixWord ++ tailWord_89149).sum := by decide
  have hdescent : baseEnd_89149 < baseStart_89149 := by decide
  rcases family_descends (prefixWord ++ tailWord_89149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89213 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_89213 : Nat := 118140960795 + 89213 * 2 ^ 59
def prefixEnd_89213 : Nat := 4983230072969 + 3 ^ 40 * 89213 * 2
def baseEnd_89213 : Nat := 15269716543221562475741

theorem tailTrace_89213 : CollatzResearch.WordTrace tailWord_89213 prefixEnd_89213 15269716543221562475741 := by
  unfold tailWord_89213
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253865425804012212480293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2169243617202674808320195 3253865425804012212480293)
  ·
    refine ⟨610099767338252289840055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3253865425804012212480293 610099767338252289840055)
    ·
      refine ⟨915149651007378434760083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610099767338252289840055 915149651007378434760083)
      ·
        refine ⟨1372724476511067652140125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915149651007378434760083 1372724476511067652140125)
        ·
          refine ⟨514771678691650369552547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372724476511067652140125 514771678691650369552547)
          ·
            refine ⟨772157518037475554328821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514771678691650369552547 772157518037475554328821)
            ·
              refine ⟨72389767316013333218327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 772157518037475554328821 72389767316013333218327)
              ·
                refine ⟨108584650974019999827491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72389767316013333218327 108584650974019999827491)
                ·
                  refine ⟨162876976461029999741237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108584650974019999827491 162876976461029999741237)
                  ·
                    refine ⟨15269716543221562475741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162876976461029999741237 15269716543221562475741)
                    ·
                      rfl

theorem cell23_89213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_89213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89213 prefixEnd_89213 := by exact prefixLift 89213
  have htrace : WordTrace (prefixWord ++ tailWord_89213) baseStart_89213 baseEnd_89213 := by
    simpa [prefixWord, tailWord_89213, baseEnd_89213] using wordTrace_append hprefix tailTrace_89213
  have hstable : (prefixWord ++ tailWord_89213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89213).length < 2 ^ (prefixWord ++ tailWord_89213).sum := by decide
  have hdescent : baseEnd_89213 < baseStart_89213 := by decide
  rcases family_descends (prefixWord ++ tailWord_89213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89216 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_89216 : Nat := 118140960795 + 89216 * 2 ^ 59
def prefixEnd_89216 : Nat := 4983230072969 + 3 ^ 40 * 89216 * 2
def baseEnd_89216 : Nat := 45810690071628175689709

theorem tailTrace_89216 : CollatzResearch.WordTrace tailWord_89216 prefixEnd_89216 45810690071628175689709 := by
  unfold tailWord_89216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626987422396571862419751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2169316563195429149893001 1626987422396571862419751)
  ·
    refine ⟨2440481133594857793629627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626987422396571862419751 2440481133594857793629627)
    ·
      refine ⟨3660721700392286690444441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440481133594857793629627 3660721700392286690444441)
      ·
        refine ⟨2745541275294215017833331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3660721700392286690444441 2745541275294215017833331)
        ·
          refine ⟨4118311912941322526749997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745541275294215017833331 4118311912941322526749997)
          ·
            refine ⟨1544366967352995947531249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4118311912941322526749997 1544366967352995947531249)
            ·
              refine ⟨1158275225514746960648437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544366967352995947531249 1158275225514746960648437)
              ·
                refine ⟨108588302392007527560791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1158275225514746960648437 108588302392007527560791)
                ·
                  refine ⟨162882453588011291341187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108588302392007527560791 162882453588011291341187)
                  ·
                    refine ⟨244323680382016937011781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162882453588011291341187 244323680382016937011781)
                    ·
                      refine ⟨45810690071628175689709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 244323680382016937011781 45810690071628175689709)
                      ·
                        rfl

theorem cell23_89216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_89216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89216 prefixEnd_89216 := by exact prefixLift 89216
  have htrace : WordTrace (prefixWord ++ tailWord_89216) baseStart_89216 baseEnd_89216 := by
    simpa [prefixWord, tailWord_89216, baseEnd_89216] using wordTrace_append hprefix tailTrace_89216
  have hstable : (prefixWord ++ tailWord_89216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89216).length < 2 ^ (prefixWord ++ tailWord_89216).sum := by decide
  have hdescent : baseEnd_89216 < baseStart_89216 := by decide
  rcases family_descends (prefixWord ++ tailWord_89216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89283 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 3]
def baseStart_89283 : Nat := 118140960795 + 89283 * 2 ^ 59
def prefixEnd_89283 : Nat := 4983230072969 + 3 ^ 40 * 89283 * 2
def baseEnd_89283 : Nat := 45845093275479413551901

theorem tailTrace_89283 : CollatzResearch.WordTrace tailWord_89283 prefixEnd_89283 45845093275479413551901 := by
  unfold tailWord_89283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256418535550414167528503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2170945690366942778352335 3256418535550414167528503)
  ·
    refine ⟨4884627803325621251292755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3256418535550414167528503 4884627803325621251292755)
    ·
      refine ⟨7326941704988431876939133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4884627803325621251292755 7326941704988431876939133)
      ·
        refine ⟨2747603139370661953852175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7326941704988431876939133 2747603139370661953852175)
        ·
          refine ⟨4121404709055992930778263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747603139370661953852175 4121404709055992930778263)
          ·
            refine ⟨6182107063583989396167395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121404709055992930778263 6182107063583989396167395)
            ·
              refine ⟨9273160595375984094251093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182107063583989396167395 9273160595375984094251093)
              ·
                refine ⟨108669850727062313604505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9273160595375984094251093 108669850727062313604505)
                ·
                  refine ⟨81502388045296735203379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108669850727062313604505 81502388045296735203379)
                  ·
                    refine ⟨122253582067945102805069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81502388045296735203379 122253582067945102805069)
                    ·
                      refine ⟨45845093275479413551901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 122253582067945102805069 45845093275479413551901)
                      ·
                        rfl

theorem cell23_89283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_89283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89283 prefixEnd_89283 := by exact prefixLift 89283
  have htrace : WordTrace (prefixWord ++ tailWord_89283) baseStart_89283 baseEnd_89283 := by
    simpa [prefixWord, tailWord_89283, baseEnd_89283] using wordTrace_append hprefix tailTrace_89283
  have hstable : (prefixWord ++ tailWord_89283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89283).length < 2 ^ (prefixWord ++ tailWord_89283).sum := by decide
  have hdescent : baseEnd_89283 < baseStart_89283 := by decide
  rcases family_descends (prefixWord ++ tailWord_89283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89326 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_89326 : Nat := 118140960795 + 89326 * 2 ^ 59
def prefixEnd_89326 : Nat := 4983230072969 + 3 ^ 40 * 89326 * 2
def baseEnd_89326 : Nat := 45867172943622745314203

theorem tailTrace_89326 : CollatzResearch.WordTrace tailWord_89326 prefixEnd_89326 45867172943622745314203 := by
  unfold tailWord_89326
  simp only [CollatzResearch.WordTrace]
  refine ⟨407248359299329063917979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2171991249596421674229221 407248359299329063917979)
  ·
    refine ⟨610872538948993595876969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 407248359299329063917979 610872538948993595876969)
    ·
      refine ⟨458154404211745196907727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610872538948993595876969 458154404211745196907727)
      ·
        refine ⟨687231606317617795361591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458154404211745196907727 687231606317617795361591)
        ·
          refine ⟨1030847409476426693042387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687231606317617795361591 1030847409476426693042387)
          ·
            refine ⟨1546271114214640039563581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030847409476426693042387 1546271114214640039563581)
            ·
              refine ⟨579851667830490014836343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1546271114214640039563581 579851667830490014836343)
              ·
                refine ⟨869777501745735022254515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579851667830490014836343 869777501745735022254515)
                ·
                  refine ⟨1304666252618602533381773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869777501745735022254515 1304666252618602533381773)
                  ·
                    refine ⟨489249844731975950018165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304666252618602533381773 489249844731975950018165)
                    ·
                      refine ⟨45867172943622745314203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 489249844731975950018165 45867172943622745314203)
                      ·
                        rfl

theorem cell23_89326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_89326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89326 prefixEnd_89326 := by exact prefixLift 89326
  have htrace : WordTrace (prefixWord ++ tailWord_89326) baseStart_89326 baseEnd_89326 := by
    simpa [prefixWord, tailWord_89326, baseEnd_89326] using wordTrace_append hprefix tailTrace_89326
  have hstable : (prefixWord ++ tailWord_89326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89326).length < 2 ^ (prefixWord ++ tailWord_89326).sum := by decide
  have hdescent : baseEnd_89326 < baseStart_89326 := by decide
  rcases family_descends (prefixWord ++ tailWord_89326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89374 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_89374 : Nat := 118140960795 + 89374 * 2 ^ 59
def prefixEnd_89374 : Nat := 4983230072969 + 3 ^ 40 * 89374 * 2
def baseEnd_89374 : Nat := 45891820015038557513983

theorem tailTrace_89374 : CollatzResearch.WordTrace tailWord_89374 prefixEnd_89374 45891820015038557513983 := by
  unfold tailWord_89374
  simp only [CollatzResearch.WordTrace]
  refine ⟨407467197277592088636397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2173158385480491139394117 407467197277592088636397)
  ·
    refine ⟨152800198979097033238649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 407467197277592088636397 152800198979097033238649)
    ·
      refine ⟨114600149234322774928987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152800198979097033238649 114600149234322774928987)
      ·
        refine ⟨171900223851484162393481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114600149234322774928987 171900223851484162393481)
        ·
          refine ⟨128925167888613121795111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171900223851484162393481 128925167888613121795111)
          ·
            refine ⟨193387751832919682692667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128925167888613121795111 193387751832919682692667)
            ·
              refine ⟨290081627749379524039001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193387751832919682692667 290081627749379524039001)
              ·
                refine ⟨217561220812034643029251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290081627749379524039001 217561220812034643029251)
                ·
                  refine ⟨326341831218051964543877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217561220812034643029251 326341831218051964543877)
                  ·
                    refine ⟨61189093353384743351977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326341831218051964543877 61189093353384743351977)
                    ·
                      refine ⟨45891820015038557513983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61189093353384743351977 45891820015038557513983)
                      ·
                        rfl

theorem cell23_89374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_89374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89374 prefixEnd_89374 := by exact prefixLift 89374
  have htrace : WordTrace (prefixWord ++ tailWord_89374) baseStart_89374 baseEnd_89374 := by
    simpa [prefixWord, tailWord_89374, baseEnd_89374] using wordTrace_append hprefix tailTrace_89374
  have hstable : (prefixWord ++ tailWord_89374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89374).length < 2 ^ (prefixWord ++ tailWord_89374).sum := by decide
  have hdescent : baseEnd_89374 < baseStart_89374 := by decide
  rcases family_descends (prefixWord ++ tailWord_89374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89393 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_89393 : Nat := 118140960795 + 89393 * 2 ^ 59
def prefixEnd_89393 : Nat := 4983230072969 + 3 ^ 40 * 89393 * 2
def baseEnd_89393 : Nat := 15300525382491327725465

theorem tailTrace_89393 : CollatzResearch.WordTrace tailWord_89393 prefixEnd_89393 15300525382491327725465 := by
  unfold tailWord_89393
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260430565151902954032833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2173620376767935302688555 3260430565151902954032833)
  ·
    refine ⟨2445322923863927215524625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3260430565151902954032833 2445322923863927215524625)
    ·
      refine ⟨1833992192897945411643469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2445322923863927215524625 1833992192897945411643469)
      ·
        refine ⟨687747072336729529366301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1833992192897945411643469 687747072336729529366301)
        ·
          refine ⟨257905152126273573512363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 687747072336729529366301 257905152126273573512363)
          ·
            refine ⟨386857728189410360268545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257905152126273573512363 386857728189410360268545)
            ·
              refine ⟨290143296142057770201409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386857728189410360268545 290143296142057770201409)
              ·
                refine ⟨217607472106543327651057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290143296142057770201409 217607472106543327651057)
                ·
                  refine ⟨163205604079907495738293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217607472106543327651057 163205604079907495738293)
                  ·
                    refine ⟨15300525382491327725465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163205604079907495738293 15300525382491327725465)
                    ·
                      rfl

theorem cell23_89393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_89393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89393 prefixEnd_89393 := by exact prefixLift 89393
  have htrace : WordTrace (prefixWord ++ tailWord_89393) baseStart_89393 baseEnd_89393 := by
    simpa [prefixWord, tailWord_89393, baseEnd_89393] using wordTrace_append hprefix tailTrace_89393
  have hstable : (prefixWord ++ tailWord_89393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89393).length < 2 ^ (prefixWord ++ tailWord_89393).sum := by decide
  have hdescent : baseEnd_89393 < baseStart_89393 := by decide
  rcases family_descends (prefixWord ++ tailWord_89393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89397 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 5]
def baseStart_89397 : Nat := 118140960795 + 89397 * 2 ^ 59
def prefixEnd_89397 : Nat := 4983230072969 + 3 ^ 40 * 89397 * 2
def baseEnd_89397 : Nat := 5100403341121329725153

theorem tailTrace_89397 : CollatzResearch.WordTrace tailWord_89397 prefixEnd_89397 5100403341121329725153 := by
  unfold tailWord_89397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260576457137411637178445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2173717638091607758118963 3260576457137411637178445)
  ·
    refine ⟨1222716171426529363941917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3260576457137411637178445 1222716171426529363941917)
    ·
      refine ⟨458518564284948511478219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1222716171426529363941917 458518564284948511478219)
      ·
        refine ⟨687777846427422767217329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458518564284948511478219 687777846427422767217329)
        ·
          refine ⟨515833384820567075412997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687777846427422767217329 515833384820567075412997)
          ·
            refine ⟨96718759653856326639937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 515833384820567075412997 96718759653856326639937)
            ·
              refine ⟨72539069740392244979953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96718759653856326639937 72539069740392244979953)
              ·
                refine ⟨54404302305294183734965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72539069740392244979953 54404302305294183734965)
                ·
                  refine ⟨5100403341121329725153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54404302305294183734965 5100403341121329725153)
                  ·
                    rfl

theorem cell23_89397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_89397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89397 prefixEnd_89397 := by exact prefixLift 89397
  have htrace : WordTrace (prefixWord ++ tailWord_89397) baseStart_89397 baseEnd_89397 := by
    simpa [prefixWord, tailWord_89397, baseEnd_89397] using wordTrace_append hprefix tailTrace_89397
  have hstable : (prefixWord ++ tailWord_89397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89397).length < 2 ^ (prefixWord ++ tailWord_89397).sum := by decide
  have hdescent : baseEnd_89397 < baseStart_89397 := by decide
  rcases family_descends (prefixWord ++ tailWord_89397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89453 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 8]
def baseStart_89453 : Nat := 118140960795 + 89453 * 2 ^ 59
def prefixEnd_89453 : Nat := 4983230072969 + 3 ^ 40 * 89453 * 2
def baseEnd_89453 : Nat := 5103598331860416491791

theorem tailTrace_89453 : CollatzResearch.WordTrace tailWord_89453 prefixEnd_89453 5103598331860416491791 := by
  unfold tailWord_89453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262618944934533201217013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2175079296623022134144675 3262618944934533201217013)
  ·
    refine ⟨305870526087612487614095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3262618944934533201217013 305870526087612487614095)
    ·
      refine ⟨458805789131418731421143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305870526087612487614095 458805789131418731421143)
      ·
        refine ⟨688208683697128097131715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458805789131418731421143 688208683697128097131715)
        ·
          refine ⟨1032313025545692145697573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688208683697128097131715 1032313025545692145697573)
          ·
            refine ⟨193558692289817277318295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1032313025545692145697573 193558692289817277318295)
            ·
              refine ⟨290338038434725915977443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193558692289817277318295 290338038434725915977443)
              ·
                refine ⟨435507057652088873966165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290338038434725915977443 435507057652088873966165)
                ·
                  refine ⟨5103598331860416491791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 435507057652088873966165 5103598331860416491791)
                  ·
                    rfl

theorem cell23_89453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_89453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89453 prefixEnd_89453 := by exact prefixLift 89453
  have htrace : WordTrace (prefixWord ++ tailWord_89453) baseStart_89453 baseEnd_89453 := by
    simpa [prefixWord, tailWord_89453, baseEnd_89453] using wordTrace_append hprefix tailTrace_89453
  have hstable : (prefixWord ++ tailWord_89453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89453).length < 2 ^ (prefixWord ++ tailWord_89453).sum := by decide
  have hdescent : baseEnd_89453 < baseStart_89453 := by decide
  rcases family_descends (prefixWord ++ tailWord_89453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89456 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_89456 : Nat := 118140960795 + 89456 * 2 ^ 59
def prefixEnd_89456 : Nat := 4983230072969 + 3 ^ 40 * 89456 * 2
def baseEnd_89456 : Nat := 45933925428707236688605

theorem tailTrace_89456 : CollatzResearch.WordTrace tailWord_89456 prefixEnd_89456 45933925428707236688605 := by
  unfold tailWord_89456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631364181961832356788111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2175152242615776475717481 1631364181961832356788111)
  ·
    refine ⟨2447046272942748535182167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631364181961832356788111 2447046272942748535182167)
    ·
      refine ⟨3670569409414122802773251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447046272942748535182167 3670569409414122802773251)
      ·
        refine ⟨5505854114121184204159877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670569409414122802773251 5505854114121184204159877)
        ·
          refine ⟨1032347646397722038279977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5505854114121184204159877 1032347646397722038279977)
          ·
            refine ⟨774260734798291528709983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032347646397722038279977 774260734798291528709983)
            ·
              refine ⟨1161391102197437293064975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774260734798291528709983 1161391102197437293064975)
              ·
                refine ⟨1742086653296155939597463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161391102197437293064975 1742086653296155939597463)
                ·
                  refine ⟨2613129979944233909396195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742086653296155939597463 2613129979944233909396195)
                  ·
                    refine ⟨3919694969916350864094293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613129979944233909396195 3919694969916350864094293)
                    ·
                      refine ⟨45933925428707236688605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 3919694969916350864094293 45933925428707236688605)
                      ·
                        rfl

theorem cell23_89456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_89456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89456 prefixEnd_89456 := by exact prefixLift 89456
  have htrace : WordTrace (prefixWord ++ tailWord_89456) baseStart_89456 baseEnd_89456 := by
    simpa [prefixWord, tailWord_89456, baseEnd_89456] using wordTrace_append hprefix tailTrace_89456
  have hstable : (prefixWord ++ tailWord_89456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89456).length < 2 ^ (prefixWord ++ tailWord_89456).sum := by decide
  have hdescent : baseEnd_89456 < baseStart_89456 := by decide
  rcases family_descends (prefixWord ++ tailWord_89456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89533 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_89533 : Nat := 118140960795 + 89533 * 2 ^ 59
def prefixEnd_89533 : Nat := 4983230072969 + 3 ^ 40 * 89533 * 2
def baseEnd_89533 : Nat := 45973463439103435425751

theorem tailTrace_89533 : CollatzResearch.WordTrace tailWord_89533 prefixEnd_89533 45973463439103435425751 := by
  unfold tailWord_89533
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265536784644706864129253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2177024523096471242752835 3265536784644706864129253)
  ·
    refine ⟨612288147120882537024235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3265536784644706864129253 612288147120882537024235)
    ·
      refine ⟨918432220681323805536353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612288147120882537024235 918432220681323805536353)
      ·
        refine ⟨688824165510992854152265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918432220681323805536353 688824165510992854152265)
        ·
          refine ⟨516618124133244640614199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688824165510992854152265 516618124133244640614199)
          ·
            refine ⟨774927186199866960921299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516618124133244640614199 774927186199866960921299)
            ·
              refine ⟨1162390779299800441381949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774927186199866960921299 1162390779299800441381949)
              ·
                refine ⟨435896542237425165518231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162390779299800441381949 435896542237425165518231)
                ·
                  refine ⟨653844813356137748277347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435896542237425165518231 653844813356137748277347)
                  ·
                    refine ⟨980767220034206622416021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653844813356137748277347 980767220034206622416021)
                    ·
                      refine ⟨45973463439103435425751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 980767220034206622416021 45973463439103435425751)
                      ·
                        rfl

theorem cell23_89533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_89533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89533 prefixEnd_89533 := by exact prefixLift 89533
  have htrace : WordTrace (prefixWord ++ tailWord_89533) baseStart_89533 baseEnd_89533 := by
    simpa [prefixWord, tailWord_89533, baseEnd_89533] using wordTrace_append hprefix tailTrace_89533
  have hstable : (prefixWord ++ tailWord_89533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89533).length < 2 ^ (prefixWord ++ tailWord_89533).sum := by decide
  have hdescent : baseEnd_89533 < baseStart_89533 := by decide
  rcases family_descends (prefixWord ++ tailWord_89533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89571 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 1, 2, 2]
def baseStart_89571 : Nat := 118140960795 + 89571 * 2 ^ 59
def prefixEnd_89571 : Nat := 4983230072969 + 3 ^ 40 * 89571 * 2
def baseEnd_89571 : Nat := 45992975703974286750577

theorem tailTrace_89571 : CollatzResearch.WordTrace tailWord_89571 prefixEnd_89571 45992975703974286750577 := by
  unfold tailWord_89571
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266922758507039354012567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2177948505671359569341711 3266922758507039354012567)
  ·
    refine ⟨4900384137760559031018851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266922758507039354012567 4900384137760559031018851)
    ·
      refine ⟨7350576206640838546528277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900384137760559031018851 7350576206640838546528277)
      ·
        refine ⟨344558259686289306868513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7350576206640838546528277 344558259686289306868513)
        ·
          refine ⟨258418694764716980151385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344558259686289306868513 258418694764716980151385)
          ·
            refine ⟨193814021073537735113539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258418694764716980151385 193814021073537735113539)
            ·
              refine ⟨290721031610306602670309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193814021073537735113539 290721031610306602670309)
              ·
                refine ⟨54510193426932488000683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290721031610306602670309 54510193426932488000683)
                ·
                  refine ⟨81765290140398732001025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54510193426932488000683 81765290140398732001025)
                  ·
                    refine ⟨61323967605299049000769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81765290140398732001025 61323967605299049000769)
                    ·
                      refine ⟨45992975703974286750577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61323967605299049000769 45992975703974286750577)
                      ·
                        rfl

theorem cell23_89571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_89571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89571 prefixEnd_89571 := by exact prefixLift 89571
  have htrace : WordTrace (prefixWord ++ tailWord_89571) baseStart_89571 baseEnd_89571 := by
    simpa [prefixWord, tailWord_89571, baseEnd_89571] using wordTrace_append hprefix tailTrace_89571
  have hstable : (prefixWord ++ tailWord_89571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89571).length < 2 ^ (prefixWord ++ tailWord_89571).sum := by decide
  have hdescent : baseEnd_89571 < baseStart_89571 := by decide
  rcases family_descends (prefixWord ++ tailWord_89571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89593 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_89593 : Nat := 118140960795 + 89593 * 2 ^ 59
def prefixEnd_89593 : Nat := 4983230072969 + 3 ^ 40 * 89593 * 2
def baseEnd_89593 : Nat := 46004272278373200675475

theorem tailTrace_89593 : CollatzResearch.WordTrace tailWord_89593 prefixEnd_89593 46004272278373200675475 := by
  unfold tailWord_89593
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267725164427337111313433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2178483442951558074208955 3267725164427337111313433)
  ·
    refine ⟨2450793873320502833485075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3267725164427337111313433 2450793873320502833485075)
    ·
      refine ⟨3676190809980754250227613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2450793873320502833485075 3676190809980754250227613)
      ·
        refine ⟨1378571553742782843835355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3676190809980754250227613 1378571553742782843835355)
        ·
          refine ⟨2067857330614174265753033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378571553742782843835355 2067857330614174265753033)
          ·
            refine ⟨1550892997960630699314775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067857330614174265753033 1550892997960630699314775)
            ·
              refine ⟨2326339496940946048972163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550892997960630699314775 2326339496940946048972163)
              ·
                refine ⟨3489509245411419073458245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326339496940946048972163 3489509245411419073458245)
                ·
                  refine ⟨654282983514641076273421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3489509245411419073458245 654282983514641076273421)
                  ·
                    refine ⟨245356118817990403602533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654282983514641076273421 245356118817990403602533)
                    ·
                      refine ⟨46004272278373200675475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 245356118817990403602533 46004272278373200675475)
                      ·
                        rfl

theorem cell23_89593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_89593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89593 prefixEnd_89593 := by exact prefixLift 89593
  have htrace : WordTrace (prefixWord ++ tailWord_89593) baseStart_89593 baseEnd_89593 := by
    simpa [prefixWord, tailWord_89593, baseEnd_89593] using wordTrace_append hprefix tailTrace_89593
  have hstable : (prefixWord ++ tailWord_89593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89593).length < 2 ^ (prefixWord ++ tailWord_89593).sum := by decide
  have hdescent : baseEnd_89593 < baseStart_89593 := by decide
  rcases family_descends (prefixWord ++ tailWord_89593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89597 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_89597 : Nat := 118140960795 + 89597 * 2 ^ 59
def prefixEnd_89597 : Nat := 4983230072969 + 3 ^ 40 * 89597 * 2
def baseEnd_89597 : Nat := 46006326200991185025457

theorem tailTrace_89597 : CollatzResearch.WordTrace tailWord_89597 prefixEnd_89597 46006326200991185025457 := by
  unfold tailWord_89597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267871056412845794459045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2178580704275230529639363 3267871056412845794459045)
  ·
    refine ⟨612725823077408586461071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3267871056412845794459045 612725823077408586461071)
    ·
      refine ⟨919088734616112879691607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612725823077408586461071 919088734616112879691607)
      ·
        refine ⟨1378633101924169319537411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919088734616112879691607 1378633101924169319537411)
        ·
          refine ⟨2067949652886253979306117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378633101924169319537411 2067949652886253979306117)
          ·
            refine ⟨387740559916172621119897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2067949652886253979306117 387740559916172621119897)
            ·
              refine ⟨290805419937129465839923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387740559916172621119897 290805419937129465839923)
              ·
                refine ⟨436208129905694198759885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290805419937129465839923 436208129905694198759885)
                ·
                  refine ⟨163578048714635324534957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436208129905694198759885 163578048714635324534957)
                  ·
                    refine ⟨61341768267988246700609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163578048714635324534957 61341768267988246700609)
                    ·
                      refine ⟨46006326200991185025457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61341768267988246700609 46006326200991185025457)
                      ·
                        rfl

theorem cell23_89597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_89597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89597 prefixEnd_89597 := by exact prefixLift 89597
  have htrace : WordTrace (prefixWord ++ tailWord_89597) baseStart_89597 baseEnd_89597 := by
    simpa [prefixWord, tailWord_89597, baseEnd_89597] using wordTrace_append hprefix tailTrace_89597
  have hstable : (prefixWord ++ tailWord_89597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89597).length < 2 ^ (prefixWord ++ tailWord_89597).sum := by decide
  have hdescent : baseEnd_89597 < baseStart_89597 := by decide
  rcases family_descends (prefixWord ++ tailWord_89597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89673 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_89673 : Nat := 118140960795 + 89673 * 2 ^ 59
def prefixEnd_89673 : Nat := 4983230072969 + 3 ^ 40 * 89673 * 2
def baseEnd_89673 : Nat := 46045350730732887675107

theorem tailTrace_89673 : CollatzResearch.WordTrace tailWord_89673 prefixEnd_89673 46045350730732887675107 := by
  unfold tailWord_89673
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270643004137510774225673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2180428669425007182817115 3270643004137510774225673)
  ·
    refine ⟨2452982253103133080669255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3270643004137510774225673 2452982253103133080669255)
    ·
      refine ⟨3679473379654699621003883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452982253103133080669255 3679473379654699621003883)
      ·
        refine ⟨5519210069482049431505825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679473379654699621003883 5519210069482049431505825)
        ·
          refine ⟨4139407552111537073629369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519210069482049431505825 4139407552111537073629369)
          ·
            refine ⟨3104555664083652805222027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4139407552111537073629369 3104555664083652805222027)
            ·
              refine ⟨4656833496125479207833041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104555664083652805222027 4656833496125479207833041)
              ·
                refine ⟨3492625122094109405874781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4656833496125479207833041 3492625122094109405874781)
                ·
                  refine ⟨1309734420785291027203043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3492625122094109405874781 1309734420785291027203043)
                  ·
                    refine ⟨1964601631177936540804565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309734420785291027203043 1964601631177936540804565)
                    ·
                      refine ⟨46045350730732887675107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1964601631177936540804565 46045350730732887675107)
                      ·
                        rfl

theorem cell23_89673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_89673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89673 prefixEnd_89673 := by exact prefixLift 89673
  have htrace : WordTrace (prefixWord ++ tailWord_89673) baseStart_89673 baseEnd_89673 := by
    simpa [prefixWord, tailWord_89673, baseEnd_89673] using wordTrace_append hprefix tailTrace_89673
  have hstable : (prefixWord ++ tailWord_89673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89673).length < 2 ^ (prefixWord ++ tailWord_89673).sum := by decide
  have hdescent : baseEnd_89673 < baseStart_89673 := by decide
  rcases family_descends (prefixWord ++ tailWord_89673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89680 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_89680 : Nat := 118140960795 + 89680 * 2 ^ 59
def prefixEnd_89680 : Nat := 4983230072969 + 3 ^ 40 * 89680 * 2
def baseEnd_89680 : Nat := 15349648365104786762525

theorem tailTrace_89680 : CollatzResearch.WordTrace tailWord_89680 prefixEnd_89680 15349648365104786762525 := by
  unfold tailWord_89680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635449157556075484865247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2180598876741433979820329 1635449157556075484865247)
  ·
    refine ⟨2453173736334113227297871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1635449157556075484865247 2453173736334113227297871)
    ·
      refine ⟨3679760604501169840946807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2453173736334113227297871 3679760604501169840946807)
      ·
        refine ⟨5519640906751754761420211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679760604501169840946807 5519640906751754761420211)
        ·
          refine ⟨8279461360127632142130317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5519640906751754761420211 8279461360127632142130317)
          ·
            refine ⟨3104798010047862053298869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8279461360127632142130317 3104798010047862053298869)
            ·
              refine ⟨291074813441987067496769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3104798010047862053298869 291074813441987067496769)
              ·
                refine ⟨218306110081490300622577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291074813441987067496769 218306110081490300622577)
                ·
                  refine ⟨163729582561117725466933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218306110081490300622577 163729582561117725466933)
                  ·
                    refine ⟨15349648365104786762525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163729582561117725466933 15349648365104786762525)
                    ·
                      rfl

theorem cell23_89680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_89680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89680 prefixEnd_89680 := by exact prefixLift 89680
  have htrace : WordTrace (prefixWord ++ tailWord_89680) baseStart_89680 baseEnd_89680 := by
    simpa [prefixWord, tailWord_89680, baseEnd_89680] using wordTrace_append hprefix tailTrace_89680
  have hstable : (prefixWord ++ tailWord_89680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89680).length < 2 ^ (prefixWord ++ tailWord_89680).sum := by decide
  have hdescent : baseEnd_89680 < baseStart_89680 := by decide
  rcases family_descends (prefixWord ++ tailWord_89680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89684 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 5]
def baseStart_89684 : Nat := 118140960795 + 89684 * 2 ^ 59
def prefixEnd_89684 : Nat := 4983230072969 + 3 ^ 40 * 89684 * 2
def baseEnd_89684 : Nat := 5116777668659149404173

theorem tailTrace_89684 : CollatzResearch.WordTrace tailWord_89684 prefixEnd_89684 5116777668659149404173 := by
  unfold tailWord_89684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635522103548829826438053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2180696138065106435250737 1635522103548829826438053)
  ·
    refine ⟨306660394415405592457135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1635522103548829826438053 306660394415405592457135)
    ·
      refine ⟨459990591623108388685703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306660394415405592457135 459990591623108388685703)
      ·
        refine ⟨689985887434662583028555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459990591623108388685703 689985887434662583028555)
        ·
          refine ⟨1034978831151993874542833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689985887434662583028555 1034978831151993874542833)
          ·
            refine ⟨776234123363995405907125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034978831151993874542833 776234123363995405907125)
            ·
              refine ⟨72771949065374569303793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 776234123363995405907125 72771949065374569303793)
              ·
                refine ⟨54578961799030926977845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72771949065374569303793 54578961799030926977845)
                ·
                  refine ⟨5116777668659149404173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54578961799030926977845 5116777668659149404173)
                  ·
                    rfl

theorem cell23_89684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_89684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89684 prefixEnd_89684 := by exact prefixLift 89684
  have htrace : WordTrace (prefixWord ++ tailWord_89684) baseStart_89684 baseEnd_89684 := by
    simpa [prefixWord, tailWord_89684, baseEnd_89684] using wordTrace_append hprefix tailTrace_89684
  have hstable : (prefixWord ++ tailWord_89684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89684).length < 2 ^ (prefixWord ++ tailWord_89684).sum := by decide
  have hdescent : baseEnd_89684 < baseStart_89684 := by decide
  rcases family_descends (prefixWord ++ tailWord_89684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89737 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_89737 : Nat := 118140960795 + 89737 * 2 ^ 59
def prefixEnd_89737 : Nat := 4983230072969 + 3 ^ 40 * 89737 * 2
def baseEnd_89737 : Nat := 46078213492620637274813

theorem tailTrace_89737 : CollatzResearch.WordTrace tailWord_89737 prefixEnd_89737 46078213492620637274813 := by
  unfold tailWord_89737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272977275905649704555465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2181984850603766469703643 3272977275905649704555465)
  ·
    refine ⟨2454732956929237278416599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3272977275905649704555465 2454732956929237278416599)
    ·
      refine ⟨3682099435393855917624899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454732956929237278416599 3682099435393855917624899)
      ·
        refine ⟨5523149153090783876437349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682099435393855917624899 5523149153090783876437349)
        ·
          refine ⟨1035590466204521976832003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5523149153090783876437349 1035590466204521976832003)
          ·
            refine ⟨1553385699306782965248005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035590466204521976832003 1553385699306782965248005)
            ·
              refine ⟨291259818620021805984001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1553385699306782965248005 291259818620021805984001)
              ·
                refine ⟨218444863965016354488001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291259818620021805984001 218444863965016354488001)
                ·
                  refine ⟨163833647973762265866001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218444863965016354488001 163833647973762265866001)
                  ·
                    refine ⟨122875235980321699399501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163833647973762265866001 122875235980321699399501)
                    ·
                      refine ⟨46078213492620637274813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 122875235980321699399501 46078213492620637274813)
                      ·
                        rfl

theorem cell23_89737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_89737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89737 prefixEnd_89737 := by exact prefixLift 89737
  have htrace : WordTrace (prefixWord ++ tailWord_89737) baseStart_89737 baseEnd_89737 := by
    simpa [prefixWord, tailWord_89737, baseEnd_89737] using wordTrace_append hprefix tailTrace_89737
  have hstable : (prefixWord ++ tailWord_89737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89737).length < 2 ^ (prefixWord ++ tailWord_89737).sum := by decide
  have hdescent : baseEnd_89737 < baseStart_89737 := by decide
  rcases family_descends (prefixWord ++ tailWord_89737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89817 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_89817 : Nat := 118140960795 + 89817 * 2 ^ 59
def prefixEnd_89817 : Nat := 4983230072969 + 3 ^ 40 * 89817 * 2
def baseEnd_89817 : Nat := 15373097314993441424815

theorem tailTrace_89817 : CollatzResearch.WordTrace tailWord_89817 prefixEnd_89817 15373097314993441424815 := by
  unfold tailWord_89817
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275895115615823367467705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2183930077077215578311803 3275895115615823367467705)
  ·
    refine ⟨2456921336711867525600779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3275895115615823367467705 2456921336711867525600779)
    ·
      refine ⟨3685382005067801288401169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456921336711867525600779 3685382005067801288401169)
      ·
        refine ⟨2764036503800850966300877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3685382005067801288401169 2764036503800850966300877)
        ·
          refine ⟨1036513688925319112362829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2764036503800850966300877 1036513688925319112362829)
          ·
            refine ⟨388692633346994667136061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1036513688925319112362829 388692633346994667136061)
            ·
              refine ⟨145759737505123000176023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388692633346994667136061 145759737505123000176023)
              ·
                refine ⟨218639606257684500264035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145759737505123000176023 218639606257684500264035)
                ·
                  refine ⟨327959409386526750396053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218639606257684500264035 327959409386526750396053)
                  ·
                    refine ⟨15373097314993441424815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 327959409386526750396053 15373097314993441424815)
                    ·
                      rfl

theorem cell23_89817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_89817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89817 prefixEnd_89817 := by exact prefixLift 89817
  have htrace : WordTrace (prefixWord ++ tailWord_89817) baseStart_89817 baseEnd_89817 := by
    simpa [prefixWord, tailWord_89817, baseEnd_89817] using wordTrace_append hprefix tailTrace_89817
  have hstable : (prefixWord ++ tailWord_89817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89817).length < 2 ^ (prefixWord ++ tailWord_89817).sum := by decide
  have hdescent : baseEnd_89817 < baseStart_89817 := by decide
  rcases family_descends (prefixWord ++ tailWord_89817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89908 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_89908 : Nat := 118140960795 + 89908 * 2 ^ 59
def prefixEnd_89908 : Nat := 4983230072969 + 3 ^ 40 * 89908 * 2
def baseEnd_89908 : Nat := 46166018684539468236527

theorem tailTrace_89908 : CollatzResearch.WordTrace tailWord_89908 prefixEnd_89908 46166018684539468236527 := by
  unfold tailWord_89908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639607079143072954515189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2186142772190763939353585 1639607079143072954515189)
  ·
    refine ⟨153713163669663089485799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1639607079143072954515189 153713163669663089485799)
    ·
      refine ⟨230569745504494634228699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153713163669663089485799 230569745504494634228699)
      ·
        refine ⟨345854618256741951343049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230569745504494634228699 345854618256741951343049)
        ·
          refine ⟨259390963692556463507287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345854618256741951343049 259390963692556463507287)
          ·
            refine ⟨389086445538834695260931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259390963692556463507287 389086445538834695260931)
            ·
              refine ⟨583629668308252042891397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389086445538834695260931 583629668308252042891397)
              ·
                refine ⟨109430562807797258042137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583629668308252042891397 109430562807797258042137)
                ·
                  refine ⟨82072922105847943531603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109430562807797258042137 82072922105847943531603)
                  ·
                    refine ⟨123109383158771915297405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82072922105847943531603 123109383158771915297405)
                    ·
                      refine ⟨46166018684539468236527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123109383158771915297405 46166018684539468236527)
                      ·
                        rfl

theorem cell23_89908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_89908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89908 prefixEnd_89908 := by exact prefixLift 89908
  have htrace : WordTrace (prefixWord ++ tailWord_89908) baseStart_89908 baseEnd_89908 := by
    simpa [prefixWord, tailWord_89908, baseEnd_89908] using wordTrace_append hprefix tailTrace_89908
  have hstable : (prefixWord ++ tailWord_89908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89908).length < 2 ^ (prefixWord ++ tailWord_89908).sum := by decide
  have hdescent : baseEnd_89908 < baseStart_89908 := by decide
  rcases family_descends (prefixWord ++ tailWord_89908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89909 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_89909 : Nat := 118140960795 + 89909 * 2 ^ 59
def prefixEnd_89909 : Nat := 4983230072969 + 3 ^ 40 * 89909 * 2
def baseEnd_89909 : Nat := 46166532165193964324023

theorem tailTrace_89909 : CollatzResearch.WordTrace tailWord_89909 prefixEnd_89909 46166532165193964324023 := by
  unfold tailWord_89909
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279250631282523079816781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186167087521682053211187 3279250631282523079816781)
  ·
    refine ⟨1229718986730946154931293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3279250631282523079816781 1229718986730946154931293)
    ·
      refine ⟨461144620024104808099235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1229718986730946154931293 461144620024104808099235)
      ·
        refine ⟨691716930036157212148853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461144620024104808099235 691716930036157212148853)
        ·
          refine ⟨64848462190889738638955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 691716930036157212148853 64848462190889738638955)
          ·
            refine ⟨97272693286334607958433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64848462190889738638955 97272693286334607958433)
            ·
              refine ⟨72954519964750955968825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97272693286334607958433 72954519964750955968825)
              ·
                refine ⟨54715889973563216976619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72954519964750955968825 54715889973563216976619)
                ·
                  refine ⟨82073834960344825464929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54715889973563216976619 82073834960344825464929)
                  ·
                    refine ⟨61555376220258619098697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82073834960344825464929 61555376220258619098697)
                    ·
                      refine ⟨46166532165193964324023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61555376220258619098697 46166532165193964324023)
                      ·
                        rfl

theorem cell23_89909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_89909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89909 prefixEnd_89909 := by exact prefixLift 89909
  have htrace : WordTrace (prefixWord ++ tailWord_89909) baseStart_89909 baseEnd_89909 := by
    simpa [prefixWord, tailWord_89909, baseEnd_89909] using wordTrace_append hprefix tailTrace_89909
  have hstable : (prefixWord ++ tailWord_89909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89909).length < 2 ^ (prefixWord ++ tailWord_89909).sum := by decide
  have hdescent : baseEnd_89909 < baseStart_89909 := by decide
  rcases family_descends (prefixWord ++ tailWord_89909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89927 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_89927 : Nat := 118140960795 + 89927 * 2 ^ 59
def prefixEnd_89927 : Nat := 4983230072969 + 3 ^ 40 * 89927 * 2
def baseEnd_89927 : Nat := 46175774816974893898939

theorem tailTrace_89927 : CollatzResearch.WordTrace tailWord_89927 prefixEnd_89927 46175774816974893898939 := by
  unfold tailWord_89927
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279907145217312153972035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186604763478208102648023 3279907145217312153972035)
  ·
    refine ⟨4919860717825968230958053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279907145217312153972035 4919860717825968230958053)
    ·
      refine ⟨922473884592369043304635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4919860717825968230958053 922473884592369043304635)
      ·
        refine ⟨1383710826888553564956953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922473884592369043304635 1383710826888553564956953)
        ·
          refine ⟨1037783120166415173717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383710826888553564956953 1037783120166415173717715)
          ·
            refine ⟨1556674680249622760576573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037783120166415173717715 1556674680249622760576573)
            ·
              refine ⟨583753005093608535216215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1556674680249622760576573 583753005093608535216215)
              ·
                refine ⟨875629507640412802824323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583753005093608535216215 875629507640412802824323)
                ·
                  refine ⟨1313444261460619204236485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875629507640412802824323 1313444261460619204236485)
                  ·
                    refine ⟨246270799023866100794341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313444261460619204236485 246270799023866100794341)
                    ·
                      refine ⟨46175774816974893898939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 246270799023866100794341 46175774816974893898939)
                      ·
                        rfl

theorem cell23_89927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_89927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89927 prefixEnd_89927 := by exact prefixLift 89927
  have htrace : WordTrace (prefixWord ++ tailWord_89927) baseStart_89927 baseEnd_89927 := by
    simpa [prefixWord, tailWord_89927, baseEnd_89927] using wordTrace_append hprefix tailTrace_89927
  have hstable : (prefixWord ++ tailWord_89927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89927).length < 2 ^ (prefixWord ++ tailWord_89927).sum := by decide
  have hdescent : baseEnd_89927 < baseStart_89927 := by decide
  rcases family_descends (prefixWord ++ tailWord_89927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89937 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 9]
def baseStart_89937 : Nat := 118140960795 + 89937 * 2 ^ 59
def prefixEnd_89937 : Nat := 4983230072969 + 3 ^ 40 * 89937 * 2
def baseEnd_89937 : Nat := 5131212180391094974877

theorem tailTrace_89937 : CollatzResearch.WordTrace tailWord_89937 prefixEnd_89937 5131212180391094974877 := by
  unfold tailWord_89937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280271875181083861836065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186847916787389241224043 3280271875181083861836065)
  ·
    refine ⟨2460203906385812896377049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3280271875181083861836065 2460203906385812896377049)
    ·
      refine ⟨1845152929789359672282787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2460203906385812896377049 1845152929789359672282787)
      ·
        refine ⟨2767729394684039508424181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845152929789359672282787 2767729394684039508424181)
        ·
          refine ⟨259474630751628703914767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2767729394684039508424181 259474630751628703914767)
          ·
            refine ⟨389211946127443055872151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259474630751628703914767 389211946127443055872151)
            ·
              refine ⟨583817919191164583808227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389211946127443055872151 583817919191164583808227)
              ·
                refine ⟨875726878786746875712341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583817919191164583808227 875726878786746875712341)
                ·
                  refine ⟨5131212180391094974877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 875726878786746875712341 5131212180391094974877)
                  ·
                    rfl

theorem cell23_89937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_89937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89937 prefixEnd_89937 := by exact prefixLift 89937
  have htrace : WordTrace (prefixWord ++ tailWord_89937) baseStart_89937 baseEnd_89937 := by
    simpa [prefixWord, tailWord_89937, baseEnd_89937] using wordTrace_append hprefix tailTrace_89937
  have hstable : (prefixWord ++ tailWord_89937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89937).length < 2 ^ (prefixWord ++ tailWord_89937).sum := by decide
  have hdescent : baseEnd_89937 < baseStart_89937 := by decide
  rcases family_descends (prefixWord ++ tailWord_89937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89964 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_89964 : Nat := 118140960795 + 89964 * 2 ^ 59
def prefixEnd_89964 : Nat := 4983230072969 + 3 ^ 40 * 89964 * 2
def baseEnd_89964 : Nat := 46194773601191249136269

theorem tailTrace_89964 : CollatzResearch.WordTrace tailWord_89964 prefixEnd_89964 46194773601191249136269 := by
  unfold tailWord_89964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640628323041633736534473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2187504430722178315379297 1640628323041633736534473)
  ·
    refine ⟨1230471242281225302400855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1640628323041633736534473 1230471242281225302400855)
    ·
      refine ⟨1845706863421837953601283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230471242281225302400855 1845706863421837953601283)
      ·
        refine ⟨2768560295132756930401925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845706863421837953601283 2768560295132756930401925)
        ·
          refine ⟨519105055337391924450361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2768560295132756930401925 519105055337391924450361)
          ·
            refine ⟨389328791503043943337771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519105055337391924450361 389328791503043943337771)
            ·
              refine ⟨583993187254565915006657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389328791503043943337771 583993187254565915006657)
              ·
                refine ⟨437994890440924436254993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583993187254565915006657 437994890440924436254993)
                ·
                  refine ⟨328496167830693327191245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437994890440924436254993 328496167830693327191245)
                  ·
                    refine ⟨123186062936509997696717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 328496167830693327191245 123186062936509997696717)
                    ·
                      refine ⟨46194773601191249136269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123186062936509997696717 46194773601191249136269)
                      ·
                        rfl

theorem cell23_89964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_89964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89964 prefixEnd_89964 := by exact prefixLift 89964
  have htrace : WordTrace (prefixWord ++ tailWord_89964) baseStart_89964 baseEnd_89964 := by
    simpa [prefixWord, tailWord_89964, baseEnd_89964] using wordTrace_append hprefix tailTrace_89964
  have hstable : (prefixWord ++ tailWord_89964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89964).length < 2 ^ (prefixWord ++ tailWord_89964).sum := by decide
  have hdescent : baseEnd_89964 < baseStart_89964 := by decide
  rcases family_descends (prefixWord ++ tailWord_89964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89977 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_89977 : Nat := 118140960795 + 89977 * 2 ^ 59
def prefixEnd_89977 : Nat := 4983230072969 + 3 ^ 40 * 89977 * 2
def baseEnd_89977 : Nat := 46201448849699698273709

theorem tailTrace_89977 : CollatzResearch.WordTrace tailWord_89977 prefixEnd_89977 46201448849699698273709 := by
  unfold tailWord_89977
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281730795036170693292185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2187820530024113795528123 3281730795036170693292185)
  ·
    refine ⟨2461298096277128019969139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3281730795036170693292185 2461298096277128019969139)
    ·
      refine ⟨3691947144415692029953709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461298096277128019969139 3691947144415692029953709)
      ·
        refine ⟨1384480179155884511232641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3691947144415692029953709 1384480179155884511232641)
        ·
          refine ⟨1038360134366913383424481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384480179155884511232641 1038360134366913383424481)
          ·
            refine ⟨778770100775185037568361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038360134366913383424481 778770100775185037568361)
            ·
              refine ⟨584077575581388778176271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778770100775185037568361 584077575581388778176271)
              ·
                refine ⟨876116363372083167264407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584077575581388778176271 876116363372083167264407)
                ·
                  refine ⟨1314174545058124750896611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876116363372083167264407 1314174545058124750896611)
                  ·
                    refine ⟨1971261817587187126344917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1314174545058124750896611 1971261817587187126344917)
                    ·
                      refine ⟨46201448849699698273709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1971261817587187126344917 46201448849699698273709)
                      ·
                        rfl

theorem cell23_89977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_89977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_89977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_89977 prefixEnd_89977 := by exact prefixLift 89977
  have htrace : WordTrace (prefixWord ++ tailWord_89977) baseStart_89977 baseEnd_89977 := by
    simpa [prefixWord, tailWord_89977, baseEnd_89977] using wordTrace_append hprefix tailTrace_89977
  have hstable : (prefixWord ++ tailWord_89977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89977).length < 2 ^ (prefixWord ++ tailWord_89977).sum := by decide
  have hdescent : baseEnd_89977 < baseStart_89977 := by decide
  rcases family_descends (prefixWord ++ tailWord_89977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90057 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_90057 : Nat := 118140960795 + 90057 * 2 ^ 59
def prefixEnd_90057 : Nat := 4983230072969 + 3 ^ 40 * 90057 * 2
def baseEnd_90057 : Nat := 15414175767353128424447

theorem tailTrace_90057 : CollatzResearch.WordTrace tailWord_90057 prefixEnd_90057 15414175767353128424447 := by
  unfold tailWord_90057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284648634746344356204425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2189765756497562904136283 3284648634746344356204425)
  ·
    refine ⟨2463486476059758267153319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3284648634746344356204425 2463486476059758267153319)
    ·
      refine ⟨3695229714089637400729979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463486476059758267153319 3695229714089637400729979)
      ·
        refine ⟨5542844571134456101094969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695229714089637400729979 5542844571134456101094969)
        ·
          refine ⟨4157133428350842075821227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5542844571134456101094969 4157133428350842075821227)
          ·
            refine ⟨6235700142526263113731841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157133428350842075821227 6235700142526263113731841)
            ·
              refine ⟨4676775106894697335298881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235700142526263113731841 4676775106894697335298881)
              ·
                refine ⟨3507581330171023001474161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676775106894697335298881 3507581330171023001474161)
                ·
                  refine ⟨2630685997628267251105621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507581330171023001474161 2630685997628267251105621)
                  ·
                    refine ⟨15414175767353128424447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2630685997628267251105621 15414175767353128424447)
                    ·
                      rfl

theorem cell23_90057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_90057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90057 prefixEnd_90057 := by exact prefixLift 90057
  have htrace : WordTrace (prefixWord ++ tailWord_90057) baseStart_90057 baseEnd_90057 := by
    simpa [prefixWord, tailWord_90057, baseEnd_90057] using wordTrace_append hprefix tailTrace_90057
  have hstable : (prefixWord ++ tailWord_90057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90057).length < 2 ^ (prefixWord ++ tailWord_90057).sum := by decide
  have hdescent : baseEnd_90057 < baseStart_90057 := by decide
  rcases family_descends (prefixWord ++ tailWord_90057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90082 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_90082 : Nat := 118140960795 + 90082 * 2 ^ 59
def prefixEnd_90082 : Nat := 4983230072969 + 3 ^ 40 * 90082 * 2
def baseEnd_90082 : Nat := 15418454772807262486909

theorem tailTrace_90082 : CollatzResearch.WordTrace tailWord_90082 prefixEnd_90082 15418454772807262486909 := by
  unfold tailWord_90082
  simp only [CollatzResearch.WordTrace]
  refine ⟨821390114913943406466125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2190373639770515750576333 821390114913943406466125)
  ·
    refine ⟨308021293092728777424797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 821390114913943406466125 308021293092728777424797)
    ·
      refine ⟨115507984909773291534299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308021293092728777424797 115507984909773291534299)
      ·
        refine ⟨173261977364659937301449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115507984909773291534299 173261977364659937301449)
        ·
          refine ⟨129946483023494952976087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173261977364659937301449 129946483023494952976087)
          ·
            refine ⟨194919724535242429464131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129946483023494952976087 194919724535242429464131)
            ·
              refine ⟨292379586802863644196197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194919724535242429464131 292379586802863644196197)
              ·
                refine ⟨54821172525536933286787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292379586802863644196197 54821172525536933286787)
                ·
                  refine ⟨82231758788305399930181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54821172525536933286787 82231758788305399930181)
                  ·
                    refine ⟨15418454772807262486909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82231758788305399930181 15418454772807262486909)
                    ·
                      rfl

theorem cell23_90082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_90082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90082 prefixEnd_90082 := by exact prefixLift 90082
  have htrace : WordTrace (prefixWord ++ tailWord_90082) baseStart_90082 baseEnd_90082 := by
    simpa [prefixWord, tailWord_90082, baseEnd_90082] using wordTrace_append hprefix tailTrace_90082
  have hstable : (prefixWord ++ tailWord_90082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90082).length < 2 ^ (prefixWord ++ tailWord_90082).sum := by decide
  have hdescent : baseEnd_90082 < baseStart_90082 := by decide
  rcases family_descends (prefixWord ++ tailWord_90082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90104 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_90104 : Nat := 118140960795 + 90104 * 2 ^ 59
def prefixEnd_90104 : Nat := 4983230072969 + 3 ^ 40 * 90104 * 2
def baseEnd_90104 : Nat := 15422220297606900461875

theorem tailTrace_90104 : CollatzResearch.WordTrace tailWord_90104 prefixEnd_90104 15422220297606900461875 := by
  unfold tailWord_90104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643181432788035691582683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2190908577050714255443577 1643181432788035691582683)
  ·
    refine ⟨2464772149182053537374025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643181432788035691582683 2464772149182053537374025)
    ·
      refine ⟨1848579111886540153030519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464772149182053537374025 1848579111886540153030519)
      ·
        refine ⟨2772868667829810229545779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848579111886540153030519 2772868667829810229545779)
        ·
          refine ⟨4159303001744715344318669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772868667829810229545779 4159303001744715344318669)
          ·
            refine ⟨1559738625654268254119501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4159303001744715344318669 1559738625654268254119501)
            ·
              refine ⟨584901984620350595294813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559738625654268254119501 584901984620350595294813)
              ·
                refine ⟨219338244232631473235555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584901984620350595294813 219338244232631473235555)
                ·
                  refine ⟨329007366348947209853333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219338244232631473235555 329007366348947209853333)
                  ·
                    refine ⟨15422220297606900461875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 329007366348947209853333 15422220297606900461875)
                    ·
                      rfl

theorem cell23_90104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_90104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90104 prefixEnd_90104 := by exact prefixLift 90104
  have htrace : WordTrace (prefixWord ++ tailWord_90104) baseStart_90104 baseEnd_90104 := by
    simpa [prefixWord, tailWord_90104, baseEnd_90104] using wordTrace_append hprefix tailTrace_90104
  have hstable : (prefixWord ++ tailWord_90104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90104).length < 2 ^ (prefixWord ++ tailWord_90104).sum := by decide
  have hdescent : baseEnd_90104 < baseStart_90104 := by decide
  rcases family_descends (prefixWord ++ tailWord_90104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90122 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_90122 : Nat := 118140960795 + 90122 * 2 ^ 59
def prefixEnd_90122 : Nat := 4983230072969 + 3 ^ 40 * 90122 * 2
def baseEnd_90122 : Nat := 46275903544601630960543

theorem tailTrace_90122 : CollatzResearch.WordTrace tailWord_90122 prefixEnd_90122 46275903544601630960543 := by
  unfold tailWord_90122
  simp only [CollatzResearch.WordTrace]
  refine ⟨821754844877715114330155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2191346253007240304880413 821754844877715114330155)
  ·
    refine ⟨1232632267316572671495233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 821754844877715114330155 1232632267316572671495233)
    ·
      refine ⟨924474200487429503621425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232632267316572671495233 924474200487429503621425)
      ·
        refine ⟨693355650365572127716069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 924474200487429503621425 693355650365572127716069)
        ·
          refine ⟨130004184443544773946763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 693355650365572127716069 130004184443544773946763)
          ·
            refine ⟨195006276665317160920145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130004184443544773946763 195006276665317160920145)
            ·
              refine ⟨146254707498987870690109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195006276665317160920145 146254707498987870690109)
              ·
                refine ⟨54845515312120451508791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146254707498987870690109 54845515312120451508791)
                ·
                  refine ⟨82268272968180677263187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54845515312120451508791 82268272968180677263187)
                  ·
                    refine ⟨123402409452271015894781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82268272968180677263187 123402409452271015894781)
                    ·
                      refine ⟨46275903544601630960543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123402409452271015894781 46275903544601630960543)
                      ·
                        rfl

theorem cell23_90122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_90122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90122 prefixEnd_90122 := by exact prefixLift 90122
  have htrace : WordTrace (prefixWord ++ tailWord_90122) baseStart_90122 baseEnd_90122 := by
    simpa [prefixWord, tailWord_90122, baseEnd_90122] using wordTrace_append hprefix tailTrace_90122
  have hstable : (prefixWord ++ tailWord_90122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90122).length < 2 ^ (prefixWord ++ tailWord_90122).sum := by decide
  have hdescent : baseEnd_90122 < baseStart_90122 := by decide
  rcases family_descends (prefixWord ++ tailWord_90122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90138 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_90138 : Nat := 118140960795 + 90138 * 2 ^ 59
def prefixEnd_90138 : Nat := 4983230072969 + 3 ^ 40 * 90138 * 2
def baseEnd_90138 : Nat := 15428039745024522786823

theorem tailTrace_90138 : CollatzResearch.WordTrace tailWord_90138 prefixEnd_90138 15428039745024522786823 := by
  unfold tailWord_90138
  simp only [CollatzResearch.WordTrace]
  refine ⟨821900736863223797475767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2191735298301930126602045 821900736863223797475767)
  ·
    refine ⟨1232851105294835696213651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 821900736863223797475767 1232851105294835696213651)
    ·
      refine ⟨1849276657942253544320477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232851105294835696213651 1849276657942253544320477)
      ·
        refine ⟨693478746728345079120179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1849276657942253544320477 693478746728345079120179)
        ·
          refine ⟨1040218120092517618680269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693478746728345079120179 1040218120092517618680269)
          ·
            refine ⟨390081795034694107005101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1040218120092517618680269 390081795034694107005101)
            ·
              refine ⟨146280673138010290126913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390081795034694107005101 146280673138010290126913)
              ·
                refine ⟨109710504853507717595185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146280673138010290126913 109710504853507717595185)
                ·
                  refine ⟨82282878640130788196389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109710504853507717595185 82282878640130788196389)
                  ·
                    refine ⟨15428039745024522786823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82282878640130788196389 15428039745024522786823)
                    ·
                      rfl

theorem cell23_90138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_90138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90138 prefixEnd_90138 := by exact prefixLift 90138
  have htrace : WordTrace (prefixWord ++ tailWord_90138) baseStart_90138 baseEnd_90138 := by
    simpa [prefixWord, tailWord_90138, baseEnd_90138] using wordTrace_append hprefix tailTrace_90138
  have hstable : (prefixWord ++ tailWord_90138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90138).length < 2 ^ (prefixWord ++ tailWord_90138).sum := by decide
  have hdescent : baseEnd_90138 < baseStart_90138 := by decide
  rcases family_descends (prefixWord ++ tailWord_90138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90148 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_90148 : Nat := 118140960795 + 90148 * 2 ^ 59
def prefixEnd_90148 : Nat := 4983230072969 + 3 ^ 40 * 90148 * 2
def baseEnd_90148 : Nat := 46289254041618529235423

theorem tailTrace_90148 : CollatzResearch.WordTrace tailWord_90148 prefixEnd_90148 46289254041618529235423 := by
  unfold tailWord_90148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643983838708333448883549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2191978451611111265178065 1643983838708333448883549)
  ·
    refine ⟨616493939515625043331331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1643983838708333448883549 616493939515625043331331)
    ·
      refine ⟨924740909273437564996997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616493939515625043331331 924740909273437564996997)
      ·
        refine ⟨173388920488769543436937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 924740909273437564996997 173388920488769543436937)
        ·
          refine ⟨130041690366577157577703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173388920488769543436937 130041690366577157577703)
          ·
            refine ⟨195062535549865736366555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130041690366577157577703 195062535549865736366555)
            ·
              refine ⟨292593803324798604549833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195062535549865736366555 292593803324798604549833)
              ·
                refine ⟨219445352493598953412375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292593803324798604549833 219445352493598953412375)
                ·
                  refine ⟨329168028740398430118563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219445352493598953412375 329168028740398430118563)
                  ·
                    refine ⟨493752043110597645177845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329168028740398430118563 493752043110597645177845)
                    ·
                      refine ⟨46289254041618529235423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 493752043110597645177845 46289254041618529235423)
                      ·
                        rfl

theorem cell23_90148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_90148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90148 prefixEnd_90148 := by exact prefixLift 90148
  have htrace : WordTrace (prefixWord ++ tailWord_90148) baseStart_90148 baseEnd_90148 := by
    simpa [prefixWord, tailWord_90148, baseEnd_90148] using wordTrace_append hprefix tailTrace_90148
  have hstable : (prefixWord ++ tailWord_90148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90148).length < 2 ^ (prefixWord ++ tailWord_90148).sum := by decide
  have hdescent : baseEnd_90148 < baseStart_90148 := by decide
  rcases family_descends (prefixWord ++ tailWord_90148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90158 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_90158 : Nat := 118140960795 + 90158 * 2 ^ 59
def prefixEnd_90158 : Nat := 4983230072969 + 3 ^ 40 * 90158 * 2
def baseEnd_90158 : Nat := 46294388848163490110377

theorem tailTrace_90158 : CollatzResearch.WordTrace tailWord_90158 prefixEnd_90158 46294388848163490110377 := by
  unfold tailWord_90158
  simp only [CollatzResearch.WordTrace]
  refine ⟨411041550922554825703891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2192221604920292403754085 411041550922554825703891)
  ·
    refine ⟨616562326383832238555837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 411041550922554825703891 616562326383832238555837)
    ·
      refine ⟨231210872393937089458439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 616562326383832238555837 231210872393937089458439)
      ·
        refine ⟨346816308590905634187659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231210872393937089458439 346816308590905634187659)
        ·
          refine ⟨520224462886358451281489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346816308590905634187659 520224462886358451281489)
          ·
            refine ⟨390168347164768838461117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520224462886358451281489 390168347164768838461117)
            ·
              refine ⟨146313130186788314422919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390168347164768838461117 146313130186788314422919)
              ·
                refine ⟨219469695280182471634379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146313130186788314422919 219469695280182471634379)
                ·
                  refine ⟨329204542920273707451569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219469695280182471634379 329204542920273707451569)
                  ·
                    refine ⟨246903407190205280588677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 329204542920273707451569 246903407190205280588677)
                    ·
                      refine ⟨46294388848163490110377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 246903407190205280588677 46294388848163490110377)
                      ·
                        rfl

theorem cell23_90158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_90158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90158 prefixEnd_90158 := by exact prefixLift 90158
  have htrace : WordTrace (prefixWord ++ tailWord_90158) baseStart_90158 baseEnd_90158 := by
    simpa [prefixWord, tailWord_90158, baseEnd_90158] using wordTrace_append hprefix tailTrace_90158
  have hstable : (prefixWord ++ tailWord_90158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90158).length < 2 ^ (prefixWord ++ tailWord_90158).sum := by decide
  have hdescent : baseEnd_90158 < baseStart_90158 := by decide
  rcases family_descends (prefixWord ++ tailWord_90158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90168 : List Nat := [2, 1, 2, 1, 6, 2, 2, 7]
def baseStart_90168 : Nat := 118140960795 + 90168 * 2 ^ 59
def prefixEnd_90168 : Nat := 4983230072969 + 3 ^ 40 * 90168 * 2
def baseEnd_90168 : Nat := 1714797172396609295753

theorem tailTrace_90168 : CollatzResearch.WordTrace tailWord_90168 prefixEnd_90168 1714797172396609295753 := by
  unfold tailWord_90168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644348568672105156747579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2192464758229473542330105 1644348568672105156747579)
  ·
    refine ⟨2466522853008157735121369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644348568672105156747579 2466522853008157735121369)
    ·
      refine ⟨1849892139756118301341027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2466522853008157735121369 1849892139756118301341027)
      ·
        refine ⟨2774838209634177452011541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849892139756118301341027 2774838209634177452011541)
        ·
          refine ⟨130070541076602068063041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2774838209634177452011541 130070541076602068063041)
          ·
            refine ⟨97552905807451551047281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130070541076602068063041 97552905807451551047281)
            ·
              refine ⟨73164679355588663285461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97552905807451551047281 73164679355588663285461)
              ·
                refine ⟨1714797172396609295753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73164679355588663285461 1714797172396609295753)
                ·
                  rfl

theorem cell23_90168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 7].length) (baseStart_90168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90168 prefixEnd_90168 := by exact prefixLift 90168
  have htrace : WordTrace (prefixWord ++ tailWord_90168) baseStart_90168 baseEnd_90168 := by
    simpa [prefixWord, tailWord_90168, baseEnd_90168] using wordTrace_append hprefix tailTrace_90168
  have hstable : (prefixWord ++ tailWord_90168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90168).length < 2 ^ (prefixWord ++ tailWord_90168).sum := by decide
  have hdescent : baseEnd_90168 < baseStart_90168 := by decide
  rcases family_descends (prefixWord ++ tailWord_90168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90206 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_90206 : Nat := 118140960795 + 90206 * 2 ^ 59
def prefixEnd_90206 : Nat := 4983230072969 + 3 ^ 40 * 90206 * 2
def baseEnd_90206 : Nat := 15439678639859767436719

theorem tailTrace_90206 : CollatzResearch.WordTrace tailWord_90206 prefixEnd_90206 15439678639859767436719 := by
  unfold tailWord_90206
  simp only [CollatzResearch.WordTrace]
  refine ⟨411260388900817850422309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2193388740804361868918981 411260388900817850422309)
  ·
    refine ⟨77111322918903346954183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 411260388900817850422309 77111322918903346954183)
    ·
      refine ⟨115666984378355020431275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77111322918903346954183 115666984378355020431275)
      ·
        refine ⟨173500476567532530646913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115666984378355020431275 173500476567532530646913)
        ·
          refine ⟨130125357425649397985185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173500476567532530646913 130125357425649397985185)
          ·
            refine ⟨97594018069237048488889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130125357425649397985185 97594018069237048488889)
            ·
              refine ⟨73195513551927786366667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97594018069237048488889 73195513551927786366667)
              ·
                refine ⟨109793270327891679550001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73195513551927786366667 109793270327891679550001)
                ·
                  refine ⟨82344952745918759662501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109793270327891679550001 82344952745918759662501)
                  ·
                    refine ⟨15439678639859767436719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82344952745918759662501 15439678639859767436719)
                    ·
                      rfl

theorem cell23_90206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_90206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90206 prefixEnd_90206 := by exact prefixLift 90206
  have htrace : WordTrace (prefixWord ++ tailWord_90206) baseStart_90206 baseEnd_90206 := by
    simpa [prefixWord, tailWord_90206, baseEnd_90206] using wordTrace_append hprefix tailTrace_90206
  have hstable : (prefixWord ++ tailWord_90206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90206).length < 2 ^ (prefixWord ++ tailWord_90206).sum := by decide
  have hdescent : baseEnd_90206 < baseStart_90206 := by decide
  rcases family_descends (prefixWord ++ tailWord_90206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90221 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_90221 : Nat := 118140960795 + 90221 * 2 ^ 59
def prefixEnd_90221 : Nat := 4983230072969 + 3 ^ 40 * 90221 * 2
def baseEnd_90221 : Nat := 46326738129396743622587

theorem tailTrace_90221 : CollatzResearch.WordTrace tailWord_90221 prefixEnd_90221 46326738129396743622587 := by
  unfold tailWord_90221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290630206152200365174517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2193753470768133576783011 3290630206152200365174517)
  ·
    refine ⟨308496581826768784235111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3290630206152200365174517 308496581826768784235111)
    ·
      refine ⟨462744872740153176352667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308496581826768784235111 462744872740153176352667)
      ·
        refine ⟨694117309110229764529001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462744872740153176352667 694117309110229764529001)
        ·
          refine ⟨520587981832672323396751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694117309110229764529001 520587981832672323396751)
          ·
            refine ⟨780881972749008485095127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520587981832672323396751 780881972749008485095127)
            ·
              refine ⟨1171322959123512727642691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780881972749008485095127 1171322959123512727642691)
              ·
                refine ⟨1756984438685269091464037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171322959123512727642691 1756984438685269091464037)
                ·
                  refine ⟨329434582253487954649507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756984438685269091464037 329434582253487954649507)
                  ·
                    refine ⟨494151873380231931974261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329434582253487954649507 494151873380231931974261)
                    ·
                      refine ⟨46326738129396743622587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 494151873380231931974261 46326738129396743622587)
                      ·
                        rfl

theorem cell23_90221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_90221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90221 prefixEnd_90221 := by exact prefixLift 90221
  have htrace : WordTrace (prefixWord ++ tailWord_90221) baseStart_90221 baseEnd_90221 := by
    simpa [prefixWord, tailWord_90221, baseEnd_90221] using wordTrace_append hprefix tailTrace_90221
  have hstable : (prefixWord ++ tailWord_90221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90221).length < 2 ^ (prefixWord ++ tailWord_90221).sum := by decide
  have hdescent : baseEnd_90221 < baseStart_90221 := by decide
  rcases family_descends (prefixWord ++ tailWord_90221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90268 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_90268 : Nat := 118140960795 + 90268 * 2 ^ 59
def prefixEnd_90268 : Nat := 4983230072969 + 3 ^ 40 * 90268 * 2
def baseEnd_90268 : Nat := 46350871720158059734871

theorem tailTrace_90268 : CollatzResearch.WordTrace tailWord_90268 prefixEnd_90268 46350871720158059734871 := by
  unfold tailWord_90268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646172218490963696067729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2194896291321284928090305 1646172218490963696067729)
  ·
    refine ⟨1234629163868222772050797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1646172218490963696067729 1234629163868222772050797)
    ·
      refine ⟨462985936450583539519049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1234629163868222772050797 462985936450583539519049)
      ·
        refine ⟨347239452337937654639287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462985936450583539519049 347239452337937654639287)
        ·
          refine ⟨520859178506906481958931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347239452337937654639287 520859178506906481958931)
          ·
            refine ⟨781288767760359722938397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520859178506906481958931 781288767760359722938397)
            ·
              refine ⟨292983287910134896101899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 781288767760359722938397 292983287910134896101899)
              ·
                refine ⟨439474931865202344152849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292983287910134896101899 439474931865202344152849)
                ·
                  refine ⟨329606198898901758114637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439474931865202344152849 329606198898901758114637)
                  ·
                    refine ⟨123602324587088159292989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329606198898901758114637 123602324587088159292989)
                    ·
                      refine ⟨46350871720158059734871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123602324587088159292989 46350871720158059734871)
                      ·
                        rfl

theorem cell23_90268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_90268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90268 prefixEnd_90268 := by exact prefixLift 90268
  have htrace : WordTrace (prefixWord ++ tailWord_90268) baseStart_90268 baseEnd_90268 := by
    simpa [prefixWord, tailWord_90268, baseEnd_90268] using wordTrace_append hprefix tailTrace_90268
  have hstable : (prefixWord ++ tailWord_90268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90268).length < 2 ^ (prefixWord ++ tailWord_90268).sum := by decide
  have hdescent : baseEnd_90268 < baseStart_90268 := by decide
  rcases family_descends (prefixWord ++ tailWord_90268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90328 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_90328 : Nat := 118140960795 + 90328 * 2 ^ 59
def prefixEnd_90328 : Nat := 4983230072969 + 3 ^ 40 * 90328 * 2
def baseEnd_90328 : Nat := 46381680559427824984595

theorem tailTrace_90328 : CollatzResearch.WordTrace tailWord_90328 prefixEnd_90328 46381680559427824984595 := by
  unfold tailWord_90328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647266408382278819659819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2196355211176371759546425 1647266408382278819659819)
  ·
    refine ⟨2470899612573418229489729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647266408382278819659819 2470899612573418229489729)
    ·
      refine ⟨1853174709430063672117297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470899612573418229489729 1853174709430063672117297)
      ·
        refine ⟨1389881032072547754087973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853174709430063672117297 1389881032072547754087973)
        ·
          refine ⟨260602693513602703891495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1389881032072547754087973 260602693513602703891495)
          ·
            refine ⟨390904040270404055837243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260602693513602703891495 390904040270404055837243)
            ·
              refine ⟨586356060405606083755865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390904040270404055837243 586356060405606083755865)
              ·
                refine ⟨439767045304204562816899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586356060405606083755865 439767045304204562816899)
                ·
                  refine ⟨659650567956306844225349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439767045304204562816899 659650567956306844225349)
                  ·
                    refine ⟨123684481491807533292253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659650567956306844225349 123684481491807533292253)
                    ·
                      refine ⟨46381680559427824984595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123684481491807533292253 46381680559427824984595)
                      ·
                        rfl

theorem cell23_90328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_90328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90328 prefixEnd_90328 := by exact prefixLift 90328
  have htrace : WordTrace (prefixWord ++ tailWord_90328) baseStart_90328 baseEnd_90328 := by
    simpa [prefixWord, tailWord_90328, baseEnd_90328] using wordTrace_append hprefix tailTrace_90328
  have hstable : (prefixWord ++ tailWord_90328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90328).length < 2 ^ (prefixWord ++ tailWord_90328).sum := by decide
  have hdescent : baseEnd_90328 < baseStart_90328 := by decide
  rcases family_descends (prefixWord ++ tailWord_90328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90402 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_90402 : Nat := 118140960795 + 90402 * 2 ^ 59
def prefixEnd_90402 : Nat := 4983230072969 + 3 ^ 40 * 90402 * 2
def baseEnd_90402 : Nat := 46419678127860535459255

theorem tailTrace_90402 : CollatzResearch.WordTrace tailWord_90402 prefixEnd_90402 46419678127860535459255 := by
  unfold tailWord_90402
  simp only [CollatzResearch.WordTrace]
  refine ⟨824307954624117069378365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2198154545664312185008973 824307954624117069378365)
  ·
    refine ⟨309115482984043901016887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 824307954624117069378365 309115482984043901016887)
    ·
      refine ⟨463673224476065851525331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309115482984043901016887 463673224476065851525331)
      ·
        refine ⟨695509836714098777287997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463673224476065851525331 695509836714098777287997)
        ·
          refine ⟨260816188767787041482999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695509836714098777287997 260816188767787041482999)
          ·
            refine ⟨391224283151680562224499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260816188767787041482999 391224283151680562224499)
            ·
              refine ⟨586836424727520843336749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391224283151680562224499 586836424727520843336749)
              ·
                refine ⟨220063659272820316251281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586836424727520843336749 220063659272820316251281)
                ·
                  refine ⟨165047744454615237188461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220063659272820316251281 165047744454615237188461)
                  ·
                    refine ⟨61892904170480713945673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165047744454615237188461 61892904170480713945673)
                    ·
                      refine ⟨46419678127860535459255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61892904170480713945673 46419678127860535459255)
                      ·
                        rfl

theorem cell23_90402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_90402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90402 prefixEnd_90402 := by exact prefixLift 90402
  have htrace : WordTrace (prefixWord ++ tailWord_90402) baseStart_90402 baseEnd_90402 := by
    simpa [prefixWord, tailWord_90402, baseEnd_90402] using wordTrace_append hprefix tailTrace_90402
  have hstable : (prefixWord ++ tailWord_90402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90402).length < 2 ^ (prefixWord ++ tailWord_90402).sum := by decide
  have hdescent : baseEnd_90402 < baseStart_90402 := by decide
  rcases family_descends (prefixWord ++ tailWord_90402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90426 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3]
def baseStart_90426 : Nat := 118140960795 + 90426 * 2 ^ 59
def prefixEnd_90426 : Nat := 4983230072969 + 3 ^ 40 * 90426 * 2
def baseEnd_90426 : Nat := 46432001663568441559145

theorem tailTrace_90426 : CollatzResearch.WordTrace tailWord_90426 prefixEnd_90426 46432001663568441559145 := by
  unfold tailWord_90426
  simp only [CollatzResearch.WordTrace]
  refine ⟨824526792602380094096783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2198738113606346917591421 824526792602380094096783)
  ·
    refine ⟨1236790188903570141145175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 824526792602380094096783 1236790188903570141145175)
    ·
      refine ⟨1855185283355355211717763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236790188903570141145175 1855185283355355211717763)
      ·
        refine ⟨2782777925033032817576645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855185283355355211717763 2782777925033032817576645)
        ·
          refine ⟨521770860943693653295621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2782777925033032817576645 521770860943693653295621)
          ·
            refine ⟨97832036426942559992929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 521770860943693653295621 97832036426942559992929)
            ·
              refine ⟨73374027320206919994697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97832036426942559992929 73374027320206919994697)
              ·
                refine ⟨55030520490155189996023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73374027320206919994697 55030520490155189996023)
                ·
                  refine ⟨82545780735232784994035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55030520490155189996023 82545780735232784994035)
                  ·
                    refine ⟨123818671102849177491053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82545780735232784994035 123818671102849177491053)
                    ·
                      refine ⟨46432001663568441559145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123818671102849177491053 46432001663568441559145)
                      ·
                        rfl

theorem cell23_90426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_90426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90426 prefixEnd_90426 := by exact prefixLift 90426
  have htrace : WordTrace (prefixWord ++ tailWord_90426) baseStart_90426 baseEnd_90426 := by
    simpa [prefixWord, tailWord_90426, baseEnd_90426] using wordTrace_append hprefix tailTrace_90426
  have hstable : (prefixWord ++ tailWord_90426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90426).length < 2 ^ (prefixWord ++ tailWord_90426).sum := by decide
  have hdescent : baseEnd_90426 < baseStart_90426 := by decide
  rcases family_descends (prefixWord ++ tailWord_90426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90428 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_90428 : Nat := 118140960795 + 90428 * 2 ^ 59
def prefixEnd_90428 : Nat := 4983230072969 + 3 ^ 40 * 90428 * 2
def baseEnd_90428 : Nat := 46433028624877433734135

theorem tailTrace_90428 : CollatzResearch.WordTrace tailWord_90428 prefixEnd_90428 46433028624877433734135 := by
  unfold tailWord_90428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649090058201137358979969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2198786744268183145306625 1649090058201137358979969)
  ·
    refine ⟨1236817543650853019234977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1649090058201137358979969 1236817543650853019234977)
    ·
      refine ⟨927613157738139764426233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1236817543650853019234977 927613157738139764426233)
      ·
        refine ⟨695709868303604823319675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927613157738139764426233 695709868303604823319675)
        ·
          refine ⟨1043564802455407234979513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695709868303604823319675 1043564802455407234979513)
          ·
            refine ⟨782673601841555426234635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1043564802455407234979513 782673601841555426234635)
            ·
              refine ⟨1174010402762333139351953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782673601841555426234635 1174010402762333139351953)
              ·
                refine ⟨880507802071749854513965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174010402762333139351953 880507802071749854513965)
                ·
                  refine ⟨330190425776906195442737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880507802071749854513965 330190425776906195442737)
                  ·
                    refine ⟨247642819332679646582053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330190425776906195442737 247642819332679646582053)
                    ·
                      refine ⟨46433028624877433734135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 247642819332679646582053 46433028624877433734135)
                      ·
                        rfl

theorem cell23_90428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_90428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90428 prefixEnd_90428 := by exact prefixLift 90428
  have htrace : WordTrace (prefixWord ++ tailWord_90428) baseStart_90428 baseEnd_90428 := by
    simpa [prefixWord, tailWord_90428, baseEnd_90428] using wordTrace_append hprefix tailTrace_90428
  have hstable : (prefixWord ++ tailWord_90428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90428).length < 2 ^ (prefixWord ++ tailWord_90428).sum := by decide
  have hdescent : baseEnd_90428 < baseStart_90428 := by decide
  rcases family_descends (prefixWord ++ tailWord_90428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90466 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_90466 : Nat := 118140960795 + 90466 * 2 ^ 59
def prefixEnd_90466 : Nat := 4983230072969 + 3 ^ 40 * 90466 * 2
def baseEnd_90466 : Nat := 46452540889748285058961

theorem tailTrace_90466 : CollatzResearch.WordTrace tailWord_90466 prefixEnd_90466 46452540889748285058961 := by
  unfold tailWord_90466
  simp only [CollatzResearch.WordTrace]
  refine ⟨824891522566151801960813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2199710726843071471895501 824891522566151801960813)
  ·
    refine ⟨309334320962306925735305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 824891522566151801960813 309334320962306925735305)
    ·
      refine ⟨232000740721730194301479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309334320962306925735305 232000740721730194301479)
      ·
        refine ⟨348001111082595291452219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232000740721730194301479 348001111082595291452219)
        ·
          refine ⟨522001666623892937178329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348001111082595291452219 522001666623892937178329)
          ·
            refine ⟨391501249967919702883747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522001666623892937178329 391501249967919702883747)
            ·
              refine ⟨587251874951879554325621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391501249967919702883747 587251874951879554325621)
              ·
                refine ⟨55054863276738708218027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587251874951879554325621 55054863276738708218027)
                ·
                  refine ⟨82582294915108062327041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55054863276738708218027 82582294915108062327041)
                  ·
                    refine ⟨61936721186331046745281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82582294915108062327041 61936721186331046745281)
                    ·
                      refine ⟨46452540889748285058961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61936721186331046745281 46452540889748285058961)
                      ·
                        rfl

theorem cell23_90466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_90466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90466 prefixEnd_90466 := by exact prefixLift 90466
  have htrace : WordTrace (prefixWord ++ tailWord_90466) baseStart_90466 baseEnd_90466 := by
    simpa [prefixWord, tailWord_90466, baseEnd_90466] using wordTrace_append hprefix tailTrace_90466
  have hstable : (prefixWord ++ tailWord_90466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90466).length < 2 ^ (prefixWord ++ tailWord_90466).sum := by decide
  have hdescent : baseEnd_90466 < baseStart_90466 := by decide
  rcases family_descends (prefixWord ++ tailWord_90466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90469 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_90469 : Nat := 118140960795 + 90469 * 2 ^ 59
def prefixEnd_90469 : Nat := 4983230072969 + 3 ^ 40 * 90469 * 2
def baseEnd_90469 : Nat := 46454081331711773321447

theorem tailTrace_90469 : CollatzResearch.WordTrace tailWord_90469 prefixEnd_90469 46454081331711773321447 := by
  unfold tailWord_90469
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299675509253738720202461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2199783672835825813468307 3299675509253738720202461)
  ·
    refine ⟨1237378315970152020075923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3299675509253738720202461 1237378315970152020075923)
    ·
      refine ⟨1856067473955228030113885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1237378315970152020075923 1856067473955228030113885)
      ·
        refine ⟨696025302733210511292707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1856067473955228030113885 696025302733210511292707)
        ·
          refine ⟨1044037954099815766939061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696025302733210511292707 1044037954099815766939061)
          ·
            refine ⟨97878558196857728150537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1044037954099815766939061 97878558196857728150537)
            ·
              refine ⟨73408918647643296112903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97878558196857728150537 73408918647643296112903)
              ·
                refine ⟨110113377971464944169355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73408918647643296112903 110113377971464944169355)
                ·
                  refine ⟨165170066957197416254033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110113377971464944169355 165170066957197416254033)
                  ·
                    refine ⟨123877550217898062190525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165170066957197416254033 123877550217898062190525)
                    ·
                      refine ⟨46454081331711773321447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123877550217898062190525 46454081331711773321447)
                      ·
                        rfl

theorem cell23_90469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_90469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90469 prefixEnd_90469 := by exact prefixLift 90469
  have htrace : WordTrace (prefixWord ++ tailWord_90469) baseStart_90469 baseEnd_90469 := by
    simpa [prefixWord, tailWord_90469, baseEnd_90469] using wordTrace_append hprefix tailTrace_90469
  have hstable : (prefixWord ++ tailWord_90469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90469).length < 2 ^ (prefixWord ++ tailWord_90469).sum := by decide
  have hdescent : baseEnd_90469 < baseStart_90469 := by decide
  rcases family_descends (prefixWord ++ tailWord_90469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90482 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_90482 : Nat := 118140960795 + 90482 * 2 ^ 59
def prefixEnd_90482 : Nat := 4983230072969 + 3 ^ 40 * 90482 * 2
def baseEnd_90482 : Nat := 46460756580220222458887

theorem tailTrace_90482 : CollatzResearch.WordTrace tailWord_90482 prefixEnd_90482 46460756580220222458887 := by
  unfold tailWord_90482
  simp only [CollatzResearch.WordTrace]
  refine ⟨825037414551660485106425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2200099772137761293617133 825037414551660485106425)
  ·
    refine ⟨618778060913745363829819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 825037414551660485106425 618778060913745363829819)
    ·
      refine ⟨928167091370618045744729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618778060913745363829819 928167091370618045744729)
      ·
        refine ⟨696125318527963534308547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928167091370618045744729 696125318527963534308547)
        ·
          refine ⟨1044187977791945301462821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696125318527963534308547 1044187977791945301462821)
          ·
            refine ⟨195785245835989744024279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1044187977791945301462821 195785245835989744024279)
            ·
              refine ⟨293677868753984616036419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195785245835989744024279 293677868753984616036419)
              ·
                refine ⟨440516803130976924054629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293677868753984616036419 440516803130976924054629)
                ·
                  refine ⟨82596900587058173260243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440516803130976924054629 82596900587058173260243)
                  ·
                    refine ⟨123895350880587259890365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82596900587058173260243 123895350880587259890365)
                    ·
                      refine ⟨46460756580220222458887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123895350880587259890365 46460756580220222458887)
                      ·
                        rfl

theorem cell23_90482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_90482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90482 prefixEnd_90482 := by exact prefixLift 90482
  have htrace : WordTrace (prefixWord ++ tailWord_90482) baseStart_90482 baseEnd_90482 := by
    simpa [prefixWord, tailWord_90482, baseEnd_90482] using wordTrace_append hprefix tailTrace_90482
  have hstable : (prefixWord ++ tailWord_90482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90482).length < 2 ^ (prefixWord ++ tailWord_90482).sum := by decide
  have hdescent : baseEnd_90482 < baseStart_90482 := by decide
  rcases family_descends (prefixWord ++ tailWord_90482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90499 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 1, 3, 3]
def baseStart_90499 : Nat := 118140960795 + 90499 * 2 ^ 59
def prefixEnd_90499 : Nat := 4983230072969 + 3 ^ 40 * 90499 * 2
def baseEnd_90499 : Nat := 46469485751346655946309

theorem tailTrace_90499 : CollatzResearch.WordTrace tailWord_90499 prefixEnd_90499 46469485751346655946309 := by
  unfold tailWord_90499
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300769699145053843794551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2200513132763369229196367 3300769699145053843794551)
  ·
    refine ⟨4951154548717580765691827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300769699145053843794551 4951154548717580765691827)
    ·
      refine ⟨7426731823076371148537741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951154548717580765691827 7426731823076371148537741)
      ·
        refine ⟨2785024433653639180701653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7426731823076371148537741 2785024433653639180701653)
        ·
          refine ⟨65274010163757168297695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2785024433653639180701653 65274010163757168297695)
          ·
            refine ⟨97911015245635752446543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65274010163757168297695 97911015245635752446543)
            ·
              refine ⟨146866522868453628669815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97911015245635752446543 146866522868453628669815)
              ·
                refine ⟨220299784302680443004723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146866522868453628669815 220299784302680443004723)
                ·
                  refine ⟨330449676454020664507085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220299784302680443004723 330449676454020664507085)
                  ·
                    refine ⟨123918628670257749190157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330449676454020664507085 123918628670257749190157)
                    ·
                      refine ⟨46469485751346655946309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 123918628670257749190157 46469485751346655946309)
                      ·
                        rfl

theorem cell23_90499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_90499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90499 prefixEnd_90499 := by exact prefixLift 90499
  have htrace : WordTrace (prefixWord ++ tailWord_90499) baseStart_90499 baseEnd_90499 := by
    simpa [prefixWord, tailWord_90499, baseEnd_90499] using wordTrace_append hprefix tailTrace_90499
  have hstable : (prefixWord ++ tailWord_90499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90499).length < 2 ^ (prefixWord ++ tailWord_90499).sum := by decide
  have hdescent : baseEnd_90499 < baseStart_90499 := by decide
  rcases family_descends (prefixWord ++ tailWord_90499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90526 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_90526 : Nat := 118140960795 + 90526 * 2 ^ 59
def prefixEnd_90526 : Nat := 4983230072969 + 3 ^ 40 * 90526 * 2
def baseEnd_90526 : Nat := 46483349729018050308685

theorem tailTrace_90526 : CollatzResearch.WordTrace tailWord_90526 prefixEnd_90526 46483349729018050308685 := by
  unfold tailWord_90526
  simp only [CollatzResearch.WordTrace]
  refine ⟨412719308755904681878429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2201169646698158303351621 412719308755904681878429)
  ·
    refine ⟨154769740783464255704411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 412719308755904681878429 154769740783464255704411)
    ·
      refine ⟨232154611175196383556617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154769740783464255704411 232154611175196383556617)
      ·
        refine ⟨174115958381397287667463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232154611175196383556617 174115958381397287667463)
        ·
          refine ⟨261173937572095931501195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174115958381397287667463 261173937572095931501195)
          ·
            refine ⟨391760906358143897251793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261173937572095931501195 391760906358143897251793)
            ·
              refine ⟨293820679768607922938845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391760906358143897251793 293820679768607922938845)
              ·
                refine ⟨110182754913227971102067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293820679768607922938845 110182754913227971102067)
                ·
                  refine ⟨165274132369841956653101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110182754913227971102067 165274132369841956653101)
                  ·
                    refine ⟨61977799638690733744913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165274132369841956653101 61977799638690733744913)
                    ·
                      refine ⟨46483349729018050308685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61977799638690733744913 46483349729018050308685)
                      ·
                        rfl

theorem cell23_90526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_90526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90526 prefixEnd_90526 := by exact prefixLift 90526
  have htrace : WordTrace (prefixWord ++ tailWord_90526) baseStart_90526 baseEnd_90526 := by
    simpa [prefixWord, tailWord_90526, baseEnd_90526] using wordTrace_append hprefix tailTrace_90526
  have hstable : (prefixWord ++ tailWord_90526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90526).length < 2 ^ (prefixWord ++ tailWord_90526).sum := by decide
  have hdescent : baseEnd_90526 < baseStart_90526 := by decide
  rcases family_descends (prefixWord ++ tailWord_90526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90545 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 7]
def baseStart_90545 : Nat := 118140960795 + 90545 * 2 ^ 59
def prefixEnd_90545 : Nat := 4983230072969 + 3 ^ 40 * 90545 * 2
def baseEnd_90545 : Nat := 5165900651272608441233

theorem tailTrace_90545 : CollatzResearch.WordTrace tailWord_90545 prefixEnd_90545 5165900651272608441233 := by
  unfold tailWord_90545
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302447456978403699969089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2201631637985602466646059 3302447456978403699969089)
  ·
    refine ⟨2476835592733802774976817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3302447456978403699969089 2476835592733802774976817)
    ·
      refine ⟨1857626694550352081232613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2476835592733802774976817 1857626694550352081232613)
      ·
        refine ⟨348305005228191015231115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1857626694550352081232613 348305005228191015231115)
        ·
          refine ⟨522457507842286522846673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348305005228191015231115 522457507842286522846673)
          ·
            refine ⟨391843130881714892135005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522457507842286522846673 391843130881714892135005)
            ·
              refine ⟨146941174080643084550627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 391843130881714892135005 146941174080643084550627)
              ·
                refine ⟨220411761120964626825941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146941174080643084550627 220411761120964626825941)
                ·
                  refine ⟨5165900651272608441233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220411761120964626825941 5165900651272608441233)
                  ·
                    rfl

theorem cell23_90545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_90545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90545 prefixEnd_90545 := by exact prefixLift 90545
  have htrace : WordTrace (prefixWord ++ tailWord_90545) baseStart_90545 baseEnd_90545 := by
    simpa [prefixWord, tailWord_90545, baseEnd_90545] using wordTrace_append hprefix tailTrace_90545
  have hstable : (prefixWord ++ tailWord_90545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90545).length < 2 ^ (prefixWord ++ tailWord_90545).sum := by decide
  have hdescent : baseEnd_90545 < baseStart_90545 := by decide
  rcases family_descends (prefixWord ++ tailWord_90545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90556 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_90556 : Nat := 118140960795 + 90556 * 2 ^ 59
def prefixEnd_90556 : Nat := 4983230072969 + 3 ^ 40 * 90556 * 2
def baseEnd_90556 : Nat := 46498754148652932933547

theorem tailTrace_90556 : CollatzResearch.WordTrace tailWord_90556 prefixEnd_90556 46498754148652932933547 := by
  unfold tailWord_90556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651424329969276289309761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2201899106625701719079681 1651424329969276289309761)
  ·
    refine ⟨1238568247476957216982321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1651424329969276289309761 1238568247476957216982321)
    ·
      refine ⟨928926185607717912736741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1238568247476957216982321 928926185607717912736741)
      ·
        refine ⟨174173659801447108638139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 928926185607717912736741 174173659801447108638139)
        ·
          refine ⟨261260489702170662957209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174173659801447108638139 261260489702170662957209)
          ·
            refine ⟨195945367276627997217907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261260489702170662957209 195945367276627997217907)
            ·
              refine ⟨293918050914941995826861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195945367276627997217907 293918050914941995826861)
              ·
                refine ⟨110219269093103248435073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293918050914941995826861 110219269093103248435073)
                ·
                  refine ⟨82664451819827436326305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110219269093103248435073 82664451819827436326305)
                  ·
                    refine ⟨61998338864870577244729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82664451819827436326305 61998338864870577244729)
                    ·
                      refine ⟨46498754148652932933547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 61998338864870577244729 46498754148652932933547)
                      ·
                        rfl

theorem cell23_90556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_90556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90556 prefixEnd_90556 := by exact prefixLift 90556
  have htrace : WordTrace (prefixWord ++ tailWord_90556) baseStart_90556 baseEnd_90556 := by
    simpa [prefixWord, tailWord_90556, baseEnd_90556] using wordTrace_append hprefix tailTrace_90556
  have hstable : (prefixWord ++ tailWord_90556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90556).length < 2 ^ (prefixWord ++ tailWord_90556).sum := by decide
  have hdescent : baseEnd_90556 < baseStart_90556 := by decide
  rcases family_descends (prefixWord ++ tailWord_90556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90626 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_90626 : Nat := 118140960795 + 90626 * 2 ^ 59
def prefixEnd_90626 : Nat := 4983230072969 + 3 ^ 40 * 90626 * 2
def baseEnd_90626 : Nat := 15511565931489219686075

theorem tailTrace_90626 : CollatzResearch.WordTrace tailWord_90626 prefixEnd_90626 15511565931489219686075 := by
  unfold tailWord_90626
  simp only [CollatzResearch.WordTrace]
  refine ⟨826350442421238633416933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2203601179789969689111821 826350442421238633416933)
  ·
    refine ⟨154940707953982243765675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 826350442421238633416933 154940707953982243765675)
    ·
      refine ⟨232411061930973365648513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154940707953982243765675 232411061930973365648513)
      ·
        refine ⟨174308296448230024236385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232411061930973365648513 174308296448230024236385)
        ·
          refine ⟨130731222336172518177289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174308296448230024236385 130731222336172518177289)
          ·
            refine ⟨98048416752129388632967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130731222336172518177289 98048416752129388632967)
            ·
              refine ⟨147072625128194082949451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98048416752129388632967 147072625128194082949451)
              ·
                refine ⟨220608937692291124424177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147072625128194082949451 220608937692291124424177)
                ·
                  refine ⟨165456703269218343318133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220608937692291124424177 165456703269218343318133)
                  ·
                    refine ⟨15511565931489219686075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165456703269218343318133 15511565931489219686075)
                    ·
                      rfl

theorem cell23_90626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_90626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90626 prefixEnd_90626 := by exact prefixLift 90626
  have htrace : WordTrace (prefixWord ++ tailWord_90626) baseStart_90626 baseEnd_90626 := by
    simpa [prefixWord, tailWord_90626, baseEnd_90626] using wordTrace_append hprefix tailTrace_90626
  have hstable : (prefixWord ++ tailWord_90626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90626).length < 2 ^ (prefixWord ++ tailWord_90626).sum := by decide
  have hdescent : baseEnd_90626 < baseStart_90626 := by decide
  rcases family_descends (prefixWord ++ tailWord_90626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90652 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 6]
def baseStart_90652 : Nat := 118140960795 + 90652 * 2 ^ 59
def prefixEnd_90652 : Nat := 4983230072969 + 3 ^ 40 * 90652 * 2
def baseEnd_90652 : Nat := 5172005365720506370345

theorem tailTrace_90652 : CollatzResearch.WordTrace tailWord_90652 prefixEnd_90652 5172005365720506370345 := by
  unfold tailWord_90652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653175033795380487057105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2204233378393840649409473 1653175033795380487057105)
  ·
    refine ⟨1239881275346535365292829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1653175033795380487057105 1239881275346535365292829)
    ·
      refine ⟨464955478254950761984811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1239881275346535365292829 464955478254950761984811)
      ·
        refine ⟨697433217382426142977217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464955478254950761984811 697433217382426142977217)
        ·
          refine ⟨523074913036819607232913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697433217382426142977217 523074913036819607232913)
          ·
            refine ⟨392306184777614705424685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523074913036819607232913 392306184777614705424685)
            ·
              refine ⟨147114819291605514534257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392306184777614705424685 147114819291605514534257)
              ·
                refine ⟨110336114468704135900693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147114819291605514534257 110336114468704135900693)
                ·
                  refine ⟨5172005365720506370345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110336114468704135900693 5172005365720506370345)
                  ·
                    rfl

theorem cell23_90652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_90652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90652 prefixEnd_90652 := by exact prefixLift 90652
  have htrace : WordTrace (prefixWord ++ tailWord_90652) baseStart_90652 baseEnd_90652 := by
    simpa [prefixWord, tailWord_90652, baseEnd_90652] using wordTrace_append hprefix tailTrace_90652
  have hstable : (prefixWord ++ tailWord_90652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90652).length < 2 ^ (prefixWord ++ tailWord_90652).sum := by decide
  have hdescent : baseEnd_90652 < baseStart_90652 := by decide
  rcases family_descends (prefixWord ++ tailWord_90652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90672 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2]
def baseStart_90672 : Nat := 118140960795 + 90672 * 2 ^ 59
def prefixEnd_90672 : Nat := 4983230072969 + 3 ^ 40 * 90672 * 2
def baseEnd_90672 : Nat := 46558317904574479083013

theorem tailTrace_90672 : CollatzResearch.WordTrace tailWord_90672 prefixEnd_90672 46558317904574479083013 := by
  unfold tailWord_90672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653539763759152194921135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2204719685012202926561513 1653539763759152194921135)
  ·
    refine ⟨2480309645638728292381703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653539763759152194921135 2480309645638728292381703)
    ·
      refine ⟨3720464468458092438572555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2480309645638728292381703 3720464468458092438572555)
      ·
        refine ⟨5580696702687138657858833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720464468458092438572555 5580696702687138657858833)
        ·
          refine ⟨4185522527015353993394125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5580696702687138657858833 4185522527015353993394125)
          ·
            refine ⟨1569570947630757747522797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4185522527015353993394125 1569570947630757747522797)
            ·
              refine ⟨588589105361534155321049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569570947630757747522797 588589105361534155321049)
              ·
                refine ⟨441441829021150616490787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588589105361534155321049 441441829021150616490787)
                ·
                  refine ⟨662162743531725924736181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441441829021150616490787 662162743531725924736181)
                  ·
                    refine ⟨62077757206099305444017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662162743531725924736181 62077757206099305444017)
                    ·
                      refine ⟨46558317904574479083013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62077757206099305444017 46558317904574479083013)
                      ·
                        rfl

theorem cell23_90672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 5, 2].length) (baseStart_90672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90672 prefixEnd_90672 := by exact prefixLift 90672
  have htrace : WordTrace (prefixWord ++ tailWord_90672) baseStart_90672 baseEnd_90672 := by
    simpa [prefixWord, tailWord_90672, baseEnd_90672] using wordTrace_append hprefix tailTrace_90672
  have hstable : (prefixWord ++ tailWord_90672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90672).length < 2 ^ (prefixWord ++ tailWord_90672).sum := by decide
  have hdescent : baseEnd_90672 < baseStart_90672 := by decide
  rcases family_descends (prefixWord ++ tailWord_90672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90682 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_90682 : Nat := 118140960795 + 90682 * 2 ^ 59
def prefixEnd_90682 : Nat := 4983230072969 + 3 ^ 40 * 90682 * 2
def baseEnd_90682 : Nat := 15521150903706479985989

theorem tailTrace_90682 : CollatzResearch.WordTrace tailWord_90682 prefixEnd_90682 15521150903706479985989 := by
  unfold tailWord_90682
  simp only [CollatzResearch.WordTrace]
  refine ⟨826861064370519024426575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2204962838321384065137533 826861064370519024426575)
  ·
    refine ⟨1240291596555778536639863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826861064370519024426575 1240291596555778536639863)
    ·
      refine ⟨1860437394833667804959795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240291596555778536639863 1860437394833667804959795)
      ·
        refine ⟨2790656092250501707439693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1860437394833667804959795 2790656092250501707439693)
        ·
          refine ⟨1046496034593938140289885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2790656092250501707439693 1046496034593938140289885)
          ·
            refine ⟨392436012972726802608707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1046496034593938140289885 392436012972726802608707)
            ·
              refine ⟨588654019459090203913061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392436012972726802608707 588654019459090203913061)
              ·
                refine ⟨110372628648579413233699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588654019459090203913061 110372628648579413233699)
                ·
                  refine ⟨165558942972869119850549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110372628648579413233699 165558942972869119850549)
                  ·
                    refine ⟨15521150903706479985989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165558942972869119850549 15521150903706479985989)
                    ·
                      rfl

theorem cell23_90682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_90682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90682 prefixEnd_90682 := by exact prefixLift 90682
  have htrace : WordTrace (prefixWord ++ tailWord_90682) baseStart_90682 baseEnd_90682 := by
    simpa [prefixWord, tailWord_90682, baseEnd_90682] using wordTrace_append hprefix tailTrace_90682
  have hstable : (prefixWord ++ tailWord_90682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90682).length < 2 ^ (prefixWord ++ tailWord_90682).sum := by decide
  have hdescent : baseEnd_90682 < baseStart_90682 := by decide
  rcases family_descends (prefixWord ++ tailWord_90682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90689 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_90689 : Nat := 118140960795 + 90689 * 2 ^ 59
def prefixEnd_90689 : Nat := 4983230072969 + 3 ^ 40 * 90689 * 2
def baseEnd_90689 : Nat := 46567047075700912570435

theorem tailTrace_90689 : CollatzResearch.WordTrace tailWord_90689 prefixEnd_90689 46567047075700912570435 := by
  unfold tailWord_90689
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307699568456716293211121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2205133045637810862140747 3307699568456716293211121)
  ·
    refine ⟨2480774676342537219908341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3307699568456716293211121 2480774676342537219908341)
    ·
      refine ⟨232572625907112864366407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2480774676342537219908341 232572625907112864366407)
      ·
        refine ⟨348858938860669296549611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232572625907112864366407 348858938860669296549611)
        ·
          refine ⟨523288408291003944824417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348858938860669296549611 523288408291003944824417)
          ·
            refine ⟨392466306218252958618313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523288408291003944824417 392466306218252958618313)
            ·
              refine ⟨294349729663689718963735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392466306218252958618313 294349729663689718963735)
              ·
                refine ⟨441524594495534578445603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294349729663689718963735 441524594495534578445603)
                ·
                  refine ⟨662286891743301867668405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441524594495534578445603 662286891743301867668405)
                  ·
                    refine ⟨62089396100934550093913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 662286891743301867668405 62089396100934550093913)
                    ·
                      refine ⟨46567047075700912570435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62089396100934550093913 46567047075700912570435)
                      ·
                        rfl

theorem cell23_90689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_90689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90689 prefixEnd_90689 := by exact prefixLift 90689
  have htrace : WordTrace (prefixWord ++ tailWord_90689) baseStart_90689 baseEnd_90689 := by
    simpa [prefixWord, tailWord_90689, baseEnd_90689] using wordTrace_append hprefix tailTrace_90689
  have hstable : (prefixWord ++ tailWord_90689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90689).length < 2 ^ (prefixWord ++ tailWord_90689).sum := by decide
  have hdescent : baseEnd_90689 < baseStart_90689 := by decide
  rcases family_descends (prefixWord ++ tailWord_90689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90712 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_90712 : Nat := 118140960795 + 90712 * 2 ^ 59
def prefixEnd_90712 : Nat := 4983230072969 + 3 ^ 40 * 90712 * 2
def baseEnd_90712 : Nat := 15526285710251440860943

theorem tailTrace_90712 : CollatzResearch.WordTrace tailWord_90712 prefixEnd_90712 15526285710251440860943 := by
  unfold tailWord_90712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654269223686695610649195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2205692298248927480865593 1654269223686695610649195)
  ·
    refine ⟨2481403835530043415973793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654269223686695610649195 2481403835530043415973793)
    ·
      refine ⟨1861052876647532561980345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2481403835530043415973793 1861052876647532561980345)
      ·
        refine ⟨1395789657485649421485259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1861052876647532561980345 1395789657485649421485259)
        ·
          refine ⟨2093684486228474132227889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395789657485649421485259 2093684486228474132227889)
          ·
            refine ⟨1570263364671355599170917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2093684486228474132227889 1570263364671355599170917)
            ·
              refine ⟨294424380875879174844547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1570263364671355599170917 294424380875879174844547)
              ·
                refine ⟨441636571313818762266821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294424380875879174844547 441636571313818762266821)
                ·
                  refine ⟨82806857121341017925029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441636571313818762266821 82806857121341017925029)
                  ·
                    refine ⟨15526285710251440860943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82806857121341017925029 15526285710251440860943)
                    ·
                      rfl

theorem cell23_90712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_90712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90712 prefixEnd_90712 := by exact prefixLift 90712
  have htrace : WordTrace (prefixWord ++ tailWord_90712) baseStart_90712 baseEnd_90712 := by
    simpa [prefixWord, tailWord_90712, baseEnd_90712] using wordTrace_append hprefix tailTrace_90712
  have hstable : (prefixWord ++ tailWord_90712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90712).length < 2 ^ (prefixWord ++ tailWord_90712).sum := by decide
  have hdescent : baseEnd_90712 < baseStart_90712 := by decide
  rcases family_descends (prefixWord ++ tailWord_90712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90736 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_90736 : Nat := 118140960795 + 90736 * 2 ^ 59
def prefixEnd_90736 : Nat := 4983230072969 + 3 ^ 40 * 90736 * 2
def baseEnd_90736 : Nat := 46591180666462228682719

theorem tailTrace_90736 : CollatzResearch.WordTrace tailWord_90736 prefixEnd_90736 46591180666462228682719 := by
  unfold tailWord_90736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654706899643221660086031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2206275866190962213448041 1654706899643221660086031)
  ·
    refine ⟨2482060349464832490129047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654706899643221660086031 2482060349464832490129047)
    ·
      refine ⟨3723090524197248735193571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482060349464832490129047 3723090524197248735193571)
      ·
        refine ⟨5584635786295873102790357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3723090524197248735193571 5584635786295873102790357)
        ·
          refine ⟨130889901241309525846649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5584635786295873102790357 130889901241309525846649)
          ·
            refine ⟨98167425930982144384987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130889901241309525846649 98167425930982144384987)
            ·
              refine ⟨147251138896473216577481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98167425930982144384987 147251138896473216577481)
              ·
                refine ⟨110438354172354912433111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147251138896473216577481 110438354172354912433111)
                ·
                  refine ⟨165657531258532368649667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110438354172354912433111 165657531258532368649667)
                  ·
                    refine ⟨248486296887798552974501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165657531258532368649667 248486296887798552974501)
                    ·
                      refine ⟨46591180666462228682719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 248486296887798552974501 46591180666462228682719)
                      ·
                        rfl

theorem cell23_90736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_90736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90736 prefixEnd_90736 := by exact prefixLift 90736
  have htrace : WordTrace (prefixWord ++ tailWord_90736) baseStart_90736 baseEnd_90736 := by
    simpa [prefixWord, tailWord_90736, baseEnd_90736] using wordTrace_append hprefix tailTrace_90736
  have hstable : (prefixWord ++ tailWord_90736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90736).length < 2 ^ (prefixWord ++ tailWord_90736).sum := by decide
  have hdescent : baseEnd_90736 < baseStart_90736 := by decide
  rcases family_descends (prefixWord ++ tailWord_90736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90749 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_90749 : Nat := 118140960795 + 90749 * 2 ^ 59
def prefixEnd_90749 : Nat := 4983230072969 + 3 ^ 40 * 90749 * 2
def baseEnd_90749 : Nat := 46597855914970677820159

theorem tailTrace_90749 : CollatzResearch.WordTrace tailWord_90749 prefixEnd_90749 46597855914970677820159 := by
  unfold tailWord_90749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309887948239346540395301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2206591965492897693596867 3309887948239346540395301)
  ·
    refine ⟨620603990294877476324119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3309887948239346540395301 620603990294877476324119)
    ·
      refine ⟨930905985442316214486179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620603990294877476324119 930905985442316214486179)
      ·
        refine ⟨1396358978163474321729269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930905985442316214486179 1396358978163474321729269)
        ·
          refine ⟨130908654202825717662119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1396358978163474321729269 130908654202825717662119)
          ·
            refine ⟨196362981304238576493179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130908654202825717662119 196362981304238576493179)
            ·
              refine ⟨294544471956357864739769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196362981304238576493179 294544471956357864739769)
              ·
                refine ⟨220908353967268398554827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294544471956357864739769 220908353967268398554827)
                ·
                  refine ⟨331362530950902597832241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220908353967268398554827 331362530950902597832241)
                  ·
                    refine ⟨248521898213176948374181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 331362530950902597832241 248521898213176948374181)
                    ·
                      refine ⟨46597855914970677820159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 248521898213176948374181 46597855914970677820159)
                      ·
                        rfl

theorem cell23_90749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_90749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90749 prefixEnd_90749 := by exact prefixLift 90749
  have htrace : WordTrace (prefixWord ++ tailWord_90749) baseStart_90749 baseEnd_90749 := by
    simpa [prefixWord, tailWord_90749, baseEnd_90749] using wordTrace_append hprefix tailTrace_90749
  have hstable : (prefixWord ++ tailWord_90749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90749).length < 2 ^ (prefixWord ++ tailWord_90749).sum := by decide
  have hdescent : baseEnd_90749 < baseStart_90749 := by decide
  rcases family_descends (prefixWord ++ tailWord_90749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90752 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_90752 : Nat := 118140960795 + 90752 * 2 ^ 59
def prefixEnd_90752 : Nat := 4983230072969 + 3 ^ 40 * 90752 * 2
def baseEnd_90752 : Nat := 46599396356934166082645

theorem tailTrace_90752 : CollatzResearch.WordTrace tailWord_90752 prefixEnd_90752 46599396356934166082645 := by
  unfold tailWord_90752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654998683614239026377255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2206664911485652035169673 1654998683614239026377255)
  ·
    refine ⟨2482498025421358539565883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654998683614239026377255 2482498025421358539565883)
    ·
      refine ⟨3723747038132037809348825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482498025421358539565883 3723747038132037809348825)
      ·
        refine ⟨2792810278599028357011619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3723747038132037809348825 2792810278599028357011619)
        ·
          refine ⟨4189215417898542535517429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792810278599028357011619 4189215417898542535517429)
          ·
            refine ⟨392738945427988362704759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4189215417898542535517429 392738945427988362704759)
            ·
              refine ⟨589108418141982544057139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392738945427988362704759 589108418141982544057139)
              ·
                refine ⟨883662627212973816085709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589108418141982544057139 883662627212973816085709)
                ·
                  refine ⟨331373485204865181032141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883662627212973816085709 331373485204865181032141)
                  ·
                    refine ⟨124265056951824442887053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331373485204865181032141 124265056951824442887053)
                    ·
                      refine ⟨46599396356934166082645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 124265056951824442887053 46599396356934166082645)
                      ·
                        rfl

theorem cell23_90752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_90752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90752 prefixEnd_90752 := by exact prefixLift 90752
  have htrace : WordTrace (prefixWord ++ tailWord_90752) baseStart_90752 baseEnd_90752 := by
    simpa [prefixWord, tailWord_90752, baseEnd_90752] using wordTrace_append hprefix tailTrace_90752
  have hstable : (prefixWord ++ tailWord_90752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90752).length < 2 ^ (prefixWord ++ tailWord_90752).sum := by decide
  have hdescent : baseEnd_90752 < baseStart_90752 := by decide
  rcases family_descends (prefixWord ++ tailWord_90752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90753 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_90753 : Nat := 118140960795 + 90753 * 2 ^ 59
def prefixEnd_90753 : Nat := 4983230072969 + 3 ^ 40 * 90753 * 2
def baseEnd_90753 : Nat := 46599909837588662170141

theorem tailTrace_90753 : CollatzResearch.WordTrace tailWord_90753 prefixEnd_90753 46599909837588662170141 := by
  unfold tailWord_90753
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310033840224855223540913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2206689226816570149027275 3310033840224855223540913)
  ·
    refine ⟨2482525380168641417655685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3310033840224855223540913 2482525380168641417655685)
    ·
      refine ⟨465473508781620265810441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2482525380168641417655685 465473508781620265810441)
      ·
        refine ⟨349105131586215199357831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465473508781620265810441 349105131586215199357831)
        ·
          refine ⟨523657697379322799036747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349105131586215199357831 523657697379322799036747)
          ·
            refine ⟨785486546068984198555121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523657697379322799036747 785486546068984198555121)
            ·
              refine ⟨589114909551738148916341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785486546068984198555121 589114909551738148916341)
              ·
                refine ⟨55229522770475451460907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 589114909551738148916341 55229522770475451460907)
                ·
                  refine ⟨82844284155713177191361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55229522770475451460907 82844284155713177191361)
                  ·
                    refine ⟨62133213116784882893521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82844284155713177191361 62133213116784882893521)
                    ·
                      refine ⟨46599909837588662170141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62133213116784882893521 46599909837588662170141)
                      ·
                        rfl

theorem cell23_90753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_90753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90753 prefixEnd_90753 := by exact prefixLift 90753
  have htrace : WordTrace (prefixWord ++ tailWord_90753) baseStart_90753 baseEnd_90753 := by
    simpa [prefixWord, tailWord_90753, baseEnd_90753] using wordTrace_append hprefix tailTrace_90753
  have hstable : (prefixWord ++ tailWord_90753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90753).length < 2 ^ (prefixWord ++ tailWord_90753).sum := by decide
  have hdescent : baseEnd_90753 < baseStart_90753 := by decide
  rcases family_descends (prefixWord ++ tailWord_90753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90770 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_90770 : Nat := 118140960795 + 90770 * 2 ^ 59
def prefixEnd_90770 : Nat := 4983230072969 + 3 ^ 40 * 90770 * 2
def baseEnd_90770 : Nat := 46608639008715095657563

theorem tailTrace_90770 : CollatzResearch.WordTrace tailWord_90770 prefixEnd_90770 46608639008715095657563 := by
  unfold tailWord_90770
  simp only [CollatzResearch.WordTrace]
  refine ⟨827663470290816781727441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2207102587442178084606509 827663470290816781727441)
  ·
    refine ⟨620747602718112586295581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 827663470290816781727441 620747602718112586295581)
    ·
      refine ⟨232780351019292219860843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 620747602718112586295581 232780351019292219860843)
      ·
        refine ⟨349170526528938329791265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232780351019292219860843 349170526528938329791265)
        ·
          refine ⟨261877894896703747343449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349170526528938329791265 261877894896703747343449)
          ·
            refine ⟨196408421172527810507587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261877894896703747343449 196408421172527810507587)
            ·
              refine ⟨294612631758791715761381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196408421172527810507587 294612631758791715761381)
              ·
                refine ⟨55239868454773446705259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294612631758791715761381 55239868454773446705259)
                ·
                  refine ⟨82859802682160170057889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55239868454773446705259 82859802682160170057889)
                  ·
                    refine ⟨62144852011620127543417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82859802682160170057889 62144852011620127543417)
                    ·
                      refine ⟨46608639008715095657563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62144852011620127543417 46608639008715095657563)
                      ·
                        rfl

theorem cell23_90770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_90770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90770 prefixEnd_90770 := by exact prefixLift 90770
  have htrace : WordTrace (prefixWord ++ tailWord_90770) baseStart_90770 baseEnd_90770 := by
    simpa [prefixWord, tailWord_90770, baseEnd_90770] using wordTrace_append hprefix tailTrace_90770
  have hstable : (prefixWord ++ tailWord_90770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90770).length < 2 ^ (prefixWord ++ tailWord_90770).sum := by decide
  have hdescent : baseEnd_90770 < baseStart_90770 := by decide
  rcases family_descends (prefixWord ++ tailWord_90770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90812 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_90812 : Nat := 118140960795 + 90812 * 2 ^ 59
def prefixEnd_90812 : Nat := 4983230072969 + 3 ^ 40 * 90812 * 2
def baseEnd_90812 : Nat := 46630205196203931332369

theorem tailTrace_90812 : CollatzResearch.WordTrace tailWord_90812 prefixEnd_90812 46630205196203931332369 := by
  unfold tailWord_90812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656092873505554149969345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2208123831340738866625793 1656092873505554149969345)
  ·
    refine ⟨1242069655129165612477009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1656092873505554149969345 1242069655129165612477009)
    ·
      refine ⟨931552241346874209357757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1242069655129165612477009 931552241346874209357757)
      ·
        refine ⟨349332090505077828509159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 931552241346874209357757 349332090505077828509159)
        ·
          refine ⟨523998135757616742763739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349332090505077828509159 523998135757616742763739)
          ·
            refine ⟨785997203636425114145609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523998135757616742763739 785997203636425114145609)
            ·
              refine ⟨589497902727318835609207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785997203636425114145609 589497902727318835609207)
              ·
                refine ⟨884246854090978253413811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589497902727318835609207 884246854090978253413811)
                ·
                  refine ⟨1326370281136467380120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884246854090978253413811 1326370281136467380120717)
                  ·
                    refine ⟨497388855426175267545269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1326370281136467380120717 497388855426175267545269)
                    ·
                      refine ⟨46630205196203931332369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 497388855426175267545269 46630205196203931332369)
                      ·
                        rfl

theorem cell23_90812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_90812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90812 prefixEnd_90812 := by exact prefixLift 90812
  have htrace : WordTrace (prefixWord ++ tailWord_90812) baseStart_90812 baseEnd_90812 := by
    simpa [prefixWord, tailWord_90812, baseEnd_90812] using wordTrace_append hprefix tailTrace_90812
  have hstable : (prefixWord ++ tailWord_90812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90812).length < 2 ^ (prefixWord ++ tailWord_90812).sum := by decide
  have hdescent : baseEnd_90812 < baseStart_90812 := by decide
  rcases family_descends (prefixWord ++ tailWord_90812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90813 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_90813 : Nat := 118140960795 + 90813 * 2 ^ 59
def prefixEnd_90813 : Nat := 4983230072969 + 3 ^ 40 * 90813 * 2
def baseEnd_90813 : Nat := 46630718676858427419865

theorem tailTrace_90813 : CollatzResearch.WordTrace tailWord_90813 prefixEnd_90813 46630718676858427419865 := by
  unfold tailWord_90813
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312222220007485470725093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2208148146671656980483395 3312222220007485470725093)
  ·
    refine ⟨621041666251403525760955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3312222220007485470725093 621041666251403525760955)
    ·
      refine ⟨931562499377105288641433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621041666251403525760955 931562499377105288641433)
      ·
        refine ⟨698671874532828966481075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 931562499377105288641433 698671874532828966481075)
        ·
          refine ⟨1048007811799243449721613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698671874532828966481075 1048007811799243449721613)
          ·
            refine ⟨393002929424716293645605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1048007811799243449721613 393002929424716293645605)
            ·
              refine ⟨73688049267134305058551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 393002929424716293645605 73688049267134305058551)
              ·
                refine ⟨110532073900701457587827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73688049267134305058551 110532073900701457587827)
                ·
                  refine ⟨165798110851052186381741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110532073900701457587827 165798110851052186381741)
                  ·
                    refine ⟨62174291569144569893153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165798110851052186381741 62174291569144569893153)
                    ·
                      refine ⟨46630718676858427419865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62174291569144569893153 46630718676858427419865)
                      ·
                        rfl

theorem cell23_90813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_90813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90813 prefixEnd_90813 := by exact prefixLift 90813
  have htrace : WordTrace (prefixWord ++ tailWord_90813) baseStart_90813 baseEnd_90813 := by
    simpa [prefixWord, tailWord_90813, baseEnd_90813] using wordTrace_append hprefix tailTrace_90813
  have hstable : (prefixWord ++ tailWord_90813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90813).length < 2 ^ (prefixWord ++ tailWord_90813).sum := by decide
  have hdescent : baseEnd_90813 < baseStart_90813 := by decide
  rcases family_descends (prefixWord ++ tailWord_90813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90866 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_90866 : Nat := 118140960795 + 90866 * 2 ^ 59
def prefixEnd_90866 : Nat := 4983230072969 + 3 ^ 40 * 90866 * 2
def baseEnd_90866 : Nat := 5184214794616302228569

theorem tailTrace_90866 : CollatzResearch.WordTrace tailWord_90866 prefixEnd_90866 5184214794616302228569 := by
  unfold tailWord_90866
  simp only [CollatzResearch.WordTrace]
  refine ⟨828538822203868880601113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2209436859210317014936301 828538822203868880601113)
  ·
    refine ⟨621404116652901660450835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 828538822203868880601113 621404116652901660450835)
    ·
      refine ⟨932106174979352490676253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621404116652901660450835 932106174979352490676253)
      ·
        refine ⟨349539815617257184003595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 932106174979352490676253 349539815617257184003595)
        ·
          refine ⟨524309723425885776005393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349539815617257184003595 524309723425885776005393)
          ·
            refine ⟨393232292569414332004045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524309723425885776005393 393232292569414332004045)
            ·
              refine ⟨147462109713530374501517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393232292569414332004045 147462109713530374501517)
              ·
                refine ⟨55298291142573890438069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147462109713530374501517 55298291142573890438069)
                ·
                  refine ⟨5184214794616302228569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55298291142573890438069 5184214794616302228569)
                  ·
                    rfl

theorem cell23_90866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_90866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90866 prefixEnd_90866 := by exact prefixLift 90866
  have htrace : WordTrace (prefixWord ++ tailWord_90866) baseStart_90866 baseEnd_90866 := by
    simpa [prefixWord, tailWord_90866, baseEnd_90866] using wordTrace_append hprefix tailTrace_90866
  have hstable : (prefixWord ++ tailWord_90866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90866).length < 2 ^ (prefixWord ++ tailWord_90866).sum := by decide
  have hdescent : baseEnd_90866 < baseStart_90866 := by decide
  rcases family_descends (prefixWord ++ tailWord_90866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90872 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_90872 : Nat := 118140960795 + 90872 * 2 ^ 59
def prefixEnd_90872 : Nat := 4983230072969 + 3 ^ 40 * 90872 * 2
def baseEnd_90872 : Nat := 46661014035473696582093

theorem tailTrace_90872 : CollatzResearch.WordTrace tailWord_90872 prefixEnd_90872 46661014035473696582093 := by
  unfold tailWord_90872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657187063396869273561435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2209582751195825698081913 1657187063396869273561435)
  ·
    refine ⟨2485780595095303910342153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1657187063396869273561435 2485780595095303910342153)
    ·
      refine ⟨1864335446321477932756615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485780595095303910342153 1864335446321477932756615)
      ·
        refine ⟨2796503169482216899134923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864335446321477932756615 2796503169482216899134923)
        ·
          refine ⟨4194754754223325348702385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796503169482216899134923 4194754754223325348702385)
          ·
            refine ⟨3146066065667494011526789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194754754223325348702385 3146066065667494011526789)
            ·
              refine ⟨589887387312655127161273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3146066065667494011526789 589887387312655127161273)
              ·
                refine ⟨442415540484491345370955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589887387312655127161273 442415540484491345370955)
                ·
                  refine ⟨663623310726737018056433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442415540484491345370955 663623310726737018056433)
                  ·
                    refine ⟨497717483045052763542325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663623310726737018056433 497717483045052763542325)
                    ·
                      refine ⟨46661014035473696582093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 497717483045052763542325 46661014035473696582093)
                      ·
                        rfl

theorem cell23_90872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_90872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90872 prefixEnd_90872 := by exact prefixLift 90872
  have htrace : WordTrace (prefixWord ++ tailWord_90872) baseStart_90872 baseEnd_90872 := by
    simpa [prefixWord, tailWord_90872, baseEnd_90872] using wordTrace_append hprefix tailTrace_90872
  have hstable : (prefixWord ++ tailWord_90872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90872).length < 2 ^ (prefixWord ++ tailWord_90872).sum := by decide
  have hdescent : baseEnd_90872 < baseStart_90872 := by decide
  rcases family_descends (prefixWord ++ tailWord_90872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90899 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 6, 2]
def baseStart_90899 : Nat := 118140960795 + 90899 * 2 ^ 59
def prefixEnd_90899 : Nat := 4983230072969 + 3 ^ 40 * 90899 * 2
def baseEnd_90899 : Nat := 46674878013145090944469

theorem tailTrace_90899 : CollatzResearch.WordTrace tailWord_90899 prefixEnd_90899 46674878013145090944469 := by
  unfold tailWord_90899
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315358897695922158355751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2210239265130614772237167 3315358897695922158355751)
  ·
    refine ⟨4973038346543883237533627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315358897695922158355751 4973038346543883237533627)
    ·
      refine ⟨7459557519815824856300441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973038346543883237533627 7459557519815824856300441)
      ·
        refine ⟨5594668139861868642225331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7459557519815824856300441 5594668139861868642225331)
        ·
          refine ⟨8392002209792802963337997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594668139861868642225331 8392002209792802963337997)
          ·
            refine ⟨3147000828672301111251749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8392002209792802963337997 3147000828672301111251749)
            ·
              refine ⟨590062655376056458359703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3147000828672301111251749 590062655376056458359703)
              ·
                refine ⟨885093983064084687539555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590062655376056458359703 885093983064084687539555)
                ·
                  refine ⟨1327640974596127031309333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885093983064084687539555 1327640974596127031309333)
                  ·
                    refine ⟨62233170684193454592625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1327640974596127031309333 62233170684193454592625)
                    ·
                      refine ⟨46674878013145090944469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62233170684193454592625 46674878013145090944469)
                      ·
                        rfl

theorem cell23_90899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6, 2].length) (baseStart_90899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90899 prefixEnd_90899 := by exact prefixLift 90899
  have htrace : WordTrace (prefixWord ++ tailWord_90899) baseStart_90899 baseEnd_90899 := by
    simpa [prefixWord, tailWord_90899, baseEnd_90899] using wordTrace_append hprefix tailTrace_90899
  have hstable : (prefixWord ++ tailWord_90899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90899).length < 2 ^ (prefixWord ++ tailWord_90899).sum := by decide
  have hdescent : baseEnd_90899 < baseStart_90899 := by decide
  rcases family_descends (prefixWord ++ tailWord_90899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90943 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 1, 4]
def baseStart_90943 : Nat := 118140960795 + 90943 * 2 ^ 59
def prefixEnd_90943 : Nat := 4983230072969 + 3 ^ 40 * 90943 * 2
def baseEnd_90943 : Nat := 15565823720647639598089

theorem tailTrace_90943 : CollatzResearch.WordTrace tailWord_90943 prefixEnd_90943 15565823720647639598089 := by
  unfold tailWord_90943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3316963709536517672957483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2211309139691011781971655 3316963709536517672957483)
  ·
    refine ⟨4975445564304776509436225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3316963709536517672957483 4975445564304776509436225)
    ·
      refine ⟨3731584173228582382077169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4975445564304776509436225 3731584173228582382077169)
      ·
        refine ⟨2798688129921436786557877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3731584173228582382077169 2798688129921436786557877)
        ·
          refine ⟨262377012180134698739801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2798688129921436786557877 262377012180134698739801)
          ·
            refine ⟨196782759135101024054851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262377012180134698739801 196782759135101024054851)
            ·
              refine ⟨295174138702651536082277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196782759135101024054851 295174138702651536082277)
              ·
                refine ⟨55345151006747163015427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295174138702651536082277 55345151006747163015427)
                ·
                  refine ⟨83017726510120744523141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55345151006747163015427 83017726510120744523141)
                  ·
                    refine ⟨15565823720647639598089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83017726510120744523141 15565823720647639598089)
                    ·
                      rfl

theorem cell23_90943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 4].length) (baseStart_90943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90943 prefixEnd_90943 := by exact prefixLift 90943
  have htrace : WordTrace (prefixWord ++ tailWord_90943) baseStart_90943 baseEnd_90943 := by
    simpa [prefixWord, tailWord_90943, baseEnd_90943] using wordTrace_append hprefix tailTrace_90943
  have hstable : (prefixWord ++ tailWord_90943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90943).length < 2 ^ (prefixWord ++ tailWord_90943).sum := by decide
  have hdescent : baseEnd_90943 < baseStart_90943 := by decide
  rcases family_descends (prefixWord ++ tailWord_90943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90969 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_90969 : Nat := 118140960795 + 90969 * 2 ^ 59
def prefixEnd_90969 : Nat := 4983230072969 + 3 ^ 40 * 90969 * 2
def baseEnd_90969 : Nat := 15570273886319939023049

theorem tailTrace_90969 : CollatzResearch.WordTrace tailWord_90969 prefixEnd_90969 15570273886319939023049 := by
  unfold tailWord_90969
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317912007442324113403961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2211941338294882742269307 3317912007442324113403961)
  ·
    refine ⟨2488434005581743085052971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3317912007442324113403961 2488434005581743085052971)
    ·
      refine ⟨3732651008372614627579457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488434005581743085052971 3732651008372614627579457)
      ·
        refine ⟨2799488256279460970684593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3732651008372614627579457 2799488256279460970684593)
        ·
          refine ⟨2099616192209595728013445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799488256279460970684593 2099616192209595728013445)
          ·
            refine ⟨393678036039299199002521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2099616192209595728013445 393678036039299199002521)
            ·
              refine ⟨295258527029474399251891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393678036039299199002521 295258527029474399251891)
              ·
                refine ⟨442887790544211598877837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295258527029474399251891 442887790544211598877837)
                ·
                  refine ⟨166082921454079349579189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 442887790544211598877837 166082921454079349579189)
                  ·
                    refine ⟨15570273886319939023049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166082921454079349579189 15570273886319939023049)
                    ·
                      rfl

theorem cell23_90969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_90969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90969 prefixEnd_90969 := by exact prefixLift 90969
  have htrace : WordTrace (prefixWord ++ tailWord_90969) baseStart_90969 baseEnd_90969 := by
    simpa [prefixWord, tailWord_90969, baseEnd_90969] using wordTrace_append hprefix tailTrace_90969
  have hstable : (prefixWord ++ tailWord_90969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90969).length < 2 ^ (prefixWord ++ tailWord_90969).sum := by decide
  have hdescent : baseEnd_90969 < baseStart_90969 := by decide
  rcases family_descends (prefixWord ++ tailWord_90969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90976 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2]
def baseStart_90976 : Nat := 118140960795 + 90976 * 2 ^ 59
def prefixEnd_90976 : Nat := 4983230072969 + 3 ^ 40 * 90976 * 2
def baseEnd_90976 : Nat := 46714416023541289681615

theorem tailTrace_90976 : CollatzResearch.WordTrace tailWord_90976 prefixEnd_90976 46714416023541289681615 := by
  unfold tailWord_90976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659083659208482154454391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2212111545611309539272521 1659083659208482154454391)
  ·
    refine ⟨2488625488812723231681587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1659083659208482154454391 2488625488812723231681587)
    ·
      refine ⟨3732938233219084847522381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488625488812723231681587 3732938233219084847522381)
      ·
        refine ⟨1399851837457156817820893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3732938233219084847522381 1399851837457156817820893)
        ·
          refine ⟨524944439046433806682835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1399851837457156817820893 524944439046433806682835)
          ·
            refine ⟨787416658569650710024253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524944439046433806682835 787416658569650710024253)
            ·
              refine ⟨295281246963619016259095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787416658569650710024253 295281246963619016259095)
              ·
                refine ⟨442921870445428524388643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295281246963619016259095 442921870445428524388643)
                ·
                  refine ⟨664382805668142786582965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442921870445428524388643 664382805668142786582965)
                  ·
                    refine ⟨62285888031388386242153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 664382805668142786582965 62285888031388386242153)
                    ·
                      refine ⟨46714416023541289681615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62285888031388386242153 46714416023541289681615)
                      ·
                        rfl

theorem cell23_90976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_90976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90976 prefixEnd_90976 := by exact prefixLift 90976
  have htrace : WordTrace (prefixWord ++ tailWord_90976) baseStart_90976 baseEnd_90976 := by
    simpa [prefixWord, tailWord_90976, baseEnd_90976] using wordTrace_append hprefix tailTrace_90976
  have hstable : (prefixWord ++ tailWord_90976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90976).length < 2 ^ (prefixWord ++ tailWord_90976).sum := by decide
  have hdescent : baseEnd_90976 < baseStart_90976 := by decide
  rcases family_descends (prefixWord ++ tailWord_90976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90990 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_90990 : Nat := 118140960795 + 90990 * 2 ^ 59
def prefixEnd_90990 : Nat := 4983230072969 + 3 ^ 40 * 90990 * 2
def baseEnd_90990 : Nat := 5191289416967137211839

theorem tailTrace_90990 : CollatzResearch.WordTrace tailWord_90990 prefixEnd_90990 5191289416967137211839 := by
  unfold tailWord_90990
  simp only [CollatzResearch.WordTrace]
  refine ⟨414834742545780587489803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2212451960244163133278949 414834742545780587489803)
  ·
    refine ⟨622252113818670881234705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414834742545780587489803 622252113818670881234705)
    ·
      refine ⟨466689085364003160926029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622252113818670881234705 466689085364003160926029)
      ·
        refine ⟨175008407011501185347261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466689085364003160926029 175008407011501185347261)
        ·
          refine ⟨65628152629312944505223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175008407011501185347261 65628152629312944505223)
          ·
            refine ⟨98442228943969416757835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65628152629312944505223 98442228943969416757835)
            ·
              refine ⟨147663343415954125136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98442228943969416757835 147663343415954125136753)
              ·
                refine ⟨110747507561965593852565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147663343415954125136753 110747507561965593852565)
                ·
                  refine ⟨5191289416967137211839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110747507561965593852565 5191289416967137211839)
                  ·
                    rfl

theorem cell23_90990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_90990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_90990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_90990 prefixEnd_90990 := by exact prefixLift 90990
  have htrace : WordTrace (prefixWord ++ tailWord_90990) baseStart_90990 baseEnd_90990 := by
    simpa [prefixWord, tailWord_90990, baseEnd_90990] using wordTrace_append hprefix tailTrace_90990
  have hstable : (prefixWord ++ tailWord_90990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90990).length < 2 ^ (prefixWord ++ tailWord_90990).sum := by decide
  have hdescent : baseEnd_90990 < baseStart_90990 := by decide
  rcases family_descends (prefixWord ++ tailWord_90990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91016 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_91016 : Nat := 118140960795 + 91016 * 2 ^ 59
def prefixEnd_91016 : Nat := 4983230072969 + 3 ^ 40 * 91016 * 2
def baseEnd_91016 : Nat := 15578318416573711060477

theorem tailTrace_91016 : CollatzResearch.WordTrace tailWord_91016 prefixEnd_91016 15578318416573711060477 := by
  unfold tailWord_91016
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659813119136025570182451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2213084158848034093576601 1659813119136025570182451)
  ·
    refine ⟨2489719678704038355273677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1659813119136025570182451 2489719678704038355273677)
    ·
      refine ⟨933644879514014383227629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2489719678704038355273677 933644879514014383227629)
      ·
        refine ⟨350116829817755393710361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 933644879514014383227629 350116829817755393710361)
        ·
          refine ⟨262587622363316545282771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350116829817755393710361 262587622363316545282771)
          ·
            refine ⟨393881433544974817924157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262587622363316545282771 393881433544974817924157)
            ·
              refine ⟨147705537579365556721559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393881433544974817924157 147705537579365556721559)
              ·
                refine ⟨221558306369048335082339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147705537579365556721559 221558306369048335082339)
                ·
                  refine ⟨332337459553572502623509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221558306369048335082339 332337459553572502623509)
                  ·
                    refine ⟨15578318416573711060477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 332337459553572502623509 15578318416573711060477)
                    ·
                      rfl

theorem cell23_91016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_91016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91016 prefixEnd_91016 := by exact prefixLift 91016
  have htrace : WordTrace (prefixWord ++ tailWord_91016) baseStart_91016 baseEnd_91016 := by
    simpa [prefixWord, tailWord_91016, baseEnd_91016] using wordTrace_append hprefix tailTrace_91016
  have hstable : (prefixWord ++ tailWord_91016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91016).length < 2 ^ (prefixWord ++ tailWord_91016).sum := by decide
  have hdescent : baseEnd_91016 < baseStart_91016 := by decide
  rcases family_descends (prefixWord ++ tailWord_91016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91029 : List Nat := [1, 3, 2, 1, 1, 5, 1, 9]
def baseStart_91029 : Nat := 118140960795 + 91029 * 2 ^ 59
def prefixEnd_91029 : Nat := 4983230072969 + 3 ^ 40 * 91029 * 2
def baseEnd_91029 : Nat := 1731171499934428974773

theorem tailTrace_91029 : CollatzResearch.WordTrace tailWord_91029 prefixEnd_91029 1731171499934428974773 := by
  unfold tailWord_91029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320100387224954360588141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2213400258149969573725427 3320100387224954360588141)
  ·
    refine ⟨1245037645209357885220553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3320100387224954360588141 1245037645209357885220553)
    ·
      refine ⟨933778233907018413915415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1245037645209357885220553 933778233907018413915415)
      ·
        refine ⟨1400667350860527620873123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933778233907018413915415 1400667350860527620873123)
        ·
          refine ⟨2101001026290791431309685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400667350860527620873123 2101001026290791431309685)
          ·
            refine ⟨196968846214761696685283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2101001026290791431309685 196968846214761696685283)
            ·
              refine ⟨295453269322142545027925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196968846214761696685283 295453269322142545027925)
              ·
                refine ⟨1731171499934428974773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 295453269322142545027925 1731171499934428974773)
                ·
                  rfl

theorem cell23_91029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 9].length) (baseStart_91029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91029 prefixEnd_91029 := by exact prefixLift 91029
  have htrace : WordTrace (prefixWord ++ tailWord_91029) baseStart_91029 baseEnd_91029 := by
    simpa [prefixWord, tailWord_91029, baseEnd_91029] using wordTrace_append hprefix tailTrace_91029
  have hstable : (prefixWord ++ tailWord_91029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91029).length < 2 ^ (prefixWord ++ tailWord_91029).sum := by decide
  have hdescent : baseEnd_91029 < baseStart_91029 := by decide
  rcases family_descends (prefixWord ++ tailWord_91029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91034 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3]
def baseStart_91034 : Nat := 118140960795 + 91034 * 2 ^ 59
def prefixEnd_91034 : Nat := 4983230072969 + 3 ^ 40 * 91034 * 2
def baseEnd_91034 : Nat := 46744197901502062756349

theorem tailTrace_91034 : CollatzResearch.WordTrace tailWord_91034 prefixEnd_91034 46744197901502062756349 := by
  unfold tailWord_91034
  simp only [CollatzResearch.WordTrace]
  refine ⟨830070688051710053630039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2213521834804560143013437 830070688051710053630039)
  ·
    refine ⟨1245106032077565080445059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830070688051710053630039 1245106032077565080445059)
    ·
      refine ⟨1867659048116347620667589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245106032077565080445059 1867659048116347620667589)
      ·
        refine ⟨350186071521815178875173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1867659048116347620667589 350186071521815178875173)
        ·
          refine ⟨65659888410340346039095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 350186071521815178875173 65659888410340346039095)
          ·
            refine ⟨98489832615510519058643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65659888410340346039095 98489832615510519058643)
            ·
              refine ⟨147734748923265778587965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98489832615510519058643 147734748923265778587965)
              ·
                refine ⟨55400530846224666970487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147734748923265778587965 55400530846224666970487)
                ·
                  refine ⟨83100796269337000455731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55400530846224666970487 83100796269337000455731)
                  ·
                    refine ⟨124651194404005500683597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83100796269337000455731 124651194404005500683597)
                    ·
                      refine ⟨46744197901502062756349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 124651194404005500683597 46744197901502062756349)
                      ·
                        rfl

theorem cell23_91034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_91034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91034 prefixEnd_91034 := by exact prefixLift 91034
  have htrace : WordTrace (prefixWord ++ tailWord_91034) baseStart_91034 baseEnd_91034 := by
    simpa [prefixWord, tailWord_91034, baseEnd_91034] using wordTrace_append hprefix tailTrace_91034
  have hstable : (prefixWord ++ tailWord_91034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91034).length < 2 ^ (prefixWord ++ tailWord_91034).sum := by decide
  have hdescent : baseEnd_91034 < baseStart_91034 := by decide
  rcases family_descends (prefixWord ++ tailWord_91034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91057 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_91057 : Nat := 118140960795 + 91057 * 2 ^ 59
def prefixEnd_91057 : Nat := 4983230072969 + 3 ^ 40 * 91057 * 2
def baseEnd_91057 : Nat := 46756007956555472768743

theorem tailTrace_91057 : CollatzResearch.WordTrace tailWord_91057 prefixEnd_91057 46756007956555472768743 := by
  unfold tailWord_91057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321121631123515142607425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2214081087415676761738283 3321121631123515142607425)
  ·
    refine ⟨2490841223342636356955569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3321121631123515142607425 2490841223342636356955569)
    ·
      refine ⟨1868130917506977267716677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2490841223342636356955569 1868130917506977267716677)
      ·
        refine ⟨350274547032558237696877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1868130917506977267716677 350274547032558237696877)
        ·
          refine ⟨131352955137209339136329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350274547032558237696877 131352955137209339136329)
          ·
            refine ⟨98514716352907004352247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131352955137209339136329 98514716352907004352247)
            ·
              refine ⟨147772074529360506528371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98514716352907004352247 147772074529360506528371)
              ·
                refine ⟨221658111794040759792557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147772074529360506528371 221658111794040759792557)
                ·
                  refine ⟨83121791922765284922209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221658111794040759792557 83121791922765284922209)
                  ·
                    refine ⟨62341343942073963691657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83121791922765284922209 62341343942073963691657)
                    ·
                      refine ⟨46756007956555472768743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62341343942073963691657 46756007956555472768743)
                      ·
                        rfl

theorem cell23_91057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_91057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91057 prefixEnd_91057 := by exact prefixLift 91057
  have htrace : WordTrace (prefixWord ++ tailWord_91057) baseStart_91057 baseEnd_91057 := by
    simpa [prefixWord, tailWord_91057, baseEnd_91057] using wordTrace_append hprefix tailTrace_91057
  have hstable : (prefixWord ++ tailWord_91057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91057).length < 2 ^ (prefixWord ++ tailWord_91057).sum := by decide
  have hdescent : baseEnd_91057 < baseStart_91057 := by decide
  rcases family_descends (prefixWord ++ tailWord_91057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91083 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 3, 3, 2]
def baseStart_91083 : Nat := 118140960795 + 91083 * 2 ^ 59
def prefixEnd_91083 : Nat := 4983230072969 + 3 ^ 40 * 91083 * 2
def baseEnd_91083 : Nat := 46769358453572371043623

theorem tailTrace_91083 : CollatzResearch.WordTrace tailWord_91083 prefixEnd_91083 46769358453572371043623 := by
  unfold tailWord_91083
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322069929029321583053903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2214713286019547722035935 3322069929029321583053903)
  ·
    refine ⟨4983104893543982374580855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3322069929029321583053903 4983104893543982374580855)
    ·
      refine ⟨7474657340315973561871283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4983104893543982374580855 7474657340315973561871283)
      ·
        refine ⟨11211986010473960342806925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474657340315973561871283 11211986010473960342806925)
        ·
          refine ⟨4204494753927735128552597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11211986010473960342806925 4204494753927735128552597)
          ·
            refine ⟨197085691590362584150903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4204494753927735128552597 197085691590362584150903)
            ·
              refine ⟨295628537385543876226355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197085691590362584150903 295628537385543876226355)
              ·
                refine ⟨443442806078315814339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295628537385543876226355 443442806078315814339533)
                ·
                  refine ⟨166291052279368430377325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443442806078315814339533 166291052279368430377325)
                  ·
                    refine ⟨62359144604763161391497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166291052279368430377325 62359144604763161391497)
                    ·
                      refine ⟨46769358453572371043623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62359144604763161391497 46769358453572371043623)
                      ·
                        rfl

theorem cell23_91083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 3, 2].length) (baseStart_91083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91083 prefixEnd_91083 := by exact prefixLift 91083
  have htrace : WordTrace (prefixWord ++ tailWord_91083) baseStart_91083 baseEnd_91083 := by
    simpa [prefixWord, tailWord_91083, baseEnd_91083] using wordTrace_append hprefix tailTrace_91083
  have hstable : (prefixWord ++ tailWord_91083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91083).length < 2 ^ (prefixWord ++ tailWord_91083).sum := by decide
  have hdescent : baseEnd_91083 < baseStart_91083 := by decide
  rcases family_descends (prefixWord ++ tailWord_91083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91164 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_91164 : Nat := 118140960795 + 91164 * 2 ^ 59
def prefixEnd_91164 : Nat := 4983230072969 + 3 ^ 40 * 91164 * 2
def baseEnd_91164 : Nat := 46810950386586554130751

theorem tailTrace_91164 : CollatzResearch.WordTrace tailWord_91164 prefixEnd_91164 46810950386586554130751 := by
  unfold tailWord_91164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662512120867936208376273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2216682827823914944501697 1662512120867936208376273)
  ·
    refine ⟨1246884090650952156282205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1662512120867936208376273 1246884090650952156282205)
    ·
      refine ⟨467581533994107058605827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1246884090650952156282205 467581533994107058605827)
      ·
        refine ⟨701372300991160587908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467581533994107058605827 701372300991160587908741)
        ·
          refine ⟨131507306435842610232889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 701372300991160587908741 131507306435842610232889)
          ·
            refine ⟨98630479826881957674667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131507306435842610232889 98630479826881957674667)
            ·
              refine ⟨147945719740322936512001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98630479826881957674667 147945719740322936512001)
              ·
                refine ⟨110959289805242202384001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147945719740322936512001 110959289805242202384001)
                ·
                  refine ⟨83219467353931651788001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110959289805242202384001 83219467353931651788001)
                  ·
                    refine ⟨62414600515448738841001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83219467353931651788001 62414600515448738841001)
                    ·
                      refine ⟨46810950386586554130751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62414600515448738841001 46810950386586554130751)
                      ·
                        rfl

theorem cell23_91164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_91164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91164 prefixEnd_91164 := by exact prefixLift 91164
  have htrace : WordTrace (prefixWord ++ tailWord_91164) baseStart_91164 baseEnd_91164 := by
    simpa [prefixWord, tailWord_91164, baseEnd_91164] using wordTrace_append hprefix tailTrace_91164
  have hstable : (prefixWord ++ tailWord_91164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91164).length < 2 ^ (prefixWord ++ tailWord_91164).sum := by decide
  have hdescent : baseEnd_91164 < baseStart_91164 := by decide
  rcases family_descends (prefixWord ++ tailWord_91164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91186 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_91186 : Nat := 118140960795 + 91186 * 2 ^ 59
def prefixEnd_91186 : Nat := 4983230072969 + 3 ^ 40 * 91186 * 2
def baseEnd_91186 : Nat := 46822246960985468055649

theorem tailTrace_91186 : CollatzResearch.WordTrace tailWord_91186 prefixEnd_91186 46822246960985468055649 := by
  unfold tailWord_91186
  simp only [CollatzResearch.WordTrace]
  refine ⟨831456661914042543513353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2217217765104113449368941 831456661914042543513353)
  ·
    refine ⟨623592496435531907635015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831456661914042543513353 623592496435531907635015)
    ·
      refine ⟨935388744653297861452523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623592496435531907635015 935388744653297861452523)
      ·
        refine ⟨1403083116979946792178785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935388744653297861452523 1403083116979946792178785)
        ·
          refine ⟨1052312337734960094134089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403083116979946792178785 1052312337734960094134089)
          ·
            refine ⟨789234253301220070600567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052312337734960094134089 789234253301220070600567)
            ·
              refine ⟨1183851379951830105900851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789234253301220070600567 1183851379951830105900851)
              ·
                refine ⟨1775777069927745158851277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183851379951830105900851 1775777069927745158851277)
                ·
                  refine ⟨665916401222904434569229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1775777069927745158851277 665916401222904434569229)
                  ·
                    refine ⟨249718650458589162963461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 665916401222904434569229 249718650458589162963461)
                    ·
                      refine ⟨46822246960985468055649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 249718650458589162963461 46822246960985468055649)
                      ·
                        rfl

theorem cell23_91186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_91186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91186 prefixEnd_91186 := by exact prefixLift 91186
  have htrace : WordTrace (prefixWord ++ tailWord_91186) baseStart_91186 baseEnd_91186 := by
    simpa [prefixWord, tailWord_91186, baseEnd_91186] using wordTrace_append hprefix tailTrace_91186
  have hstable : (prefixWord ++ tailWord_91186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91186).length < 2 ^ (prefixWord ++ tailWord_91186).sum := by decide
  have hdescent : baseEnd_91186 < baseStart_91186 := by decide
  rcases family_descends (prefixWord ++ tailWord_91186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91293 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_91293 : Nat := 118140960795 + 91293 * 2 ^ 59
def prefixEnd_91293 : Nat := 4983230072969 + 3 ^ 40 * 91293 * 2
def baseEnd_91293 : Nat := 46877189391016549417657

theorem tailTrace_91293 : CollatzResearch.WordTrace tailWord_91293 prefixEnd_91293 46877189391016549417657 := by
  unfold tailWord_91293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329729258268527448198533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2219819505512351632132355 3329729258268527448198533)
  ·
    refine ⟨624324235925348896537225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3329729258268527448198533 624324235925348896537225)
    ·
      refine ⟨468243176944011672402919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 624324235925348896537225 468243176944011672402919)
      ·
        refine ⟨702364765416017508604379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468243176944011672402919 702364765416017508604379)
        ·
          refine ⟨1053547148124026262906569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702364765416017508604379 1053547148124026262906569)
          ·
            refine ⟨790160361093019697179927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053547148124026262906569 790160361093019697179927)
            ·
              refine ⟨1185240541639529545769891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790160361093019697179927 1185240541639529545769891)
              ·
                refine ⟨1777860812459294318654837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185240541639529545769891 1777860812459294318654837)
                ·
                  refine ⟨166674451168058842373891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777860812459294318654837 166674451168058842373891)
                  ·
                    refine ⟨250011676752088263560837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166674451168058842373891 250011676752088263560837)
                    ·
                      refine ⟨46877189391016549417657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 250011676752088263560837 46877189391016549417657)
                      ·
                        rfl

theorem cell23_91293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_91293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91293 prefixEnd_91293 := by exact prefixLift 91293
  have htrace : WordTrace (prefixWord ++ tailWord_91293) baseStart_91293 baseEnd_91293 := by
    simpa [prefixWord, tailWord_91293, baseEnd_91293] using wordTrace_append hprefix tailTrace_91293
  have hstable : (prefixWord ++ tailWord_91293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91293).length < 2 ^ (prefixWord ++ tailWord_91293).sum := by decide
  have hdescent : baseEnd_91293 < baseStart_91293 := by decide
  rcases family_descends (prefixWord ++ tailWord_91293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91360 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_91360 : Nat := 118140960795 + 91360 * 2 ^ 59
def prefixEnd_91360 : Nat := 4983230072969 + 3 ^ 40 * 91360 * 2
def baseEnd_91360 : Nat := 46911592594867787279849

theorem tailTrace_91360 : CollatzResearch.WordTrace tailWord_91360 prefixEnd_91360 46911592594867787279849 := by
  unfold tailWord_91360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666086474512898945443767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2221448632683865260591689 1666086474512898945443767)
  ·
    refine ⟨2499129711769348418165651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666086474512898945443767 2499129711769348418165651)
    ·
      refine ⟨3748694567654022627248477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499129711769348418165651 3748694567654022627248477)
      ·
        refine ⟨1405760462870258485218179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3748694567654022627248477 1405760462870258485218179)
        ·
          refine ⟨2108640694305387727827269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405760462870258485218179 2108640694305387727827269)
          ·
            refine ⟨395370130182260198967613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2108640694305387727827269 395370130182260198967613)
            ·
              refine ⟨148263798818347574612855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395370130182260198967613 148263798818347574612855)
              ·
                refine ⟨222395698227521361919283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148263798818347574612855 222395698227521361919283)
                ·
                  refine ⟨333593547341282042878925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222395698227521361919283 333593547341282042878925)
                  ·
                    refine ⟨125097580252980766079597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333593547341282042878925 125097580252980766079597)
                    ·
                      refine ⟨46911592594867787279849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125097580252980766079597 46911592594867787279849)
                      ·
                        rfl

theorem cell23_91360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_91360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91360 prefixEnd_91360 := by exact prefixLift 91360
  have htrace : WordTrace (prefixWord ++ tailWord_91360) baseStart_91360 baseEnd_91360 := by
    simpa [prefixWord, tailWord_91360, baseEnd_91360] using wordTrace_append hprefix tailTrace_91360
  have hstable : (prefixWord ++ tailWord_91360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91360).length < 2 ^ (prefixWord ++ tailWord_91360).sum := by decide
  have hdescent : baseEnd_91360 < baseStart_91360 := by decide
  rcases family_descends (prefixWord ++ tailWord_91360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91367 : List Nat := [1, 1, 5, 3, 2, 2, 2, 7]
def baseStart_91367 : Nat := 118140960795 + 91367 * 2 ^ 59
def prefixEnd_91367 : Nat := 4983230072969 + 3 ^ 40 * 91367 * 2
def baseEnd_91367 : Nat := 1737599517016639255271

theorem tailTrace_91367 : CollatzResearch.WordTrace tailWord_91367 prefixEnd_91367 1737599517016639255271 := by
  unfold tailWord_91367
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332428260000438086392355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2221618840000292057594903 3332428260000438086392355)
  ·
    refine ⟨4998642390000657129588533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332428260000438086392355 4998642390000657129588533)
    ·
      refine ⟨468622724062561605898925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4998642390000657129588533 468622724062561605898925)
      ·
        refine ⟨175733521523460602212097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468622724062561605898925 175733521523460602212097)
        ·
          refine ⟨131800141142595451659073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175733521523460602212097 131800141142595451659073)
          ·
            refine ⟨98850105856946588744305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131800141142595451659073 98850105856946588744305)
            ·
              refine ⟨74137579392709941558229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98850105856946588744305 74137579392709941558229)
              ·
                refine ⟨1737599517016639255271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74137579392709941558229 1737599517016639255271)
                ·
                  rfl

theorem cell23_91367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 7].length) (baseStart_91367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91367 prefixEnd_91367 := by exact prefixLift 91367
  have htrace : WordTrace (prefixWord ++ tailWord_91367) baseStart_91367 baseEnd_91367 := by
    simpa [prefixWord, tailWord_91367, baseEnd_91367] using wordTrace_append hprefix tailTrace_91367
  have hstable : (prefixWord ++ tailWord_91367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91367).length < 2 ^ (prefixWord ++ tailWord_91367).sum := by decide
  have hdescent : baseEnd_91367 < baseStart_91367 := by decide
  rcases family_descends (prefixWord ++ tailWord_91367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91378 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_91378 : Nat := 118140960795 + 91378 * 2 ^ 59
def prefixEnd_91378 : Nat := 4983230072969 + 3 ^ 40 * 91378 * 2
def baseEnd_91378 : Nat := 46920835246648716854767

theorem tailTrace_91378 : CollatzResearch.WordTrace tailWord_91378 prefixEnd_91378 46920835246648716854767 := by
  unfold tailWord_91378
  simp only [CollatzResearch.WordTrace]
  refine ⟨833207365740146741260697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2221886308640391310028525 833207365740146741260697)
  ·
    refine ⟨624905524305110055945523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 833207365740146741260697 624905524305110055945523)
    ·
      refine ⟨937358286457665083918285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624905524305110055945523 937358286457665083918285)
      ·
        refine ⟨351509357421624406469357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 937358286457665083918285 351509357421624406469357)
        ·
          refine ⟨131816009033109152426009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351509357421624406469357 131816009033109152426009)
          ·
            refine ⟨98862006774831864319507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131816009033109152426009 98862006774831864319507)
            ·
              refine ⟨148293010162247796479261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98862006774831864319507 148293010162247796479261)
              ·
                refine ⟨55609878810842923679723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148293010162247796479261 55609878810842923679723)
                ·
                  refine ⟨83414818216264385519585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55609878810842923679723 83414818216264385519585)
                  ·
                    refine ⟨62561113662198289139689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83414818216264385519585 62561113662198289139689)
                    ·
                      refine ⟨46920835246648716854767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62561113662198289139689 46920835246648716854767)
                      ·
                        rfl

theorem cell23_91378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_91378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91378 prefixEnd_91378 := by exact prefixLift 91378
  have htrace : WordTrace (prefixWord ++ tailWord_91378) baseStart_91378 baseEnd_91378 := by
    simpa [prefixWord, tailWord_91378, baseEnd_91378] using wordTrace_append hprefix tailTrace_91378
  have hstable : (prefixWord ++ tailWord_91378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91378).length < 2 ^ (prefixWord ++ tailWord_91378).sum := by decide
  have hdescent : baseEnd_91378 < baseStart_91378 := by decide
  rcases family_descends (prefixWord ++ tailWord_91378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91413 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_91413 : Nat := 118140960795 + 91413 * 2 ^ 59
def prefixEnd_91413 : Nat := 4983230072969 + 3 ^ 40 * 91413 * 2
def baseEnd_91413 : Nat := 46938807069556079917105

theorem tailTrace_91413 : CollatzResearch.WordTrace tailWord_91413 prefixEnd_91413 46938807069556079917105 := by
  unfold tailWord_91413
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334106017833787942566893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2222737345222525295044595 3334106017833787942566893)
  ·
    refine ⟨1250289756687670478462585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3334106017833787942566893 1250289756687670478462585)
    ·
      refine ⟨937717317515752858846939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250289756687670478462585 937717317515752858846939)
      ·
        refine ⟨1406575976273629288270409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937717317515752858846939 1406575976273629288270409)
        ·
          refine ⟨1054931982205221966202807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406575976273629288270409 1054931982205221966202807)
          ·
            refine ⟨1582397973307832949304211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054931982205221966202807 1582397973307832949304211)
            ·
              refine ⟨2373596959961749423956317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582397973307832949304211 2373596959961749423956317)
              ·
                refine ⟨890098859985656033983619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2373596959961749423956317 890098859985656033983619)
                ·
                  refine ⟨1335148289978484050975429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890098859985656033983619 1335148289978484050975429)
                  ·
                    refine ⟨250340304370965759557893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1335148289978484050975429 250340304370965759557893)
                    ·
                      refine ⟨46938807069556079917105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 250340304370965759557893 46938807069556079917105)
                      ·
                        rfl

theorem cell23_91413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_91413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91413 prefixEnd_91413 := by exact prefixLift 91413
  have htrace : WordTrace (prefixWord ++ tailWord_91413) baseStart_91413 baseEnd_91413 := by
    simpa [prefixWord, tailWord_91413, baseEnd_91413] using wordTrace_append hprefix tailTrace_91413
  have hstable : (prefixWord ++ tailWord_91413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91413).length < 2 ^ (prefixWord ++ tailWord_91413).sum := by decide
  have hdescent : baseEnd_91413 < baseStart_91413 := by decide
  rcases family_descends (prefixWord ++ tailWord_91413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91421 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_91421 : Nat := 118140960795 + 91421 * 2 ^ 59
def prefixEnd_91421 : Nat := 4983230072969 + 3 ^ 40 * 91421 * 2
def baseEnd_91421 : Nat := 46942914914792048617069

theorem tailTrace_91421 : CollatzResearch.WordTrace tailWord_91421 prefixEnd_91421 46942914914792048617069 := by
  unfold tailWord_91421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334397801804805308858117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2222931867869870205905411 3334397801804805308858117)
  ·
    refine ⟨625199587838400995410897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3334397801804805308858117 625199587838400995410897)
    ·
      refine ⟨468899690878800746558173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 625199587838400995410897 468899690878800746558173)
      ·
        refine ⟨175837384079550279959315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 468899690878800746558173 175837384079550279959315)
        ·
          refine ⟨263756076119325419938973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175837384079550279959315 263756076119325419938973)
          ·
            refine ⟨98908528544747032477115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263756076119325419938973 98908528544747032477115)
            ·
              refine ⟨148362792817120548715673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98908528544747032477115 148362792817120548715673)
              ·
                refine ⟨111272094612840411536755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148362792817120548715673 111272094612840411536755)
                ·
                  refine ⟨166908141919260617305133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111272094612840411536755 166908141919260617305133)
                  ·
                    refine ⟨62590553219722731489425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166908141919260617305133 62590553219722731489425)
                    ·
                      refine ⟨46942914914792048617069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62590553219722731489425 46942914914792048617069)
                      ·
                        rfl

theorem cell23_91421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_91421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91421 prefixEnd_91421 := by exact prefixLift 91421
  have htrace : WordTrace (prefixWord ++ tailWord_91421) baseStart_91421 baseEnd_91421 := by
    simpa [prefixWord, tailWord_91421, baseEnd_91421] using wordTrace_append hprefix tailTrace_91421
  have hstable : (prefixWord ++ tailWord_91421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91421).length < 2 ^ (prefixWord ++ tailWord_91421).sum := by decide
  have hdescent : baseEnd_91421 < baseStart_91421 := by decide
  rcases family_descends (prefixWord ++ tailWord_91421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91434 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_91434 : Nat := 118140960795 + 91434 * 2 ^ 59
def prefixEnd_91434 : Nat := 4983230072969 + 3 ^ 40 * 91434 * 2
def baseEnd_91434 : Nat := 46949590163300497754509

theorem tailTrace_91434 : CollatzResearch.WordTrace tailWord_91434 prefixEnd_91434 46949590163300497754509 := by
  unfold tailWord_91434
  simp only [CollatzResearch.WordTrace]
  refine ⟨833717987689427132270339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2223247967171805686054237 833717987689427132270339)
  ·
    refine ⟨1250576981534140698405509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833717987689427132270339 1250576981534140698405509)
    ·
      refine ⟨234483184037651380951033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1250576981534140698405509 234483184037651380951033)
      ·
        refine ⟨175862388028238535713275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234483184037651380951033 175862388028238535713275)
        ·
          refine ⟨263793582042357803569913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175862388028238535713275 263793582042357803569913)
          ·
            refine ⟨197845186531768352677435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263793582042357803569913 197845186531768352677435)
            ·
              refine ⟨296767779797652529016153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197845186531768352677435 296767779797652529016153)
              ·
                refine ⟨222575834848239396762115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296767779797652529016153 222575834848239396762115)
                ·
                  refine ⟨333863752272359095143173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222575834848239396762115 333863752272359095143173)
                  ·
                    refine ⟨62599453551067330339345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 333863752272359095143173 62599453551067330339345)
                    ·
                      refine ⟨46949590163300497754509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62599453551067330339345 46949590163300497754509)
                      ·
                        rfl

theorem cell23_91434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_91434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91434 prefixEnd_91434 := by exact prefixLift 91434
  have htrace : WordTrace (prefixWord ++ tailWord_91434) baseStart_91434 baseEnd_91434 := by
    simpa [prefixWord, tailWord_91434, baseEnd_91434] using wordTrace_append hprefix tailTrace_91434
  have hstable : (prefixWord ++ tailWord_91434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91434).length < 2 ^ (prefixWord ++ tailWord_91434).sum := by decide
  have hdescent : baseEnd_91434 < baseStart_91434 := by decide
  rcases family_descends (prefixWord ++ tailWord_91434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91437 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_91437 : Nat := 118140960795 + 91437 * 2 ^ 59
def prefixEnd_91437 : Nat := 4983230072969 + 3 ^ 40 * 91437 * 2
def baseEnd_91437 : Nat := 46951130605263986016995

theorem tailTrace_91437 : CollatzResearch.WordTrace tailWord_91437 prefixEnd_91437 46951130605263986016995 := by
  unfold tailWord_91437
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334981369746840041440565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2223320913164560027627043 3334981369746840041440565)
  ·
    refine ⟨312654503413766253885053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3334981369746840041440565 312654503413766253885053)
    ·
      refine ⟨117245438780162345206895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312654503413766253885053 117245438780162345206895)
      ·
        refine ⟨175868158170243517810343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117245438780162345206895 175868158170243517810343)
        ·
          refine ⟨263802237255365276715515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175868158170243517810343 263802237255365276715515)
          ·
            refine ⟨395703355883047915073273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263802237255365276715515 395703355883047915073273)
            ·
              refine ⟨296777516912285936304955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395703355883047915073273 296777516912285936304955)
              ·
                refine ⟨445166275368428904457433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296777516912285936304955 445166275368428904457433)
                ·
                  refine ⟨333874706526321678343075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445166275368428904457433 333874706526321678343075)
                  ·
                    refine ⟨500812059789482517514613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333874706526321678343075 500812059789482517514613)
                    ·
                      refine ⟨46951130605263986016995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 500812059789482517514613 46951130605263986016995)
                      ·
                        rfl

theorem cell23_91437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_91437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91437 prefixEnd_91437 := by exact prefixLift 91437
  have htrace : WordTrace (prefixWord ++ tailWord_91437) baseStart_91437 baseEnd_91437 := by
    simpa [prefixWord, tailWord_91437, baseEnd_91437] using wordTrace_append hprefix tailTrace_91437
  have hstable : (prefixWord ++ tailWord_91437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91437).length < 2 ^ (prefixWord ++ tailWord_91437).sum := by decide
  have hdescent : baseEnd_91437 < baseStart_91437 := by decide
  rcases family_descends (prefixWord ++ tailWord_91437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91440 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 5]
def baseStart_91440 : Nat := 118140960795 + 91440 * 2 ^ 59
def prefixEnd_91440 : Nat := 4983230072969 + 3 ^ 40 * 91440 * 2
def baseEnd_91440 : Nat := 5216963449691941586609

theorem tailTrace_91440 : CollatzResearch.WordTrace tailWord_91440 prefixEnd_91440 5216963449691941586609 := by
  unfold tailWord_91440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667545394367985776899887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2223393859157314369199849 1667545394367985776899887)
  ·
    refine ⟨2501318091551978665349831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1667545394367985776899887 2501318091551978665349831)
    ·
      refine ⟨3751977137327967998024747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501318091551978665349831 3751977137327967998024747)
      ·
        refine ⟨5627965705991951997037121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751977137327967998024747 5627965705991951997037121)
        ·
          refine ⟨4220974279493963997777841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5627965705991951997037121 4220974279493963997777841)
          ·
            refine ⟨3165730709620472998333381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4220974279493963997777841 3165730709620472998333381)
            ·
              refine ⟨593574508053838687187509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3165730709620472998333381 593574508053838687187509)
              ·
                refine ⟨55647610130047376923829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 593574508053838687187509 55647610130047376923829)
                ·
                  refine ⟨5216963449691941586609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55647610130047376923829 5216963449691941586609)
                  ·
                    rfl

theorem cell23_91440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 5].length) (baseStart_91440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91440 prefixEnd_91440 := by exact prefixLift 91440
  have htrace : WordTrace (prefixWord ++ tailWord_91440) baseStart_91440 baseEnd_91440 := by
    simpa [prefixWord, tailWord_91440, baseEnd_91440] using wordTrace_append hprefix tailTrace_91440
  have hstable : (prefixWord ++ tailWord_91440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91440).length < 2 ^ (prefixWord ++ tailWord_91440).sum := by decide
  have hdescent : baseEnd_91440 < baseStart_91440 := by decide
  rcases family_descends (prefixWord ++ tailWord_91440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91450 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_91450 : Nat := 118140960795 + 91450 * 2 ^ 59
def prefixEnd_91450 : Nat := 4983230072969 + 3 ^ 40 * 91450 * 2
def baseEnd_91450 : Nat := 46957805853772435154435

theorem tailTrace_91450 : CollatzResearch.WordTrace tailWord_91450 prefixEnd_91450 46957805853772435154435 := by
  unfold tailWord_91450
  simp only [CollatzResearch.WordTrace]
  refine ⟨833863879674935815415951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2223637012466495507775869 833863879674935815415951)
  ·
    refine ⟨1250795819512403723123927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833863879674935815415951 1250795819512403723123927)
    ·
      refine ⟨1876193729268605584685891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250795819512403723123927 1876193729268605584685891)
      ·
        refine ⟨2814290593902908377028837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876193729268605584685891 2814290593902908377028837)
        ·
          refine ⟨527679486356795320692907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2814290593902908377028837 527679486356795320692907)
          ·
            refine ⟨791519229535192981039361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527679486356795320692907 791519229535192981039361)
            ·
              refine ⟨593639422151394735779521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791519229535192981039361 593639422151394735779521)
              ·
                refine ⟨445229566613546051834641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593639422151394735779521 445229566613546051834641)
                ·
                  refine ⟨333922174960159538875981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445229566613546051834641 333922174960159538875981)
                  ·
                    refine ⟨125220815610059827078493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333922174960159538875981 125220815610059827078493)
                    ·
                      refine ⟨46957805853772435154435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125220815610059827078493 46957805853772435154435)
                      ·
                        rfl

theorem cell23_91450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_91450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91450 prefixEnd_91450 := by exact prefixLift 91450
  have htrace : WordTrace (prefixWord ++ tailWord_91450) baseStart_91450 baseEnd_91450 := by
    simpa [prefixWord, tailWord_91450, baseEnd_91450] using wordTrace_append hprefix tailTrace_91450
  have hstable : (prefixWord ++ tailWord_91450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91450).length < 2 ^ (prefixWord ++ tailWord_91450).sum := by decide
  have hdescent : baseEnd_91450 < baseStart_91450 := by decide
  rcases family_descends (prefixWord ++ tailWord_91450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91503 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_91503 : Nat := 118140960795 + 91503 * 2 ^ 59
def prefixEnd_91503 : Nat := 4983230072969 + 3 ^ 40 * 91503 * 2
def baseEnd_91503 : Nat := 46985020328460727791691

theorem tailTrace_91503 : CollatzResearch.WordTrace tailWord_91503 prefixEnd_91503 46985020328460727791691 := by
  unfold tailWord_91503
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337388587507733313343163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2224925725005155542228775 3337388587507733313343163)
  ·
    refine ⟨5006082881261599970014745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3337388587507733313343163 5006082881261599970014745)
    ·
      refine ⟨3754562160946199977511059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5006082881261599970014745 3754562160946199977511059)
      ·
        refine ⟨5631843241419299966266589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754562160946199977511059 5631843241419299966266589)
        ·
          refine ⟨2111941215532237487349971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5631843241419299966266589 2111941215532237487349971)
          ·
            refine ⟨3167911823298356231024957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111941215532237487349971 3167911823298356231024957)
            ·
              refine ⟨1187966933736883586634359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3167911823298356231024957 1187966933736883586634359)
              ·
                refine ⟨1781950400605325379951539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187966933736883586634359 1781950400605325379951539)
                ·
                  refine ⟨2672925600907988069927309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1781950400605325379951539 2672925600907988069927309)
                  ·
                    refine ⟨1002347100340495526222741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2672925600907988069927309 1002347100340495526222741)
                    ·
                      refine ⟨46985020328460727791691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1002347100340495526222741 46985020328460727791691)
                      ·
                        rfl

theorem cell23_91503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_91503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91503 prefixEnd_91503 := by exact prefixLift 91503
  have htrace : WordTrace (prefixWord ++ tailWord_91503) baseStart_91503 baseEnd_91503 := by
    simpa [prefixWord, tailWord_91503, baseEnd_91503] using wordTrace_append hprefix tailTrace_91503
  have hstable : (prefixWord ++ tailWord_91503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91503).length < 2 ^ (prefixWord ++ tailWord_91503).sum := by decide
  have hdescent : baseEnd_91503 < baseStart_91503 := by decide
  rcases family_descends (prefixWord ++ tailWord_91503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91517 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_91517 : Nat := 118140960795 + 91517 * 2 ^ 59
def prefixEnd_91517 : Nat := 4983230072969 + 3 ^ 40 * 91517 * 2
def baseEnd_91517 : Nat := 15664069685874557672209

theorem tailTrace_91517 : CollatzResearch.WordTrace tailWord_91517 prefixEnd_91517 15664069685874557672209 := by
  unfold tailWord_91517
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337899209457013704352805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2225266139638009136235203 3337899209457013704352805)
  ·
    refine ⟨625856101773190069566151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3337899209457013704352805 625856101773190069566151)
    ·
      refine ⟨938784152659785104349227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625856101773190069566151 938784152659785104349227)
      ·
        refine ⟨1408176228989677656523841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938784152659785104349227 1408176228989677656523841)
        ·
          refine ⟨1056132171742258242392881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408176228989677656523841 1056132171742258242392881)
          ·
            refine ⟨792099128806693681794661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056132171742258242392881 792099128806693681794661)
            ·
              refine ⟨148518586651255065336499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 792099128806693681794661 148518586651255065336499)
              ·
                refine ⟨222777879976882598004749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148518586651255065336499 222777879976882598004749)
                ·
                  refine ⟨83541704991330974251781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222777879976882598004749 83541704991330974251781)
                  ·
                    refine ⟨15664069685874557672209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83541704991330974251781 15664069685874557672209)
                    ·
                      rfl

theorem cell23_91517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_91517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91517 prefixEnd_91517 := by exact prefixLift 91517
  have htrace : WordTrace (prefixWord ++ tailWord_91517) baseStart_91517 baseEnd_91517 := by
    simpa [prefixWord, tailWord_91517, baseEnd_91517] using wordTrace_append hprefix tailTrace_91517
  have hstable : (prefixWord ++ tailWord_91517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91517).length < 2 ^ (prefixWord ++ tailWord_91517).sum := by decide
  have hdescent : baseEnd_91517 < baseStart_91517 := by decide
  rcases family_descends (prefixWord ++ tailWord_91517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91551 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 1, 4]
def baseStart_91551 : Nat := 118140960795 + 91551 * 2 ^ 59
def prefixEnd_91551 : Nat := 4983230072969 + 3 ^ 40 * 91551 * 2
def baseEnd_91551 : Nat := 15669889133292179997157

theorem tailTrace_91551 : CollatzResearch.WordTrace tailWord_91551 prefixEnd_91551 15669889133292179997157 := by
  unfold tailWord_91551
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339139291333837511090507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2226092860889225007393671 3339139291333837511090507)
  ·
    refine ⟨5008708937000756266635761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3339139291333837511090507 5008708937000756266635761)
    ·
      refine ⟨3756531702750567199976821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5008708937000756266635761 3756531702750567199976821)
      ·
        refine ⟨352174847132865674997827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3756531702750567199976821 352174847132865674997827)
        ·
          refine ⟨528262270699298512496741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352174847132865674997827 528262270699298512496741)
          ·
            refine ⟨99049175756118471093139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 528262270699298512496741 99049175756118471093139)
            ·
              refine ⟨148573763634177706639709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99049175756118471093139 148573763634177706639709)
              ·
                refine ⟨55715161362816639989891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148573763634177706639709 55715161362816639989891)
                ·
                  refine ⟨83572742044224959984837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55715161362816639989891 83572742044224959984837)
                  ·
                    refine ⟨15669889133292179997157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83572742044224959984837 15669889133292179997157)
                    ·
                      rfl

theorem cell23_91551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 4].length) (baseStart_91551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91551 prefixEnd_91551 := by exact prefixLift 91551
  have htrace : WordTrace (prefixWord ++ tailWord_91551) baseStart_91551 baseEnd_91551 := by
    simpa [prefixWord, tailWord_91551, baseEnd_91551] using wordTrace_append hprefix tailTrace_91551
  have hstable : (prefixWord ++ tailWord_91551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91551).length < 2 ^ (prefixWord ++ tailWord_91551).sum := by decide
  have hdescent : baseEnd_91551 < baseStart_91551 := by decide
  rcases family_descends (prefixWord ++ tailWord_91551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91594 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_91594 : Nat := 118140960795 + 91594 * 2 ^ 59
def prefixEnd_91594 : Nat := 4983230072969 + 3 ^ 40 * 91594 * 2
def baseEnd_91594 : Nat := 15677249022673290584591

theorem tailTrace_91594 : CollatzResearch.WordTrace tailWord_91594 prefixEnd_91594 15677249022673290584591 := by
  unfold tailWord_91594
  simp only [CollatzResearch.WordTrace]
  refine ⟨835176907544513963726459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2227138420118703903270557 835176907544513963726459)
  ·
    refine ⟨1252765361316770945589689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835176907544513963726459 1252765361316770945589689)
    ·
      refine ⟨939574020987578209192267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1252765361316770945589689 939574020987578209192267)
      ·
        refine ⟨1409361031481367313788401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939574020987578209192267 1409361031481367313788401)
        ·
          refine ⟨1057020773611025485341301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409361031481367313788401 1057020773611025485341301)
          ·
            refine ⟨99095697526033639250747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1057020773611025485341301 99095697526033639250747)
            ·
              refine ⟨148643546289050458876121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99095697526033639250747 148643546289050458876121)
              ·
                refine ⟨111482659716787844157091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148643546289050458876121 111482659716787844157091)
                ·
                  refine ⟨167223989575181766235637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111482659716787844157091 167223989575181766235637)
                  ·
                    refine ⟨15677249022673290584591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 167223989575181766235637 15677249022673290584591)
                    ·
                      rfl

theorem cell23_91594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_91594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91594 prefixEnd_91594 := by exact prefixLift 91594
  have htrace : WordTrace (prefixWord ++ tailWord_91594) baseStart_91594 baseEnd_91594 := by
    simpa [prefixWord, tailWord_91594, baseEnd_91594] using wordTrace_append hprefix tailTrace_91594
  have hstable : (prefixWord ++ tailWord_91594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91594).length < 2 ^ (prefixWord ++ tailWord_91594).sum := by decide
  have hdescent : baseEnd_91594 < baseStart_91594 := by decide
  rcases family_descends (prefixWord ++ tailWord_91594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91600 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_91600 : Nat := 118140960795 + 91600 * 2 ^ 59
def prefixEnd_91600 : Nat := 4983230072969 + 3 ^ 40 * 91600 * 2
def baseEnd_91600 : Nat := 47034827951946848278745

theorem tailTrace_91600 : CollatzResearch.WordTrace tailWord_91600 prefixEnd_91600 47034827951946848278745 := by
  unfold tailWord_91600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670463234078159439812127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2227284312104212586416169 1670463234078159439812127)
  ·
    refine ⟨2505694851117239159718191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670463234078159439812127 2505694851117239159718191)
    ·
      refine ⟨3758542276675858739577287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505694851117239159718191 3758542276675858739577287)
      ·
        refine ⟨5637813415013788109365931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758542276675858739577287 5637813415013788109365931)
        ·
          refine ⟨8456720122520682164048897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637813415013788109365931 8456720122520682164048897)
          ·
            refine ⟨6342540091890511623036673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8456720122520682164048897 6342540091890511623036673)
            ·
              refine ⟨4756905068917883717277505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6342540091890511623036673 4756905068917883717277505)
              ·
                refine ⟨3567678801688412787958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756905068917883717277505 3567678801688412787958129)
                ·
                  refine ⟨2675759101266309590968597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567678801688412787958129 2675759101266309590968597)
                  ·
                    refine ⟨125426207871858262076653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2675759101266309590968597 125426207871858262076653)
                    ·
                      refine ⟨47034827951946848278745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125426207871858262076653 47034827951946848278745)
                      ·
                        rfl

theorem cell23_91600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_91600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91600 prefixEnd_91600 := by exact prefixLift 91600
  have htrace : WordTrace (prefixWord ++ tailWord_91600) baseStart_91600 baseEnd_91600 := by
    simpa [prefixWord, tailWord_91600, baseEnd_91600] using wordTrace_append hprefix tailTrace_91600
  have hstable : (prefixWord ++ tailWord_91600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91600).length < 2 ^ (prefixWord ++ tailWord_91600).sum := by decide
  have hdescent : baseEnd_91600 < baseStart_91600 := by decide
  rcases family_descends (prefixWord ++ tailWord_91600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91617 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_91617 : Nat := 118140960795 + 91617 * 2 ^ 59
def prefixEnd_91617 : Nat := 4983230072969 + 3 ^ 40 * 91617 * 2
def baseEnd_91617 : Nat := 47043557123073281766167

theorem tailTrace_91617 : CollatzResearch.WordTrace tailWord_91617 prefixEnd_91617 47043557123073281766167 := by
  unfold tailWord_91617
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341546509094730782993105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2227697672729820521995403 3341546509094730782993105)
  ·
    refine ⟨2506159881821048087244829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3341546509094730782993105 2506159881821048087244829)
    ·
      refine ⟨939809955682893032716811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2506159881821048087244829 939809955682893032716811)
      ·
        refine ⟨1409714933524339549075217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939809955682893032716811 1409714933524339549075217)
        ·
          refine ⟨1057286200143254661806413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409714933524339549075217 1057286200143254661806413)
          ·
            refine ⟨396482325053720498177405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1057286200143254661806413 396482325053720498177405)
            ·
              refine ⟨148680871895145186816527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396482325053720498177405 148680871895145186816527)
              ·
                refine ⟨223021307842717780224791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148680871895145186816527 223021307842717780224791)
                ·
                  refine ⟨334531961764076670337187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223021307842717780224791 334531961764076670337187)
                  ·
                    refine ⟨501797942646115005505781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 334531961764076670337187 501797942646115005505781)
                    ·
                      refine ⟨47043557123073281766167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 501797942646115005505781 47043557123073281766167)
                      ·
                        rfl

theorem cell23_91617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_91617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91617 prefixEnd_91617 := by exact prefixLift 91617
  have htrace : WordTrace (prefixWord ++ tailWord_91617) baseStart_91617 baseEnd_91617 := by
    simpa [prefixWord, tailWord_91617, baseEnd_91617] using wordTrace_append hprefix tailTrace_91617
  have hstable : (prefixWord ++ tailWord_91617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91617).length < 2 ^ (prefixWord ++ tailWord_91617).sum := by decide
  have hdescent : baseEnd_91617 < baseStart_91617 := by decide
  rcases family_descends (prefixWord ++ tailWord_91617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91624 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_91624 : Nat := 118140960795 + 91624 * 2 ^ 59
def prefixEnd_91624 : Nat := 4983230072969 + 3 ^ 40 * 91624 * 2
def baseEnd_91624 : Nat := 15682383829218251459545

theorem tailTrace_91624 : CollatzResearch.WordTrace tailWord_91624 prefixEnd_91624 15682383829218251459545 := by
  unfold tailWord_91624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670900910034685489248963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2227867880046247318998617 1670900910034685489248963)
  ·
    refine ⟨2506351365052028233873445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670900910034685489248963 2506351365052028233873445)
    ·
      refine ⟨469940880947255293851271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2506351365052028233873445 469940880947255293851271)
      ·
        refine ⟨704911321420882940776907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469940880947255293851271 704911321420882940776907)
        ·
          refine ⟨1057366982131324411165361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704911321420882940776907 1057366982131324411165361)
          ·
            refine ⟨793025236598493308374021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057366982131324411165361 793025236598493308374021)
            ·
              refine ⟨148692231862217495320129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 793025236598493308374021 148692231862217495320129)
              ·
                refine ⟨111519173896663121490097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148692231862217495320129 111519173896663121490097)
                ·
                  refine ⟨83639380422497341117573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111519173896663121490097 83639380422497341117573)
                  ·
                    refine ⟨15682383829218251459545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83639380422497341117573 15682383829218251459545)
                    ·
                      rfl

theorem cell23_91624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_91624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91624 prefixEnd_91624 := by exact prefixLift 91624
  have htrace : WordTrace (prefixWord ++ tailWord_91624) baseStart_91624 baseEnd_91624 := by
    simpa [prefixWord, tailWord_91624, baseEnd_91624] using wordTrace_append hprefix tailTrace_91624
  have hstable : (prefixWord ++ tailWord_91624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91624).length < 2 ^ (prefixWord ++ tailWord_91624).sum := by decide
  have hdescent : baseEnd_91624 < baseStart_91624 := by decide
  rcases family_descends (prefixWord ++ tailWord_91624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91634 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_91634 : Nat := 118140960795 + 91634 * 2 ^ 59
def prefixEnd_91634 : Nat := 4983230072969 + 3 ^ 40 * 91634 * 2
def baseEnd_91634 : Nat := 47052286294199715253589

theorem tailTrace_91634 : CollatzResearch.WordTrace tailWord_91634 prefixEnd_91634 47052286294199715253589 := by
  unfold tailWord_91634
  simp only [CollatzResearch.WordTrace]
  refine ⟨835541637508285671590489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2228111033355428457574637 835541637508285671590489)
  ·
    refine ⟨626656228131214253692867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835541637508285671590489 626656228131214253692867)
    ·
      refine ⟨939984342196821380539301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626656228131214253692867 939984342196821380539301)
      ·
        refine ⟨176247064161904008851119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 939984342196821380539301 176247064161904008851119)
        ·
          refine ⟨264370596242856013276679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176247064161904008851119 264370596242856013276679)
          ·
            refine ⟨396555894364284019915019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264370596242856013276679 396555894364284019915019)
            ·
              refine ⟨594833841546426029872529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396555894364284019915019 594833841546426029872529)
              ·
                refine ⟨446125381159819522404397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594833841546426029872529 446125381159819522404397)
                ·
                  refine ⟨167297017934932320901649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446125381159819522404397 167297017934932320901649)
                  ·
                    refine ⟨125472763451199240676237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167297017934932320901649 125472763451199240676237)
                    ·
                      refine ⟨47052286294199715253589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125472763451199240676237 47052286294199715253589)
                      ·
                        rfl

theorem cell23_91634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_91634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91634 prefixEnd_91634 := by exact prefixLift 91634
  have htrace : WordTrace (prefixWord ++ tailWord_91634) baseStart_91634 baseEnd_91634 := by
    simpa [prefixWord, tailWord_91634, baseEnd_91634] using wordTrace_append hprefix tailTrace_91634
  have hstable : (prefixWord ++ tailWord_91634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91634).length < 2 ^ (prefixWord ++ tailWord_91634).sum := by decide
  have hdescent : baseEnd_91634 < baseStart_91634 := by decide
  rcases family_descends (prefixWord ++ tailWord_91634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91668 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_91668 : Nat := 118140960795 + 91668 * 2 ^ 59
def prefixEnd_91668 : Nat := 4983230072969 + 3 ^ 40 * 91668 * 2
def baseEnd_91668 : Nat := 47069744636452582228433

theorem tailTrace_91668 : CollatzResearch.WordTrace tailWord_91668 prefixEnd_91668 47069744636452582228433 := by
  unfold tailWord_91668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671703315954983246549829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2228937754606644328733105 1671703315954983246549829)
  ·
    refine ⟨313444371741559358728093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1671703315954983246549829 313444371741559358728093)
    ·
      refine ⟨117541639403084759523035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313444371741559358728093 117541639403084759523035)
      ·
        refine ⟨176312459104627139284553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117541639403084759523035 176312459104627139284553)
        ·
          refine ⟨132234344328470354463415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176312459104627139284553 132234344328470354463415)
          ·
            refine ⟨198351516492705531695123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132234344328470354463415 198351516492705531695123)
            ·
              refine ⟨297527274739058297542685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198351516492705531695123 297527274739058297542685)
              ·
                refine ⟨111572728027146861578507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297527274739058297542685 111572728027146861578507)
                ·
                  refine ⟨167359092040720292367761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111572728027146861578507 167359092040720292367761)
                  ·
                    refine ⟨125519319030540219275821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167359092040720292367761 125519319030540219275821)
                    ·
                      refine ⟨47069744636452582228433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125519319030540219275821 47069744636452582228433)
                      ·
                        rfl

theorem cell23_91668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_91668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91668 prefixEnd_91668 := by exact prefixLift 91668
  have htrace : WordTrace (prefixWord ++ tailWord_91668) baseStart_91668 baseEnd_91668 := by
    simpa [prefixWord, tailWord_91668, baseEnd_91668] using wordTrace_append hprefix tailTrace_91668
  have hstable : (prefixWord ++ tailWord_91668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91668).length < 2 ^ (prefixWord ++ tailWord_91668).sum := by decide
  have hdescent : baseEnd_91668 < baseStart_91668 := by decide
  rcases family_descends (prefixWord ++ tailWord_91668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91681 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_91681 : Nat := 118140960795 + 91681 * 2 ^ 59
def prefixEnd_91681 : Nat := 4983230072969 + 3 ^ 40 * 91681 * 2
def baseEnd_91681 : Nat := 47076419884961031365873

theorem tailTrace_91681 : CollatzResearch.WordTrace tailWord_91681 prefixEnd_91681 47076419884961031365873 := by
  unfold tailWord_91681
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343880780862869713322897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2229253853908579808881931 3343880780862869713322897)
  ·
    refine ⟨2507910585647152284992173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3343880780862869713322897 2507910585647152284992173)
    ·
      refine ⟨940466469617682106872065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2507910585647152284992173 940466469617682106872065)
      ·
        refine ⟨705349852213261580154049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 940466469617682106872065 705349852213261580154049)
        ·
          refine ⟨529012389159946185115537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705349852213261580154049 529012389159946185115537)
          ·
            refine ⟨396759291869959638836653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529012389159946185115537 396759291869959638836653)
            ·
              refine ⟨148784734451234864563745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396759291869959638836653 148784734451234864563745)
              ·
                refine ⟨111588550838426148422809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148784734451234864563745 111588550838426148422809)
                ·
                  refine ⟨83691413128819611317107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111588550838426148422809 83691413128819611317107)
                  ·
                    refine ⟨125537119693229416975661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83691413128819611317107 125537119693229416975661)
                    ·
                      refine ⟨47076419884961031365873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125537119693229416975661 47076419884961031365873)
                      ·
                        rfl

theorem cell23_91681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_91681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91681 prefixEnd_91681 := by exact prefixLift 91681
  have htrace : WordTrace (prefixWord ++ tailWord_91681) baseStart_91681 baseEnd_91681 := by
    simpa [prefixWord, tailWord_91681, baseEnd_91681] using wordTrace_append hprefix tailTrace_91681
  have hstable : (prefixWord ++ tailWord_91681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91681).length < 2 ^ (prefixWord ++ tailWord_91681).sum := by decide
  have hdescent : baseEnd_91681 < baseStart_91681 := by decide
  rcases family_descends (prefixWord ++ tailWord_91681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91708 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_91708 : Nat := 118140960795 + 91708 * 2 ^ 59
def prefixEnd_91708 : Nat := 4983230072969 + 3 ^ 40 * 91708 * 2
def baseEnd_91708 : Nat := 47090283862632425728249

theorem tailTrace_91708 : CollatzResearch.WordTrace tailWord_91708 prefixEnd_91708 47090283862632425728249 := by
  unfold tailWord_91708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1672432775882526662277889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2229910367843368883037185 1672432775882526662277889)
  ·
    refine ⟨1254324581911894996708417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1672432775882526662277889 1254324581911894996708417)
    ·
      refine ⟨940743436433921247531313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1254324581911894996708417 940743436433921247531313)
      ·
        refine ⟨705557577325440935648485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 940743436433921247531313 705557577325440935648485)
        ·
          refine ⟨132292045748520175434091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 705557577325440935648485 132292045748520175434091)
          ·
            refine ⟨198438068622780263151137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132292045748520175434091 198438068622780263151137)
            ·
              refine ⟨148828551467085197363353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198438068622780263151137 148828551467085197363353)
              ·
                refine ⟨111621413600313898022515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148828551467085197363353 111621413600313898022515)
                ·
                  refine ⟨167432120400470847033773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111621413600313898022515 167432120400470847033773)
                  ·
                    refine ⟨62787045150176567637665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167432120400470847033773 62787045150176567637665)
                    ·
                      refine ⟨47090283862632425728249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62787045150176567637665 47090283862632425728249)
                      ·
                        rfl

theorem cell23_91708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_91708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91708 prefixEnd_91708 := by exact prefixLift 91708
  have htrace : WordTrace (prefixWord ++ tailWord_91708) baseStart_91708 baseEnd_91708 := by
    simpa [prefixWord, tailWord_91708, baseEnd_91708] using wordTrace_append hprefix tailTrace_91708
  have hstable : (prefixWord ++ tailWord_91708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91708).length < 2 ^ (prefixWord ++ tailWord_91708).sum := by decide
  have hdescent : baseEnd_91708 < baseStart_91708 := by decide
  rcases family_descends (prefixWord ++ tailWord_91708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91737 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_91737 : Nat := 118140960795 + 91737 * 2 ^ 59
def prefixEnd_91737 : Nat := 4983230072969 + 3 ^ 40 * 91737 * 2
def baseEnd_91737 : Nat := 47105174801612812265615

theorem tailTrace_91737 : CollatzResearch.WordTrace tailWord_91737 prefixEnd_91737 47105174801612812265615 := by
  unfold tailWord_91737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345923268659991277361465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2230615512439994184907643 3345923268659991277361465)
  ·
    refine ⟨2509442451494993458021099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3345923268659991277361465 2509442451494993458021099)
    ·
      refine ⟨3764163677242490187031649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2509442451494993458021099 3764163677242490187031649)
      ·
        refine ⟨2823122757931867640273737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3764163677242490187031649 2823122757931867640273737)
        ·
          refine ⟨2117342068448900730205303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2823122757931867640273737 2117342068448900730205303)
          ·
            refine ⟨3176013102673351095307955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117342068448900730205303 3176013102673351095307955)
            ·
              refine ⟨4764019654010026642961933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176013102673351095307955 4764019654010026642961933)
              ·
                refine ⟨1786507370253759991110725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4764019654010026642961933 1786507370253759991110725)
                ·
                  refine ⟨334970131922579998333261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786507370253759991110725 334970131922579998333261)
                  ·
                    refine ⟨125613799470967499374973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334970131922579998333261 125613799470967499374973)
                    ·
                      refine ⟨47105174801612812265615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125613799470967499374973 47105174801612812265615)
                      ·
                        rfl

theorem cell23_91737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_91737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91737 prefixEnd_91737 := by exact prefixLift 91737
  have htrace : WordTrace (prefixWord ++ tailWord_91737) baseStart_91737 baseEnd_91737 := by
    simpa [prefixWord, tailWord_91737, baseEnd_91737] using wordTrace_append hprefix tailTrace_91737
  have hstable : (prefixWord ++ tailWord_91737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91737).length < 2 ^ (prefixWord ++ tailWord_91737).sum := by decide
  have hdescent : baseEnd_91737 < baseStart_91737 := by decide
  rcases family_descends (prefixWord ++ tailWord_91737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91821 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_91821 : Nat := 118140960795 + 91821 * 2 ^ 59
def prefixEnd_91821 : Nat := 4983230072969 + 3 ^ 40 * 91821 * 2
def baseEnd_91821 : Nat := 15716102392196827871743

theorem tailTrace_91821 : CollatzResearch.WordTrace tailWord_91821 prefixEnd_91821 15716102392196827871743 := by
  unfold tailWord_91821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348987000355673623419317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2232658000237115748946211 3348987000355673623419317)
  ·
    refine ⟨313967531283344402195561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3348987000355673623419317 313967531283344402195561)
    ·
      refine ⟨235475648462508301646671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313967531283344402195561 235475648462508301646671)
      ·
        refine ⟨353213472693762452470007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235475648462508301646671 353213472693762452470007)
        ·
          refine ⟨529820209040643678705011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353213472693762452470007 529820209040643678705011)
          ·
            refine ⟨794730313560965518057517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529820209040643678705011 794730313560965518057517)
            ·
              refine ⟨298023867585362069271569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 794730313560965518057517 298023867585362069271569)
              ·
                refine ⟨223517900689021551953677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298023867585362069271569 223517900689021551953677)
                ·
                  refine ⟨83819212758383081982629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223517900689021551953677 83819212758383081982629)
                  ·
                    refine ⟨15716102392196827871743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83819212758383081982629 15716102392196827871743)
                    ·
                      rfl

theorem cell23_91821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_91821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91821 prefixEnd_91821 := by exact prefixLift 91821
  have htrace : WordTrace (prefixWord ++ tailWord_91821) baseStart_91821 baseEnd_91821 := by
    simpa [prefixWord, tailWord_91821, baseEnd_91821] using wordTrace_append hprefix tailTrace_91821
  have hstable : (prefixWord ++ tailWord_91821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91821).length < 2 ^ (prefixWord ++ tailWord_91821).sum := by decide
  have hdescent : baseEnd_91821 < baseStart_91821 := by decide
  rcases family_descends (prefixWord ++ tailWord_91821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91831 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_91831 : Nat := 118140960795 + 91831 * 2 ^ 59
def prefixEnd_91831 : Nat := 4983230072969 + 3 ^ 40 * 91831 * 2
def baseEnd_91831 : Nat := 47153441983135444490183

theorem tailTrace_91831 : CollatzResearch.WordTrace tailWord_91831 prefixEnd_91831 47153441983135444490183 := by
  unfold tailWord_91831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349351730319445331283347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2232901153546296887522231 3349351730319445331283347)
  ·
    refine ⟨5024027595479167996925021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349351730319445331283347 5024027595479167996925021)
    ·
      refine ⟨1884010348304687998846883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5024027595479167996925021 1884010348304687998846883)
      ·
        refine ⟨2826015522457031998270325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884010348304687998846883 2826015522457031998270325)
        ·
          refine ⟨264938955230346749837843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2826015522457031998270325 264938955230346749837843)
          ·
            refine ⟨397408432845520124756765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264938955230346749837843 397408432845520124756765)
            ·
              refine ⟨149028162317070046783787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397408432845520124756765 149028162317070046783787)
              ·
                refine ⟨223542243475605070175681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149028162317070046783787 223542243475605070175681)
                ·
                  refine ⟨167656682606703802631761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223542243475605070175681 167656682606703802631761)
                  ·
                    refine ⟨125742511955027851973821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167656682606703802631761 125742511955027851973821)
                    ·
                      refine ⟨47153441983135444490183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125742511955027851973821 47153441983135444490183)
                      ·
                        rfl

theorem cell23_91831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_91831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91831 prefixEnd_91831 := by exact prefixLift 91831
  have htrace : WordTrace (prefixWord ++ tailWord_91831) baseStart_91831 baseEnd_91831 := by
    simpa [prefixWord, tailWord_91831, baseEnd_91831] using wordTrace_append hprefix tailTrace_91831
  have hstable : (prefixWord ++ tailWord_91831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91831).length < 2 ^ (prefixWord ++ tailWord_91831).sum := by decide
  have hdescent : baseEnd_91831 < baseStart_91831 := by decide
  rcases family_descends (prefixWord ++ tailWord_91831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91838 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_91838 : Nat := 118140960795 + 91838 * 2 ^ 59
def prefixEnd_91838 : Nat := 4983230072969 + 3 ^ 40 * 91838 * 2
def baseEnd_91838 : Nat := 15719012115905639034217

theorem tailTrace_91838 : CollatzResearch.WordTrace tailWord_91838 prefixEnd_91838 15719012115905639034217 := by
  unfold tailWord_91838
  simp only [CollatzResearch.WordTrace]
  refine ⟨418700880161760690848521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2233071360862723684525445 418700880161760690848521)
  ·
    refine ⟨314025660121320518136391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 418700880161760690848521 314025660121320518136391)
    ·
      refine ⟨471038490181980777204587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314025660121320518136391 471038490181980777204587)
      ·
        refine ⟨706557735272971165806881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471038490181980777204587 706557735272971165806881)
        ·
          refine ⟨529918301454728374355161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706557735272971165806881 529918301454728374355161)
          ·
            refine ⟨397438726091046280766371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529918301454728374355161 397438726091046280766371)
            ·
              refine ⟨596158089136569421149557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397438726091046280766371 596158089136569421149557)
              ·
                refine ⟨55889820856553383232771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 596158089136569421149557 55889820856553383232771)
                ·
                  refine ⟨83834731284830074849157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55889820856553383232771 83834731284830074849157)
                  ·
                    refine ⟨15719012115905639034217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83834731284830074849157 15719012115905639034217)
                    ·
                      rfl

theorem cell23_91838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_91838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91838 prefixEnd_91838 := by exact prefixLift 91838
  have htrace : WordTrace (prefixWord ++ tailWord_91838) baseStart_91838 baseEnd_91838 := by
    simpa [prefixWord, tailWord_91838, baseEnd_91838] using wordTrace_append hprefix tailTrace_91838
  have hstable : (prefixWord ++ tailWord_91838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91838).length < 2 ^ (prefixWord ++ tailWord_91838).sum := by decide
  have hdescent : baseEnd_91838 < baseStart_91838 := by decide
  rcases family_descends (prefixWord ++ tailWord_91838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91884 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_91884 : Nat := 118140960795 + 91884 * 2 ^ 59
def prefixEnd_91884 : Nat := 4983230072969 + 3 ^ 40 * 91884 * 2
def baseEnd_91884 : Nat := 47180656457823737127439

theorem tailTrace_91884 : CollatzResearch.WordTrace tailWord_91884 prefixEnd_91884 47180656457823737127439 := by
  unfold tailWord_91884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675642399563717691481353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2234189866084956921975137 1675642399563717691481353)
  ·
    refine ⟨1256731799672788268611015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1675642399563717691481353 1256731799672788268611015)
    ·
      refine ⟨1885097699509182402916523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256731799672788268611015 1885097699509182402916523)
      ·
        refine ⟨2827646549263773604374785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885097699509182402916523 2827646549263773604374785)
        ·
          refine ⟨2120734911947830203281089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827646549263773604374785 2120734911947830203281089)
          ·
            refine ⟨1590551183960872652460817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120734911947830203281089 1590551183960872652460817)
            ·
              refine ⟨1192913387970654489345613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590551183960872652460817 1192913387970654489345613)
              ·
                refine ⟨447342520488995433504605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192913387970654489345613 447342520488995433504605)
                ·
                  refine ⟨167753445183373287564227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 447342520488995433504605 167753445183373287564227)
                  ·
                    refine ⟨251630167775059931346341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167753445183373287564227 251630167775059931346341)
                    ·
                      refine ⟨47180656457823737127439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 251630167775059931346341 47180656457823737127439)
                      ·
                        rfl

theorem cell23_91884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_91884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91884 prefixEnd_91884 := by exact prefixLift 91884
  have htrace : WordTrace (prefixWord ++ tailWord_91884) baseStart_91884 baseEnd_91884 := by
    simpa [prefixWord, tailWord_91884, baseEnd_91884] using wordTrace_append hprefix tailTrace_91884
  have hstable : (prefixWord ++ tailWord_91884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91884).length < 2 ^ (prefixWord ++ tailWord_91884).sum := by decide
  have hdescent : baseEnd_91884 < baseStart_91884 := by decide
  rcases family_descends (prefixWord ++ tailWord_91884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91907 : List Nat := [1, 1, 1, 3, 2, 2, 13]
def baseStart_91907 : Nat := 118140960795 + 91907 * 2 ^ 59
def prefixEnd_91907 : Nat := 4983230072969 + 3 ^ 40 * 91907 * 2
def baseEnd_91907 : Nat := 582623043368853668393

theorem tailTrace_91907 : CollatzResearch.WordTrace tailWord_91907 prefixEnd_91907 582623043368853668393 := by
  unfold tailWord_91907
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352123678044110311049975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2234749118696073540699983 3352123678044110311049975)
  ·
    refine ⟨5028185517066165466574963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352123678044110311049975 5028185517066165466574963)
    ·
      refine ⟨7542278275599248199862445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028185517066165466574963 7542278275599248199862445)
      ·
        refine ⟨2828354353349718074948417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7542278275599248199862445 2828354353349718074948417)
        ·
          refine ⟨2121265765012288556211313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828354353349718074948417 2121265765012288556211313)
          ·
            refine ⟨1590949323759216417158485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121265765012288556211313 1590949323759216417158485)
            ·
              refine ⟨582623043368853668393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 1590949323759216417158485 582623043368853668393)
              ·
                rfl

theorem cell23_91907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 13].length) (baseStart_91907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91907 prefixEnd_91907 := by exact prefixLift 91907
  have htrace : WordTrace (prefixWord ++ tailWord_91907) baseStart_91907 baseEnd_91907 := by
    simpa [prefixWord, tailWord_91907, baseEnd_91907] using wordTrace_append hprefix tailTrace_91907
  have hstable : (prefixWord ++ tailWord_91907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91907).length < 2 ^ (prefixWord ++ tailWord_91907).sum := by decide
  have hdescent : baseEnd_91907 < baseStart_91907 := by decide
  rcases family_descends (prefixWord ++ tailWord_91907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91914 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_91914 : Nat := 118140960795 + 91914 * 2 ^ 59
def prefixEnd_91914 : Nat := 4983230072969 + 3 ^ 40 * 91914 * 2
def baseEnd_91914 : Nat := 47196060877458619752301

theorem tailTrace_91914 : CollatzResearch.WordTrace tailWord_91914 prefixEnd_91914 47196060877458619752301 := by
  unfold tailWord_91914
  simp only [CollatzResearch.WordTrace]
  refine ⟨838094747254687626638699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2234919326012500337703197 838094747254687626638699)
  ·
    refine ⟨1257142120882031439958049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 838094747254687626638699 1257142120882031439958049)
    ·
      refine ⟨942856590661523579968537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1257142120882031439958049 942856590661523579968537)
      ·
        refine ⟨707142442996142684976403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942856590661523579968537 707142442996142684976403)
        ·
          refine ⟨1060713664494214027464605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707142442996142684976403 1060713664494214027464605)
          ·
            refine ⟨397767624185330260299227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060713664494214027464605 397767624185330260299227)
            ·
              refine ⟨596651436277995390448841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397767624185330260299227 596651436277995390448841)
              ·
                refine ⟨447488577208496542836631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596651436277995390448841 447488577208496542836631)
                ·
                  refine ⟨671232865812744814254947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447488577208496542836631 671232865812744814254947)
                  ·
                    refine ⟨1006849298719117221382421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671232865812744814254947 1006849298719117221382421)
                    ·
                      refine ⟨47196060877458619752301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1006849298719117221382421 47196060877458619752301)
                      ·
                        rfl

theorem cell23_91914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_91914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91914 prefixEnd_91914 := by exact prefixLift 91914
  have htrace : WordTrace (prefixWord ++ tailWord_91914) baseStart_91914 baseEnd_91914 := by
    simpa [prefixWord, tailWord_91914, baseEnd_91914] using wordTrace_append hprefix tailTrace_91914
  have hstable : (prefixWord ++ tailWord_91914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91914).length < 2 ^ (prefixWord ++ tailWord_91914).sum := by decide
  have hdescent : baseEnd_91914 < baseStart_91914 := by decide
  rcases family_descends (prefixWord ++ tailWord_91914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91928 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 2, 4]
def baseStart_91928 : Nat := 118140960795 + 91928 * 2 ^ 59
def prefixEnd_91928 : Nat := 4983230072969 + 3 ^ 40 * 91928 * 2
def baseEnd_91928 : Nat := 15734416535540521659079

theorem tailTrace_91928 : CollatzResearch.WordTrace tailWord_91928 prefixEnd_91928 15734416535540521659079 := by
  unfold tailWord_91928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676444805484015448782219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2235259740645353931709625 1676444805484015448782219)
  ·
    refine ⟨2514667208226023173173329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676444805484015448782219 2514667208226023173173329)
    ·
      refine ⟨1886000406169517379879997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2514667208226023173173329 1886000406169517379879997)
      ·
        refine ⟨707250152313569017454999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1886000406169517379879997 707250152313569017454999)
        ·
          refine ⟨1060875228470353526182499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707250152313569017454999 1060875228470353526182499)
          ·
            refine ⟨1591312842705530289273749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060875228470353526182499 1591312842705530289273749)
            ·
              refine ⟨74592789501821732309707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1591312842705530289273749 74592789501821732309707)
              ·
                refine ⟨111889184252732598464561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74592789501821732309707 111889184252732598464561)
                ·
                  refine ⟨83916888189549448848421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111889184252732598464561 83916888189549448848421)
                  ·
                    refine ⟨15734416535540521659079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83916888189549448848421 15734416535540521659079)
                    ·
                      rfl

theorem cell23_91928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_91928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91928 prefixEnd_91928 := by exact prefixLift 91928
  have htrace : WordTrace (prefixWord ++ tailWord_91928) baseStart_91928 baseEnd_91928 := by
    simpa [prefixWord, tailWord_91928, baseEnd_91928] using wordTrace_append hprefix tailTrace_91928
  have hstable : (prefixWord ++ tailWord_91928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91928).length < 2 ^ (prefixWord ++ tailWord_91928).sum := by decide
  have hdescent : baseEnd_91928 < baseStart_91928 := by decide
  rcases family_descends (prefixWord ++ tailWord_91928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91955 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 1, 2, 3]
def baseStart_91955 : Nat := 118140960795 + 91955 * 2 ^ 59
def prefixEnd_91955 : Nat := 4983230072969 + 3 ^ 40 * 91955 * 2
def baseEnd_91955 : Nat := 47217113584292959339613

theorem tailTrace_91955 : CollatzResearch.WordTrace tailWord_91955 prefixEnd_91955 47217113584292959339613 := by
  unfold tailWord_91955
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353874381870214508797319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2235916254580143005864879 3353874381870214508797319)
  ·
    refine ⟨5030811572805321763195979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353874381870214508797319 5030811572805321763195979)
    ·
      refine ⟨7546217359207982644793969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030811572805321763195979 7546217359207982644793969)
      ·
        refine ⟨5659663019405986983595477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546217359207982644793969 5659663019405986983595477)
        ·
          refine ⟨132648352017327819928019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5659663019405986983595477 132648352017327819928019)
          ·
            refine ⟨198972528025991729892029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132648352017327819928019 198972528025991729892029)
            ·
              refine ⟨74614698009746898709511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198972528025991729892029 74614698009746898709511)
              ·
                refine ⟨111922047014620348064267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74614698009746898709511 111922047014620348064267)
                ·
                  refine ⟨167883070521930522096401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111922047014620348064267 167883070521930522096401)
                  ·
                    refine ⟨125912302891447891572301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167883070521930522096401 125912302891447891572301)
                    ·
                      refine ⟨47217113584292959339613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 125912302891447891572301 47217113584292959339613)
                      ·
                        rfl

theorem cell23_91955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 2, 3].length) (baseStart_91955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91955 prefixEnd_91955 := by exact prefixLift 91955
  have htrace : WordTrace (prefixWord ++ tailWord_91955) baseStart_91955 baseEnd_91955 := by
    simpa [prefixWord, tailWord_91955, baseEnd_91955] using wordTrace_append hprefix tailTrace_91955
  have hstable : (prefixWord ++ tailWord_91955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91955).length < 2 ^ (prefixWord ++ tailWord_91955).sum := by decide
  have hdescent : baseEnd_91955 < baseStart_91955 := by decide
  rcases family_descends (prefixWord ++ tailWord_91955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91964 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_91964 : Nat := 118140960795 + 91964 * 2 ^ 59
def prefixEnd_91964 : Nat := 4983230072969 + 3 ^ 40 * 91964 * 2
def baseEnd_91964 : Nat := 47221734910183424127071

theorem tailTrace_91964 : CollatzResearch.WordTrace tailWord_91964 prefixEnd_91964 47221734910183424127071 := by
  unfold tailWord_91964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677101319418804522937473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2236135092558406030583297 1677101319418804522937473)
  ·
    refine ⟨1257825989564103392203105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1677101319418804522937473 1257825989564103392203105)
    ·
      refine ⟨943369492173077544152329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1257825989564103392203105 943369492173077544152329)
      ·
        refine ⟨707527119129808158114247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943369492173077544152329 707527119129808158114247)
        ·
          refine ⟨1061290678694712237171371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707527119129808158114247 1061290678694712237171371)
          ·
            refine ⟨1591936018042068355757057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061290678694712237171371 1591936018042068355757057)
            ·
              refine ⟨1193952013531551266817793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591936018042068355757057 1193952013531551266817793)
              ·
                refine ⟨895464010148663450113345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193952013531551266817793 895464010148663450113345)
                ·
                  refine ⟨671598007611497587585009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 895464010148663450113345 671598007611497587585009)
                  ·
                    refine ⟨503698505708623190688757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 671598007611497587585009 503698505708623190688757)
                    ·
                      refine ⟨47221734910183424127071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 503698505708623190688757 47221734910183424127071)
                      ·
                        rfl

theorem cell23_91964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_91964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_91964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_91964 prefixEnd_91964 := by exact prefixLift 91964
  have htrace : WordTrace (prefixWord ++ tailWord_91964) baseStart_91964 baseEnd_91964 := by
    simpa [prefixWord, tailWord_91964, baseEnd_91964] using wordTrace_append hprefix tailTrace_91964
  have hstable : (prefixWord ++ tailWord_91964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91964).length < 2 ^ (prefixWord ++ tailWord_91964).sum := by decide
  have hdescent : baseEnd_91964 < baseStart_91964 := by decide
  rcases family_descends (prefixWord ++ tailWord_91964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92008 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_92008 : Nat := 118140960795 + 92008 * 2 ^ 59
def prefixEnd_92008 : Nat := 4983230072969 + 3 ^ 40 * 92008 * 2
def baseEnd_92008 : Nat := 47244328058981251976869

theorem tailTrace_92008 : CollatzResearch.WordTrace tailWord_92008 prefixEnd_92008 47244328058981251976869 := by
  unfold tailWord_92008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677903725339102280238339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2237204967118803040317785 1677903725339102280238339)
  ·
    refine ⟨2516855588008653420357509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677903725339102280238339 2516855588008653420357509)
    ·
      refine ⟨471910422751622516317033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2516855588008653420357509 471910422751622516317033)
      ·
        refine ⟨353932817063716887237775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471910422751622516317033 353932817063716887237775)
        ·
          refine ⟨530899225595575330856663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353932817063716887237775 530899225595575330856663)
          ·
            refine ⟨796348838393362996284995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530899225595575330856663 796348838393362996284995)
            ·
              refine ⟨1194523257590044494427493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796348838393362996284995 1194523257590044494427493)
              ·
                refine ⟨223973110798133342705155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1194523257590044494427493 223973110798133342705155)
                ·
                  refine ⟨335959666197200014057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223973110798133342705155 335959666197200014057733)
                  ·
                    refine ⟨62992437411975002635825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335959666197200014057733 62992437411975002635825)
                    ·
                      refine ⟨47244328058981251976869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62992437411975002635825 47244328058981251976869)
                      ·
                        rfl

theorem cell23_92008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_92008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92008 prefixEnd_92008 := by exact prefixLift 92008
  have htrace : WordTrace (prefixWord ++ tailWord_92008) baseStart_92008 baseEnd_92008 := by
    simpa [prefixWord, tailWord_92008, baseEnd_92008] using wordTrace_append hprefix tailTrace_92008
  have hstable : (prefixWord ++ tailWord_92008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92008).length < 2 ^ (prefixWord ++ tailWord_92008).sum := by decide
  have hdescent : baseEnd_92008 < baseStart_92008 := by decide
  rcases family_descends (prefixWord ++ tailWord_92008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92012 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_92012 : Nat := 118140960795 + 92012 * 2 ^ 59
def prefixEnd_92012 : Nat := 4983230072969 + 3 ^ 40 * 92012 * 2
def baseEnd_92012 : Nat := 47246381981599236326851

theorem tailTrace_92012 : CollatzResearch.WordTrace tailWord_92012 prefixEnd_92012 47246381981599236326851 := by
  unfold tailWord_92012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677976671331856621811145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2237302228442475495748193 1677976671331856621811145)
  ·
    refine ⟨1258482503498892466358359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1677976671331856621811145 1258482503498892466358359)
    ·
      refine ⟨1887723755248338699537539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258482503498892466358359 1887723755248338699537539)
      ·
        refine ⟨2831585632872508049306309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887723755248338699537539 2831585632872508049306309)
        ·
          refine ⟨530922306163595259244933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2831585632872508049306309 530922306163595259244933)
          ·
            refine ⟨99547932405674111108425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 530922306163595259244933 99547932405674111108425)
            ·
              refine ⟨74660949304255583331319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99547932405674111108425 74660949304255583331319)
              ·
                refine ⟨111991423956383374996979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74660949304255583331319 111991423956383374996979)
                ·
                  refine ⟨167987135934575062495469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111991423956383374996979 167987135934575062495469)
                  ·
                    refine ⟨62995175975465648435801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167987135934575062495469 62995175975465648435801)
                    ·
                      refine ⟨47246381981599236326851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 62995175975465648435801 47246381981599236326851)
                      ·
                        rfl

theorem cell23_92012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_92012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92012 prefixEnd_92012 := by exact prefixLift 92012
  have htrace : WordTrace (prefixWord ++ tailWord_92012) baseStart_92012 baseEnd_92012 := by
    simpa [prefixWord, tailWord_92012, baseEnd_92012] using wordTrace_append hprefix tailTrace_92012
  have hstable : (prefixWord ++ tailWord_92012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92012).length < 2 ^ (prefixWord ++ tailWord_92012).sum := by decide
  have hdescent : baseEnd_92012 < baseStart_92012 := by decide
  rcases family_descends (prefixWord ++ tailWord_92012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92021 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_92021 : Nat := 118140960795 + 92021 * 2 ^ 59
def prefixEnd_92021 : Nat := 4983230072969 + 3 ^ 40 * 92021 * 2
def baseEnd_92021 : Nat := 47251003307489701114309

theorem tailTrace_92021 : CollatzResearch.WordTrace tailWord_92021 prefixEnd_92021 47251003307489701114309 := by
  unfold tailWord_92021
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356281599631107780699917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2237521066420738520466611 3356281599631107780699917)
  ·
    refine ⟨1258605599861665417762469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3356281599631107780699917 1258605599861665417762469)
    ·
      refine ⟨235988549974062265830463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1258605599861665417762469 235988549974062265830463)
      ·
        refine ⟨353982824961093398745695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235988549974062265830463 353982824961093398745695)
        ·
          refine ⟨530974237441640098118543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353982824961093398745695 530974237441640098118543)
          ·
            refine ⟨796461356162460147177815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530974237441640098118543 796461356162460147177815)
            ·
              refine ⟨1194692034243690220766723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796461356162460147177815 1194692034243690220766723)
              ·
                refine ⟨1792038051365535331150085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194692034243690220766723 1792038051365535331150085)
                ·
                  refine ⟨336007134631037874590641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792038051365535331150085 336007134631037874590641)
                  ·
                    refine ⟨252005350973278405942981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 336007134631037874590641 252005350973278405942981)
                    ·
                      refine ⟨47251003307489701114309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 252005350973278405942981 47251003307489701114309)
                      ·
                        rfl

theorem cell23_92021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_92021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92021 prefixEnd_92021 := by exact prefixLift 92021
  have htrace : WordTrace (prefixWord ++ tailWord_92021) baseStart_92021 baseEnd_92021 := by
    simpa [prefixWord, tailWord_92021, baseEnd_92021] using wordTrace_append hprefix tailTrace_92021
  have hstable : (prefixWord ++ tailWord_92021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92021).length < 2 ^ (prefixWord ++ tailWord_92021).sum := by decide
  have hdescent : baseEnd_92021 < baseStart_92021 := by decide
  rcases family_descends (prefixWord ++ tailWord_92021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92041 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_92041 : Nat := 118140960795 + 92041 * 2 ^ 59
def prefixEnd_92041 : Nat := 4983230072969 + 3 ^ 40 * 92041 * 2
def baseEnd_92041 : Nat := 47261272920579622864217

theorem tailTrace_92041 : CollatzResearch.WordTrace tailWord_92041 prefixEnd_92041 47261272920579622864217 := by
  unfold tailWord_92041
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357011059558651196427977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2238007373039100797618651 3357011059558651196427977)
  ·
    refine ⟨2517758294668988397320983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357011059558651196427977 2517758294668988397320983)
    ·
      refine ⟨3776637442003482595981475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517758294668988397320983 3776637442003482595981475)
      ·
        refine ⟨5664956163005223893972213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776637442003482595981475 5664956163005223893972213)
        ·
          refine ⟨531089640281739740059895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5664956163005223893972213 531089640281739740059895)
          ·
            refine ⟨796634460422609610089843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531089640281739740059895 796634460422609610089843)
            ·
              refine ⟨1194951690633914415134765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796634460422609610089843 1194951690633914415134765)
              ·
                refine ⟨448106883987717905675537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194951690633914415134765 448106883987717905675537)
                ·
                  refine ⟨336080162990788429256653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448106883987717905675537 336080162990788429256653)
                  ·
                    refine ⟨126030061121545660971245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336080162990788429256653 126030061121545660971245)
                    ·
                      refine ⟨47261272920579622864217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126030061121545660971245 47261272920579622864217)
                      ·
                        rfl

theorem cell23_92041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_92041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92041 prefixEnd_92041 := by exact prefixLift 92041
  have htrace : WordTrace (prefixWord ++ tailWord_92041) baseStart_92041 baseEnd_92041 := by
    simpa [prefixWord, tailWord_92041, baseEnd_92041] using wordTrace_append hprefix tailTrace_92041
  have hstable : (prefixWord ++ tailWord_92041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92041).length < 2 ^ (prefixWord ++ tailWord_92041).sum := by decide
  have hdescent : baseEnd_92041 < baseStart_92041 := by decide
  rcases family_descends (prefixWord ++ tailWord_92041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92042 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_92042 : Nat := 118140960795 + 92042 * 2 ^ 59
def prefixEnd_92042 : Nat := 4983230072969 + 3 ^ 40 * 92042 * 2
def baseEnd_92042 : Nat := 47261786401234118951713

theorem tailTrace_92042 : CollatzResearch.WordTrace tailWord_92042 prefixEnd_92042 47261786401234118951713 := by
  unfold tailWord_92042
  simp only [CollatzResearch.WordTrace]
  refine ⟨839261883138757091803595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2238031688370018911476253 839261883138757091803595)
  ·
    refine ⟨1258892824708135637705393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839261883138757091803595 1258892824708135637705393)
    ·
      refine ⟨944169618531101728279045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1258892824708135637705393 944169618531101728279045)
      ·
        refine ⟨177031803474581574052321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 944169618531101728279045 177031803474581574052321)
        ·
          refine ⟨132773852605936180539241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177031803474581574052321 132773852605936180539241)
          ·
            refine ⟨99580389454452135404431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132773852605936180539241 99580389454452135404431)
            ·
              refine ⟨149370584181678203106647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99580389454452135404431 149370584181678203106647)
              ·
                refine ⟨224055876272517304659971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149370584181678203106647 224055876272517304659971)
                ·
                  refine ⟨336083814408775956989957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224055876272517304659971 336083814408775956989957)
                  ·
                    refine ⟨63015715201645491935617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336083814408775956989957 63015715201645491935617)
                    ·
                      refine ⟨47261786401234118951713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63015715201645491935617 47261786401234118951713)
                      ·
                        rfl

theorem cell23_92042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_92042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92042 prefixEnd_92042 := by exact prefixLift 92042
  have htrace : WordTrace (prefixWord ++ tailWord_92042) baseStart_92042 baseEnd_92042 := by
    simpa [prefixWord, tailWord_92042, baseEnd_92042] using wordTrace_append hprefix tailTrace_92042
  have hstable : (prefixWord ++ tailWord_92042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92042).length < 2 ^ (prefixWord ++ tailWord_92042).sum := by decide
  have hdescent : baseEnd_92042 < baseStart_92042 := by decide
  rcases family_descends (prefixWord ++ tailWord_92042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92051 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 7, 2]
def baseStart_92051 : Nat := 118140960795 + 92051 * 2 ^ 59
def prefixEnd_92051 : Nat := 4983230072969 + 3 ^ 40 * 92051 * 2
def baseEnd_92051 : Nat := 47266407727124583739171

theorem tailTrace_92051 : CollatzResearch.WordTrace tailWord_92051 prefixEnd_92051 47266407727124583739171 := by
  unfold tailWord_92051
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357375789522422904292007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2238250526348281936194671 3357375789522422904292007)
  ·
    refine ⟨5036063684283634356438011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357375789522422904292007 5036063684283634356438011)
    ·
      refine ⟨7554095526425451534657017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5036063684283634356438011 7554095526425451534657017)
      ·
        refine ⟨5665571644819088650992763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7554095526425451534657017 5665571644819088650992763)
        ·
          refine ⟨8498357467228632976489145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665571644819088650992763 8498357467228632976489145)
          ·
            refine ⟨6373768100421474732366859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8498357467228632976489145 6373768100421474732366859)
            ·
              refine ⟨9560652150632212098550289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373768100421474732366859 9560652150632212098550289)
              ·
                refine ⟨7170489112974159073912717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9560652150632212098550289 7170489112974159073912717)
                ·
                  refine ⟨2688933417365309652717269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170489112974159073912717 2688933417365309652717269)
                  ·
                    refine ⟨63021876969499444985561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2688933417365309652717269 63021876969499444985561)
                    ·
                      refine ⟨47266407727124583739171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63021876969499444985561 47266407727124583739171)
                      ·
                        rfl

theorem cell23_92051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7, 2].length) (baseStart_92051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92051 prefixEnd_92051 := by exact prefixLift 92051
  have htrace : WordTrace (prefixWord ++ tailWord_92051) baseStart_92051 baseEnd_92051 := by
    simpa [prefixWord, tailWord_92051, baseEnd_92051] using wordTrace_append hprefix tailTrace_92051
  have hstable : (prefixWord ++ tailWord_92051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92051).length < 2 ^ (prefixWord ++ tailWord_92051).sum := by decide
  have hdescent : baseEnd_92051 < baseStart_92051 := by decide
  rcases family_descends (prefixWord ++ tailWord_92051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92061 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_92061 : Nat := 118140960795 + 92061 * 2 ^ 59
def prefixEnd_92061 : Nat := 4983230072969 + 3 ^ 40 * 92061 * 2
def baseEnd_92061 : Nat := 15757180844556514871375

theorem tailTrace_92061 : CollatzResearch.WordTrace tailWord_92061 prefixEnd_92061 15757180844556514871375 := by
  unfold tailWord_92061
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357740519486194612156037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2238493679657463074770691 3357740519486194612156037)
  ·
    refine ⟨629576347403661489779257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3357740519486194612156037 629576347403661489779257)
    ·
      refine ⟨472182260552746117334443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 629576347403661489779257 472182260552746117334443)
      ·
        refine ⟨708273390829119176001665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472182260552746117334443 708273390829119176001665)
        ·
          refine ⟨531205043121839382001249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708273390829119176001665 531205043121839382001249)
          ·
            refine ⟨398403782341379536500937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531205043121839382001249 398403782341379536500937)
            ·
              refine ⟨298802836756034652375703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398403782341379536500937 298802836756034652375703)
              ·
                refine ⟨448204255134051978563555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298802836756034652375703 448204255134051978563555)
                ·
                  refine ⟨672306382701077967845333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448204255134051978563555 672306382701077967845333)
                  ·
                    refine ⟨15757180844556514871375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 672306382701077967845333 15757180844556514871375)
                    ·
                      rfl

theorem cell23_92061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_92061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92061 prefixEnd_92061 := by exact prefixLift 92061
  have htrace : WordTrace (prefixWord ++ tailWord_92061) baseStart_92061 baseEnd_92061 := by
    simpa [prefixWord, tailWord_92061, baseEnd_92061] using wordTrace_append hprefix tailTrace_92061
  have hstable : (prefixWord ++ tailWord_92061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92061).length < 2 ^ (prefixWord ++ tailWord_92061).sum := by decide
  have hdescent : baseEnd_92061 < baseStart_92061 := by decide
  rcases family_descends (prefixWord ++ tailWord_92061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92101 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_92101 : Nat := 118140960795 + 92101 * 2 ^ 59
def prefixEnd_92101 : Nat := 4983230072969 + 3 ^ 40 * 92101 * 2
def baseEnd_92101 : Nat := 47292081759849388113941

theorem tailTrace_92101 : CollatzResearch.WordTrace tailWord_92101 prefixEnd_92101 47292081759849388113941 := by
  unfold tailWord_92101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359199439341281443612157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2239466292894187629074771 3359199439341281443612157)
  ·
    refine ⟨1259699789752980541354559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3359199439341281443612157 1259699789752980541354559)
    ·
      refine ⟨1889549684629470812031839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259699789752980541354559 1889549684629470812031839)
      ·
        refine ⟨2834324526944206218047759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889549684629470812031839 2834324526944206218047759)
        ·
          refine ⟨4251486790416309327071639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834324526944206218047759 4251486790416309327071639)
          ·
            refine ⟨6377230185624463990607459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251486790416309327071639 6377230185624463990607459)
            ·
              refine ⟨9565845278436695985911189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377230185624463990607459 9565845278436695985911189)
              ·
                refine ⟨448398997426720124339587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9565845278436695985911189 448398997426720124339587)
                ·
                  refine ⟨672598496140080186509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448398997426720124339587 672598496140080186509381)
                  ·
                    refine ⟨126112218026265034970509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672598496140080186509381 126112218026265034970509)
                    ·
                      refine ⟨47292081759849388113941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126112218026265034970509 47292081759849388113941)
                      ·
                        rfl

theorem cell23_92101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_92101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92101 prefixEnd_92101 := by exact prefixLift 92101
  have htrace : WordTrace (prefixWord ++ tailWord_92101) baseStart_92101 baseEnd_92101 := by
    simpa [prefixWord, tailWord_92101, baseEnd_92101] using wordTrace_append hprefix tailTrace_92101
  have hstable : (prefixWord ++ tailWord_92101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92101).length < 2 ^ (prefixWord ++ tailWord_92101).sum := by decide
  have hdescent : baseEnd_92101 < baseStart_92101 := by decide
  rcases family_descends (prefixWord ++ tailWord_92101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92138 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_92138 : Nat := 118140960795 + 92138 * 2 ^ 59
def prefixEnd_92138 : Nat := 4983230072969 + 3 ^ 40 * 92138 * 2
def baseEnd_92138 : Nat := 5256786727118415927919

theorem tailTrace_92138 : CollatzResearch.WordTrace tailWord_92138 prefixEnd_92138 5256786727118415927919 := by
  unfold tailWord_92138
  simp only [CollatzResearch.WordTrace]
  refine ⟨840137235051809190677267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2240365960138157841806045 840137235051809190677267)
  ·
    refine ⟨1260205852577713786015901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840137235051809190677267 1260205852577713786015901)
    ·
      refine ⟨472577194716642669755963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1260205852577713786015901 472577194716642669755963)
      ·
        refine ⟨708865792074964004633945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472577194716642669755963 708865792074964004633945)
        ·
          refine ⟨531649344056223003475459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708865792074964004633945 531649344056223003475459)
          ·
            refine ⟨797474016084334505213189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531649344056223003475459 797474016084334505213189)
            ·
              refine ⟨149526378015812719727473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 797474016084334505213189 149526378015812719727473)
              ·
                refine ⟨112144783511859539795605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149526378015812719727473 112144783511859539795605)
                ·
                  refine ⟨5256786727118415927919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112144783511859539795605 5256786727118415927919)
                  ·
                    rfl

theorem cell23_92138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_92138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92138 prefixEnd_92138 := by exact prefixLift 92138
  have htrace : WordTrace (prefixWord ++ tailWord_92138) baseStart_92138 baseEnd_92138 := by
    simpa [prefixWord, tailWord_92138, baseEnd_92138] using wordTrace_append hprefix tailTrace_92138
  have hstable : (prefixWord ++ tailWord_92138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92138).length < 2 ^ (prefixWord ++ tailWord_92138).sum := by decide
  have hdescent : baseEnd_92138 < baseStart_92138 := by decide
  rcases family_descends (prefixWord ++ tailWord_92138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92142 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_92142 : Nat := 118140960795 + 92142 * 2 ^ 59
def prefixEnd_92142 : Nat := 4983230072969 + 3 ^ 40 * 92142 * 2
def baseEnd_92142 : Nat := 15771044822227909233751

theorem tailTrace_92142 : CollatzResearch.WordTrace tailWord_92142 prefixEnd_92142 15771044822227909233751 := by
  unfold tailWord_92142
  simp only [CollatzResearch.WordTrace]
  refine ⟨420086854024093180731835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2240463221461830297236453 420086854024093180731835)
  ·
    refine ⟨630130281036139771097753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420086854024093180731835 630130281036139771097753)
    ·
      refine ⟨472597710777104828323315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630130281036139771097753 472597710777104828323315)
      ·
        refine ⟨708896566165657242484973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472597710777104828323315 708896566165657242484973)
        ·
          refine ⟨265836212312121465931865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708896566165657242484973 265836212312121465931865)
          ·
            refine ⟨199377159234091099448899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265836212312121465931865 199377159234091099448899)
            ·
              refine ⟨299065738851136649173349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199377159234091099448899 299065738851136649173349)
              ·
                refine ⟨56074826034588121720003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299065738851136649173349 56074826034588121720003)
                ·
                  refine ⟨84112239051882182580005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56074826034588121720003 84112239051882182580005)
                  ·
                    refine ⟨15771044822227909233751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84112239051882182580005 15771044822227909233751)
                    ·
                      rfl

theorem cell23_92142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_92142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92142 prefixEnd_92142 := by exact prefixLift 92142
  have htrace : WordTrace (prefixWord ++ tailWord_92142) baseStart_92142 baseEnd_92142 := by
    simpa [prefixWord, tailWord_92142, baseEnd_92142] using wordTrace_append hprefix tailTrace_92142
  have hstable : (prefixWord ++ tailWord_92142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92142).length < 2 ^ (prefixWord ++ tailWord_92142).sum := by decide
  have hdescent : baseEnd_92142 < baseStart_92142 := by decide
  rcases family_descends (prefixWord ++ tailWord_92142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92161 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_92161 : Nat := 118140960795 + 92161 * 2 ^ 59
def prefixEnd_92161 : Nat := 4983230072969 + 3 ^ 40 * 92161 * 2
def baseEnd_92161 : Nat := 47322890599119153363665

theorem tailTrace_92161 : CollatzResearch.WordTrace tailWord_92161 prefixEnd_92161 47322890599119153363665 := by
  unfold tailWord_92161
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361387819123911690796337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2240925212749274460530891 3361387819123911690796337)
  ·
    refine ⟨2521040864342933768097253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3361387819123911690796337 2521040864342933768097253)
    ·
      refine ⟨472695162064300081518235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2521040864342933768097253 472695162064300081518235)
      ·
        refine ⟨709042743096450122277353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472695162064300081518235 709042743096450122277353)
        ·
          refine ⟨531782057322337591708015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709042743096450122277353 531782057322337591708015)
          ·
            refine ⟨797673085983506387562023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531782057322337591708015 797673085983506387562023)
            ·
              refine ⟨1196509628975259581343035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797673085983506387562023 1196509628975259581343035)
              ·
                refine ⟨1794764443462889372014553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196509628975259581343035 1794764443462889372014553)
                ·
                  refine ⟨1346073332597167029010915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794764443462889372014553 1346073332597167029010915)
                  ·
                    refine ⟨2019109998895750543516373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1346073332597167029010915 2019109998895750543516373)
                    ·
                      refine ⟨47322890599119153363665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2019109998895750543516373 47322890599119153363665)
                      ·
                        rfl

theorem cell23_92161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_92161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92161 prefixEnd_92161 := by exact prefixLift 92161
  have htrace : WordTrace (prefixWord ++ tailWord_92161) baseStart_92161 baseEnd_92161 := by
    simpa [prefixWord, tailWord_92161, baseEnd_92161] using wordTrace_append hprefix tailTrace_92161
  have hstable : (prefixWord ++ tailWord_92161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92161).length < 2 ^ (prefixWord ++ tailWord_92161).sum := by decide
  have hdescent : baseEnd_92161 < baseStart_92161 := by decide
  rcases family_descends (prefixWord ++ tailWord_92161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92165 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_92165 : Nat := 118140960795 + 92165 * 2 ^ 59
def prefixEnd_92165 : Nat := 4983230072969 + 3 ^ 40 * 92165 * 2
def baseEnd_92165 : Nat := 47324944521737137713647

theorem tailTrace_92165 : CollatzResearch.WordTrace tailWord_92165 prefixEnd_92165 47324944521737137713647 := by
  unfold tailWord_92165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361533711109420373941949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2241022474072946915961299 3361533711109420373941949)
  ·
    refine ⟨1260575141666032640228231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3361533711109420373941949 1260575141666032640228231)
    ·
      refine ⟨1890862712499048960342347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260575141666032640228231 1890862712499048960342347)
      ·
        refine ⟨2836294068748573440513521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890862712499048960342347 2836294068748573440513521)
        ·
          refine ⟨2127220551561430080385141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836294068748573440513521 2127220551561430080385141)
          ·
            refine ⟨199426926708884070036107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2127220551561430080385141 199426926708884070036107)
            ·
              refine ⟨299140390063326105054161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199426926708884070036107 299140390063326105054161)
              ·
                refine ⟨224355292547494578790621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299140390063326105054161 224355292547494578790621)
                ·
                  refine ⟨84133234705310467046483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224355292547494578790621 84133234705310467046483)
                  ·
                    refine ⟨126199852057965700569725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84133234705310467046483 126199852057965700569725)
                    ·
                      refine ⟨47324944521737137713647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126199852057965700569725 47324944521737137713647)
                      ·
                        rfl

theorem cell23_92165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_92165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92165 prefixEnd_92165 := by exact prefixLift 92165
  have htrace : WordTrace (prefixWord ++ tailWord_92165) baseStart_92165 baseEnd_92165 := by
    simpa [prefixWord, tailWord_92165, baseEnd_92165] using wordTrace_append hprefix tailTrace_92165
  have hstable : (prefixWord ++ tailWord_92165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92165).length < 2 ^ (prefixWord ++ tailWord_92165).sum := by decide
  have hdescent : baseEnd_92165 < baseStart_92165 := by decide
  rcases family_descends (prefixWord ++ tailWord_92165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92168 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_92168 : Nat := 118140960795 + 92168 * 2 ^ 59
def prefixEnd_92168 : Nat := 4983230072969 + 3 ^ 40 * 92168 * 2
def baseEnd_92168 : Nat := 15775494987900208658711

theorem tailTrace_92168 : CollatzResearch.WordTrace tailWord_92168 prefixEnd_92168 15775494987900208658711 := by
  unfold tailWord_92168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680821565049275943150579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2241095420065701257534105 1680821565049275943150579)
  ·
    refine ⟨2521232347573913914725869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1680821565049275943150579 2521232347573913914725869)
    ·
      refine ⟨945462130340217718022201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2521232347573913914725869 945462130340217718022201)
      ·
        refine ⟨709096597755163288516651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945462130340217718022201 709096597755163288516651)
        ·
          refine ⟨1063644896632744932774977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709096597755163288516651 1063644896632744932774977)
          ·
            refine ⟨797733672474558699581233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063644896632744932774977 797733672474558699581233)
            ·
              refine ⟨598300254355919024685925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797733672474558699581233 598300254355919024685925)
              ·
                refine ⟨112181297691734817128611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598300254355919024685925 112181297691734817128611)
                ·
                  refine ⟨168271946537602225692917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112181297691734817128611 168271946537602225692917)
                  ·
                    refine ⟨15775494987900208658711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168271946537602225692917 15775494987900208658711)
                    ·
                      rfl

theorem cell23_92168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_92168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92168 prefixEnd_92168 := by exact prefixLift 92168
  have htrace : WordTrace (prefixWord ++ tailWord_92168) baseStart_92168 baseEnd_92168 := by
    simpa [prefixWord, tailWord_92168, baseEnd_92168] using wordTrace_append hprefix tailTrace_92168
  have hstable : (prefixWord ++ tailWord_92168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92168).length < 2 ^ (prefixWord ++ tailWord_92168).sum := by decide
  have hdescent : baseEnd_92168 < baseStart_92168 := by decide
  rcases family_descends (prefixWord ++ tailWord_92168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92199 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_92199 : Nat := 118140960795 + 92199 * 2 ^ 59
def prefixEnd_92199 : Nat := 4983230072969 + 3 ^ 40 * 92199 * 2
def baseEnd_92199 : Nat := 47342402863990004688491

theorem tailTrace_92199 : CollatzResearch.WordTrace tailWord_92199 prefixEnd_92199 47342402863990004688491 := by
  unfold tailWord_92199
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362773792986244180679651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2241849195324162787119767 3362773792986244180679651)
  ·
    refine ⟨5044160689479366271019477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362773792986244180679651 5044160689479366271019477)
    ·
      refine ⟨118222516159672646977019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5044160689479366271019477 118222516159672646977019)
      ·
        refine ⟨177333774239508970465529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118222516159672646977019 177333774239508970465529)
        ·
          refine ⟨133000330679631727849147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177333774239508970465529 133000330679631727849147)
          ·
            refine ⟨199500496019447591773721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133000330679631727849147 199500496019447591773721)
            ·
              refine ⟨149625372014585693830291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199500496019447591773721 149625372014585693830291)
              ·
                refine ⟨224438058021878540745437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149625372014585693830291 224438058021878540745437)
                ·
                  refine ⟨84164271758204452779539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224438058021878540745437 84164271758204452779539)
                  ·
                    refine ⟨126246407637306679169309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84164271758204452779539 126246407637306679169309)
                    ·
                      refine ⟨47342402863990004688491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126246407637306679169309 47342402863990004688491)
                      ·
                        rfl

theorem cell23_92199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_92199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92199 prefixEnd_92199 := by exact prefixLift 92199
  have htrace : WordTrace (prefixWord ++ tailWord_92199) baseStart_92199 baseEnd_92199 := by
    simpa [prefixWord, tailWord_92199, baseEnd_92199] using wordTrace_append hprefix tailTrace_92199
  have hstable : (prefixWord ++ tailWord_92199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92199).length < 2 ^ (prefixWord ++ tailWord_92199).sum := by decide
  have hdescent : baseEnd_92199 < baseStart_92199 := by decide
  rcases family_descends (prefixWord ++ tailWord_92199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92208 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_92208 : Nat := 118140960795 + 92208 * 2 ^ 59
def prefixEnd_92208 : Nat := 4983230072969 + 3 ^ 40 * 92208 * 2
def baseEnd_92208 : Nat := 47347024189880469475949

theorem tailTrace_92208 : CollatzResearch.WordTrace tailWord_92208 prefixEnd_92208 47347024189880469475949 := by
  unfold tailWord_92208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681551024976819358878639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2242068033302425811838185 1681551024976819358878639)
  ·
    refine ⟨2522326537465229038317959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1681551024976819358878639 2522326537465229038317959)
    ·
      refine ⟨3783489806197843557476939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522326537465229038317959 3783489806197843557476939)
      ·
        refine ⟨5675234709296765336215409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3783489806197843557476939 5675234709296765336215409)
        ·
          refine ⟨4256426031972574002161557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5675234709296765336215409 4256426031972574002161557)
          ·
            refine ⟨199519970248714406351323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4256426031972574002161557 199519970248714406351323)
            ·
              refine ⟨299279955373071609526985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199519970248714406351323 299279955373071609526985)
              ·
                refine ⟨224459966529803707145239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299279955373071609526985 224459966529803707145239)
                ·
                  refine ⟨336689949794705560717859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224459966529803707145239 336689949794705560717859)
                  ·
                    refine ⟨505034924692058341076789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336689949794705560717859 505034924692058341076789)
                    ·
                      refine ⟨47347024189880469475949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 505034924692058341076789 47347024189880469475949)
                      ·
                        rfl

theorem cell23_92208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_92208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92208 prefixEnd_92208 := by exact prefixLift 92208
  have htrace : WordTrace (prefixWord ++ tailWord_92208) baseStart_92208 baseEnd_92208 := by
    simpa [prefixWord, tailWord_92208, baseEnd_92208] using wordTrace_append hprefix tailTrace_92208
  have hstable : (prefixWord ++ tailWord_92208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92208).length < 2 ^ (prefixWord ++ tailWord_92208).sum := by decide
  have hdescent : baseEnd_92208 < baseStart_92208 := by decide
  rcases family_descends (prefixWord ++ tailWord_92208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92241 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_92241 : Nat := 118140960795 + 92241 * 2 ^ 59
def prefixEnd_92241 : Nat := 4983230072969 + 3 ^ 40 * 92241 * 2
def baseEnd_92241 : Nat := 15787989683826280121099

theorem tailTrace_92241 : CollatzResearch.WordTrace tailWord_92241 prefixEnd_92241 15787989683826280121099 := by
  unfold tailWord_92241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364305658834085353708577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2242870439222723569139051 3364305658834085353708577)
  ·
    refine ⟨2523229244125564015281433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3364305658834085353708577 2523229244125564015281433)
    ·
      refine ⟨1892421933094173011461075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2523229244125564015281433 1892421933094173011461075)
      ·
        refine ⟨2838632899641259517191613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892421933094173011461075 2838632899641259517191613)
        ·
          refine ⟨1064487337365472318946855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2838632899641259517191613 1064487337365472318946855)
          ·
            refine ⟨1596731006048208478420283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064487337365472318946855 1596731006048208478420283)
            ·
              refine ⟨2395096509072312717630425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596731006048208478420283 2395096509072312717630425)
              ·
                refine ⟨1796322381804234538222819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2395096509072312717630425 1796322381804234538222819)
                ·
                  refine ⟨2694483572706351807334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796322381804234538222819 2694483572706351807334229)
                  ·
                    refine ⟨15787989683826280121099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2694483572706351807334229 15787989683826280121099)
                    ·
                      rfl

theorem cell23_92241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_92241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92241 prefixEnd_92241 := by exact prefixLift 92241
  have htrace : WordTrace (prefixWord ++ tailWord_92241) baseStart_92241 baseEnd_92241 := by
    simpa [prefixWord, tailWord_92241, baseEnd_92241] using wordTrace_append hprefix tailTrace_92241
  have hstable : (prefixWord ++ tailWord_92241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92241).length < 2 ^ (prefixWord ++ tailWord_92241).sum := by decide
  have hdescent : baseEnd_92241 < baseStart_92241 := by decide
  rcases family_descends (prefixWord ++ tailWord_92241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92256 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 1, 2, 2]
def baseStart_92256 : Nat := 118140960795 + 92256 * 2 ^ 59
def prefixEnd_92256 : Nat := 4983230072969 + 3 ^ 40 * 92256 * 2
def baseEnd_92256 : Nat := 47371671261296281675729

theorem tailTrace_92256 : CollatzResearch.WordTrace tailWord_92256 prefixEnd_92256 47371671261296281675729 := by
  unfold tailWord_92256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682426376889871457752311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2243235169186495277003081 1682426376889871457752311)
  ·
    refine ⟨2523639565334807186628467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682426376889871457752311 2523639565334807186628467)
    ·
      refine ⟨3785459348002210779942701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523639565334807186628467 3785459348002210779942701)
      ·
        refine ⟨1419547255500829042478513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3785459348002210779942701 1419547255500829042478513)
        ·
          refine ⟨1064660441625621781858885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419547255500829042478513 1064660441625621781858885)
          ·
            refine ⟨199623832804804084098541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1064660441625621781858885 199623832804804084098541)
            ·
              refine ⟨74858937301801531536953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199623832804804084098541 74858937301801531536953)
              ·
                refine ⟨56144202976351148652715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74858937301801531536953 56144202976351148652715)
                ·
                  refine ⟨84216304464526722979073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56144202976351148652715 84216304464526722979073)
                  ·
                    refine ⟨63162228348395042234305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84216304464526722979073 63162228348395042234305)
                    ·
                      refine ⟨47371671261296281675729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63162228348395042234305 47371671261296281675729)
                      ·
                        rfl

theorem cell23_92256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_92256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92256 prefixEnd_92256 := by exact prefixLift 92256
  have htrace : WordTrace (prefixWord ++ tailWord_92256) baseStart_92256 baseEnd_92256 := by
    simpa [prefixWord, tailWord_92256, baseEnd_92256] using wordTrace_append hprefix tailTrace_92256
  have hstable : (prefixWord ++ tailWord_92256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92256).length < 2 ^ (prefixWord ++ tailWord_92256).sum := by decide
  have hdescent : baseEnd_92256 < baseStart_92256 := by decide
  rcases family_descends (prefixWord ++ tailWord_92256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92265 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 3, 3, 2]
def baseStart_92265 : Nat := 118140960795 + 92265 * 2 ^ 59
def prefixEnd_92265 : Nat := 4983230072969 + 3 ^ 40 * 92265 * 2
def baseEnd_92265 : Nat := 47376292587186746463187

theorem tailTrace_92265 : CollatzResearch.WordTrace tailWord_92265 prefixEnd_92265 47376292587186746463187 := by
  unfold tailWord_92265
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365181010747137452582249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2243454007164758301721499 3365181010747137452582249)
  ·
    refine ⟨2523885758060353089436687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3365181010747137452582249 2523885758060353089436687)
    ·
      refine ⟨3785828637090529634155031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523885758060353089436687 3785828637090529634155031)
      ·
        refine ⟨5678742955635794451232547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785828637090529634155031 5678742955635794451232547)
        ·
          refine ⟨8518114433453691676848821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678742955635794451232547 8518114433453691676848821)
          ·
            refine ⟨798573228136283594704577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8518114433453691676848821 798573228136283594704577)
            ·
              refine ⟨598929921102212696028433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798573228136283594704577 598929921102212696028433)
              ·
                refine ⟨449197440826659522021325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598929921102212696028433 449197440826659522021325)
                ·
                  refine ⟨168449040309997320757997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449197440826659522021325 168449040309997320757997)
                  ·
                    refine ⟨63168390116248995284249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168449040309997320757997 63168390116248995284249)
                    ·
                      refine ⟨47376292587186746463187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63168390116248995284249 47376292587186746463187)
                      ·
                        rfl

theorem cell23_92265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3, 2].length) (baseStart_92265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92265 prefixEnd_92265 := by exact prefixLift 92265
  have htrace : WordTrace (prefixWord ++ tailWord_92265) baseStart_92265 baseEnd_92265 := by
    simpa [prefixWord, tailWord_92265, baseEnd_92265] using wordTrace_append hprefix tailTrace_92265
  have hstable : (prefixWord ++ tailWord_92265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92265).length < 2 ^ (prefixWord ++ tailWord_92265).sum := by decide
  have hdescent : baseEnd_92265 < baseStart_92265 := by decide
  rcases family_descends (prefixWord ++ tailWord_92265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92266 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_92266 : Nat := 118140960795 + 92266 * 2 ^ 59
def prefixEnd_92266 : Nat := 4983230072969 + 3 ^ 40 * 92266 * 2
def baseEnd_92266 : Nat := 15792268689280414183561

theorem tailTrace_92266 : CollatzResearch.WordTrace tailWord_92266 prefixEnd_92266 15792268689280414183561 := by
  unfold tailWord_92266
  simp only [CollatzResearch.WordTrace]
  refine ⟨841304370935878655842163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2243478322495676415579101 841304370935878655842163)
  ·
    refine ⟨1261956556403817983763245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841304370935878655842163 1261956556403817983763245)
    ·
      refine ⟨473233708651431743911217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1261956556403817983763245 473233708651431743911217)
      ·
        refine ⟨354925281488573807933413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473233708651431743911217 354925281488573807933413)
        ·
          refine ⟨66548490279107588987515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354925281488573807933413 66548490279107588987515)
          ·
            refine ⟨99822735418661383481273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66548490279107588987515 99822735418661383481273)
            ·
              refine ⟨74867051563996037610955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99822735418661383481273 74867051563996037610955)
              ·
                refine ⟨112300577345994056416433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74867051563996037610955 112300577345994056416433)
                ·
                  refine ⟨84225433009495542312325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112300577345994056416433 84225433009495542312325)
                  ·
                    refine ⟨15792268689280414183561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84225433009495542312325 15792268689280414183561)
                    ·
                      rfl

theorem cell23_92266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_92266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92266 prefixEnd_92266 := by exact prefixLift 92266
  have htrace : WordTrace (prefixWord ++ tailWord_92266) baseStart_92266 baseEnd_92266 := by
    simpa [prefixWord, tailWord_92266, baseEnd_92266] using wordTrace_append hprefix tailTrace_92266
  have hstable : (prefixWord ++ tailWord_92266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92266).length < 2 ^ (prefixWord ++ tailWord_92266).sum := by decide
  have hdescent : baseEnd_92266 < baseStart_92266 := by decide
  rcases family_descends (prefixWord ++ tailWord_92266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92272 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3]
def baseStart_92272 : Nat := 118140960795 + 92272 * 2 ^ 59
def prefixEnd_92272 : Nat := 4983230072969 + 3 ^ 40 * 92272 * 2
def baseEnd_92272 : Nat := 47379886951768219075655

theorem tailTrace_92272 : CollatzResearch.WordTrace tailWord_92272 prefixEnd_92272 47379886951768219075655 := by
  unfold tailWord_92272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682718160860888824043535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2243624214481185098724713 1682718160860888824043535)
  ·
    refine ⟨2524077241291333236065303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682718160860888824043535 2524077241291333236065303)
    ·
      refine ⟨3786115861936999854097955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524077241291333236065303 3786115861936999854097955)
      ·
        refine ⟨5679173792905499781146933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786115861936999854097955 5679173792905499781146933)
        ·
          refine ⟨532422543084890604482525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5679173792905499781146933 532422543084890604482525)
          ·
            refine ⟨199658453656833976680947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 532422543084890604482525 199658453656833976680947)
            ·
              refine ⟨299487680485250965021421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199658453656833976680947 299487680485250965021421)
              ·
                refine ⟨112307880181969111883033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299487680485250965021421 112307880181969111883033)
                ·
                  refine ⟨84230910136476833912275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112307880181969111883033 84230910136476833912275)
                  ·
                    refine ⟨126346365204715250868413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84230910136476833912275 126346365204715250868413)
                    ·
                      refine ⟨47379886951768219075655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126346365204715250868413 47379886951768219075655)
                      ·
                        rfl

theorem cell23_92272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_92272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92272 prefixEnd_92272 := by exact prefixLift 92272
  have htrace : WordTrace (prefixWord ++ tailWord_92272) baseStart_92272 baseEnd_92272 := by
    simpa [prefixWord, tailWord_92272, baseEnd_92272] using wordTrace_append hprefix tailTrace_92272
  have hstable : (prefixWord ++ tailWord_92272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92272).length < 2 ^ (prefixWord ++ tailWord_92272).sum := by decide
  have hdescent : baseEnd_92272 < baseStart_92272 := by decide
  rcases family_descends (prefixWord ++ tailWord_92272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92295 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_92295 : Nat := 118140960795 + 92295 * 2 ^ 59
def prefixEnd_92295 : Nat := 4983230072969 + 3 ^ 40 * 92295 * 2
def baseEnd_92295 : Nat := 47391697006821629088049

theorem tailTrace_92295 : CollatzResearch.WordTrace tailWord_92295 prefixEnd_92295 47391697006821629088049 := by
  unfold tailWord_92295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366275200638452576174339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2244183467092301717449559 3366275200638452576174339)
  ·
    refine ⟨5049412800957678864261509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3366275200638452576174339 5049412800957678864261509)
    ·
      refine ⟨946764900179564787049033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5049412800957678864261509 946764900179564787049033)
      ·
        refine ⟨710073675134673590286775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 946764900179564787049033 710073675134673590286775)
        ·
          refine ⟨1065110512702010385430163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710073675134673590286775 1065110512702010385430163)
          ·
            refine ⟨1597665769053015578145245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065110512702010385430163 1597665769053015578145245)
            ·
              refine ⟨599124663394880841804467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1597665769053015578145245 599124663394880841804467)
              ·
                refine ⟨898686995092321262706701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599124663394880841804467 898686995092321262706701)
                ·
                  refine ⟨337007623159620473515013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898686995092321262706701 337007623159620473515013)
                  ·
                    refine ⟨63188929342428838784065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337007623159620473515013 63188929342428838784065)
                    ·
                      refine ⟨47391697006821629088049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63188929342428838784065 47391697006821629088049)
                      ·
                        rfl

theorem cell23_92295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_92295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92295 prefixEnd_92295 := by exact prefixLift 92295
  have htrace : WordTrace (prefixWord ++ tailWord_92295) baseStart_92295 baseEnd_92295 := by
    simpa [prefixWord, tailWord_92295, baseEnd_92295] using wordTrace_append hprefix tailTrace_92295
  have hstable : (prefixWord ++ tailWord_92295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92295).length < 2 ^ (prefixWord ++ tailWord_92295).sum := by decide
  have hdescent : baseEnd_92295 < baseStart_92295 := by decide
  rcases family_descends (prefixWord ++ tailWord_92295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92352 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 5]
def baseStart_92352 : Nat := 118140960795 + 92352 * 2 ^ 59
def prefixEnd_92352 : Nat := 4983230072969 + 3 ^ 40 * 92352 * 2
def baseEnd_92352 : Nat := 5268996156014211786143

theorem tailTrace_92352 : CollatzResearch.WordTrace tailWord_92352 prefixEnd_92352 5268996156014211786143 := by
  unfold tailWord_92352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684177080715975655499655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2245569440954634207332873 1684177080715975655499655)
  ·
    refine ⟨2526265621073963483249483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684177080715975655499655 2526265621073963483249483)
    ·
      refine ⟨3789398431610945224874225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2526265621073963483249483 3789398431610945224874225)
      ·
        refine ⟨2842048823708208918655669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789398431610945224874225 2842048823708208918655669)
        ·
          refine ⟨266442077222644586123969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2842048823708208918655669 266442077222644586123969)
          ·
            refine ⟨199831557916983439592977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266442077222644586123969 199831557916983439592977)
            ·
              refine ⟨149873668437737579694733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199831557916983439592977 149873668437737579694733)
              ·
                refine ⟨56202625664151592385525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149873668437737579694733 56202625664151592385525)
                ·
                  refine ⟨5268996156014211786143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56202625664151592385525 5268996156014211786143)
                  ·
                    rfl

theorem cell23_92352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 5].length) (baseStart_92352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92352 prefixEnd_92352 := by exact prefixLift 92352
  have htrace : WordTrace (prefixWord ++ tailWord_92352) baseStart_92352 baseEnd_92352 := by
    simpa [prefixWord, tailWord_92352, baseEnd_92352] using wordTrace_append hprefix tailTrace_92352
  have hstable : (prefixWord ++ tailWord_92352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92352).length < 2 ^ (prefixWord ++ tailWord_92352).sum := by decide
  have hdescent : baseEnd_92352 < baseStart_92352 := by decide
  rcases family_descends (prefixWord ++ tailWord_92352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92380 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_92380 : Nat := 118140960795 + 92380 * 2 ^ 59
def prefixEnd_92380 : Nat := 4983230072969 + 3 ^ 40 * 92380 * 2
def baseEnd_92380 : Nat := 47435342862453796525159

theorem tailTrace_92380 : CollatzResearch.WordTrace tailWord_92380 prefixEnd_92380 47435342862453796525159 := by
  unfold tailWord_92380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684687702665256046509297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2246250270220341395345729 1684687702665256046509297)
  ·
    refine ⟨1263515776998942034881973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1684687702665256046509297 1263515776998942034881973)
    ·
      refine ⟨118454604093650815770185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1263515776998942034881973 118454604093650815770185)
      ·
        refine ⟨88840953070238111827639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118454604093650815770185 88840953070238111827639)
        ·
          refine ⟨133261429605357167741459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88840953070238111827639 133261429605357167741459)
          ·
            refine ⟨199892144408035751612189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133261429605357167741459 199892144408035751612189)
            ·
              refine ⟨74959554153013406854571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199892144408035751612189 74959554153013406854571)
              ·
                refine ⟨112439331229520110281857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74959554153013406854571 112439331229520110281857)
                ·
                  refine ⟨84329498422140082711393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112439331229520110281857 84329498422140082711393)
                  ·
                    refine ⟨63247123816605062033545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84329498422140082711393 63247123816605062033545)
                    ·
                      refine ⟨47435342862453796525159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63247123816605062033545 47435342862453796525159)
                      ·
                        rfl

theorem cell23_92380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_92380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92380 prefixEnd_92380 := by exact prefixLift 92380
  have htrace : WordTrace (prefixWord ++ tailWord_92380) baseStart_92380 baseEnd_92380 := by
    simpa [prefixWord, tailWord_92380, baseEnd_92380] using wordTrace_append hprefix tailTrace_92380
  have hstable : (prefixWord ++ tailWord_92380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92380).length < 2 ^ (prefixWord ++ tailWord_92380).sum := by decide
  have hdescent : baseEnd_92380 < baseStart_92380 := by decide
  rcases family_descends (prefixWord ++ tailWord_92380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92395 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 3, 4]
def baseStart_92395 : Nat := 118140960795 + 92395 * 2 ^ 59
def prefixEnd_92395 : Nat := 4983230072969 + 3 ^ 40 * 92395 * 2
def baseEnd_92395 : Nat := 15814348357423745945863

theorem tailTrace_92395 : CollatzResearch.WordTrace tailWord_92395 prefixEnd_92395 15814348357423745945863 := by
  unfold tailWord_92395
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369922500276169654814639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2246615000184113103209759 3369922500276169654814639)
  ·
    refine ⟨5054883750414254482221959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369922500276169654814639 5054883750414254482221959)
    ·
      refine ⟨7582325625621381723332939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054883750414254482221959 7582325625621381723332939)
      ·
        refine ⟨11373488438432072584999409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582325625621381723332939 11373488438432072584999409)
        ·
          refine ⟨8530116328824054438749557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11373488438432072584999409 8530116328824054438749557)
          ·
            refine ⟨799698405827255103632771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8530116328824054438749557 799698405827255103632771)
            ·
              refine ⟨1199547608740882655449157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799698405827255103632771 1199547608740882655449157)
              ·
                refine ⟨224915176638915497896717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1199547608740882655449157 224915176638915497896717)
                ·
                  refine ⟨84343191239593311711269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224915176638915497896717 84343191239593311711269)
                  ·
                    refine ⟨15814348357423745945863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84343191239593311711269 15814348357423745945863)
                    ·
                      rfl

theorem cell23_92395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 4].length) (baseStart_92395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92395 prefixEnd_92395 := by exact prefixLift 92395
  have htrace : WordTrace (prefixWord ++ tailWord_92395) baseStart_92395 baseEnd_92395 := by
    simpa [prefixWord, tailWord_92395, baseEnd_92395] using wordTrace_append hprefix tailTrace_92395
  have hstable : (prefixWord ++ tailWord_92395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92395).length < 2 ^ (prefixWord ++ tailWord_92395).sum := by decide
  have hdescent : baseEnd_92395 < baseStart_92395 := by decide
  rcases family_descends (prefixWord ++ tailWord_92395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92442 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_92442 : Nat := 118140960795 + 92442 * 2 ^ 59
def prefixEnd_92442 : Nat := 4983230072969 + 3 ^ 40 * 92442 * 2
def baseEnd_92442 : Nat := 5274130962559172661097

theorem tailTrace_92442 : CollatzResearch.WordTrace tailWord_92442 prefixEnd_92442 5274130962559172661097 := by
  unfold tailWord_92442
  simp only [CollatzResearch.WordTrace]
  refine ⟨842909182776474170443895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2247757820737264454517053 842909182776474170443895)
  ·
    refine ⟨1264363774164711255665843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842909182776474170443895 1264363774164711255665843)
    ·
      refine ⟨1896545661247066883498765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264363774164711255665843 1896545661247066883498765)
      ·
        refine ⟨711204622967650081312037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1896545661247066883498765 711204622967650081312037)
        ·
          refine ⟨133350866806434390246007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 711204622967650081312037 133350866806434390246007)
          ·
            refine ⟨200026300209651585369011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133350866806434390246007 200026300209651585369011)
            ·
              refine ⟨300039450314477378053517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200026300209651585369011 300039450314477378053517)
              ·
                refine ⟨112514793867929016770069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300039450314477378053517 112514793867929016770069)
                ·
                  refine ⟨5274130962559172661097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112514793867929016770069 5274130962559172661097)
                  ·
                    rfl

theorem cell23_92442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_92442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92442 prefixEnd_92442 := by exact prefixLift 92442
  have htrace : WordTrace (prefixWord ++ tailWord_92442) baseStart_92442 baseEnd_92442 := by
    simpa [prefixWord, tailWord_92442, baseEnd_92442] using wordTrace_append hprefix tailTrace_92442
  have hstable : (prefixWord ++ tailWord_92442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92442).length < 2 ^ (prefixWord ++ tailWord_92442).sum := by decide
  have hdescent : baseEnd_92442 < baseStart_92442 := by decide
  rcases family_descends (prefixWord ++ tailWord_92442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92546 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_92546 : Nat := 118140960795 + 92546 * 2 ^ 59
def prefixEnd_92546 : Nat := 4983230072969 + 3 ^ 40 * 92546 * 2
def baseEnd_92546 : Nat := 47520580651100147049395

theorem tailTrace_92546 : CollatzResearch.WordTrace tailWord_92546 prefixEnd_92546 47520580651100147049395 := by
  unfold tailWord_92546
  simp only [CollatzResearch.WordTrace]
  refine ⟨843857480682280610890373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2250286615152748295707661 843857480682280610890373)
  ·
    refine ⟨158223277627927614541945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 843857480682280610890373 158223277627927614541945)
    ·
      refine ⟨118667458220945710906459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158223277627927614541945 118667458220945710906459)
      ·
        refine ⟨178001187331418566359689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118667458220945710906459 178001187331418566359689)
        ·
          refine ⟨133500890498563924769767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178001187331418566359689 133500890498563924769767)
          ·
            refine ⟨200251335747845887154651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133500890498563924769767 200251335747845887154651)
            ·
              refine ⟨300377003621768830731977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200251335747845887154651 300377003621768830731977)
              ·
                refine ⟨225282752716326623048983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300377003621768830731977 225282752716326623048983)
                ·
                  refine ⟨337924129074489934573475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225282752716326623048983 337924129074489934573475)
                  ·
                    refine ⟨506886193611734901860213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 337924129074489934573475 506886193611734901860213)
                    ·
                      refine ⟨47520580651100147049395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 506886193611734901860213 47520580651100147049395)
                      ·
                        rfl

theorem cell23_92546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_92546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92546 prefixEnd_92546 := by exact prefixLift 92546
  have htrace : WordTrace (prefixWord ++ tailWord_92546) baseStart_92546 baseEnd_92546 := by
    simpa [prefixWord, tailWord_92546, baseEnd_92546] using wordTrace_append hprefix tailTrace_92546
  have hstable : (prefixWord ++ tailWord_92546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92546).length < 2 ^ (prefixWord ++ tailWord_92546).sum := by decide
  have hdescent : baseEnd_92546 < baseStart_92546 := by decide
  rcases family_descends (prefixWord ++ tailWord_92546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92577 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_92577 : Nat := 118140960795 + 92577 * 2 ^ 59
def prefixEnd_92577 : Nat := 4983230072969 + 3 ^ 40 * 92577 * 2
def baseEnd_92577 : Nat := 47536498551389525761753

theorem tailTrace_92577 : CollatzResearch.WordTrace tailWord_92577 prefixEnd_92577 47536498551389525761753 := by
  unfold tailWord_92577
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376560585616814737939985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251040390411209825293323 3376560585616814737939985)
  ·
    refine ⟨2532420439212611053454989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3376560585616814737939985 2532420439212611053454989)
    ·
      refine ⟨949657664704729145045621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2532420439212611053454989 949657664704729145045621)
      ·
        refine ⟨89030406066068357348027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 949657664704729145045621 89030406066068357348027)
        ·
          refine ⟨133545609099102536022041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89030406066068357348027 133545609099102536022041)
          ·
            refine ⟨100159206824326902016531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133545609099102536022041 100159206824326902016531)
            ·
              refine ⟨150238810236490353024797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100159206824326902016531 150238810236490353024797)
              ·
                refine ⟨56339553838683882384299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150238810236490353024797 56339553838683882384299)
                ·
                  refine ⟨84509330758025823576449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56339553838683882384299 84509330758025823576449)
                  ·
                    refine ⟨63381998068519367682337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84509330758025823576449 63381998068519367682337)
                    ·
                      refine ⟨47536498551389525761753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63381998068519367682337 47536498551389525761753)
                      ·
                        rfl

theorem cell23_92577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_92577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92577 prefixEnd_92577 := by exact prefixLift 92577
  have htrace : WordTrace (prefixWord ++ tailWord_92577) baseStart_92577 baseEnd_92577 := by
    simpa [prefixWord, tailWord_92577, baseEnd_92577] using wordTrace_append hprefix tailTrace_92577
  have hstable : (prefixWord ++ tailWord_92577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92577).length < 2 ^ (prefixWord ++ tailWord_92577).sum := by decide
  have hdescent : baseEnd_92577 < baseStart_92577 := by decide
  rcases family_descends (prefixWord ++ tailWord_92577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92620 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_92620 : Nat := 118140960795 + 92620 * 2 ^ 59
def prefixEnd_92620 : Nat := 4983230072969 + 3 ^ 40 * 92620 * 2
def baseEnd_92620 : Nat := 47558578219532857524055

theorem tailTrace_92620 : CollatzResearch.WordTrace tailWord_92620 prefixEnd_92620 47558578219532857524055 := by
  unfold tailWord_92620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689064462230516540877657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2252085949640688721170209 1689064462230516540877657)
  ·
    refine ⟨1266798346672887405658243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689064462230516540877657 1266798346672887405658243)
    ·
      refine ⟨1900197520009331108487365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266798346672887405658243 1900197520009331108487365)
      ·
        refine ⟨356287035001749582841381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1900197520009331108487365 356287035001749582841381)
        ·
          refine ⟨66803819062828046782759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356287035001749582841381 66803819062828046782759)
          ·
            refine ⟨100205728594242070174139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66803819062828046782759 100205728594242070174139)
            ·
              refine ⟨150308592891363105261209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100205728594242070174139 150308592891363105261209)
              ·
                refine ⟨112731444668522328945907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150308592891363105261209 112731444668522328945907)
                ·
                  refine ⟨169097167002783493418861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112731444668522328945907 169097167002783493418861)
                  ·
                    refine ⟨63411437626043810032073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169097167002783493418861 63411437626043810032073)
                    ·
                      refine ⟨47558578219532857524055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63411437626043810032073 47558578219532857524055)
                      ·
                        rfl

theorem cell23_92620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_92620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92620 prefixEnd_92620 := by exact prefixLift 92620
  have htrace : WordTrace (prefixWord ++ tailWord_92620) baseStart_92620 baseEnd_92620 := by
    simpa [prefixWord, tailWord_92620, baseEnd_92620] using wordTrace_append hprefix tailTrace_92620
  have hstable : (prefixWord ++ tailWord_92620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92620).length < 2 ^ (prefixWord ++ tailWord_92620).sum := by decide
  have hdescent : baseEnd_92620 < baseStart_92620 := by decide
  rcases family_descends (prefixWord ++ tailWord_92620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92625 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_92625 : Nat := 118140960795 + 92625 * 2 ^ 59
def prefixEnd_92625 : Nat := 4983230072969 + 3 ^ 40 * 92625 * 2
def baseEnd_92625 : Nat := 47561145622805337961531

theorem tailTrace_92625 : CollatzResearch.WordTrace tailWord_92625 prefixEnd_92625 47561145622805337961531 := by
  unfold tailWord_92625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378311289442918935687329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2252207526295279290458219 3378311289442918935687329)
  ·
    refine ⟨2533733467082189201765497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3378311289442918935687329 2533733467082189201765497)
    ·
      refine ⟨1900300100311641901324123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2533733467082189201765497 1900300100311641901324123)
      ·
        refine ⟨2850450150467462851986185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900300100311641901324123 2850450150467462851986185)
        ·
          refine ⟨2137837612850597138989639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2850450150467462851986185 2137837612850597138989639)
          ·
            refine ⟨3206756419275895708484459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137837612850597138989639 3206756419275895708484459)
            ·
              refine ⟨4810134628913843562726689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206756419275895708484459 4810134628913843562726689)
              ·
                refine ⟨3607600971685382672045017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810134628913843562726689 3607600971685382672045017)
                ·
                  refine ⟨2705700728764037004033763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607600971685382672045017 2705700728764037004033763)
                  ·
                    refine ⟨4058551093146055506050645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705700728764037004033763 4058551093146055506050645)
                    ·
                      refine ⟨47561145622805337961531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4058551093146055506050645 47561145622805337961531)
                      ·
                        rfl

theorem cell23_92625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_92625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92625 prefixEnd_92625 := by exact prefixLift 92625
  have htrace : WordTrace (prefixWord ++ tailWord_92625) baseStart_92625 baseEnd_92625 := by
    simpa [prefixWord, tailWord_92625, baseEnd_92625] using wordTrace_append hprefix tailTrace_92625
  have hstable : (prefixWord ++ tailWord_92625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92625).length < 2 ^ (prefixWord ++ tailWord_92625).sum := by decide
  have hdescent : baseEnd_92625 < baseStart_92625 := by decide
  rcases family_descends (prefixWord ++ tailWord_92625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92632 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_92632 : Nat := 118140960795 + 92632 * 2 ^ 59
def prefixEnd_92632 : Nat := 4983230072969 + 3 ^ 40 * 92632 * 2
def baseEnd_92632 : Nat := 47564739987386810573999

theorem tailTrace_92632 : CollatzResearch.WordTrace tailWord_92632 prefixEnd_92632 47564739987386810573999 := by
  unfold tailWord_92632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689283300208779565596075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2252377733611706087461433 1689283300208779565596075)
  ·
    refine ⟨2533924950313169348394113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689283300208779565596075 2533924950313169348394113)
    ·
      refine ⟨1900443712734877011295585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2533924950313169348394113 1900443712734877011295585)
      ·
        refine ⟨1425332784551157758471689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900443712734877011295585 1425332784551157758471689)
        ·
          refine ⟨1068999588413368318853767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425332784551157758471689 1068999588413368318853767)
          ·
            refine ⟨1603499382620052478280651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068999588413368318853767 1603499382620052478280651)
            ·
              refine ⟨2405249073930078717420977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603499382620052478280651 2405249073930078717420977)
              ·
                refine ⟨1803936805447559038065733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405249073930078717420977 1803936805447559038065733)
                ·
                  refine ⟨338238151021417319637325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803936805447559038065733 338238151021417319637325)
                  ·
                    refine ⟨126839306633031494863997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338238151021417319637325 126839306633031494863997)
                    ·
                      refine ⟨47564739987386810573999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126839306633031494863997 47564739987386810573999)
                      ·
                        rfl

theorem cell23_92632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_92632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92632 prefixEnd_92632 := by exact prefixLift 92632
  have htrace : WordTrace (prefixWord ++ tailWord_92632) baseStart_92632 baseEnd_92632 := by
    simpa [prefixWord, tailWord_92632, baseEnd_92632] using wordTrace_append hprefix tailTrace_92632
  have hstable : (prefixWord ++ tailWord_92632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92632).length < 2 ^ (prefixWord ++ tailWord_92632).sum := by decide
  have hdescent : baseEnd_92632 < baseStart_92632 := by decide
  rcases family_descends (prefixWord ++ tailWord_92632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92652 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_92652 : Nat := 118140960795 + 92652 * 2 ^ 59
def prefixEnd_92652 : Nat := 4983230072969 + 3 ^ 40 * 92652 * 2
def baseEnd_92652 : Nat := 15858336533492244107969

theorem tailTrace_92652 : CollatzResearch.WordTrace tailWord_92652 prefixEnd_92652 15858336533492244107969 := by
  unfold tailWord_92652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689648030172551273460105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2252864040230068364613473 1689648030172551273460105)
  ·
    refine ⟨1267236022629413455095079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689648030172551273460105 1267236022629413455095079)
    ·
      refine ⟨1900854033944120182642619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267236022629413455095079 1900854033944120182642619)
      ·
        refine ⟨2851281050916180273963929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900854033944120182642619 2851281050916180273963929)
        ·
          refine ⟨2138460788187135205472947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851281050916180273963929 2138460788187135205472947)
          ·
            refine ⟨3207691182280702808209421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138460788187135205472947 3207691182280702808209421)
            ·
              refine ⟨1202884193355263553078533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3207691182280702808209421 1202884193355263553078533)
              ·
                refine ⟨225540786254111916202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1202884193355263553078533 225540786254111916202225)
                ·
                  refine ⟨169155589690583937151669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225540786254111916202225 169155589690583937151669)
                  ·
                    refine ⟨15858336533492244107969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169155589690583937151669 15858336533492244107969)
                    ·
                      rfl

theorem cell23_92652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_92652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92652 prefixEnd_92652 := by exact prefixLift 92652
  have htrace : WordTrace (prefixWord ++ tailWord_92652) baseStart_92652 baseEnd_92652 := by
    simpa [prefixWord, tailWord_92652, baseEnd_92652] using wordTrace_append hprefix tailTrace_92652
  have hstable : (prefixWord ++ tailWord_92652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92652).length < 2 ^ (prefixWord ++ tailWord_92652).sum := by decide
  have hdescent : baseEnd_92652 < baseStart_92652 := by decide
  rcases family_descends (prefixWord ++ tailWord_92652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92686 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_92686 : Nat := 118140960795 + 92686 * 2 ^ 59
def prefixEnd_92686 : Nat := 4983230072969 + 3 ^ 40 * 92686 * 2
def baseEnd_92686 : Nat := 15864155980909866432917

theorem tailTrace_92686 : CollatzResearch.WordTrace tailWord_92686 prefixEnd_92686 15864155980909866432917 := by
  unfold tailWord_92686
  simp only [CollatzResearch.WordTrace]
  refine ⟨422567017777740794207239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2253690761481284235771941 422567017777740794207239)
  ·
    refine ⟨633850526666611191310859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422567017777740794207239 633850526666611191310859)
    ·
      refine ⟨950775789999916786966289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633850526666611191310859 950775789999916786966289)
      ·
        refine ⟨713081842499937590224717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950775789999916786966289 713081842499937590224717)
        ·
          refine ⟨267405690937476596334269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713081842499937590224717 267405690937476596334269)
          ·
            refine ⟨100277134101553723625351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267405690937476596334269 100277134101553723625351)
            ·
              refine ⟨150415701152330585438027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100277134101553723625351 150415701152330585438027)
              ·
                refine ⟨225623551728495878157041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150415701152330585438027 225623551728495878157041)
                ·
                  refine ⟨169217663796371908617781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225623551728495878157041 169217663796371908617781)
                  ·
                    refine ⟨15864155980909866432917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169217663796371908617781 15864155980909866432917)
                    ·
                      rfl

theorem cell23_92686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_92686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92686 prefixEnd_92686 := by exact prefixLift 92686
  have htrace : WordTrace (prefixWord ++ tailWord_92686) baseStart_92686 baseEnd_92686 := by
    simpa [prefixWord, tailWord_92686, baseEnd_92686] using wordTrace_append hprefix tailTrace_92686
  have hstable : (prefixWord ++ tailWord_92686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92686).length < 2 ^ (prefixWord ++ tailWord_92686).sum := by decide
  have hdescent : baseEnd_92686 < baseStart_92686 := by decide
  rcases family_descends (prefixWord ++ tailWord_92686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92709 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_92709 : Nat := 118140960795 + 92709 * 2 ^ 59
def prefixEnd_92709 : Nat := 4983230072969 + 3 ^ 40 * 92709 * 2
def baseEnd_92709 : Nat := 47604277997783009311145

theorem tailTrace_92709 : CollatzResearch.WordTrace tailWord_92709 prefixEnd_92709 47604277997783009311145 := by
  unfold tailWord_92709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381375021138601281745181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2254250014092400854496787 3381375021138601281745181)
  ·
    refine ⟨1268015632926975480654443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3381375021138601281745181 1268015632926975480654443)
    ·
      refine ⟨1902023449390463220981665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268015632926975480654443 1902023449390463220981665)
      ·
        refine ⟨1426517587042847415736249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1902023449390463220981665 1426517587042847415736249)
        ·
          refine ⟨1069888190282135561802187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426517587042847415736249 1069888190282135561802187)
          ·
            refine ⟨1604832285423203342703281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069888190282135561802187 1604832285423203342703281)
            ·
              refine ⟨1203624214067402507027461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604832285423203342703281 1203624214067402507027461)
              ·
                refine ⟨225679540137637970067649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1203624214067402507027461 225679540137637970067649)
                ·
                  refine ⟨169259655103228477550737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225679540137637970067649 169259655103228477550737)
                  ·
                    refine ⟨126944741327421358163053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169259655103228477550737 126944741327421358163053)
                    ·
                      refine ⟨47604277997783009311145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126944741327421358163053 47604277997783009311145)
                      ·
                        rfl

theorem cell23_92709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_92709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92709 prefixEnd_92709 := by exact prefixLift 92709
  have htrace : WordTrace (prefixWord ++ tailWord_92709) baseStart_92709 baseEnd_92709 := by
    simpa [prefixWord, tailWord_92709, baseEnd_92709] using wordTrace_append hprefix tailTrace_92709
  have hstable : (prefixWord ++ tailWord_92709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92709).length < 2 ^ (prefixWord ++ tailWord_92709).sum := by decide
  have hdescent : baseEnd_92709 < baseStart_92709 := by decide
  rcases family_descends (prefixWord ++ tailWord_92709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92726 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_92726 : Nat := 118140960795 + 92726 * 2 ^ 59
def prefixEnd_92726 : Nat := 4983230072969 + 3 ^ 40 * 92726 * 2
def baseEnd_92726 : Nat := 47613007168909442798567

theorem tailTrace_92726 : CollatzResearch.WordTrace tailWord_92726 prefixEnd_92726 47613007168909442798567 := by
  unfold tailWord_92726
  simp only [CollatzResearch.WordTrace]
  refine ⟨211374691379813324069627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2254663374718008790076021 211374691379813324069627)
  ·
    refine ⟨317062037069719986104441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211374691379813324069627 317062037069719986104441)
    ·
      refine ⟨237796527802289989578331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317062037069719986104441 237796527802289989578331)
      ·
        refine ⟨356694791703434984367497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237796527802289989578331 356694791703434984367497)
        ·
          refine ⟨267521093777576238275623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356694791703434984367497 267521093777576238275623)
          ·
            refine ⟨401281640666364357413435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267521093777576238275623 401281640666364357413435)
            ·
              refine ⟨601922460999546536120153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401281640666364357413435 601922460999546536120153)
              ·
                refine ⟨451441845749659902090115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601922460999546536120153 451441845749659902090115)
                ·
                  refine ⟨677162768624489853135173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451441845749659902090115 677162768624489853135173)
                  ·
                    refine ⟨126968019117091847462845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 677162768624489853135173 126968019117091847462845)
                    ·
                      refine ⟨47613007168909442798567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 126968019117091847462845 47613007168909442798567)
                      ·
                        rfl

theorem cell23_92726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_92726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92726 prefixEnd_92726 := by exact prefixLift 92726
  have htrace : WordTrace (prefixWord ++ tailWord_92726) baseStart_92726 baseEnd_92726 := by
    simpa [prefixWord, tailWord_92726, baseEnd_92726] using wordTrace_append hprefix tailTrace_92726
  have hstable : (prefixWord ++ tailWord_92726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92726).length < 2 ^ (prefixWord ++ tailWord_92726).sum := by decide
  have hdescent : baseEnd_92726 < baseStart_92726 := by decide
  rcases family_descends (prefixWord ++ tailWord_92726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92759 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 1, 5]
def baseStart_92759 : Nat := 118140960795 + 92759 * 2 ^ 59
def prefixEnd_92759 : Nat := 4983230072969 + 3 ^ 40 * 92759 * 2
def baseEnd_92759 : Nat := 15876650676835937895305

theorem tailTrace_92759 : CollatzResearch.WordTrace tailWord_92759 prefixEnd_92759 15876650676835937895305 := by
  unfold tailWord_92759
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383198670957459821065331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255465780638306547376887 3383198670957459821065331)
  ·
    refine ⟨5074798006436189731597997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383198670957459821065331 5074798006436189731597997)
    ·
      refine ⟨1903049252413571149349249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5074798006436189731597997 1903049252413571149349249)
      ·
        refine ⟨1427286939310178362011937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1903049252413571149349249 1427286939310178362011937)
        ·
          refine ⟨1070465204482633771508953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1427286939310178362011937 1070465204482633771508953)
          ·
            refine ⟨802848903361975328631715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070465204482633771508953 802848903361975328631715)
            ·
              refine ⟨1204273355042962992947573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802848903361975328631715 1204273355042962992947573)
              ·
                refine ⟨112900627035277780588835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1204273355042962992947573 112900627035277780588835)
                ·
                  refine ⟨169350940552916670883253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112900627035277780588835 169350940552916670883253)
                  ·
                    refine ⟨15876650676835937895305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169350940552916670883253 15876650676835937895305)
                    ·
                      rfl

theorem cell23_92759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_92759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92759 prefixEnd_92759 := by exact prefixLift 92759
  have htrace : WordTrace (prefixWord ++ tailWord_92759) baseStart_92759 baseEnd_92759 := by
    simpa [prefixWord, tailWord_92759, baseEnd_92759] using wordTrace_append hprefix tailTrace_92759
  have hstable : (prefixWord ++ tailWord_92759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92759).length < 2 ^ (prefixWord ++ tailWord_92759).sum := by decide
  have hdescent : baseEnd_92759 < baseStart_92759 := by decide
  rcases family_descends (prefixWord ++ tailWord_92759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92779 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 6, 2]
def baseStart_92779 : Nat := 118140960795 + 92779 * 2 ^ 59
def prefixEnd_92779 : Nat := 4983230072969 + 3 ^ 40 * 92779 * 2
def baseEnd_92779 : Nat := 47640221643597735435823

theorem tailTrace_92779 : CollatzResearch.WordTrace tailWord_92779 prefixEnd_92779 47640221643597735435823 := by
  unfold tailWord_92779
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383928130885003236793391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255952087256668824528927 3383928130885003236793391)
  ·
    refine ⟨5075892196327504855190087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383928130885003236793391 5075892196327504855190087)
    ·
      refine ⟨7613838294491257282785131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5075892196327504855190087 7613838294491257282785131)
      ·
        refine ⟨11420757441736885924177697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613838294491257282785131 11420757441736885924177697)
        ·
          refine ⟨8565568081302664443133273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11420757441736885924177697 8565568081302664443133273)
          ·
            refine ⟨6424176060976998332349955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8565568081302664443133273 6424176060976998332349955)
            ·
              refine ⟨9636264091465497498524933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424176060976998332349955 9636264091465497498524933)
              ·
                refine ⟨1806799517149780780973425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9636264091465497498524933 1806799517149780780973425)
                ·
                  refine ⟨1355099637862335585730069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806799517149780780973425 1355099637862335585730069)
                  ·
                    refine ⟨63520295524796980581097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1355099637862335585730069 63520295524796980581097)
                    ·
                      refine ⟨47640221643597735435823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63520295524796980581097 47640221643597735435823)
                      ·
                        rfl

theorem cell23_92779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 6, 2].length) (baseStart_92779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92779 prefixEnd_92779 := by exact prefixLift 92779
  have htrace : WordTrace (prefixWord ++ tailWord_92779) baseStart_92779 baseEnd_92779 := by
    simpa [prefixWord, tailWord_92779, baseEnd_92779] using wordTrace_append hprefix tailTrace_92779
  have hstable : (prefixWord ++ tailWord_92779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92779).length < 2 ^ (prefixWord ++ tailWord_92779).sum := by decide
  have hdescent : baseEnd_92779 < baseStart_92779 := by decide
  rcases family_descends (prefixWord ++ tailWord_92779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92796 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_92796 : Nat := 118140960795 + 92796 * 2 ^ 59
def prefixEnd_92796 : Nat := 4983230072969 + 3 ^ 40 * 92796 * 2
def baseEnd_92796 : Nat := 47648950814724168923245

theorem tailTrace_92796 : CollatzResearch.WordTrace tailWord_92796 prefixEnd_92796 47648950814724168923245 := by
  unfold tailWord_92796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692274085911707570081121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2256365447882276760108161 1692274085911707570081121)
  ·
    refine ⟨1269205564433780677560841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1692274085911707570081121 1269205564433780677560841)
    ·
      refine ⟨951904173325335508170631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1269205564433780677560841 951904173325335508170631)
      ·
        refine ⟨1427856259988003262255947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951904173325335508170631 1427856259988003262255947)
        ·
          refine ⟨2141784389982004893383921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427856259988003262255947 2141784389982004893383921)
          ·
            refine ⟨1606338292486503670037941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141784389982004893383921 1606338292486503670037941)
            ·
              refine ⟨150594214920609719066057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1606338292486503670037941 150594214920609719066057)
              ·
                refine ⟨112945661190457289299543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150594214920609719066057 112945661190457289299543)
                ·
                  refine ⟨169418491785685933949315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112945661190457289299543 169418491785685933949315)
                  ·
                    refine ⟨254127737678528900923973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169418491785685933949315 254127737678528900923973)
                    ·
                      refine ⟨47648950814724168923245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 254127737678528900923973 47648950814724168923245)
                      ·
                        rfl

theorem cell23_92796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_92796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92796 prefixEnd_92796 := by exact prefixLift 92796
  have htrace : WordTrace (prefixWord ++ tailWord_92796) baseStart_92796 baseEnd_92796 := by
    simpa [prefixWord, tailWord_92796, baseEnd_92796] using wordTrace_append hprefix tailTrace_92796
  have hstable : (prefixWord ++ tailWord_92796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92796).length < 2 ^ (prefixWord ++ tailWord_92796).sum := by decide
  have hdescent : baseEnd_92796 < baseStart_92796 := by decide
  rcases family_descends (prefixWord ++ tailWord_92796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92830 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_92830 : Nat := 118140960795 + 92830 * 2 ^ 59
def prefixEnd_92830 : Nat := 4983230072969 + 3 ^ 40 * 92830 * 2
def baseEnd_92830 : Nat := 47666409156977035898089

theorem tailTrace_92830 : CollatzResearch.WordTrace tailWord_92830 prefixEnd_92830 47666409156977035898089 := by
  unfold tailWord_92830
  simp only [CollatzResearch.WordTrace]
  refine ⟨423223531712529868362493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2257192169133492631266629 423223531712529868362493)
  ·
    refine ⟨158708824392198700635935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 423223531712529868362493 158708824392198700635935)
    ·
      refine ⟨238063236588298050953903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158708824392198700635935 238063236588298050953903)
      ·
        refine ⟨357094854882447076430855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238063236588298050953903 357094854882447076430855)
        ·
          refine ⟨535642282323670614646283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357094854882447076430855 535642282323670614646283)
          ·
            refine ⟨803463423485505921969425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535642282323670614646283 803463423485505921969425)
            ·
              refine ⟨602597567614129441477069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803463423485505921969425 602597567614129441477069)
              ·
                refine ⟨225974087855298540553901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602597567614129441477069 225974087855298540553901)
                ·
                  refine ⟨84740282945736952707713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225974087855298540553901 84740282945736952707713)
                  ·
                    refine ⟨63555212209302714530785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84740282945736952707713 63555212209302714530785)
                    ·
                      refine ⟨47666409156977035898089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63555212209302714530785 47666409156977035898089)
                      ·
                        rfl

theorem cell23_92830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_92830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92830 prefixEnd_92830 := by exact prefixLift 92830
  have htrace : WordTrace (prefixWord ++ tailWord_92830) baseStart_92830 baseEnd_92830 := by
    simpa [prefixWord, tailWord_92830, baseEnd_92830] using wordTrace_append hprefix tailTrace_92830
  have hstable : (prefixWord ++ tailWord_92830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92830).length < 2 ^ (prefixWord ++ tailWord_92830).sum := by decide
  have hdescent : baseEnd_92830 < baseStart_92830 := by decide
  rcases family_descends (prefixWord ++ tailWord_92830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92943 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 5]
def baseStart_92943 : Nat := 118140960795 + 92943 * 2 ^ 59
def prefixEnd_92943 : Nat := 4983230072969 + 3 ^ 40 * 92943 * 2
def baseEnd_92943 : Nat := 5302714718992788198341

theorem tailTrace_92943 : CollatzResearch.WordTrace tailWord_92943 prefixEnd_92943 5302714718992788198341 := by
  unfold tailWord_92943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389909702290859245763483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2259939801527239497175655 3389909702290859245763483)
  ·
    refine ⟨5084864553436288868645225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389909702290859245763483 5084864553436288868645225)
    ·
      refine ⟨3813648415077216651483919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5084864553436288868645225 3813648415077216651483919)
      ·
        refine ⟨5720472622615824977225879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813648415077216651483919 5720472622615824977225879)
        ·
          refine ⟨8580708933923737465838819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720472622615824977225879 8580708933923737465838819)
          ·
            refine ⟨12871063400885606198758229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8580708933923737465838819 12871063400885606198758229)
            ·
              refine ⟨75416387114564098820849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 12871063400885606198758229 75416387114564098820849)
              ·
                refine ⟨56562290335923074115637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75416387114564098820849 56562290335923074115637)
                ·
                  refine ⟨5302714718992788198341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56562290335923074115637 5302714718992788198341)
                  ·
                    rfl

theorem cell23_92943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 5].length) (baseStart_92943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_92943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_92943 prefixEnd_92943 := by exact prefixLift 92943
  have htrace : WordTrace (prefixWord ++ tailWord_92943) baseStart_92943 baseEnd_92943 := by
    simpa [prefixWord, tailWord_92943, baseEnd_92943] using wordTrace_append hprefix tailTrace_92943
  have hstable : (prefixWord ++ tailWord_92943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92943).length < 2 ^ (prefixWord ++ tailWord_92943).sum := by decide
  have hdescent : baseEnd_92943 < baseStart_92943 := by decide
  rcases family_descends (prefixWord ++ tailWord_92943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93020 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_93020 : Nat := 118140960795 + 93020 * 2 ^ 59
def prefixEnd_93020 : Nat := 4983230072969 + 3 ^ 40 * 93020 * 2
def baseEnd_93020 : Nat := 15921323493777097507405

theorem tailTrace_93020 : CollatzResearch.WordTrace tailWord_93020 prefixEnd_93020 15921323493777097507405 := by
  unfold tailWord_93020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696359061505950698158257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2261812082007934264211009 1696359061505950698158257)
  ·
    refine ⟨1272269296129463023618693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1696359061505950698158257 1272269296129463023618693)
    ·
      refine ⟨238550493024274316928505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1272269296129463023618693 238550493024274316928505)
      ·
        refine ⟨178912869768205737696379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238550493024274316928505 178912869768205737696379)
        ·
          refine ⟨268369304652308606544569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178912869768205737696379 268369304652308606544569)
          ·
            refine ⟨201276978489231454908427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268369304652308606544569 201276978489231454908427)
            ·
              refine ⟨301915467733847182362641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201276978489231454908427 301915467733847182362641)
              ·
                refine ⟨226436600800385386771981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301915467733847182362641 226436600800385386771981)
                ·
                  refine ⟨84913725300144520039493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226436600800385386771981 84913725300144520039493)
                  ·
                    refine ⟨15921323493777097507405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84913725300144520039493 15921323493777097507405)
                    ·
                      rfl

theorem cell23_93020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_93020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93020 prefixEnd_93020 := by exact prefixLift 93020
  have htrace : WordTrace (prefixWord ++ tailWord_93020) baseStart_93020 baseEnd_93020 := by
    simpa [prefixWord, tailWord_93020, baseEnd_93020] using wordTrace_append hprefix tailTrace_93020
  have hstable : (prefixWord ++ tailWord_93020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93020).length < 2 ^ (prefixWord ++ tailWord_93020).sum := by decide
  have hdescent : baseEnd_93020 < baseStart_93020 := by decide
  rcases family_descends (prefixWord ++ tailWord_93020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93167 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 3]
def baseStart_93167 : Nat := 118140960795 + 93167 * 2 ^ 59
def prefixEnd_93167 : Nat := 4983230072969 + 3 ^ 40 * 93167 * 2
def baseEnd_93167 : Nat := 47839452137542217384039

theorem tailTrace_93167 : CollatzResearch.WordTrace tailWord_93167 prefixEnd_93167 47839452137542217384039 := by
  unfold tailWord_93167
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398079653479345501917755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2265386435652897001278503 3398079653479345501917755)
  ·
    refine ⟨5097119480219018252876633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3398079653479345501917755 5097119480219018252876633)
    ·
      refine ⟨3822839610164263689657475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5097119480219018252876633 3822839610164263689657475)
      ·
        refine ⟨5734259415246395534486213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822839610164263689657475 5734259415246395534486213)
        ·
          refine ⟨1075173640358699162716165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5734259415246395534486213 1075173640358699162716165)
          ·
            refine ⟨201595057567256093009281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1075173640358699162716165 201595057567256093009281)
            ·
              refine ⟨151196293175442069756961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201595057567256093009281 151196293175442069756961)
              ·
                refine ⟨113397219881581552317721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151196293175442069756961 113397219881581552317721)
                ·
                  refine ⟨85047914911186164238291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113397219881581552317721 85047914911186164238291)
                  ·
                    refine ⟨127571872366779246357437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85047914911186164238291 127571872366779246357437)
                    ·
                      refine ⟨47839452137542217384039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 127571872366779246357437 47839452137542217384039)
                      ·
                        rfl

theorem cell23_93167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_93167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93167 prefixEnd_93167 := by exact prefixLift 93167
  have htrace : WordTrace (prefixWord ++ tailWord_93167) baseStart_93167 baseEnd_93167 := by
    simpa [prefixWord, tailWord_93167, baseEnd_93167] using wordTrace_append hprefix tailTrace_93167
  have hstable : (prefixWord ++ tailWord_93167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93167).length < 2 ^ (prefixWord ++ tailWord_93167).sum := by decide
  have hdescent : baseEnd_93167 < baseStart_93167 := by decide
  rcases family_descends (prefixWord ++ tailWord_93167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93207 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_93207 : Nat := 118140960795 + 93207 * 2 ^ 59
def prefixEnd_93207 : Nat := 4983230072969 + 3 ^ 40 * 93207 * 2
def baseEnd_93207 : Nat := 47859991363722060883855

theorem tailTrace_93207 : CollatzResearch.WordTrace tailWord_93207 prefixEnd_93207 47859991363722060883855 := by
  unfold tailWord_93207
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399538573334432333373875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2266359048889621555582583 3399538573334432333373875)
  ·
    refine ⟨5099307860001648500060813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3399538573334432333373875 5099307860001648500060813)
    ·
      refine ⟨1912240447500618187522805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5099307860001648500060813 1912240447500618187522805)
      ·
        refine ⟨179272541953182955080263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1912240447500618187522805 179272541953182955080263)
        ·
          refine ⟨268908812929774432620395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179272541953182955080263 268908812929774432620395)
          ·
            refine ⟨403363219394661648930593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268908812929774432620395 403363219394661648930593)
            ·
              refine ⟨302522414545996236697945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403363219394661648930593 302522414545996236697945)
              ·
                refine ⟨226891810909497177523459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302522414545996236697945 226891810909497177523459)
                ·
                  refine ⟨340337716364245766285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226891810909497177523459 340337716364245766285189)
                  ·
                    refine ⟨63813321818296081178473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340337716364245766285189 63813321818296081178473)
                    ·
                      refine ⟨47859991363722060883855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63813321818296081178473 47859991363722060883855)
                      ·
                        rfl

theorem cell23_93207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_93207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93207 prefixEnd_93207 := by exact prefixLift 93207
  have htrace : WordTrace (prefixWord ++ tailWord_93207) baseStart_93207 baseEnd_93207 := by
    simpa [prefixWord, tailWord_93207, baseEnd_93207] using wordTrace_append hprefix tailTrace_93207
  have hstable : (prefixWord ++ tailWord_93207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93207).length < 2 ^ (prefixWord ++ tailWord_93207).sum := by decide
  have hdescent : baseEnd_93207 < baseStart_93207 := by decide
  rcases family_descends (prefixWord ++ tailWord_93207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93220 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_93220 : Nat := 118140960795 + 93220 * 2 ^ 59
def prefixEnd_93220 : Nat := 4983230072969 + 3 ^ 40 * 93220 * 2
def baseEnd_93220 : Nat := 47866666612230510021295

theorem tailTrace_93220 : CollatzResearch.WordTrace tailWord_93220 prefixEnd_93220 47866666612230510021295 := by
  unfold tailWord_93220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700006361143667776798557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2266675148191557035731409 1700006361143667776798557)
  ·
    refine ⟨637502385428875416299459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1700006361143667776798557 637502385428875416299459)
    ·
      refine ⟨956253578143313124449189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637502385428875416299459 956253578143313124449189)
      ·
        refine ⟨179297545901871210834223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 956253578143313124449189 179297545901871210834223)
        ·
          refine ⟨268946318852806816251335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179297545901871210834223 268946318852806816251335)
          ·
            refine ⟨403419478279210224377003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268946318852806816251335 403419478279210224377003)
            ·
              refine ⟨605129217418815336565505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403419478279210224377003 605129217418815336565505)
              ·
                refine ⟨453846913064111502424129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605129217418815336565505 453846913064111502424129)
                ·
                  refine ⟨340385184798083626818097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453846913064111502424129 340385184798083626818097)
                  ·
                    refine ⟨255288888598562720113573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 340385184798083626818097 255288888598562720113573)
                    ·
                      refine ⟨47866666612230510021295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 255288888598562720113573 47866666612230510021295)
                      ·
                        rfl

theorem cell23_93220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_93220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93220 prefixEnd_93220 := by exact prefixLift 93220
  have htrace : WordTrace (prefixWord ++ tailWord_93220) baseStart_93220 baseEnd_93220 := by
    simpa [prefixWord, tailWord_93220, baseEnd_93220] using wordTrace_append hprefix tailTrace_93220
  have hstable : (prefixWord ++ tailWord_93220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93220).length < 2 ^ (prefixWord ++ tailWord_93220).sum := by decide
  have hdescent : baseEnd_93220 < baseStart_93220 := by decide
  rcases family_descends (prefixWord ++ tailWord_93220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93230 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_93230 : Nat := 118140960795 + 93230 * 2 ^ 59
def prefixEnd_93230 : Nat := 4983230072969 + 3 ^ 40 * 93230 * 2
def baseEnd_93230 : Nat := 5319089046530607877361

theorem tailTrace_93230 : CollatzResearch.WordTrace tailWord_93230 prefixEnd_93230 5319089046530607877361 := by
  unfold tailWord_93230
  simp only [CollatzResearch.WordTrace]
  refine ⟨425047181531388407682643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2266918301500738174307429 425047181531388407682643)
  ·
    refine ⟨637570772297082611523965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425047181531388407682643 637570772297082611523965)
    ·
      refine ⟨239089039611405979321487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 637570772297082611523965 239089039611405979321487)
      ·
        refine ⟨358633559417108968982231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239089039611405979321487 358633559417108968982231)
        ·
          refine ⟨537950339125663453473347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358633559417108968982231 537950339125663453473347)
          ·
            refine ⟨806925508688495180210021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537950339125663453473347 806925508688495180210021)
            ·
              refine ⟨151298532879092846289379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 806925508688495180210021 151298532879092846289379)
              ·
                refine ⟨226947799318639269434069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151298532879092846289379 226947799318639269434069)
                ·
                  refine ⟨5319089046530607877361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 226947799318639269434069 5319089046530607877361)
                  ·
                    rfl

theorem cell23_93230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_93230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93230 prefixEnd_93230 := by exact prefixLift 93230
  have htrace : WordTrace (prefixWord ++ tailWord_93230) baseStart_93230 baseEnd_93230 := by
    simpa [prefixWord, tailWord_93230, baseEnd_93230] using wordTrace_append hprefix tailTrace_93230
  have hstable : (prefixWord ++ tailWord_93230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93230).length < 2 ^ (prefixWord ++ tailWord_93230).sum := by decide
  have hdescent : baseEnd_93230 < baseStart_93230 := by decide
  rcases family_descends (prefixWord ++ tailWord_93230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93240 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_93240 : Nat := 118140960795 + 93240 * 2 ^ 59
def prefixEnd_93240 : Nat := 4983230072969 + 3 ^ 40 * 93240 * 2
def baseEnd_93240 : Nat := 47876936225320431771203

theorem tailTrace_93240 : CollatzResearch.WordTrace tailWord_93240 prefixEnd_93240 47876936225320431771203 := by
  unfold tailWord_93240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700371091107439484662587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2267161454809919312883449 1700371091107439484662587)
  ·
    refine ⟨2550556636661159226993881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1700371091107439484662587 2550556636661159226993881)
    ·
      refine ⟨1912917477495869420245411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550556636661159226993881 1912917477495869420245411)
      ·
        refine ⟨2869376216243804130368117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912917477495869420245411 2869376216243804130368117)
        ·
          refine ⟨269004020272856637222011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2869376216243804130368117 269004020272856637222011)
          ·
            refine ⟨403506030409284955833017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269004020272856637222011 403506030409284955833017)
            ·
              refine ⟨302629522806963716874763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403506030409284955833017 302629522806963716874763)
              ·
                refine ⟨453944284210445575312145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302629522806963716874763 453944284210445575312145)
                ·
                  refine ⟨340458213157834181484109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453944284210445575312145 340458213157834181484109)
                  ·
                    refine ⟨127671829934187818056541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340458213157834181484109 127671829934187818056541)
                    ·
                      refine ⟨47876936225320431771203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 127671829934187818056541 47876936225320431771203)
                      ·
                        rfl

theorem cell23_93240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_93240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93240 prefixEnd_93240 := by exact prefixLift 93240
  have htrace : WordTrace (prefixWord ++ tailWord_93240) baseStart_93240 baseEnd_93240 := by
    simpa [prefixWord, tailWord_93240, baseEnd_93240] using wordTrace_append hprefix tailTrace_93240
  have hstable : (prefixWord ++ tailWord_93240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93240).length < 2 ^ (prefixWord ++ tailWord_93240).sum := by decide
  have hdescent : baseEnd_93240 < baseStart_93240 := by decide
  rcases family_descends (prefixWord ++ tailWord_93240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93241 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 2, 2, 2]
def baseStart_93241 : Nat := 118140960795 + 93241 * 2 ^ 59
def prefixEnd_93241 : Nat := 4983230072969 + 3 ^ 40 * 93241 * 2
def baseEnd_93241 : Nat := 47877449705974927858699

theorem tailTrace_93241 : CollatzResearch.WordTrace tailWord_93241 prefixEnd_93241 47877449705974927858699 := by
  unfold tailWord_93241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400778655211256140111577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2267185770140837426741051 3400778655211256140111577)
  ·
    refine ⟨2550583991408442105083683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3400778655211256140111577 2550583991408442105083683)
    ·
      refine ⟨3825875987112663157625525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550583991408442105083683 3825875987112663157625525)
      ·
        refine ⟨358675873791812171027393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3825875987112663157625525 358675873791812171027393)
        ·
          refine ⟨269006905343859128270545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358675873791812171027393 269006905343859128270545)
          ·
            refine ⟨201755179007894346202909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269006905343859128270545 201755179007894346202909)
            ·
              refine ⟨75658192127960379826091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201755179007894346202909 75658192127960379826091)
              ·
                refine ⟨113487288191940569739137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75658192127960379826091 113487288191940569739137)
                ·
                  refine ⟨85115466143955427304353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113487288191940569739137 85115466143955427304353)
                  ·
                    refine ⟨63836599607966570478265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85115466143955427304353 63836599607966570478265)
                    ·
                      refine ⟨47877449705974927858699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63836599607966570478265 47877449705974927858699)
                      ·
                        rfl

theorem cell23_93241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_93241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93241 prefixEnd_93241 := by exact prefixLift 93241
  have htrace : WordTrace (prefixWord ++ tailWord_93241) baseStart_93241 baseEnd_93241 := by
    simpa [prefixWord, tailWord_93241, baseEnd_93241] using wordTrace_append hprefix tailTrace_93241
  have hstable : (prefixWord ++ tailWord_93241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93241).length < 2 ^ (prefixWord ++ tailWord_93241).sum := by decide
  have hdescent : baseEnd_93241 < baseStart_93241 := by decide
  rcases family_descends (prefixWord ++ tailWord_93241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93280 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_93280 : Nat := 118140960795 + 93280 * 2 ^ 59
def prefixEnd_93280 : Nat := 4983230072969 + 3 ^ 40 * 93280 * 2
def baseEnd_93280 : Nat := 47897475451500275271019

theorem tailTrace_93280 : CollatzResearch.WordTrace tailWord_93280 prefixEnd_93280 47897475451500275271019 := by
  unfold tailWord_93280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701100551034982900390647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2268134068046643867187529 1701100551034982900390647)
  ·
    refine ⟨2551650826552474350585971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701100551034982900390647 2551650826552474350585971)
    ·
      refine ⟨3827476239828711525878957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551650826552474350585971 3827476239828711525878957)
      ·
        refine ⟨1435303589935766822204609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3827476239828711525878957 1435303589935766822204609)
        ·
          refine ⟨1076477692451825116653457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1435303589935766822204609 1076477692451825116653457)
          ·
            refine ⟨807358269338868837490093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076477692451825116653457 807358269338868837490093)
            ·
              refine ⟨302759351002075814058785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807358269338868837490093 302759351002075814058785)
              ·
                refine ⟨227069513251556860544089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302759351002075814058785 227069513251556860544089)
                ·
                  refine ⟨170302134938667645408067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227069513251556860544089 170302134938667645408067)
                  ·
                    refine ⟨255453202408001468112101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170302134938667645408067 255453202408001468112101)
                    ·
                      refine ⟨47897475451500275271019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 255453202408001468112101 47897475451500275271019)
                      ·
                        rfl

theorem cell23_93280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_93280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93280 prefixEnd_93280 := by exact prefixLift 93280
  have htrace : WordTrace (prefixWord ++ tailWord_93280) baseStart_93280 baseEnd_93280 := by
    simpa [prefixWord, tailWord_93280, baseEnd_93280] using wordTrace_append hprefix tailTrace_93280
  have hstable : (prefixWord ++ tailWord_93280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93280).length < 2 ^ (prefixWord ++ tailWord_93280).sum := by decide
  have hdescent : baseEnd_93280 < baseStart_93280 := by decide
  rcases family_descends (prefixWord ++ tailWord_93280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93374 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_93374 : Nat := 118140960795 + 93374 * 2 ^ 59
def prefixEnd_93374 : Nat := 4983230072969 + 3 ^ 40 * 93374 * 2
def baseEnd_93374 : Nat := 47945742633022907495587

theorem tailTrace_93374 : CollatzResearch.WordTrace tailWord_93374 prefixEnd_93374 47945742633022907495587 := by
  unfold tailWord_93374
  simp only [CollatzResearch.WordTrace]
  refine ⟨425703695466177481837897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2270419709152946569802117 425703695466177481837897)
  ·
    refine ⟨319277771599633111378423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 425703695466177481837897 319277771599633111378423)
    ·
      refine ⟨478916657399449667067635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319277771599633111378423 478916657399449667067635)
      ·
        refine ⟨718374986099174500601453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478916657399449667067635 718374986099174500601453)
        ·
          refine ⟨269390619787190437725545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 718374986099174500601453 269390619787190437725545)
          ·
            refine ⟨202042964840392828294159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269390619787190437725545 202042964840392828294159)
            ·
              refine ⟨303064447260589242441239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202042964840392828294159 303064447260589242441239)
              ·
                refine ⟨454596670890883863661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303064447260589242441239 454596670890883863661859)
                ·
                  refine ⟨681895006336325795492789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454596670890883863661859 681895006336325795492789)
                  ·
                    refine ⟨63927656844030543327449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 681895006336325795492789 63927656844030543327449)
                    ·
                      refine ⟨47945742633022907495587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63927656844030543327449 47945742633022907495587)
                      ·
                        rfl

theorem cell23_93374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_93374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93374 prefixEnd_93374 := by exact prefixLift 93374
  have htrace : WordTrace (prefixWord ++ tailWord_93374) baseStart_93374 baseEnd_93374 := by
    simpa [prefixWord, tailWord_93374, baseEnd_93374] using wordTrace_append hprefix tailTrace_93374
  have hstable : (prefixWord ++ tailWord_93374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93374).length < 2 ^ (prefixWord ++ tailWord_93374).sum := by decide
  have hdescent : baseEnd_93374 < baseStart_93374 := by decide
  rcases family_descends (prefixWord ++ tailWord_93374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93398 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_93398 : Nat := 118140960795 + 93398 * 2 ^ 59
def prefixEnd_93398 : Nat := 4983230072969 + 3 ^ 40 * 93398 * 2
def baseEnd_93398 : Nat := 47958066168730813595477

theorem tailTrace_93398 : CollatzResearch.WordTrace tailWord_93398 prefixEnd_93398 47958066168730813595477 := by
  unfold tailWord_93398
  simp only [CollatzResearch.WordTrace]
  refine ⟨212906557227654497098553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2271003277094981302384565 212906557227654497098553)
  ·
    refine ⟨159679917920740872823915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212906557227654497098553 159679917920740872823915)
    ·
      refine ⟨239519876881111309235873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159679917920740872823915 239519876881111309235873)
      ·
        refine ⟨179639907660833481926905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239519876881111309235873 179639907660833481926905)
        ·
          refine ⟨134729930745625111445179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179639907660833481926905 134729930745625111445179)
          ·
            refine ⟨202094896118437667167769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134729930745625111445179 202094896118437667167769)
            ·
              refine ⟨151571172088828250375827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202094896118437667167769 151571172088828250375827)
              ·
                refine ⟨227356758133242375563741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151571172088828250375827 227356758133242375563741)
                ·
                  refine ⟨85258784299965890836403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227356758133242375563741 85258784299965890836403)
                  ·
                    refine ⟨127888176449948836254605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85258784299965890836403 127888176449948836254605)
                    ·
                      refine ⟨47958066168730813595477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 127888176449948836254605 47958066168730813595477)
                      ·
                        rfl

theorem cell23_93398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_93398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93398 prefixEnd_93398 := by exact prefixLift 93398
  have htrace : WordTrace (prefixWord ++ tailWord_93398) baseStart_93398 baseEnd_93398 := by
    simpa [prefixWord, tailWord_93398, baseEnd_93398] using wordTrace_append hprefix tailTrace_93398
  have hstable : (prefixWord ++ tailWord_93398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93398).length < 2 ^ (prefixWord ++ tailWord_93398).sum := by decide
  have hdescent : baseEnd_93398 < baseStart_93398 := by decide
  rcases family_descends (prefixWord ++ tailWord_93398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93421 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_93421 : Nat := 118140960795 + 93421 * 2 ^ 59
def prefixEnd_93421 : Nat := 4983230072969 + 3 ^ 40 * 93421 * 2
def baseEnd_93421 : Nat := 47969876223784223607871

theorem tailTrace_93421 : CollatzResearch.WordTrace tailWord_93421 prefixEnd_93421 47969876223784223607871 := by
  unfold tailWord_93421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407343794559146881664117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2271562529706097921109411 3407343794559146881664117)
  ·
    refine ⟨319438480739920020156011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3407343794559146881664117 319438480739920020156011)
    ·
      refine ⟨479157721109880030234017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319438480739920020156011 479157721109880030234017)
      ·
        refine ⟨359368290832410022675513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479157721109880030234017 359368290832410022675513)
        ·
          refine ⟨269526218124307517006635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359368290832410022675513 269526218124307517006635)
          ·
            refine ⟨404289327186461275509953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269526218124307517006635 404289327186461275509953)
            ·
              refine ⟨303216995389845956632465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404289327186461275509953 303216995389845956632465)
              ·
                refine ⟨227412746542384467474349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303216995389845956632465 227412746542384467474349)
                ·
                  refine ⟨85279779953394175302881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227412746542384467474349 85279779953394175302881)
                  ·
                    refine ⟨63959834965045631477161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85279779953394175302881 63959834965045631477161)
                    ·
                      refine ⟨47969876223784223607871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 63959834965045631477161 47969876223784223607871)
                      ·
                        rfl

theorem cell23_93421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_93421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93421 prefixEnd_93421 := by exact prefixLift 93421
  have htrace : WordTrace (prefixWord ++ tailWord_93421) baseStart_93421 baseEnd_93421 := by
    simpa [prefixWord, tailWord_93421, baseEnd_93421] using wordTrace_append hprefix tailTrace_93421
  have hstable : (prefixWord ++ tailWord_93421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93421).length < 2 ^ (prefixWord ++ tailWord_93421).sum := by decide
  have hdescent : baseEnd_93421 < baseStart_93421 := by decide
  rcases family_descends (prefixWord ++ tailWord_93421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93427 : List Nat := [1, 1, 1, 2, 2, 7, 2, 7]
def baseStart_93427 : Nat := 118140960795 + 93427 * 2 ^ 59
def prefixEnd_93427 : Nat := 4983230072969 + 3 ^ 40 * 93427 * 2
def baseEnd_93427 : Nat := 1776776189174488893809

theorem tailTrace_93427 : CollatzResearch.WordTrace tailWord_93427 prefixEnd_93427 1776776189174488893809 := by
  unfold tailWord_93427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407562632537409906382535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2271708421691606604255023 3407562632537409906382535)
  ·
    refine ⟨5111343948806114859573803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3407562632537409906382535 5111343948806114859573803)
    ·
      refine ⟨7667015923209172289360705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5111343948806114859573803 7667015923209172289360705)
      ·
        refine ⟨5750261942406879217020529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7667015923209172289360705 5750261942406879217020529)
        ·
          refine ⟨4312696456805159412765397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750261942406879217020529 4312696456805159412765397)
          ·
            refine ⟨101078823206370923736689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4312696456805159412765397 101078823206370923736689)
            ·
              refine ⟨75809117404778192802517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101078823206370923736689 75809117404778192802517)
              ·
                refine ⟨1776776189174488893809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75809117404778192802517 1776776189174488893809)
                ·
                  rfl

theorem cell23_93427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 7].length) (baseStart_93427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93427 prefixEnd_93427 := by exact prefixLift 93427
  have htrace : WordTrace (prefixWord ++ tailWord_93427) baseStart_93427 baseEnd_93427 := by
    simpa [prefixWord, tailWord_93427, baseEnd_93427] using wordTrace_append hprefix tailTrace_93427
  have hstable : (prefixWord ++ tailWord_93427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93427).length < 2 ^ (prefixWord ++ tailWord_93427).sum := by decide
  have hdescent : baseEnd_93427 < baseStart_93427 := by decide
  rcases family_descends (prefixWord ++ tailWord_93427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93450 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_93450 : Nat := 118140960795 + 93450 * 2 ^ 59
def prefixEnd_93450 : Nat := 4983230072969 + 3 ^ 40 * 93450 * 2
def baseEnd_93450 : Nat := 47984767162764610145237

theorem tailTrace_93450 : CollatzResearch.WordTrace tailWord_93450 prefixEnd_93450 47984767162764610145237 := by
  unfold tailWord_93450
  simp only [CollatzResearch.WordTrace]
  refine ⟨852100377863521208617451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2272267674302723222979869 852100377863521208617451)
  ·
    refine ⟨1278150566795281812926177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 852100377863521208617451 1278150566795281812926177)
    ·
      refine ⟨958612925096461359694633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278150566795281812926177 958612925096461359694633)
      ·
        refine ⟨718959693822346019770975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 958612925096461359694633 718959693822346019770975)
        ·
          refine ⟨1078439540733519029656463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718959693822346019770975 1078439540733519029656463)
          ·
            refine ⟨1617659311100278544484695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078439540733519029656463 1617659311100278544484695)
            ·
              refine ⟨2426488966650417816727043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617659311100278544484695 2426488966650417816727043)
              ·
                refine ⟨3639733449975626725090565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426488966650417816727043 3639733449975626725090565)
                ·
                  refine ⟨682450021870430010954481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3639733449975626725090565 682450021870430010954481)
                  ·
                    refine ⟨511837516402822508215861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682450021870430010954481 511837516402822508215861)
                    ·
                      refine ⟨47984767162764610145237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 511837516402822508215861 47984767162764610145237)
                      ·
                        rfl

theorem cell23_93450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_93450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93450 prefixEnd_93450 := by exact prefixLift 93450
  have htrace : WordTrace (prefixWord ++ tailWord_93450) baseStart_93450 baseEnd_93450 := by
    simpa [prefixWord, tailWord_93450, baseEnd_93450] using wordTrace_append hprefix tailTrace_93450
  have hstable : (prefixWord ++ tailWord_93450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93450).length < 2 ^ (prefixWord ++ tailWord_93450).sum := by decide
  have hdescent : baseEnd_93450 < baseStart_93450 := by decide
  rcases family_descends (prefixWord ++ tailWord_93450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93454 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_93454 : Nat := 118140960795 + 93454 * 2 ^ 59
def prefixEnd_93454 : Nat := 4983230072969 + 3 ^ 40 * 93454 * 2
def baseEnd_93454 : Nat := 47986821085382594495219

theorem tailTrace_93454 : CollatzResearch.WordTrace tailWord_93454 prefixEnd_93454 47986821085382594495219 := by
  unfold tailWord_93454
  simp only [CollatzResearch.WordTrace]
  refine ⟨426068425429949189701927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2272364935626395678410277 426068425429949189701927)
  ·
    refine ⟨639102638144923784552891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426068425429949189701927 639102638144923784552891)
    ·
      refine ⟨958653957217385676829337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639102638144923784552891 958653957217385676829337)
      ·
        refine ⟨718990467913039257622003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 958653957217385676829337 718990467913039257622003)
        ·
          refine ⟨1078485701869558886433005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718990467913039257622003 1078485701869558886433005)
          ·
            refine ⟨404432138201084582412377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1078485701869558886433005 404432138201084582412377)
            ·
              refine ⟨303324103650813436809283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404432138201084582412377 303324103650813436809283)
              ·
                refine ⟨454986155476220155213925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303324103650813436809283 454986155476220155213925)
                ·
                  refine ⟨85309904151791279102611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454986155476220155213925 85309904151791279102611)
                  ·
                    refine ⟨127964856227686918653917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85309904151791279102611 127964856227686918653917)
                    ·
                      refine ⟨47986821085382594495219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 127964856227686918653917 47986821085382594495219)
                      ·
                        rfl

theorem cell23_93454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_93454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93454 prefixEnd_93454 := by exact prefixLift 93454
  have htrace : WordTrace (prefixWord ++ tailWord_93454) baseStart_93454 baseEnd_93454 := by
    simpa [prefixWord, tailWord_93454, baseEnd_93454] using wordTrace_append hprefix tailTrace_93454
  have hstable : (prefixWord ++ tailWord_93454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93454).length < 2 ^ (prefixWord ++ tailWord_93454).sum := by decide
  have hdescent : baseEnd_93454 < baseStart_93454 := by decide
  rcases family_descends (prefixWord ++ tailWord_93454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93471 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 3]
def baseStart_93471 : Nat := 118140960795 + 93471 * 2 ^ 59
def prefixEnd_93471 : Nat := 4983230072969 + 3 ^ 40 * 93471 * 2
def baseEnd_93471 : Nat := 47995550256509027982641

theorem tailTrace_93471 : CollatzResearch.WordTrace tailWord_93471 prefixEnd_93471 47995550256509027982641 := by
  unfold tailWord_93471
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409167444378005420984267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2272778296252003613989511 3409167444378005420984267)
  ·
    refine ⟨5113751166567008131476401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3409167444378005420984267 5113751166567008131476401)
    ·
      refine ⟨3835313374925256098607301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5113751166567008131476401 3835313374925256098607301)
      ·
        refine ⟨719121257798485518488869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3835313374925256098607301 719121257798485518488869)
        ·
          refine ⟨134835235837216034716663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 719121257798485518488869 134835235837216034716663)
          ·
            refine ⟨202252853755824052074995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134835235837216034716663 202252853755824052074995)
            ·
              refine ⟨303379280633736078112493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202252853755824052074995 303379280633736078112493)
              ·
                refine ⟨113767230237651029292185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303379280633736078112493 113767230237651029292185)
                ·
                  refine ⟨85325422678238271969139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113767230237651029292185 85325422678238271969139)
                  ·
                    refine ⟨127988134017357407953709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85325422678238271969139 127988134017357407953709)
                    ·
                      refine ⟨47995550256509027982641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 127988134017357407953709 47995550256509027982641)
                      ·
                        rfl

theorem cell23_93471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_93471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93471 prefixEnd_93471 := by exact prefixLift 93471
  have htrace : WordTrace (prefixWord ++ tailWord_93471) baseStart_93471 baseEnd_93471 := by
    simpa [prefixWord, tailWord_93471, baseEnd_93471] using wordTrace_append hprefix tailTrace_93471
  have hstable : (prefixWord ++ tailWord_93471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93471).length < 2 ^ (prefixWord ++ tailWord_93471).sum := by decide
  have hdescent : baseEnd_93471 < baseStart_93471 := by decide
  rcases family_descends (prefixWord ++ tailWord_93471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93511 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_93511 : Nat := 118140960795 + 93511 * 2 ^ 59
def prefixEnd_93511 : Nat := 4983230072969 + 3 ^ 40 * 93511 * 2
def baseEnd_93511 : Nat := 48016089482688871482457

theorem tailTrace_93511 : CollatzResearch.WordTrace tailWord_93511 prefixEnd_93511 48016089482688871482457 := by
  unfold tailWord_93511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410626364233092252440387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2273750909488728168293591 3410626364233092252440387)
  ·
    refine ⟨5115939546349638378660581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3410626364233092252440387 5115939546349638378660581)
    ·
      refine ⟨959238664940557195998859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5115939546349638378660581 959238664940557195998859)
      ·
        refine ⟨1438857997410835793998289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959238664940557195998859 1438857997410835793998289)
        ·
          refine ⟨1079143498058126845498717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1438857997410835793998289 1079143498058126845498717)
          ·
            refine ⟨404678811771797567062019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079143498058126845498717 404678811771797567062019)
            ·
              refine ⟨607018217657696350593029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404678811771797567062019 607018217657696350593029)
              ·
                refine ⟨113815915810818065736193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607018217657696350593029 113815915810818065736193)
                ·
                  refine ⟨85361936858113549302145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113815915810818065736193 85361936858113549302145)
                  ·
                    refine ⟨64021452643585161976609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85361936858113549302145 64021452643585161976609)
                    ·
                      refine ⟨48016089482688871482457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64021452643585161976609 48016089482688871482457)
                      ·
                        rfl

theorem cell23_93511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_93511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93511 prefixEnd_93511 := by exact prefixLift 93511
  have htrace : WordTrace (prefixWord ++ tailWord_93511) baseStart_93511 baseEnd_93511 := by
    simpa [prefixWord, tailWord_93511, baseEnd_93511] using wordTrace_append hprefix tailTrace_93511
  have hstable : (prefixWord ++ tailWord_93511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93511).length < 2 ^ (prefixWord ++ tailWord_93511).sum := by decide
  have hdescent : baseEnd_93511 < baseStart_93511 := by decide
  rcases family_descends (prefixWord ++ tailWord_93511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93527 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_93527 : Nat := 118140960795 + 93527 * 2 ^ 59
def prefixEnd_93527 : Nat := 4983230072969 + 3 ^ 40 * 93527 * 2
def baseEnd_93527 : Nat := 48024305173160808882383

theorem tailTrace_93527 : CollatzResearch.WordTrace tailWord_93527 prefixEnd_93527 48024305173160808882383 := by
  unfold tailWord_93527
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411209932175126985022835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2274139954783417990015223 3411209932175126985022835)
  ·
    refine ⟨5116814898262690477534253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3411209932175126985022835 5116814898262690477534253)
    ·
      refine ⟨1918805586848508929075345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5116814898262690477534253 1918805586848508929075345)
      ·
        refine ⟨1439104190136381696806509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1918805586848508929075345 1439104190136381696806509)
        ·
          refine ⟨539664071301143136302441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1439104190136381696806509 539664071301143136302441)
          ·
            refine ⟨404748053475857352226831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539664071301143136302441 404748053475857352226831)
            ·
              refine ⟨607122080213786028340247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404748053475857352226831 607122080213786028340247)
              ·
                refine ⟨910683120320679042510371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607122080213786028340247 910683120320679042510371)
                ·
                  refine ⟨1366024680481018563765557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910683120320679042510371 1366024680481018563765557)
                  ·
                    refine ⟨128064813795095490353021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1366024680481018563765557 128064813795095490353021)
                    ·
                      refine ⟨48024305173160808882383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 128064813795095490353021 48024305173160808882383)
                      ·
                        rfl

theorem cell23_93527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_93527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93527 prefixEnd_93527 := by exact prefixLift 93527
  have htrace : WordTrace (prefixWord ++ tailWord_93527) baseStart_93527 baseEnd_93527 := by
    simpa [prefixWord, tailWord_93527, baseEnd_93527] using wordTrace_append hprefix tailTrace_93527
  have hstable : (prefixWord ++ tailWord_93527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93527).length < 2 ^ (prefixWord ++ tailWord_93527).sum := by decide
  have hdescent : baseEnd_93527 < baseStart_93527 := by decide
  rcases family_descends (prefixWord ++ tailWord_93527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93560 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_93560 : Nat := 118140960795 + 93560 * 2 ^ 59
def prefixEnd_93560 : Nat := 4983230072969 + 3 ^ 40 * 93560 * 2
def baseEnd_93560 : Nat := 16013750011586393256577

theorem tailTrace_93560 : CollatzResearch.WordTrace tailWord_93560 prefixEnd_93560 16013750011586393256577 := by
  unfold tailWord_93560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706206770527786810487067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2274942360703715747316089 1706206770527786810487067)
  ·
    refine ⟨2559310155791680215730601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706206770527786810487067 2559310155791680215730601)
    ·
      refine ⟨1919482616843760161797951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2559310155791680215730601 1919482616843760161797951)
      ·
        refine ⟨2879223925265640242696927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919482616843760161797951 2879223925265640242696927)
        ·
          refine ⟨4318835887898460364045391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879223925265640242696927 4318835887898460364045391)
          ·
            refine ⟨6478253831847690546068087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318835887898460364045391 6478253831847690546068087)
            ·
              refine ⟨9717380747771535819102131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478253831847690546068087 9717380747771535819102131)
              ·
                refine ⟨14576071121657303728653197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717380747771535819102131 14576071121657303728653197)
                ·
                  refine ⟨5466026670621488898244949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14576071121657303728653197 5466026670621488898244949)
                  ·
                    refine ⟨16013750011586393256577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 5466026670621488898244949 16013750011586393256577)
                    ·
                      rfl

theorem cell23_93560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_93560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93560 prefixEnd_93560 := by exact prefixLift 93560
  have htrace : WordTrace (prefixWord ++ tailWord_93560) baseStart_93560 baseEnd_93560 := by
    simpa [prefixWord, tailWord_93560, baseEnd_93560] using wordTrace_append hprefix tailTrace_93560
  have hstable : (prefixWord ++ tailWord_93560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93560).length < 2 ^ (prefixWord ++ tailWord_93560).sum := by decide
  have hdescent : baseEnd_93560 < baseStart_93560 := by decide
  rcases family_descends (prefixWord ++ tailWord_93560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93594 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_93594 : Nat := 118140960795 + 93594 * 2 ^ 59
def prefixEnd_93594 : Nat := 4983230072969 + 3 ^ 40 * 93594 * 2
def baseEnd_93594 : Nat := 16019569459004015581525

theorem tailTrace_93594 : CollatzResearch.WordTrace tailWord_93594 prefixEnd_93594 16019569459004015581525 := by
  unfold tailWord_93594
  simp only [CollatzResearch.WordTrace]
  refine ⟨853413405733099356927959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2275769081954931618474557 853413405733099356927959)
  ·
    refine ⟨1280120108599649035391939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853413405733099356927959 1280120108599649035391939)
    ·
      refine ⟨1920180162899473553087909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280120108599649035391939 1920180162899473553087909)
      ·
        refine ⟨360033780543651291203983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1920180162899473553087909 360033780543651291203983)
        ·
          refine ⟨540050670815476936805975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360033780543651291203983 540050670815476936805975)
          ·
            refine ⟨810076006223215405208963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540050670815476936805975 810076006223215405208963)
            ·
              refine ⟨1215114009334823107813445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810076006223215405208963 1215114009334823107813445)
              ·
                refine ⟨227833876750279332715021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1215114009334823107813445 227833876750279332715021)
                ·
                  refine ⟨85437703781354749768133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227833876750279332715021 85437703781354749768133)
                  ·
                    refine ⟨16019569459004015581525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85437703781354749768133 16019569459004015581525)
                    ·
                      rfl

theorem cell23_93594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_93594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93594 prefixEnd_93594 := by exact prefixLift 93594
  have htrace : WordTrace (prefixWord ++ tailWord_93594) baseStart_93594 baseEnd_93594 := by
    simpa [prefixWord, tailWord_93594, baseEnd_93594] using wordTrace_append hprefix tailTrace_93594
  have hstable : (prefixWord ++ tailWord_93594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93594).length < 2 ^ (prefixWord ++ tailWord_93594).sum := by decide
  have hdescent : baseEnd_93594 < baseStart_93594 := by decide
  rcases family_descends (prefixWord ++ tailWord_93594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93604 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_93604 : Nat := 118140960795 + 93604 * 2 ^ 59
def prefixEnd_93604 : Nat := 4983230072969 + 3 ^ 40 * 93604 * 2
def baseEnd_93604 : Nat := 48063843183557007619529

theorem tailTrace_93604 : CollatzResearch.WordTrace tailWord_93604 prefixEnd_93604 48063843183557007619529 := by
  unfold tailWord_93604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707009176448084567787933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2276012235264112757050577 1707009176448084567787933)
  ·
    refine ⟨640128441168031712920475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1707009176448084567787933 640128441168031712920475)
    ·
      refine ⟨960192661752047569380713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640128441168031712920475 960192661752047569380713)
      ·
        refine ⟨720144496314035677035535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960192661752047569380713 720144496314035677035535)
        ·
          refine ⟨1080216744471053515553303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720144496314035677035535 1080216744471053515553303)
          ·
            refine ⟨1620325116706580273329955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080216744471053515553303 1620325116706580273329955)
            ·
              refine ⟨2430487675059870409994933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620325116706580273329955 2430487675059870409994933)
              ·
                refine ⟨227858219536862850937025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2430487675059870409994933 227858219536862850937025)
                ·
                  refine ⟨170893664652647138202769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227858219536862850937025 170893664652647138202769)
                  ·
                    refine ⟨128170248489485353652077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170893664652647138202769 128170248489485353652077)
                    ·
                      refine ⟨48063843183557007619529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 128170248489485353652077 48063843183557007619529)
                      ·
                        rfl

theorem cell23_93604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_93604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93604 prefixEnd_93604 := by exact prefixLift 93604
  have htrace : WordTrace (prefixWord ++ tailWord_93604) baseStart_93604 baseEnd_93604 := by
    simpa [prefixWord, tailWord_93604, baseEnd_93604] using wordTrace_append hprefix tailTrace_93604
  have hstable : (prefixWord ++ tailWord_93604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93604).length < 2 ^ (prefixWord ++ tailWord_93604).sum := by decide
  have hdescent : baseEnd_93604 < baseStart_93604 := by decide
  rcases family_descends (prefixWord ++ tailWord_93604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93607 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 10]
def baseStart_93607 : Nat := 118140960795 + 93607 * 2 ^ 59
def prefixEnd_93607 : Nat := 4983230072969 + 3 ^ 40 * 93607 * 2
def baseEnd_93607 : Nat := 5340598180613388431335

theorem tailTrace_93607 : CollatzResearch.WordTrace tailWord_93607 prefixEnd_93607 5340598180613388431335 := by
  unfold tailWord_93607
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414127771885300647935075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2276085181256867098623383 3414127771885300647935075)
  ·
    refine ⟨5121191657827950971902613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414127771885300647935075 5121191657827950971902613)
    ·
      refine ⟨240055858960685201807935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5121191657827950971902613 240055858960685201807935)
      ·
        refine ⟨360083788441027802711903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240055858960685201807935 360083788441027802711903)
        ·
          refine ⟨540125682661541704067855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360083788441027802711903 540125682661541704067855)
          ·
            refine ⟨810188523992312556101783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540125682661541704067855 810188523992312556101783)
            ·
              refine ⟨1215282785988468834152675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810188523992312556101783 1215282785988468834152675)
              ·
                refine ⟨1822924178982703251229013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215282785988468834152675 1822924178982703251229013)
                ·
                  refine ⟨5340598180613388431335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1822924178982703251229013 5340598180613388431335)
                  ·
                    rfl

theorem cell23_93607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 10].length) (baseStart_93607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93607 prefixEnd_93607 := by exact prefixLift 93607
  have htrace : WordTrace (prefixWord ++ tailWord_93607) baseStart_93607 baseEnd_93607 := by
    simpa [prefixWord, tailWord_93607, baseEnd_93607] using wordTrace_append hprefix tailTrace_93607
  have hstable : (prefixWord ++ tailWord_93607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93607).length < 2 ^ (prefixWord ++ tailWord_93607).sum := by decide
  have hdescent : baseEnd_93607 < baseStart_93607 := by decide
  rcases family_descends (prefixWord ++ tailWord_93607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93621 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_93621 : Nat := 118140960795 + 93621 * 2 ^ 59
def prefixEnd_93621 : Nat := 4983230072969 + 3 ^ 40 * 93621 * 2
def baseEnd_93621 : Nat := 48072572354683441106951

theorem tailTrace_93621 : CollatzResearch.WordTrace tailWord_93621 prefixEnd_93621 48072572354683441106951 := by
  unfold tailWord_93621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414638393834581038944717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2276425595889720692629811 3414638393834581038944717)
  ·
    refine ⟨1280489397687967889604269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3414638393834581038944717 1280489397687967889604269)
    ·
      refine ⟨480183524132987958601601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1280489397687967889604269 480183524132987958601601)
      ·
        refine ⟨360137643099740968951201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480183524132987958601601 360137643099740968951201)
        ·
          refine ⟨270103232324805726713401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360137643099740968951201 270103232324805726713401)
          ·
            refine ⟨202577424243604295035051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270103232324805726713401 202577424243604295035051)
            ·
              refine ⟨303866136365406442552577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202577424243604295035051 303866136365406442552577)
              ·
                refine ⟨227899602274054831914433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303866136365406442552577 227899602274054831914433)
                ·
                  refine ⟨170924701705541123935825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227899602274054831914433 170924701705541123935825)
                  ·
                    refine ⟨128193526279155842951869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170924701705541123935825 128193526279155842951869)
                    ·
                      refine ⟨48072572354683441106951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 128193526279155842951869 48072572354683441106951)
                      ·
                        rfl

theorem cell23_93621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_93621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93621 prefixEnd_93621 := by exact prefixLift 93621
  have htrace : WordTrace (prefixWord ++ tailWord_93621) baseStart_93621 baseEnd_93621 := by
    simpa [prefixWord, tailWord_93621, baseEnd_93621] using wordTrace_append hprefix tailTrace_93621
  have hstable : (prefixWord ++ tailWord_93621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93621).length < 2 ^ (prefixWord ++ tailWord_93621).sum := by decide
  have hdescent : baseEnd_93621 < baseStart_93621 := by decide
  rcases family_descends (prefixWord ++ tailWord_93621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93628 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_93628 : Nat := 118140960795 + 93628 * 2 ^ 59
def prefixEnd_93628 : Nat := 4983230072969 + 3 ^ 40 * 93628 * 2
def baseEnd_93628 : Nat := 16025388906421637906473

theorem tailTrace_93628 : CollatzResearch.WordTrace tailWord_93628 prefixEnd_93628 16025388906421637906473 := by
  unfold tailWord_93628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707446852404610617224769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2276595803206147489633025 1707446852404610617224769)
  ·
    refine ⟨1280585139303457962918577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1707446852404610617224769 1280585139303457962918577)
    ·
      refine ⟨960438854477593472188933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1280585139303457962918577 960438854477593472188933)
      ·
        refine ⟨180082285214548776035425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 960438854477593472188933 180082285214548776035425)
        ·
          refine ⟨135061713910911582026569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180082285214548776035425 135061713910911582026569)
          ·
            refine ⟨101296285433183686519927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135061713910911582026569 101296285433183686519927)
            ·
              refine ⟨151944428149775529779891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101296285433183686519927 151944428149775529779891)
              ·
                refine ⟨227916642224663294669837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151944428149775529779891 227916642224663294669837)
                ·
                  refine ⟨85468740834248735501189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227916642224663294669837 85468740834248735501189)
                  ·
                    refine ⟨16025388906421637906473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85468740834248735501189 16025388906421637906473)
                    ·
                      rfl

theorem cell23_93628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_93628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93628 prefixEnd_93628 := by exact prefixLift 93628
  have htrace : WordTrace (prefixWord ++ tailWord_93628) baseStart_93628 baseEnd_93628 := by
    simpa [prefixWord, tailWord_93628, baseEnd_93628] using wordTrace_append hprefix tailTrace_93628
  have hstable : (prefixWord ++ tailWord_93628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93628).length < 2 ^ (prefixWord ++ tailWord_93628).sum := by decide
  have hdescent : baseEnd_93628 < baseStart_93628 := by decide
  rcases family_descends (prefixWord ++ tailWord_93628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93687 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_93687 : Nat := 118140960795 + 93687 * 2 ^ 59
def prefixEnd_93687 : Nat := 4983230072969 + 3 ^ 40 * 93687 * 2
def baseEnd_93687 : Nat := 48106462077880182881647

theorem tailTrace_93687 : CollatzResearch.WordTrace tailWord_93687 prefixEnd_93687 48106462077880182881647 := by
  unfold tailWord_93687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417045611595474310847315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2278030407730316207231543 3417045611595474310847315)
  ·
    refine ⟨5125568417393211466270973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417045611595474310847315 5125568417393211466270973)
    ·
      refine ⟨1922088156522454299851615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5125568417393211466270973 1922088156522454299851615)
      ·
        refine ⟨2883132234783681449777423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922088156522454299851615 2883132234783681449777423)
        ·
          refine ⟨4324698352175522174666135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883132234783681449777423 4324698352175522174666135)
          ·
            refine ⟨6487047528263283261999203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324698352175522174666135 6487047528263283261999203)
            ·
              refine ⟨9730571292394924892998805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487047528263283261999203 9730571292394924892998805)
              ·
                refine ⟨456120529331012104359319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9730571292394924892998805 456120529331012104359319)
                ·
                  refine ⟨684180793996518156538979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456120529331012104359319 684180793996518156538979)
                  ·
                    refine ⟨1026271190994777234808469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684180793996518156538979 1026271190994777234808469)
                    ·
                      refine ⟨48106462077880182881647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1026271190994777234808469 48106462077880182881647)
                      ·
                        rfl

theorem cell23_93687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_93687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93687 prefixEnd_93687 := by exact prefixLift 93687
  have htrace : WordTrace (prefixWord ++ tailWord_93687) baseStart_93687 baseEnd_93687 := by
    simpa [prefixWord, tailWord_93687, baseEnd_93687] using wordTrace_append hprefix tailTrace_93687
  have hstable : (prefixWord ++ tailWord_93687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93687).length < 2 ^ (prefixWord ++ tailWord_93687).sum := by decide
  have hdescent : baseEnd_93687 < baseStart_93687 := by decide
  rcases family_descends (prefixWord ++ tailWord_93687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93704 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_93704 : Nat := 118140960795 + 93704 * 2 ^ 59
def prefixEnd_93704 : Nat := 4983230072969 + 3 ^ 40 * 93704 * 2
def baseEnd_93704 : Nat := 48115191249006616369069

theorem tailTrace_93704 : CollatzResearch.WordTrace tailWord_93704 prefixEnd_93704 48115191249006616369069 := by
  unfold tailWord_93704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708832826266943107108083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2278443768355924142810777 1708832826266943107108083)
  ·
    refine ⟨2563249239400414660662125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708832826266943107108083 2563249239400414660662125)
    ·
      refine ⟨961218464775155497748297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2563249239400414660662125 961218464775155497748297)
      ·
        refine ⟨720913848581366623311223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961218464775155497748297 720913848581366623311223)
        ·
          refine ⟨1081370772872049934966835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720913848581366623311223 1081370772872049934966835)
          ·
            refine ⟨1622056159308074902450253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081370772872049934966835 1622056159308074902450253)
            ·
              refine ⟨608271059740528088418845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1622056159308074902450253 608271059740528088418845)
              ·
                refine ⟨228101647402698033157067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608271059740528088418845 228101647402698033157067)
                ·
                  refine ⟨342152471104047049735601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228101647402698033157067 342152471104047049735601)
                  ·
                    refine ⟨256614353328035287301701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342152471104047049735601 256614353328035287301701)
                    ·
                      refine ⟨48115191249006616369069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 256614353328035287301701 48115191249006616369069)
                      ·
                        rfl

theorem cell23_93704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_93704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93704 prefixEnd_93704 := by exact prefixLift 93704
  have htrace : WordTrace (prefixWord ++ tailWord_93704) baseStart_93704 baseEnd_93704 := by
    simpa [prefixWord, tailWord_93704, baseEnd_93704] using wordTrace_append hprefix tailTrace_93704
  have hstable : (prefixWord ++ tailWord_93704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93704).length < 2 ^ (prefixWord ++ tailWord_93704).sum := by decide
  have hdescent : baseEnd_93704 < baseStart_93704 := by decide
  rcases family_descends (prefixWord ++ tailWord_93704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93728 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_93728 : Nat := 118140960795 + 93728 * 2 ^ 59
def prefixEnd_93728 : Nat := 4983230072969 + 3 ^ 40 * 93728 * 2
def baseEnd_93728 : Nat := 48127514784714522468959

theorem tailTrace_93728 : CollatzResearch.WordTrace tailWord_93728 prefixEnd_93728 48127514784714522468959 := by
  unfold tailWord_93728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709270502223469156544919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2279027336297958875393225 1709270502223469156544919)
  ·
    refine ⟨2563905753335203734817379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1709270502223469156544919 2563905753335203734817379)
    ·
      refine ⟨3845858630002805602226069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563905753335203734817379 3845858630002805602226069)
      ·
        refine ⟨180274623281381512604347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3845858630002805602226069 180274623281381512604347)
        ·
          refine ⟨270411934922072268906521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180274623281381512604347 270411934922072268906521)
          ·
            refine ⟨202808951191554201679891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270411934922072268906521 202808951191554201679891)
            ·
              refine ⟨304213426787331302519837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202808951191554201679891 304213426787331302519837)
              ·
                refine ⟨114080035045249238444939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304213426787331302519837 114080035045249238444939)
                ·
                  refine ⟨171120052567873857667409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114080035045249238444939 171120052567873857667409)
                  ·
                    refine ⟨128340039425905393250557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171120052567873857667409 128340039425905393250557)
                    ·
                      refine ⟨48127514784714522468959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 128340039425905393250557 48127514784714522468959)
                      ·
                        rfl

theorem cell23_93728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_93728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93728 prefixEnd_93728 := by exact prefixLift 93728
  have htrace : WordTrace (prefixWord ++ tailWord_93728) baseStart_93728 baseEnd_93728 := by
    simpa [prefixWord, tailWord_93728, baseEnd_93728] using wordTrace_append hprefix tailTrace_93728
  have hstable : (prefixWord ++ tailWord_93728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93728).length < 2 ^ (prefixWord ++ tailWord_93728).sum := by decide
  have hdescent : baseEnd_93728 < baseStart_93728 := by decide
  rcases family_descends (prefixWord ++ tailWord_93728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93742 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_93742 : Nat := 118140960795 + 93742 * 2 ^ 59
def prefixEnd_93742 : Nat := 4983230072969 + 3 ^ 40 * 93742 * 2
def baseEnd_93742 : Nat := 48134703513877467693895

theorem tailTrace_93742 : CollatzResearch.WordTrace tailWord_93742 prefixEnd_93742 48134703513877467693895 := by
  unfold tailWord_93742
  simp only [CollatzResearch.WordTrace]
  refine ⟨427381453299527338012435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2279367750930812469399653 427381453299527338012435)
  ·
    refine ⟨641072179949291007018653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427381453299527338012435 641072179949291007018653)
    ·
      refine ⟨240402067480984127631995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 641072179949291007018653 240402067480984127631995)
      ·
        refine ⟨360603101221476191447993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240402067480984127631995 360603101221476191447993)
        ·
          refine ⟨270452325916107143585995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360603101221476191447993 270452325916107143585995)
          ·
            refine ⟨405678488874160715378993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270452325916107143585995 405678488874160715378993)
            ·
              refine ⟨304258866655620536534245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405678488874160715378993 304258866655620536534245)
              ·
                refine ⟨57048537497928850600171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304258866655620536534245 57048537497928850600171)
                ·
                  refine ⟨85572806246893275900257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57048537497928850600171 85572806246893275900257)
                  ·
                    refine ⟨64179604685169956925193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85572806246893275900257 64179604685169956925193)
                    ·
                      refine ⟨48134703513877467693895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64179604685169956925193 48134703513877467693895)
                      ·
                        rfl

theorem cell23_93742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_93742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93742 prefixEnd_93742 := by exact prefixLift 93742
  have htrace : WordTrace (prefixWord ++ tailWord_93742) baseStart_93742 baseEnd_93742 := by
    simpa [prefixWord, tailWord_93742, baseEnd_93742] using wordTrace_append hprefix tailTrace_93742
  have hstable : (prefixWord ++ tailWord_93742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93742).length < 2 ^ (prefixWord ++ tailWord_93742).sum := by decide
  have hdescent : baseEnd_93742 < baseStart_93742 := by decide
  rcases family_descends (prefixWord ++ tailWord_93742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_93781 : Nat := 118140960795 + 93781 * 2 ^ 59
def prefixEnd_93781 : Nat := 4983230072969 + 3 ^ 40 * 93781 * 2
def baseEnd_93781 : Nat := 48154729259402815106215

theorem tailTrace_93781 : CollatzResearch.WordTrace tailWord_93781 prefixEnd_93781 48154729259402815106215 := by
  unfold tailWord_93781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3420474073254928364769197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2280316048836618909846131 3420474073254928364769197)
  ·
    refine ⟨1282677777470598136788449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3420474073254928364769197 1282677777470598136788449)
    ·
      refine ⟨962008333102948602591337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1282677777470598136788449 962008333102948602591337)
      ·
        refine ⟨721506249827211451943503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962008333102948602591337 721506249827211451943503)
        ·
          refine ⟨1082259374740817177915255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721506249827211451943503 1082259374740817177915255)
          ·
            refine ⟨1623389062111225766872883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082259374740817177915255 1623389062111225766872883)
            ·
              refine ⟨2435083593166838650309325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623389062111225766872883 2435083593166838650309325)
              ·
                refine ⟨913156347437564493865997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2435083593166838650309325 913156347437564493865997)
                ·
                  refine ⟨342433630289086685199749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913156347437564493865997 342433630289086685199749)
                  ·
                    refine ⟨64206305679203753474953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342433630289086685199749 64206305679203753474953)
                    ·
                      refine ⟨48154729259402815106215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64206305679203753474953 48154729259402815106215)
                      ·
                        rfl

theorem cell23_93781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_93781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93781 prefixEnd_93781 := by exact prefixLift 93781
  have htrace : WordTrace (prefixWord ++ tailWord_93781) baseStart_93781 baseEnd_93781 := by
    simpa [prefixWord, tailWord_93781, baseEnd_93781] using wordTrace_append hprefix tailTrace_93781
  have hstable : (prefixWord ++ tailWord_93781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93781).length < 2 ^ (prefixWord ++ tailWord_93781).sum := by decide
  have hdescent : baseEnd_93781 < baseStart_93781 := by decide
  rcases family_descends (prefixWord ++ tailWord_93781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93784 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_93784 : Nat := 118140960795 + 93784 * 2 ^ 59
def prefixEnd_93784 : Nat := 4983230072969 + 3 ^ 40 * 93784 * 2
def baseEnd_93784 : Nat := 48156269701366303368701

theorem tailTrace_93784 : CollatzResearch.WordTrace tailWord_93784 prefixEnd_93784 48156269701366303368701 := by
  unfold tailWord_93784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710291746122029938564203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2280388994829373251418937 1710291746122029938564203)
  ·
    refine ⟨2565437619183044907846305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1710291746122029938564203 2565437619183044907846305)
    ·
      refine ⟨1924078214387283680884729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2565437619183044907846305 1924078214387283680884729)
      ·
        refine ⟨1443058660790462760663547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1924078214387283680884729 1443058660790462760663547)
        ·
          refine ⟨2164587991185694140995321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443058660790462760663547 2164587991185694140995321)
          ·
            refine ⟨1623440993389270605746491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2164587991185694140995321 1623440993389270605746491)
            ·
              refine ⟨2435161490083905908619737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623440993389270605746491 2435161490083905908619737)
              ·
                refine ⟨1826371117562929431464803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435161490083905908619737 1826371117562929431464803)
                ·
                  refine ⟨2739556676344394147197205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826371117562929431464803 2739556676344394147197205)
                  ·
                    refine ⟨128416719203643475649869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2739556676344394147197205 128416719203643475649869)
                    ·
                      refine ⟨48156269701366303368701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 128416719203643475649869 48156269701366303368701)
                      ·
                        rfl

theorem cell23_93784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_93784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93784 prefixEnd_93784 := by exact prefixLift 93784
  have htrace : WordTrace (prefixWord ++ tailWord_93784) baseStart_93784 baseEnd_93784 := by
    simpa [prefixWord, tailWord_93784, baseEnd_93784] using wordTrace_append hprefix tailTrace_93784
  have hstable : (prefixWord ++ tailWord_93784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93784).length < 2 ^ (prefixWord ++ tailWord_93784).sum := by decide
  have hdescent : baseEnd_93784 < baseStart_93784 := by decide
  rcases family_descends (prefixWord ++ tailWord_93784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93855 : List Nat := [1, 1, 2, 7, 1, 1, 1, 4, 5]
def baseStart_93855 : Nat := 118140960795 + 93855 * 2 ^ 59
def prefixEnd_93855 : Nat := 4983230072969 + 3 ^ 40 * 93855 * 2
def baseEnd_93855 : Nat := 5354747425315058397875

theorem tailTrace_93855 : CollatzResearch.WordTrace tailWord_93855 prefixEnd_93855 5354747425315058397875 := by
  unfold tailWord_93855
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423173074986839002963019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2282115383324559335308679 3423173074986839002963019)
  ·
    refine ⟨5134759612480258504444529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423173074986839002963019 5134759612480258504444529)
    ·
      refine ⟨3851069709360193878333397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5134759612480258504444529 3851069709360193878333397)
      ·
        refine ⟨90259446313129544023439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3851069709360193878333397 90259446313129544023439)
        ·
          refine ⟨135389169469694316035159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90259446313129544023439 135389169469694316035159)
          ·
            refine ⟨203083754204541474052739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135389169469694316035159 203083754204541474052739)
            ·
              refine ⟨304625631306812211079109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203083754204541474052739 304625631306812211079109)
              ·
                refine ⟨57117305870027289577333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304625631306812211079109 57117305870027289577333)
                ·
                  refine ⟨5354747425315058397875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57117305870027289577333 5354747425315058397875)
                  ·
                    rfl

theorem cell23_93855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 5].length) (baseStart_93855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93855 prefixEnd_93855 := by exact prefixLift 93855
  have htrace : WordTrace (prefixWord ++ tailWord_93855) baseStart_93855 baseEnd_93855 := by
    simpa [prefixWord, tailWord_93855, baseEnd_93855] using wordTrace_append hprefix tailTrace_93855
  have hstable : (prefixWord ++ tailWord_93855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93855).length < 2 ^ (prefixWord ++ tailWord_93855).sum := by decide
  have hdescent : baseEnd_93855 < baseStart_93855 := by decide
  rcases family_descends (prefixWord ++ tailWord_93855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93881 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_93881 : Nat := 118140960795 + 93881 * 2 ^ 59
def prefixEnd_93881 : Nat := 4983230072969 + 3 ^ 40 * 93881 * 2
def baseEnd_93881 : Nat := 16068692441617474618585

theorem tailTrace_93881 : CollatzResearch.WordTrace tailWord_93881 prefixEnd_93881 16068692441617474618585 := by
  unfold tailWord_93881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424121372892645443409497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2282747581928430295606331 3424121372892645443409497)
  ·
    refine ⟨2568091029669484082557123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424121372892645443409497 2568091029669484082557123)
    ·
      refine ⟨3852136544504226123835685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568091029669484082557123 3852136544504226123835685)
      ·
        refine ⟨722275602094542398219191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3852136544504226123835685 722275602094542398219191)
        ·
          refine ⟨1083413403141813597328787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722275602094542398219191 1083413403141813597328787)
          ·
            refine ⟨1625120104712720395993181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083413403141813597328787 1625120104712720395993181)
            ·
              refine ⟨609420039267270148497443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1625120104712720395993181 609420039267270148497443)
              ·
                refine ⟨914130058900905222746165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609420039267270148497443 914130058900905222746165)
                ·
                  refine ⟨85699693021959864632453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 914130058900905222746165 85699693021959864632453)
                  ·
                    refine ⟨16068692441617474618585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85699693021959864632453 16068692441617474618585)
                    ·
                      rfl

theorem cell23_93881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_93881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93881 prefixEnd_93881 := by exact prefixLift 93881
  have htrace : WordTrace (prefixWord ++ tailWord_93881) baseStart_93881 baseEnd_93881 := by
    simpa [prefixWord, tailWord_93881, baseEnd_93881] using wordTrace_append hprefix tailTrace_93881
  have hstable : (prefixWord ++ tailWord_93881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93881).length < 2 ^ (prefixWord ++ tailWord_93881).sum := by decide
  have hdescent : baseEnd_93881 < baseStart_93881 := by decide
  rcases family_descends (prefixWord ++ tailWord_93881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93948 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_93948 : Nat := 118140960795 + 93948 * 2 ^ 59
def prefixEnd_93948 : Nat := 4983230072969 + 3 ^ 40 * 93948 * 2
def baseEnd_93948 : Nat := 48240480528703661717947

theorem tailTrace_93948 : CollatzResearch.WordTrace tailWord_93948 prefixEnd_93948 48240480528703661717947 := by
  unfold tailWord_93948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713282531824957943049249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2284376709099943924065665 1713282531824957943049249)
  ·
    refine ⟨1284961898868718457286937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1713282531824957943049249 1284961898868718457286937)
    ·
      refine ⟨963721424151538842965203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1284961898868718457286937 963721424151538842965203)
      ·
        refine ⟨1445582136227308264447805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963721424151538842965203 1445582136227308264447805)
        ·
          refine ⟨542093301085240599167927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1445582136227308264447805 542093301085240599167927)
          ·
            refine ⟨813139951627860898751891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542093301085240599167927 813139951627860898751891)
            ·
              refine ⟨1219709927441791348127837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813139951627860898751891 1219709927441791348127837)
              ·
                refine ⟨457391222790671755547939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1219709927441791348127837 457391222790671755547939)
                ·
                  refine ⟨686086834186007633321909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457391222790671755547939 686086834186007633321909)
                  ·
                    refine ⟨64320640704938215623929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 686086834186007633321909 64320640704938215623929)
                    ·
                      refine ⟨48240480528703661717947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64320640704938215623929 48240480528703661717947)
                      ·
                        rfl

theorem cell23_93948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_93948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93948 prefixEnd_93948 := by exact prefixLift 93948
  have htrace : WordTrace (prefixWord ++ tailWord_93948) baseStart_93948 baseEnd_93948 := by
    simpa [prefixWord, tailWord_93948, baseEnd_93948] using wordTrace_append hprefix tailTrace_93948
  have hstable : (prefixWord ++ tailWord_93948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93948).length < 2 ^ (prefixWord ++ tailWord_93948).sum := by decide
  have hdescent : baseEnd_93948 < baseStart_93948 := by decide
  rcases family_descends (prefixWord ++ tailWord_93948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93961 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_93961 : Nat := 118140960795 + 93961 * 2 ^ 59
def prefixEnd_93961 : Nat := 4983230072969 + 3 ^ 40 * 93961 * 2
def baseEnd_93961 : Nat := 48247155777212110855387

theorem tailTrace_93961 : CollatzResearch.WordTrace tailWord_93961 prefixEnd_93961 48247155777212110855387 := by
  unfold tailWord_93961
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427039212602819106321737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2284692808401879404214491 3427039212602819106321737)
  ·
    refine ⟨2570279409452114329741303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3427039212602819106321737 2570279409452114329741303)
    ·
      refine ⟨3855419114178171494611955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2570279409452114329741303 3855419114178171494611955)
      ·
        refine ⟨5783128671267257241917933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855419114178171494611955 5783128671267257241917933)
        ·
          refine ⟨2168673251725221465719225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5783128671267257241917933 2168673251725221465719225)
          ·
            refine ⟨1626504938793916099289419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2168673251725221465719225 1626504938793916099289419)
            ·
              refine ⟨2439757408190874148934129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626504938793916099289419 2439757408190874148934129)
              ·
                refine ⟨1829818056143155611700597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439757408190874148934129 1829818056143155611700597)
                ·
                  refine ⟨171545442763420838596931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829818056143155611700597 171545442763420838596931)
                  ·
                    refine ⟨257318164145131257895397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171545442763420838596931 257318164145131257895397)
                    ·
                      refine ⟨48247155777212110855387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 257318164145131257895397 48247155777212110855387)
                      ·
                        rfl

theorem cell23_93961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_93961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_93961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_93961 prefixEnd_93961 := by exact prefixLift 93961
  have htrace : WordTrace (prefixWord ++ tailWord_93961) baseStart_93961 baseEnd_93961 := by
    simpa [prefixWord, tailWord_93961, baseEnd_93961] using wordTrace_append hprefix tailTrace_93961
  have hstable : (prefixWord ++ tailWord_93961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93961).length < 2 ^ (prefixWord ++ tailWord_93961).sum := by decide
  have hdescent : baseEnd_93961 < baseStart_93961 := by decide
  rcases family_descends (prefixWord ++ tailWord_93961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94001 : List Nat := [1, 2, 2, 3, 2, 2, 2, 9]
def baseStart_94001 : Nat := 118140960795 + 94001 * 2 ^ 59
def prefixEnd_94001 : Nat := 4983230072969 + 3 ^ 40 * 94001 * 2
def baseEnd_94001 : Nat := 1787692407533035346489

theorem tailTrace_94001 : CollatzResearch.WordTrace tailWord_94001 prefixEnd_94001 1787692407533035346489 := by
  unfold tailWord_94001
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428498132457905937777857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2285665421638603958518571 3428498132457905937777857)
  ·
    refine ⟨2571373599343429453333393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3428498132457905937777857 2571373599343429453333393)
    ·
      refine ⟨1928530199507572090000045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571373599343429453333393 1928530199507572090000045)
      ·
        refine ⟨723198824815339533750017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1928530199507572090000045 723198824815339533750017)
        ·
          refine ⟨542399118611504650312513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723198824815339533750017 542399118611504650312513)
          ·
            refine ⟨406799338958628487734385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542399118611504650312513 406799338958628487734385)
            ·
              refine ⟨305099504218971365800789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406799338958628487734385 305099504218971365800789)
              ·
                refine ⟨1787692407533035346489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 305099504218971365800789 1787692407533035346489)
                ·
                  rfl

theorem cell23_94001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 9].length) (baseStart_94001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94001 prefixEnd_94001 := by exact prefixLift 94001
  have htrace : WordTrace (prefixWord ++ tailWord_94001) baseStart_94001 baseEnd_94001 := by
    simpa [prefixWord, tailWord_94001, baseEnd_94001] using wordTrace_append hprefix tailTrace_94001
  have hstable : (prefixWord ++ tailWord_94001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94001).length < 2 ^ (prefixWord ++ tailWord_94001).sum := by decide
  have hdescent : baseEnd_94001 < baseStart_94001 := by decide
  rcases family_descends (prefixWord ++ tailWord_94001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94008 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_94008 : Nat := 118140960795 + 94008 * 2 ^ 59
def prefixEnd_94008 : Nat := 4983230072969 + 3 ^ 40 * 94008 * 2
def baseEnd_94008 : Nat := 48271289367973426967671

theorem tailTrace_94008 : CollatzResearch.WordTrace tailWord_94008 prefixEnd_94008 48271289367973426967671 := by
  unfold tailWord_94008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714376721716273066641339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2285835628955030755521785 1714376721716273066641339)
  ·
    refine ⟨2571565082574409599962009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1714376721716273066641339 2571565082574409599962009)
    ·
      refine ⟨1928673811930807199971507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571565082574409599962009 1928673811930807199971507)
      ·
        refine ⟨2893010717896210799957261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928673811930807199971507 2893010717896210799957261)
        ·
          refine ⟨1084879019211079049983973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2893010717896210799957261 1084879019211079049983973)
          ·
            refine ⟨203414816102077321871995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1084879019211079049983973 203414816102077321871995)
            ·
              refine ⟨305122224153115982807993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203414816102077321871995 305122224153115982807993)
              ·
                refine ⟨228841668114836987105995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305122224153115982807993 228841668114836987105995)
                ·
                  refine ⟨343262502172255480658993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228841668114836987105995 343262502172255480658993)
                  ·
                    refine ⟨257446876629191610494245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 343262502172255480658993 257446876629191610494245)
                    ·
                      refine ⟨48271289367973426967671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 257446876629191610494245 48271289367973426967671)
                      ·
                        rfl

theorem cell23_94008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_94008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94008 prefixEnd_94008 := by exact prefixLift 94008
  have htrace : WordTrace (prefixWord ++ tailWord_94008) baseStart_94008 baseEnd_94008 := by
    simpa [prefixWord, tailWord_94008, baseEnd_94008] using wordTrace_append hprefix tailTrace_94008
  have hstable : (prefixWord ++ tailWord_94008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94008).length < 2 ^ (prefixWord ++ tailWord_94008).sum := by decide
  have hdescent : baseEnd_94008 < baseStart_94008 := by decide
  rcases family_descends (prefixWord ++ tailWord_94008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94015 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_94015 : Nat := 118140960795 + 94015 * 2 ^ 59
def prefixEnd_94015 : Nat := 4983230072969 + 3 ^ 40 * 94015 * 2
def baseEnd_94015 : Nat := 48274883732554899580139

theorem tailTrace_94015 : CollatzResearch.WordTrace tailWord_94015 prefixEnd_94015 48274883732554899580139 := by
  unfold tailWord_94015
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429008754407186328787499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2286005836271457552524999 3429008754407186328787499)
  ·
    refine ⟨5143513131610779493181249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3429008754407186328787499 5143513131610779493181249)
    ·
      refine ⟨3857634848708084619885937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5143513131610779493181249 3857634848708084619885937)
      ·
        refine ⟨2893226136531063464914453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3857634848708084619885937 2893226136531063464914453)
        ·
          refine ⟨135619975149893599917865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2893226136531063464914453 135619975149893599917865)
          ·
            refine ⟨101714981362420199938399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135619975149893599917865 101714981362420199938399)
            ·
              refine ⟨152572472043630299907599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101714981362420199938399 152572472043630299907599)
              ·
                refine ⟨228858708065445449861399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152572472043630299907599 228858708065445449861399)
                ·
                  refine ⟨343288062098168174792099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228858708065445449861399 343288062098168174792099)
                  ·
                    refine ⟨514932093147252262188149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343288062098168174792099 514932093147252262188149)
                    ·
                      refine ⟨48274883732554899580139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 514932093147252262188149 48274883732554899580139)
                      ·
                        rfl

theorem cell23_94015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_94015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94015 prefixEnd_94015 := by exact prefixLift 94015
  have htrace : WordTrace (prefixWord ++ tailWord_94015) baseStart_94015 baseEnd_94015 := by
    simpa [prefixWord, tailWord_94015, baseEnd_94015] using wordTrace_append hprefix tailTrace_94015
  have hstable : (prefixWord ++ tailWord_94015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94015).length < 2 ^ (prefixWord ++ tailWord_94015).sum := by decide
  have hdescent : baseEnd_94015 < baseStart_94015 := by decide
  rcases family_descends (prefixWord ++ tailWord_94015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94055 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_94055 : Nat := 118140960795 + 94055 * 2 ^ 59
def prefixEnd_94055 : Nat := 4983230072969 + 3 ^ 40 * 94055 * 2
def baseEnd_94055 : Nat := 48295422958734743079955

theorem tailTrace_94055 : CollatzResearch.WordTrace tailWord_94055 prefixEnd_94055 48295422958734743079955 := by
  unfold tailWord_94055
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430467674262273160243619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2286978449508182106829079 3430467674262273160243619)
  ·
    refine ⟨5145701511393409740365429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3430467674262273160243619 5145701511393409740365429)
    ·
      refine ⟨482409516693132163159259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5145701511393409740365429 482409516693132163159259)
      ·
        refine ⟨723614275039698244738889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482409516693132163159259 723614275039698244738889)
        ·
          refine ⟨542710706279773683554167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723614275039698244738889 542710706279773683554167)
          ·
            refine ⟨814066059419660525331251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542710706279773683554167 814066059419660525331251)
            ·
              refine ⟨1221099089129490787996877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814066059419660525331251 1221099089129490787996877)
              ·
                refine ⟨457912158423559045498829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221099089129490787996877 457912158423559045498829)
                ·
                  refine ⟨171717059408834642062061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457912158423559045498829 171717059408834642062061)
                  ·
                    refine ⟨64393897278312990773273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171717059408834642062061 64393897278312990773273)
                    ·
                      refine ⟨48295422958734743079955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64393897278312990773273 48295422958734743079955)
                      ·
                        rfl

theorem cell23_94055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_94055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94055 prefixEnd_94055 := by exact prefixLift 94055
  have htrace : WordTrace (prefixWord ++ tailWord_94055) baseStart_94055 baseEnd_94055 := by
    simpa [prefixWord, tailWord_94055, baseEnd_94055] using wordTrace_append hprefix tailTrace_94055
  have hstable : (prefixWord ++ tailWord_94055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94055).length < 2 ^ (prefixWord ++ tailWord_94055).sum := by decide
  have hdescent : baseEnd_94055 < baseStart_94055 := by decide
  rcases family_descends (prefixWord ++ tailWord_94055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94175 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_94175 : Nat := 118140960795 + 94175 * 2 ^ 59
def prefixEnd_94175 : Nat := 4983230072969 + 3 ^ 40 * 94175 * 2
def baseEnd_94175 : Nat := 48357040637274273579403

theorem tailTrace_94175 : CollatzResearch.WordTrace tailWord_94175 prefixEnd_94175 48357040637274273579403 := by
  unfold tailWord_94175
  simp only [CollatzResearch.WordTrace]
  refine ⟨3434844433827533654611979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2289896289218355769741319 3434844433827533654611979)
  ·
    refine ⟨5152266650741300481917969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3434844433827533654611979 5152266650741300481917969)
    ·
      refine ⟨3864199988055975361438477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5152266650741300481917969 3864199988055975361438477)
      ·
        refine ⟨1449074995520990760539429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3864199988055975361438477 1449074995520990760539429)
        ·
          refine ⟨271701561660185767601143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1449074995520990760539429 271701561660185767601143)
          ·
            refine ⟨407552342490278651401715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271701561660185767601143 407552342490278651401715)
            ·
              refine ⟨611328513735417977102573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407552342490278651401715 611328513735417977102573)
              ·
                refine ⟨229248192650781741413465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611328513735417977102573 229248192650781741413465)
                ·
                  refine ⟨171936144488086306060099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229248192650781741413465 171936144488086306060099)
                  ·
                    refine ⟨257904216732129459090149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171936144488086306060099 257904216732129459090149)
                    ·
                      refine ⟨48357040637274273579403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 257904216732129459090149 48357040637274273579403)
                      ·
                        rfl

theorem cell23_94175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_94175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94175 prefixEnd_94175 := by exact prefixLift 94175
  have htrace : WordTrace (prefixWord ++ tailWord_94175) baseStart_94175 baseEnd_94175 := by
    simpa [prefixWord, tailWord_94175, baseEnd_94175] using wordTrace_append hprefix tailTrace_94175
  have hstable : (prefixWord ++ tailWord_94175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94175).length < 2 ^ (prefixWord ++ tailWord_94175).sum := by decide
  have hdescent : baseEnd_94175 < baseStart_94175 := by decide
  rcases family_descends (prefixWord ++ tailWord_94175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94215 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 6]
def baseStart_94215 : Nat := 118140960795 + 94215 * 2 ^ 59
def prefixEnd_94215 : Nat := 4983230072969 + 3 ^ 40 * 94215 * 2
def baseEnd_94215 : Nat := 5375286651494901897691

theorem tailTrace_94215 : CollatzResearch.WordTrace tailWord_94215 prefixEnd_94215 5375286651494901897691 := by
  unfold tailWord_94215
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436303353682620486068099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2290868902455080324045399 3436303353682620486068099)
  ·
    refine ⟨5154455030523930729102149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3436303353682620486068099 5154455030523930729102149)
    ·
      refine ⟨966460318223237011706653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5154455030523930729102149 966460318223237011706653)
      ·
        refine ⟨362422619333713879389995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 966460318223237011706653 362422619333713879389995)
        ·
          refine ⟨543633929000570819084993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362422619333713879389995 543633929000570819084993)
          ·
            refine ⟨407725446750428114313745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543633929000570819084993 407725446750428114313745)
            ·
              refine ⟨305794085062821085735309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407725446750428114313745 305794085062821085735309)
              ·
                refine ⟨114672781898557907150741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305794085062821085735309 114672781898557907150741)
                ·
                  refine ⟨5375286651494901897691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114672781898557907150741 5375286651494901897691)
                  ·
                    rfl

theorem cell23_94215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 6].length) (baseStart_94215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94215 prefixEnd_94215 := by exact prefixLift 94215
  have htrace : WordTrace (prefixWord ++ tailWord_94215) baseStart_94215 baseEnd_94215 := by
    simpa [prefixWord, tailWord_94215, baseEnd_94215] using wordTrace_append hprefix tailTrace_94215
  have hstable : (prefixWord ++ tailWord_94215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94215).length < 2 ^ (prefixWord ++ tailWord_94215).sum := by decide
  have hdescent : baseEnd_94215 < baseStart_94215 := by decide
  rcases family_descends (prefixWord ++ tailWord_94215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94229 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_94229 : Nat := 118140960795 + 94229 * 2 ^ 59
def prefixEnd_94229 : Nat := 4983230072969 + 3 ^ 40 * 94229 * 2
def baseEnd_94229 : Nat := 48384768592617062304155

theorem tailTrace_94229 : CollatzResearch.WordTrace tailWord_94229 prefixEnd_94229 48384768592617062304155 := by
  unfold tailWord_94229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436813975631900877077741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291209317087933918051827 3436813975631900877077741)
  ·
    refine ⟨1288805240861962828904153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3436813975631900877077741 1288805240861962828904153)
    ·
      refine ⟨966603930646472121678115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1288805240861962828904153 966603930646472121678115)
      ·
        refine ⟨1449905895969708182517173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966603930646472121678115 1449905895969708182517173)
        ·
          refine ⟨135928677747160142110985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1449905895969708182517173 135928677747160142110985)
          ·
            refine ⟨101946508310370106583239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135928677747160142110985 101946508310370106583239)
            ·
              refine ⟨152919762465555159874859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101946508310370106583239 152919762465555159874859)
              ·
                refine ⟨229379643698332739812289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152919762465555159874859 229379643698332739812289)
                ·
                  refine ⟨172034732773749554859217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229379643698332739812289 172034732773749554859217)
                  ·
                    refine ⟨129026049580312166144413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172034732773749554859217 129026049580312166144413)
                    ·
                      refine ⟨48384768592617062304155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129026049580312166144413 48384768592617062304155)
                      ·
                        rfl

theorem cell23_94229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_94229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94229 prefixEnd_94229 := by exact prefixLift 94229
  have htrace : WordTrace (prefixWord ++ tailWord_94229) baseStart_94229 baseEnd_94229 := by
    simpa [prefixWord, tailWord_94229, baseEnd_94229] using wordTrace_append hprefix tailTrace_94229
  have hstable : (prefixWord ++ tailWord_94229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94229).length < 2 ^ (prefixWord ++ tailWord_94229).sum := by decide
  have hdescent : baseEnd_94229 < baseStart_94229 := by decide
  rcases family_descends (prefixWord ++ tailWord_94229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94242 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_94242 : Nat := 118140960795 + 94242 * 2 ^ 59
def prefixEnd_94242 : Nat := 4983230072969 + 3 ^ 40 * 94242 * 2
def baseEnd_94242 : Nat := 48391443841125511441595

theorem tailTrace_94242 : CollatzResearch.WordTrace tailWord_94242 prefixEnd_94242 48391443841125511441595 := by
  unfold tailWord_94242
  simp only [CollatzResearch.WordTrace]
  refine ⟨859322031146201024325245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2291525416389869398200653 859322031146201024325245)
  ·
    refine ⟨322245761679825384121967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 859322031146201024325245 322245761679825384121967)
    ·
      refine ⟨483368642519738076182951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322245761679825384121967 483368642519738076182951)
      ·
        refine ⟨725052963779607114274427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483368642519738076182951 725052963779607114274427)
        ·
          refine ⟨1087579445669410671411641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725052963779607114274427 1087579445669410671411641)
          ·
            refine ⟨815684584252058003558731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087579445669410671411641 815684584252058003558731)
            ·
              refine ⟨1223526876378087005338097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815684584252058003558731 1223526876378087005338097)
              ·
                refine ⟨917645157283565254003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223526876378087005338097 917645157283565254003573)
                ·
                  refine ⟨86029233495334242562835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 917645157283565254003573 86029233495334242562835)
                  ·
                    refine ⟨129043850243001363844253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86029233495334242562835 129043850243001363844253)
                    ·
                      refine ⟨48391443841125511441595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129043850243001363844253 48391443841125511441595)
                      ·
                        rfl

theorem cell23_94242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_94242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94242 prefixEnd_94242 := by exact prefixLift 94242
  have htrace : WordTrace (prefixWord ++ tailWord_94242) baseStart_94242 baseEnd_94242 := by
    simpa [prefixWord, tailWord_94242, baseEnd_94242] using wordTrace_append hprefix tailTrace_94242
  have hstable : (prefixWord ++ tailWord_94242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94242).length < 2 ^ (prefixWord ++ tailWord_94242).sum := by decide
  have hdescent : baseEnd_94242 < baseStart_94242 := by decide
  rcases family_descends (prefixWord ++ tailWord_94242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94259 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 1, 1, 3]
def baseStart_94259 : Nat := 118140960795 + 94259 * 2 ^ 59
def prefixEnd_94259 : Nat := 4983230072969 + 3 ^ 40 * 94259 * 2
def baseEnd_94259 : Nat := 48400173012251944929017

theorem tailTrace_94259 : CollatzResearch.WordTrace tailWord_94259 prefixEnd_94259 48400173012251944929017 := by
  unfold tailWord_94259
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437908165523216000669831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291938777015477333779887 3437908165523216000669831)
  ·
    refine ⟨5156862248284824001004747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437908165523216000669831 5156862248284824001004747)
    ·
      refine ⟨7735293372427236001507121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5156862248284824001004747 7735293372427236001507121)
      ·
        refine ⟨5801470029320427001130341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7735293372427236001507121 5801470029320427001130341)
        ·
          refine ⟨1087775630497580062711939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5801470029320427001130341 1087775630497580062711939)
          ·
            refine ⟨1631663445746370094067909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087775630497580062711939 1631663445746370094067909)
            ·
              refine ⟨305936896077444392637733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1631663445746370094067909 305936896077444392637733)
              ·
                refine ⟨57363168014520823619575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305936896077444392637733 57363168014520823619575)
                ·
                  refine ⟨86044752021781235429363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57363168014520823619575 86044752021781235429363)
                  ·
                    refine ⟨129067128032671853144045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86044752021781235429363 129067128032671853144045)
                    ·
                      refine ⟨48400173012251944929017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129067128032671853144045 48400173012251944929017)
                      ·
                        rfl

theorem cell23_94259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 1, 3].length) (baseStart_94259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94259 prefixEnd_94259 := by exact prefixLift 94259
  have htrace : WordTrace (prefixWord ++ tailWord_94259) baseStart_94259 baseEnd_94259 := by
    simpa [prefixWord, tailWord_94259, baseEnd_94259] using wordTrace_append hprefix tailTrace_94259
  have hstable : (prefixWord ++ tailWord_94259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94259).length < 2 ^ (prefixWord ++ tailWord_94259).sum := by decide
  have hdescent : baseEnd_94259 < baseStart_94259 := by decide
  rcases family_descends (prefixWord ++ tailWord_94259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94295 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_94295 : Nat := 118140960795 + 94295 * 2 ^ 59
def prefixEnd_94295 : Nat := 4983230072969 + 3 ^ 40 * 94295 * 2
def baseEnd_94295 : Nat := 48418658315813804078851

theorem tailTrace_94295 : CollatzResearch.WordTrace tailWord_94295 prefixEnd_94295 48418658315813804078851 := by
  unfold tailWord_94295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439221193392794148980339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2292814128928529432653559 3439221193392794148980339)
  ·
    refine ⟨5158831790089191223470509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439221193392794148980339 5158831790089191223470509)
    ·
      refine ⟨1934561921283446708801441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5158831790089191223470509 1934561921283446708801441)
      ·
        refine ⟨1450921440962585031601081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1934561921283446708801441 1450921440962585031601081)
        ·
          refine ⟨1088191080721938773700811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450921440962585031601081 1088191080721938773700811)
          ·
            refine ⟨1632286621082908160551217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088191080721938773700811 1632286621082908160551217)
            ·
              refine ⟨1224214965812181120413413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632286621082908160551217 1224214965812181120413413)
              ·
                refine ⟨229540306089783960077515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1224214965812181120413413 229540306089783960077515)
                ·
                  refine ⟨344310459134675940116273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229540306089783960077515 344310459134675940116273)
                  ·
                    refine ⟨258232844351006955087205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344310459134675940116273 258232844351006955087205)
                    ·
                      refine ⟨48418658315813804078851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 258232844351006955087205 48418658315813804078851)
                      ·
                        rfl

theorem cell23_94295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_94295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94295 prefixEnd_94295 := by exact prefixLift 94295
  have htrace : WordTrace (prefixWord ++ tailWord_94295) baseStart_94295 baseEnd_94295 := by
    simpa [prefixWord, tailWord_94295, baseEnd_94295] using wordTrace_append hprefix tailTrace_94295
  have hstable : (prefixWord ++ tailWord_94295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94295).length < 2 ^ (prefixWord ++ tailWord_94295).sum := by decide
  have hdescent : baseEnd_94295 < baseStart_94295 := by decide
  rcases family_descends (prefixWord ++ tailWord_94295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94316 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 3, 2, 2]
def baseStart_94316 : Nat := 118140960795 + 94316 * 2 ^ 59
def prefixEnd_94316 : Nat := 4983230072969 + 3 ^ 40 * 94316 * 2
def baseEnd_94316 : Nat := 48429441409558221916255

theorem tailTrace_94316 : CollatzResearch.WordTrace tailWord_94316 prefixEnd_94316 48429441409558221916255 := by
  unfold tailWord_94316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719993563158357367747401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2293324750877809823663201 1719993563158357367747401)
  ·
    refine ⟨1289995172368768025810551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1719993563158357367747401 1289995172368768025810551)
    ·
      refine ⟨1934992758553152038715827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289995172368768025810551 1934992758553152038715827)
      ·
        refine ⟨2902489137829728058073741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934992758553152038715827 2902489137829728058073741)
        ·
          refine ⟨1088433426686148021777653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2902489137829728058073741 1088433426686148021777653)
          ·
            refine ⟨102040633751826377041655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1088433426686148021777653 102040633751826377041655)
            ·
              refine ⟨153060950627739565562483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102040633751826377041655 153060950627739565562483)
              ·
                refine ⟨229591425941609348343725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153060950627739565562483 229591425941609348343725)
                ·
                  refine ⟨86096784728103505628897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229591425941609348343725 86096784728103505628897)
                  ·
                    refine ⟨64572588546077629221673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86096784728103505628897 64572588546077629221673)
                    ·
                      refine ⟨48429441409558221916255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64572588546077629221673 48429441409558221916255)
                      ·
                        rfl

theorem cell23_94316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_94316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94316 prefixEnd_94316 := by exact prefixLift 94316
  have htrace : WordTrace (prefixWord ++ tailWord_94316) baseStart_94316 baseEnd_94316 := by
    simpa [prefixWord, tailWord_94316, baseEnd_94316] using wordTrace_append hprefix tailTrace_94316
  have hstable : (prefixWord ++ tailWord_94316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94316).length < 2 ^ (prefixWord ++ tailWord_94316).sum := by decide
  have hdescent : baseEnd_94316 < baseStart_94316 := by decide
  rcases family_descends (prefixWord ++ tailWord_94316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94326 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_94326 : Nat := 118140960795 + 94326 * 2 ^ 59
def prefixEnd_94326 : Nat := 4983230072969 + 3 ^ 40 * 94326 * 2
def baseEnd_94326 : Nat := 16144858738701060930403

theorem tailTrace_94326 : CollatzResearch.WordTrace tailWord_94326 prefixEnd_94326 16144858738701060930403 := by
  unfold tailWord_94326
  simp only [CollatzResearch.WordTrace]
  refine ⟨215021991017530402709927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2293567904186990962239221 215021991017530402709927)
  ·
    refine ⟨322532986526295604064891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215021991017530402709927 322532986526295604064891)
    ·
      refine ⟨483799479789443406097337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322532986526295604064891 483799479789443406097337)
      ·
        refine ⟨362849609842082554573003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483799479789443406097337 362849609842082554573003)
        ·
          refine ⟨544274414763123831859505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362849609842082554573003 544274414763123831859505)
          ·
            refine ⟨408205811072342873894629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544274414763123831859505 408205811072342873894629)
            ·
              refine ⟨76538589576064288855243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 408205811072342873894629 76538589576064288855243)
              ·
                refine ⟨114807884364096433282865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76538589576064288855243 114807884364096433282865)
                ·
                  refine ⟨86105913273072324962149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114807884364096433282865 86105913273072324962149)
                  ·
                    refine ⟨16144858738701060930403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86105913273072324962149 16144858738701060930403)
                    ·
                      rfl

theorem cell23_94326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_94326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94326 prefixEnd_94326 := by exact prefixLift 94326
  have htrace : WordTrace (prefixWord ++ tailWord_94326) baseStart_94326 baseEnd_94326 := by
    simpa [prefixWord, tailWord_94326, baseEnd_94326] using wordTrace_append hprefix tailTrace_94326
  have hstable : (prefixWord ++ tailWord_94326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94326).length < 2 ^ (prefixWord ++ tailWord_94326).sum := by decide
  have hdescent : baseEnd_94326 < baseStart_94326 := by decide
  rcases family_descends (prefixWord ++ tailWord_94326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94395 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 7]
def baseStart_94395 : Nat := 118140960795 + 94395 * 2 ^ 59
def prefixEnd_94395 : Nat := 4983230072969 + 3 ^ 40 * 94395 * 2
def baseEnd_94395 : Nat := 5385556264584823647599

theorem tailTrace_94395 : CollatzResearch.WordTrace tailWord_94395 prefixEnd_94395 5385556264584823647599 := by
  unfold tailWord_94395
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442868493030511227620639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2295245662020340818413759 3442868493030511227620639)
  ·
    refine ⟨5164302739545766841430959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442868493030511227620639 5164302739545766841430959)
    ·
      refine ⟨7746454109318650262146439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5164302739545766841430959 7746454109318650262146439)
      ·
        refine ⟨11619681163977975393219659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746454109318650262146439 11619681163977975393219659)
        ·
          refine ⟨17429521745966963089829489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11619681163977975393219659 17429521745966963089829489)
          ·
            refine ⟨13072141309475222317372117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17429521745966963089829489 13072141309475222317372117)
            ·
              refine ⟨306378311940825523063409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13072141309475222317372117 306378311940825523063409)
              ·
                refine ⟨229783733955619142297557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306378311940825523063409 229783733955619142297557)
                ·
                  refine ⟨5385556264584823647599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 229783733955619142297557 5385556264584823647599)
                  ·
                    rfl

theorem cell23_94395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 7].length) (baseStart_94395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94395 prefixEnd_94395 := by exact prefixLift 94395
  have htrace : WordTrace (prefixWord ++ tailWord_94395) baseStart_94395 baseEnd_94395 := by
    simpa [prefixWord, tailWord_94395, baseEnd_94395] using wordTrace_append hprefix tailTrace_94395
  have hstable : (prefixWord ++ tailWord_94395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94395).length < 2 ^ (prefixWord ++ tailWord_94395).sum := by decide
  have hdescent : baseEnd_94395 < baseStart_94395 := by decide
  rcases family_descends (prefixWord ++ tailWord_94395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94429 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 7]
def baseStart_94429 : Nat := 118140960795 + 94429 * 2 ^ 59
def prefixEnd_94429 : Nat := 4983230072969 + 3 ^ 40 * 94429 * 2
def baseEnd_94429 : Nat := 5387496080390697755915

theorem tailTrace_94429 : CollatzResearch.WordTrace tailWord_94429 prefixEnd_94429 5387496080390697755915 := by
  unfold tailWord_94429
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444108574907335034358341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2296072383271556689572227 3444108574907335034358341)
  ·
    refine ⟨645770357795125318942189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3444108574907335034358341 645770357795125318942189)
    ·
      refine ⟨242163884173171994603321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 645770357795125318942189 242163884173171994603321)
      ·
        refine ⟨181622913129878995952491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242163884173171994603321 181622913129878995952491)
        ·
          refine ⟨272434369694818493928737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181622913129878995952491 272434369694818493928737)
          ·
            refine ⟨204325777271113870446553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272434369694818493928737 204325777271113870446553)
            ·
              refine ⟨153244332953335402834915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204325777271113870446553 153244332953335402834915)
              ·
                refine ⟨229866499430003104252373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153244332953335402834915 229866499430003104252373)
                ·
                  refine ⟨5387496080390697755915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 229866499430003104252373 5387496080390697755915)
                  ·
                    rfl

theorem cell23_94429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_94429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94429 prefixEnd_94429 := by exact prefixLift 94429
  have htrace : WordTrace (prefixWord ++ tailWord_94429) baseStart_94429 baseEnd_94429 := by
    simpa [prefixWord, tailWord_94429, baseEnd_94429] using wordTrace_append hprefix tailTrace_94429
  have hstable : (prefixWord ++ tailWord_94429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94429).length < 2 ^ (prefixWord ++ tailWord_94429).sum := by decide
  have hdescent : baseEnd_94429 < baseStart_94429 := by decide
  rcases family_descends (prefixWord ++ tailWord_94429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94439 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_94439 : Nat := 118140960795 + 94439 * 2 ^ 59
def prefixEnd_94439 : Nat := 4983230072969 + 3 ^ 40 * 94439 * 2
def baseEnd_94439 : Nat := 48492599530061240678189

theorem tailTrace_94439 : CollatzResearch.WordTrace tailWord_94439 prefixEnd_94439 48492599530061240678189 := by
  unfold tailWord_94439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444473304871106742222371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2296315536580737828148247 3444473304871106742222371)
  ·
    refine ⟨5166709957306660113333557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3444473304871106742222371 5166709957306660113333557)
    ·
      refine ⟨484379058497499385625021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5166709957306660113333557 484379058497499385625021)
      ·
        refine ⟨181642146936562269609383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484379058497499385625021 181642146936562269609383)
        ·
          refine ⟨272463220404843404414075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181642146936562269609383 272463220404843404414075)
          ·
            refine ⟨408694830607265106621113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272463220404843404414075 408694830607265106621113)
            ·
              refine ⟨306521122955448829965835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408694830607265106621113 306521122955448829965835)
              ·
                refine ⟨459781684433173244948753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306521122955448829965835 459781684433173244948753)
                ·
                  refine ⟨344836263324879933711565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459781684433173244948753 344836263324879933711565)
                  ·
                    refine ⟨129313598746829975141837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344836263324879933711565 129313598746829975141837)
                    ·
                      refine ⟨48492599530061240678189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129313598746829975141837 48492599530061240678189)
                      ·
                        rfl

theorem cell23_94439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_94439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94439 prefixEnd_94439 := by exact prefixLift 94439
  have htrace : WordTrace (prefixWord ++ tailWord_94439) baseStart_94439 baseEnd_94439 := by
    simpa [prefixWord, tailWord_94439, baseEnd_94439] using wordTrace_append hprefix tailTrace_94439
  have hstable : (prefixWord ++ tailWord_94439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94439).length < 2 ^ (prefixWord ++ tailWord_94439).sum := by decide
  have hdescent : baseEnd_94439 < baseStart_94439 := by decide
  rcases family_descends (prefixWord ++ tailWord_94439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94516 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_94516 : Nat := 118140960795 + 94516 * 2 ^ 59
def prefixEnd_94516 : Nat := 4983230072969 + 3 ^ 40 * 94516 * 2
def baseEnd_94516 : Nat := 48532137540457439415335

theorem tailTrace_94516 : CollatzResearch.WordTrace tailWord_94516 prefixEnd_94516 48532137540457439415335 := by
  unfold tailWord_94516
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723640862796074446387701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2298187817061432595183601 1723640862796074446387701)
  ·
    refine ⟨161591330887131979348847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1723640862796074446387701 161591330887131979348847)
    ·
      refine ⟨242386996330697969023271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161591330887131979348847 242386996330697969023271)
      ·
        refine ⟨363580494496046953534907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242386996330697969023271 363580494496046953534907)
        ·
          refine ⟨545370741744070430302361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363580494496046953534907 545370741744070430302361)
          ·
            refine ⟨409028056308052822726771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545370741744070430302361 409028056308052822726771)
            ·
              refine ⟨613542084462079234090157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409028056308052822726771 613542084462079234090157)
              ·
                refine ⟨230078281673279712783809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613542084462079234090157 230078281673279712783809)
                ·
                  refine ⟨172558711254959784587857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230078281673279712783809 172558711254959784587857)
                  ·
                    refine ⟨129419033441219838440893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172558711254959784587857 129419033441219838440893)
                    ·
                      refine ⟨48532137540457439415335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129419033441219838440893 48532137540457439415335)
                      ·
                        rfl

theorem cell23_94516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_94516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94516 prefixEnd_94516 := by exact prefixLift 94516
  have htrace : WordTrace (prefixWord ++ tailWord_94516) baseStart_94516 baseEnd_94516 := by
    simpa [prefixWord, tailWord_94516, baseEnd_94516] using wordTrace_append hprefix tailTrace_94516
  have hstable : (prefixWord ++ tailWord_94516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94516).length < 2 ^ (prefixWord ++ tailWord_94516).sum := by decide
  have hdescent : baseEnd_94516 < baseStart_94516 := by decide
  rcases family_descends (prefixWord ++ tailWord_94516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94539 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 4, 3, 2]
def baseStart_94539 : Nat := 118140960795 + 94539 * 2 ^ 59
def prefixEnd_94539 : Nat := 4983230072969 + 3 ^ 40 * 94539 * 2
def baseEnd_94539 : Nat := 48543947595510849427729

theorem tailTrace_94539 : CollatzResearch.WordTrace tailWord_94539 prefixEnd_94539 48543947595510849427729 := by
  unfold tailWord_94539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448120604508823820862671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2298747069672549213908447 3448120604508823820862671)
  ·
    refine ⟨5172180906763235731294007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3448120604508823820862671 5172180906763235731294007)
    ·
      refine ⟨7758271360144853596941011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5172180906763235731294007 7758271360144853596941011)
      ·
        refine ⟨11637407040217280395411517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7758271360144853596941011 11637407040217280395411517)
        ·
          refine ⟨4364027640081480148279319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11637407040217280395411517 4364027640081480148279319)
          ·
            refine ⟨6546041460122220222418979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364027640081480148279319 6546041460122220222418979)
            ·
              refine ⟨9819062190183330333628469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546041460122220222418979 9819062190183330333628469)
              ·
                refine ⟨920537080329687218777669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9819062190183330333628469 920537080329687218777669)
                ·
                  refine ⟨172600702561816353520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920537080329687218777669 172600702561816353520813)
                  ·
                    refine ⟨64725263460681132570305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172600702561816353520813 64725263460681132570305)
                    ·
                      refine ⟨48543947595510849427729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64725263460681132570305 48543947595510849427729)
                      ·
                        rfl

theorem cell23_94539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3, 2].length) (baseStart_94539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94539 prefixEnd_94539 := by exact prefixLift 94539
  have htrace : WordTrace (prefixWord ++ tailWord_94539) baseStart_94539 baseEnd_94539 := by
    simpa [prefixWord, tailWord_94539, baseEnd_94539] using wordTrace_append hprefix tailTrace_94539
  have hstable : (prefixWord ++ tailWord_94539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94539).length < 2 ^ (prefixWord ++ tailWord_94539).sum := by decide
  have hdescent : baseEnd_94539 < baseStart_94539 := by decide
  rcases family_descends (prefixWord ++ tailWord_94539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94569 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_94569 : Nat := 118140960795 + 94569 * 2 ^ 59
def prefixEnd_94569 : Nat := 4983230072969 + 3 ^ 40 * 94569 * 2
def baseEnd_94569 : Nat := 48559352015145732052591

theorem tailTrace_94569 : CollatzResearch.WordTrace tailWord_94569 prefixEnd_94569 48559352015145732052591 := by
  unfold tailWord_94569
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449214794400138944454761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2299476529600092629636507 3449214794400138944454761)
  ·
    refine ⟨2586911095800104208341071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3449214794400138944454761 2586911095800104208341071)
    ·
      refine ⟨3880366643700156312511607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2586911095800104208341071 3880366643700156312511607)
      ·
        refine ⟨5820549965550234468767411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880366643700156312511607 5820549965550234468767411)
        ·
          refine ⟨8730824948325351703151117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820549965550234468767411 8730824948325351703151117)
          ·
            refine ⟨3274059355622006888681669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8730824948325351703151117 3274059355622006888681669)
            ·
              refine ⟨613886129179126291627813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3274059355622006888681669 613886129179126291627813)
              ·
                refine ⟨115103649221086179680215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 613886129179126291627813 115103649221086179680215)
                ·
                  refine ⟨172655473831629269520323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115103649221086179680215 172655473831629269520323)
                  ·
                    refine ⟨258983210747443904280485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172655473831629269520323 258983210747443904280485)
                    ·
                      refine ⟨48559352015145732052591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 258983210747443904280485 48559352015145732052591)
                      ·
                        rfl

theorem cell23_94569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_94569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94569 prefixEnd_94569 := by exact prefixLift 94569
  have htrace : WordTrace (prefixWord ++ tailWord_94569) baseStart_94569 baseEnd_94569 := by
    simpa [prefixWord, tailWord_94569, baseEnd_94569] using wordTrace_append hprefix tailTrace_94569
  have hstable : (prefixWord ++ tailWord_94569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94569).length < 2 ^ (prefixWord ++ tailWord_94569).sum := by decide
  have hdescent : baseEnd_94569 < baseStart_94569 := by decide
  rcases family_descends (prefixWord ++ tailWord_94569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94603 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 3, 2, 2]
def baseStart_94603 : Nat := 118140960795 + 94603 * 2 ^ 59
def prefixEnd_94603 : Nat := 4983230072969 + 3 ^ 40 * 94603 * 2
def baseEnd_94603 : Nat := 48576810357398599027435

theorem tailTrace_94603 : CollatzResearch.WordTrace tailWord_94603 prefixEnd_94603 48576810357398599027435 := by
  unfold tailWord_94603
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450454876276962751192463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2300303250851308500794975 3450454876276962751192463)
  ·
    refine ⟨5175682314415444126788695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3450454876276962751192463 5175682314415444126788695)
    ·
      refine ⟨7763523471623166190183043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5175682314415444126788695 7763523471623166190183043)
      ·
        refine ⟨11645285207434749285274565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7763523471623166190183043 11645285207434749285274565)
        ·
          refine ⟨2183490976394015490988981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11645285207434749285274565 2183490976394015490988981)
          ·
            refine ⟨204702279036938952280217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2183490976394015490988981 204702279036938952280217)
            ·
              refine ⟨153526709277704214210163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204702279036938952280217 153526709277704214210163)
              ·
                refine ⟨230290063916556321315245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153526709277704214210163 230290063916556321315245)
                ·
                  refine ⟨86358773968708620493217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230290063916556321315245 86358773968708620493217)
                  ·
                    refine ⟨64769080476531465369913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86358773968708620493217 64769080476531465369913)
                    ·
                      refine ⟨48576810357398599027435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64769080476531465369913 48576810357398599027435)
                      ·
                        rfl

theorem cell23_94603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 2, 2].length) (baseStart_94603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94603 prefixEnd_94603 := by exact prefixLift 94603
  have htrace : WordTrace (prefixWord ++ tailWord_94603) baseStart_94603 baseEnd_94603 := by
    simpa [prefixWord, tailWord_94603, baseEnd_94603] using wordTrace_append hprefix tailTrace_94603
  have hstable : (prefixWord ++ tailWord_94603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94603).length < 2 ^ (prefixWord ++ tailWord_94603).sum := by decide
  have hdescent : baseEnd_94603 < baseStart_94603 := by decide
  rcases family_descends (prefixWord ++ tailWord_94603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94606 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_94606 : Nat := 118140960795 + 94606 * 2 ^ 59
def prefixEnd_94606 : Nat := 4983230072969 + 3 ^ 40 * 94606 * 2
def baseEnd_94606 : Nat := 48578350799362087289921

theorem tailTrace_94606 : CollatzResearch.WordTrace tailWord_94606 prefixEnd_94606 48578350799362087289921 := by
  unfold tailWord_94606
  simp only [CollatzResearch.WordTrace]
  refine ⟨431320536908261782943959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2300376196844062842367781 431320536908261782943959)
  ·
    refine ⟨646980805362392674415939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431320536908261782943959 646980805362392674415939)
    ·
      refine ⟨970471208043589011623909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646980805362392674415939 970471208043589011623909)
      ·
        refine ⟨181963351508172939679483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 970471208043589011623909 181963351508172939679483)
        ·
          refine ⟨272945027262259409519225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181963351508172939679483 272945027262259409519225)
          ·
            refine ⟨204708770446694557139419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272945027262259409519225 204708770446694557139419)
            ·
              refine ⟨307063155670041835709129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204708770446694557139419 307063155670041835709129)
              ·
                refine ⟨230297366752531376781847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307063155670041835709129 230297366752531376781847)
                ·
                  refine ⟨345446050128797065172771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230297366752531376781847 345446050128797065172771)
                  ·
                    refine ⟨518169075193195597759157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345446050128797065172771 518169075193195597759157)
                    ·
                      refine ⟨48578350799362087289921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 518169075193195597759157 48578350799362087289921)
                      ·
                        rfl

theorem cell23_94606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_94606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94606 prefixEnd_94606 := by exact prefixLift 94606
  have htrace : WordTrace (prefixWord ++ tailWord_94606) baseStart_94606 baseEnd_94606 := by
    simpa [prefixWord, tailWord_94606, baseEnd_94606] using wordTrace_append hprefix tailTrace_94606
  have hstable : (prefixWord ++ tailWord_94606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94606).length < 2 ^ (prefixWord ++ tailWord_94606).sum := by decide
  have hdescent : baseEnd_94606 < baseStart_94606 := by decide
  rcases family_descends (prefixWord ++ tailWord_94606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94616 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_94616 : Nat := 118140960795 + 94616 * 2 ^ 59
def prefixEnd_94616 : Nat := 4983230072969 + 3 ^ 40 * 94616 * 2
def baseEnd_94616 : Nat := 48583485605907048164875

theorem tailTrace_94616 : CollatzResearch.WordTrace tailWord_94616 prefixEnd_94616 48583485605907048164875 := by
  unfold tailWord_94616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725464512614932985707851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2300619350153243980943801 1725464512614932985707851)
  ·
    refine ⟨2588196768922399478561777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1725464512614932985707851 2588196768922399478561777)
    ·
      refine ⟨1941147576691799608921333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588196768922399478561777 1941147576691799608921333)
      ·
        refine ⟨181982585314856213336375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1941147576691799608921333 181982585314856213336375)
        ·
          refine ⟨272973877972284320004563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181982585314856213336375 272973877972284320004563)
          ·
            refine ⟨409460816958426480006845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272973877972284320004563 409460816958426480006845)
            ·
              refine ⟨153547806359409930002567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409460816958426480006845 153547806359409930002567)
              ·
                refine ⟨230321709539114895003851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153547806359409930002567 230321709539114895003851)
                ·
                  refine ⟨345482564308672342505777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230321709539114895003851 345482564308672342505777)
                  ·
                    refine ⟨259111923231504256879333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345482564308672342505777 259111923231504256879333)
                    ·
                      refine ⟨48583485605907048164875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 259111923231504256879333 48583485605907048164875)
                      ·
                        rfl

theorem cell23_94616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_94616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94616 prefixEnd_94616 := by exact prefixLift 94616
  have htrace : WordTrace (prefixWord ++ tailWord_94616) baseStart_94616 baseEnd_94616 := by
    simpa [prefixWord, tailWord_94616, baseEnd_94616] using wordTrace_append hprefix tailTrace_94616
  have hstable : (prefixWord ++ tailWord_94616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94616).length < 2 ^ (prefixWord ++ tailWord_94616).sum := by decide
  have hdescent : baseEnd_94616 < baseStart_94616 := by decide
  rcases family_descends (prefixWord ++ tailWord_94616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94733 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 9]
def baseStart_94733 : Nat := 118140960795 + 94733 * 2 ^ 59
def prefixEnd_94733 : Nat := 4983230072969 + 3 ^ 40 * 94733 * 2
def baseEnd_94733 : Nat := 5404840315831454489093

theorem tailTrace_94733 : CollatzResearch.WordTrace tailWord_94733 prefixEnd_94733 5404840315831454489093 := by
  unfold tailWord_94733
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455196365805994953424853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2303464243870663302283235 3455196365805994953424853)
  ·
    refine ⟨80981164823578006720895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3455196365805994953424853 80981164823578006720895)
    ·
      refine ⟨121471747235367010081343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80981164823578006720895 121471747235367010081343)
      ·
        refine ⟨182207620853050515122015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121471747235367010081343 182207620853050515122015)
        ·
          refine ⟨273311431279575772683023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182207620853050515122015 273311431279575772683023)
          ·
            refine ⟨409967146919363659024535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273311431279575772683023 409967146919363659024535)
            ·
              refine ⟨614950720379045488536803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409967146919363659024535 614950720379045488536803)
              ·
                refine ⟨922426080568568232805205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614950720379045488536803 922426080568568232805205)
                ·
                  refine ⟨5404840315831454489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 922426080568568232805205 5404840315831454489093)
                  ·
                    rfl

theorem cell23_94733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_94733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94733 prefixEnd_94733 := by exact prefixLift 94733
  have htrace : WordTrace (prefixWord ++ tailWord_94733) baseStart_94733 baseEnd_94733 := by
    simpa [prefixWord, tailWord_94733, baseEnd_94733] using wordTrace_append hprefix tailTrace_94733
  have hstable : (prefixWord ++ tailWord_94733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94733).length < 2 ^ (prefixWord ++ tailWord_94733).sum := by decide
  have hdescent : baseEnd_94733 < baseStart_94733 := by decide
  rcases family_descends (prefixWord ++ tailWord_94733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94746 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_94746 : Nat := 118140960795 + 94746 * 2 ^ 59
def prefixEnd_94746 : Nat := 4983230072969 + 3 ^ 40 * 94746 * 2
def baseEnd_94746 : Nat := 16216746030330513179759

theorem tailTrace_94746 : CollatzResearch.WordTrace tailWord_94746 prefixEnd_94746 16216746030330513179759 := by
  unfold tailWord_94746
  simp only [CollatzResearch.WordTrace]
  refine ⟨863917628689724543412023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2303780343172598782432061 863917628689724543412023)
  ·
    refine ⟨1295876443034586815118035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863917628689724543412023 1295876443034586815118035)
    ·
      refine ⟨1943814664551880222677053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295876443034586815118035 1943814664551880222677053)
      ·
        refine ⟨728930499206955083503895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1943814664551880222677053 728930499206955083503895)
        ·
          refine ⟨1093395748810432625255843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728930499206955083503895 1093395748810432625255843)
          ·
            refine ⟨1640093623215648937883765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093395748810432625255843 1640093623215648937883765)
            ·
              refine ⟨153758777176467087926603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1640093623215648937883765 153758777176467087926603)
              ·
                refine ⟨230638165764700631889905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153758777176467087926603 230638165764700631889905)
                ·
                  refine ⟨172978624323525473917429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230638165764700631889905 172978624323525473917429)
                  ·
                    refine ⟨16216746030330513179759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172978624323525473917429 16216746030330513179759)
                    ·
                      rfl

theorem cell23_94746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_94746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94746 prefixEnd_94746 := by exact prefixLift 94746
  have htrace : WordTrace (prefixWord ++ tailWord_94746) baseStart_94746 baseEnd_94746 := by
    simpa [prefixWord, tailWord_94746, baseEnd_94746] using wordTrace_append hprefix tailTrace_94746
  have hstable : (prefixWord ++ tailWord_94746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94746).length < 2 ^ (prefixWord ++ tailWord_94746).sum := by decide
  have hdescent : baseEnd_94746 < baseStart_94746 := by decide
  rcases family_descends (prefixWord ++ tailWord_94746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94769 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_94769 : Nat := 118140960795 + 94769 * 2 ^ 59
def prefixEnd_94769 : Nat := 4983230072969 + 3 ^ 40 * 94769 * 2
def baseEnd_94769 : Nat := 48662048146044949551671

theorem tailTrace_94769 : CollatzResearch.WordTrace tailWord_94769 prefixEnd_94769 48662048146044949551671 := by
  unfold tailWord_94769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456509393675573101735361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2304339595783715401156907 3456509393675573101735361)
  ·
    refine ⟨2592382045256679826301521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3456509393675573101735361 2592382045256679826301521)
    ·
      refine ⟨1944286533942509869726141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2592382045256679826301521 1944286533942509869726141)
      ·
        refine ⟨729107450228441201147303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1944286533942509869726141 729107450228441201147303)
        ·
          refine ⟨1093661175342661801720955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729107450228441201147303 1093661175342661801720955)
          ·
            refine ⟨1640491763013992702581433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093661175342661801720955 1640491763013992702581433)
            ·
              refine ⟨1230368822260494526936075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640491763013992702581433 1230368822260494526936075)
              ·
                refine ⟨1845553233390741790404113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230368822260494526936075 1845553233390741790404113)
                ·
                  refine ⟨1384164925043056342803085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845553233390741790404113 1384164925043056342803085)
                  ·
                    refine ⟨519061846891146128551157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384164925043056342803085 519061846891146128551157)
                    ·
                      refine ⟨48662048146044949551671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 519061846891146128551157 48662048146044949551671)
                      ·
                        rfl

theorem cell23_94769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_94769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94769 prefixEnd_94769 := by exact prefixLift 94769
  have htrace : WordTrace (prefixWord ++ tailWord_94769) baseStart_94769 baseEnd_94769 := by
    simpa [prefixWord, tailWord_94769, baseEnd_94769] using wordTrace_append hprefix tailTrace_94769
  have hstable : (prefixWord ++ tailWord_94769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94769).length < 2 ^ (prefixWord ++ tailWord_94769).sum := by decide
  have hdescent : baseEnd_94769 < baseStart_94769 := by decide
  rcases family_descends (prefixWord ++ tailWord_94769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94853 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_94853 : Nat := 118140960795 + 94853 * 2 ^ 59
def prefixEnd_94853 : Nat := 4983230072969 + 3 ^ 40 * 94853 * 2
def baseEnd_94853 : Nat := 16235060173674206967095

theorem tailTrace_94853 : CollatzResearch.WordTrace tailWord_94853 prefixEnd_94853 16235060173674206967095 := by
  unfold tailWord_94853
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459573125371255447793213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2306382083580836965195475 3459573125371255447793213)
  ·
    refine ⟨1297339922014220792922455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3459573125371255447793213 1297339922014220792922455)
    ·
      refine ⟨1946009883021331189383683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297339922014220792922455 1946009883021331189383683)
      ·
        refine ⟨2919014824531996784075525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946009883021331189383683 2919014824531996784075525)
        ·
          refine ⟨547315279599749397014161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2919014824531996784075525 547315279599749397014161)
          ·
            refine ⟨410486459699812047760621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547315279599749397014161 410486459699812047760621)
            ·
              refine ⟨153932422387429517910233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410486459699812047760621 153932422387429517910233)
              ·
                refine ⟨115449316790572138432675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153932422387429517910233 115449316790572138432675)
                ·
                  refine ⟨173173975185858207649013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115449316790572138432675 173173975185858207649013)
                  ·
                    refine ⟨16235060173674206967095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173173975185858207649013 16235060173674206967095)
                    ·
                      rfl

theorem cell23_94853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_94853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94853 prefixEnd_94853 := by exact prefixLift 94853
  have htrace : WordTrace (prefixWord ++ tailWord_94853) baseStart_94853 baseEnd_94853 := by
    simpa [prefixWord, tailWord_94853, baseEnd_94853] using wordTrace_append hprefix tailTrace_94853
  have hstable : (prefixWord ++ tailWord_94853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94853).length < 2 ^ (prefixWord ++ tailWord_94853).sum := by decide
  have hdescent : baseEnd_94853 < baseStart_94853 := by decide
  rcases family_descends (prefixWord ++ tailWord_94853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94879 : List Nat := [1, 1, 2, 19]
def baseStart_94879 : Nat := 118140960795 + 94879 * 2 ^ 59
def prefixEnd_94879 : Nat := 4983230072969 + 3 ^ 40 * 94879 * 2
def baseEnd_94879 : Nat := 22276420218582313295

theorem tailTrace_94879 : CollatzResearch.WordTrace tailWord_94879 prefixEnd_94879 22276420218582313295 := by
  unfold tailWord_94879
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460521423277061888239691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2307014282184707925493127 3460521423277061888239691)
  ·
    refine ⟨5190782134915592832359537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460521423277061888239691 5190782134915592832359537)
    ·
      refine ⟨3893086601186694624269653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5190782134915592832359537 3893086601186694624269653)
      ·
        refine ⟨22276420218582313295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 19 3893086601186694624269653 22276420218582313295)
        ·
          rfl

theorem cell23_94879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 19].length) (baseStart_94879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94879 prefixEnd_94879 := by exact prefixLift 94879
  have htrace : WordTrace (prefixWord ++ tailWord_94879) baseStart_94879 baseEnd_94879 := by
    simpa [prefixWord, tailWord_94879, baseEnd_94879] using wordTrace_append hprefix tailTrace_94879
  have hstable : (prefixWord ++ tailWord_94879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94879).length < 2 ^ (prefixWord ++ tailWord_94879).sum := by decide
  have hdescent : baseEnd_94879 < baseStart_94879 := by decide
  rcases family_descends (prefixWord ++ tailWord_94879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94910 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_94910 : Nat := 118140960795 + 94910 * 2 ^ 59
def prefixEnd_94910 : Nat := 4983230072969 + 3 ^ 40 * 94910 * 2
def baseEnd_94910 : Nat := 48734448918328897888523

theorem tailTrace_94910 : CollatzResearch.WordTrace tailWord_94910 prefixEnd_94910 48734448918328897888523 := by
  unfold tailWord_94910
  simp only [CollatzResearch.WordTrace]
  refine ⟨432706510770594272827273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2307768057443169455078789 432706510770594272827273)
  ·
    refine ⟨324529883077945704620455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 432706510770594272827273 324529883077945704620455)
    ·
      refine ⟨486794824616918556930683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324529883077945704620455 486794824616918556930683)
      ·
        refine ⟨730192236925377835396025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486794824616918556930683 730192236925377835396025)
        ·
          refine ⟨547644177694033376547019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730192236925377835396025 547644177694033376547019)
          ·
            refine ⟨821466266541050064820529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547644177694033376547019 821466266541050064820529)
            ·
              refine ⟨616099699905787548615397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821466266541050064820529 616099699905787548615397)
              ·
                refine ⟨115518693732335165365387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616099699905787548615397 115518693732335165365387)
                ·
                  refine ⟨173278040598502748048081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115518693732335165365387 173278040598502748048081)
                  ·
                    refine ⟨129958530448877061036061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173278040598502748048081 129958530448877061036061)
                    ·
                      refine ⟨48734448918328897888523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129958530448877061036061 48734448918328897888523)
                      ·
                        rfl

theorem cell23_94910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_94910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94910 prefixEnd_94910 := by exact prefixLift 94910
  have htrace : WordTrace (prefixWord ++ tailWord_94910) baseStart_94910 baseEnd_94910 := by
    simpa [prefixWord, tailWord_94910, baseEnd_94910] using wordTrace_append hprefix tailTrace_94910
  have hstable : (prefixWord ++ tailWord_94910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94910).length < 2 ^ (prefixWord ++ tailWord_94910).sum := by decide
  have hdescent : baseEnd_94910 < baseStart_94910 := by decide
  rcases family_descends (prefixWord ++ tailWord_94910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94918 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_94918 : Nat := 118140960795 + 94918 * 2 ^ 59
def prefixEnd_94918 : Nat := 4983230072969 + 3 ^ 40 * 94918 * 2
def baseEnd_94918 : Nat := 48738556763564866588487

theorem tailTrace_94918 : CollatzResearch.WordTrace tailWord_94918 prefixEnd_94918 48738556763564866588487 := by
  unfold tailWord_94918
  simp only [CollatzResearch.WordTrace]
  refine ⟨108185745941742860903419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2307962580090514365939605 108185745941742860903419)
  ·
    refine ⟨162278618912614291355129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108185745941742860903419 162278618912614291355129)
    ·
      refine ⟨121708964184460718516347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162278618912614291355129 121708964184460718516347)
      ·
        refine ⟨182563446276691077774521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121708964184460718516347 182563446276691077774521)
        ·
          refine ⟨136922584707518308330891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182563446276691077774521 136922584707518308330891)
          ·
            refine ⟨205383877061277462496337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136922584707518308330891 205383877061277462496337)
            ·
              refine ⟨154037907795958096872253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205383877061277462496337 154037907795958096872253)
              ·
                refine ⟨57764215423484286327095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154037907795958096872253 57764215423484286327095)
                ·
                  refine ⟨86646323135226429490643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57764215423484286327095 86646323135226429490643)
                  ·
                    refine ⟨129969484702839644235965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86646323135226429490643 129969484702839644235965)
                    ·
                      refine ⟨48738556763564866588487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 129969484702839644235965 48738556763564866588487)
                      ·
                        rfl

theorem cell23_94918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_94918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94918 prefixEnd_94918 := by exact prefixLift 94918
  have htrace : WordTrace (prefixWord ++ tailWord_94918) baseStart_94918 baseEnd_94918 := by
    simpa [prefixWord, tailWord_94918, baseEnd_94918] using wordTrace_append hprefix tailTrace_94918
  have hstable : (prefixWord ++ tailWord_94918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94918).length < 2 ^ (prefixWord ++ tailWord_94918).sum := by decide
  have hdescent : baseEnd_94918 < baseStart_94918 := by decide
  rcases family_descends (prefixWord ++ tailWord_94918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94924 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 1, 2, 2]
def baseStart_94924 : Nat := 118140960795 + 94924 * 2 ^ 59
def prefixEnd_94924 : Nat := 4983230072969 + 3 ^ 40 * 94924 * 2
def baseEnd_94924 : Nat := 48741637647491843113459

theorem tailTrace_94924 : CollatzResearch.WordTrace tailWord_94924 prefixEnd_94924 48741637647491843113459 := by
  unfold tailWord_94924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731081354057017286813913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2308108472076023049085217 1731081354057017286813913)
  ·
    refine ⟨1298311015542762965110435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1731081354057017286813913 1298311015542762965110435)
    ·
      refine ⟨1947466523314144447665653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298311015542762965110435 1947466523314144447665653)
      ·
        refine ⟨182574986560701041968655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1947466523314144447665653 182574986560701041968655)
        ·
          refine ⟨273862479841051562952983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182574986560701041968655 273862479841051562952983)
          ·
            refine ⟨410793719761577344429475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273862479841051562952983 410793719761577344429475)
            ·
              refine ⟨616190579642366016644213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410793719761577344429475 616190579642366016644213)
              ·
                refine ⟨57767866841471814060395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 616190579642366016644213 57767866841471814060395)
                ·
                  refine ⟨86651800262207721090593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57767866841471814060395 86651800262207721090593)
                  ·
                    refine ⟨64988850196655790817945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86651800262207721090593 64988850196655790817945)
                    ·
                      refine ⟨48741637647491843113459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 64988850196655790817945 48741637647491843113459)
                      ·
                        rfl

theorem cell23_94924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_94924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94924 prefixEnd_94924 := by exact prefixLift 94924
  have htrace : WordTrace (prefixWord ++ tailWord_94924) baseStart_94924 baseEnd_94924 := by
    simpa [prefixWord, tailWord_94924, baseEnd_94924] using wordTrace_append hprefix tailTrace_94924
  have hstable : (prefixWord ++ tailWord_94924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94924).length < 2 ^ (prefixWord ++ tailWord_94924).sum := by decide
  have hdescent : baseEnd_94924 < baseStart_94924 := by decide
  rcases family_descends (prefixWord ++ tailWord_94924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94964 : List Nat := [2, 6, 1, 1, 2, 2, 2, 7]
def baseStart_94964 : Nat := 118140960795 + 94964 * 2 ^ 59
def prefixEnd_94964 : Nat := 4983230072969 + 3 ^ 40 * 94964 * 2
def baseEnd_94964 : Nat := 1806006550876729133825

theorem tailTrace_94964 : CollatzResearch.WordTrace tailWord_94964 prefixEnd_94964 1806006550876729133825 := by
  unfold tailWord_94964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731810813984560702541973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2309081085312747603389297 1731810813984560702541973)
  ·
    refine ⟨81178631905526282931655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1731810813984560702541973 81178631905526282931655)
    ·
      refine ⟨121767947858289424397483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81178631905526282931655 121767947858289424397483)
      ·
        refine ⟨182651921787434136596225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121767947858289424397483 182651921787434136596225)
        ·
          refine ⟨136988941340575602447169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182651921787434136596225 136988941340575602447169)
          ·
            refine ⟨102741706005431701835377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136988941340575602447169 102741706005431701835377)
            ·
              refine ⟨77056279504073776376533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102741706005431701835377 77056279504073776376533)
              ·
                refine ⟨1806006550876729133825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77056279504073776376533 1806006550876729133825)
                ·
                  rfl

theorem cell23_94964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 7].length) (baseStart_94964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94964 prefixEnd_94964 := by exact prefixLift 94964
  have htrace : WordTrace (prefixWord ++ tailWord_94964) baseStart_94964 baseEnd_94964 := by
    simpa [prefixWord, tailWord_94964, baseEnd_94964] using wordTrace_append hprefix tailTrace_94964
  have hstable : (prefixWord ++ tailWord_94964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94964).length < 2 ^ (prefixWord ++ tailWord_94964).sum := by decide
  have hdescent : baseEnd_94964 < baseStart_94964 := by decide
  rcases family_descends (prefixWord ++ tailWord_94964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94980 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_94980 : Nat := 118140960795 + 94980 * 2 ^ 59
def prefixEnd_94980 : Nat := 4983230072969 + 3 ^ 40 * 94980 * 2
def baseEnd_94980 : Nat := 48770392564143624013201

theorem tailTrace_94980 : CollatzResearch.WordTrace tailWord_94980 prefixEnd_94980 48770392564143624013201 := by
  unfold tailWord_94980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732102597955578068833197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2309470130607437425110929 1732102597955578068833197)
  ·
    refine ⟨649538474233341775812449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1732102597955578068833197 649538474233341775812449)
    ·
      refine ⟨487153855675006331859337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 649538474233341775812449 487153855675006331859337)
      ·
        refine ⟨365365391756254748894503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487153855675006331859337 365365391756254748894503)
        ·
          refine ⟨548048087634382123341755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365365391756254748894503 548048087634382123341755)
          ·
            refine ⟨822072131451573185012633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548048087634382123341755 822072131451573185012633)
            ·
              refine ⟨616554098588679888759475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822072131451573185012633 616554098588679888759475)
              ·
                refine ⟨924831147883019833139213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616554098588679888759475 924831147883019833139213)
                ·
                  refine ⟨346811680456132437427205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924831147883019833139213 346811680456132437427205)
                  ·
                    refine ⟨65027190085524832017601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346811680456132437427205 65027190085524832017601)
                    ·
                      refine ⟨48770392564143624013201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65027190085524832017601 48770392564143624013201)
                      ·
                        rfl

theorem cell23_94980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_94980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94980 prefixEnd_94980 := by exact prefixLift 94980
  have htrace : WordTrace (prefixWord ++ tailWord_94980) baseStart_94980 baseEnd_94980 := by
    simpa [prefixWord, tailWord_94980, baseEnd_94980] using wordTrace_append hprefix tailTrace_94980
  have hstable : (prefixWord ++ tailWord_94980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94980).length < 2 ^ (prefixWord ++ tailWord_94980).sum := by decide
  have hdescent : baseEnd_94980 < baseStart_94980 := by decide
  rcases family_descends (prefixWord ++ tailWord_94980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94983 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_94983 : Nat := 118140960795 + 94983 * 2 ^ 59
def prefixEnd_94983 : Nat := 4983230072969 + 3 ^ 40 * 94983 * 2
def baseEnd_94983 : Nat := 48771933006107112275687

theorem tailTrace_94983 : CollatzResearch.WordTrace tailWord_94983 prefixEnd_94983 48771933006107112275687 := by
  unfold tailWord_94983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464314614900287650025603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2309543076600191766683735 3464314614900287650025603)
  ·
    refine ⟨5196471922350431475038405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464314614900287650025603 5196471922350431475038405)
    ·
      refine ⟨974338485440705901569701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5196471922350431475038405 974338485440705901569701)
      ·
        refine ⟨182688466020132356544319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 974338485440705901569701 182688466020132356544319)
        ·
          refine ⟨274032699030198534816479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182688466020132356544319 274032699030198534816479)
          ·
            refine ⟨411049048545297802224719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274032699030198534816479 411049048545297802224719)
            ·
              refine ⟨616573572817946703337079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411049048545297802224719 616573572817946703337079)
              ·
                refine ⟨924860359226920055005619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616573572817946703337079 924860359226920055005619)
                ·
                  refine ⟨1387290538840380082508429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924860359226920055005619 1387290538840380082508429)
                  ·
                    refine ⟨520233952065142530940661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1387290538840380082508429 520233952065142530940661)
                    ·
                      refine ⟨48771933006107112275687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 520233952065142530940661 48771933006107112275687)
                      ·
                        rfl

theorem cell23_94983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_94983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94983 prefixEnd_94983 := by exact prefixLift 94983
  have htrace : WordTrace (prefixWord ++ tailWord_94983) baseStart_94983 baseEnd_94983 := by
    simpa [prefixWord, tailWord_94983, baseEnd_94983] using wordTrace_append hprefix tailTrace_94983
  have hstable : (prefixWord ++ tailWord_94983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94983).length < 2 ^ (prefixWord ++ tailWord_94983).sum := by decide
  have hdescent : baseEnd_94983 < baseStart_94983 := by decide
  rcases family_descends (prefixWord ++ tailWord_94983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94997 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_94997 : Nat := 118140960795 + 94997 * 2 ^ 59
def prefixEnd_94997 : Nat := 4983230072969 + 3 ^ 40 * 94997 * 2
def baseEnd_94997 : Nat := 48779121735270057500623

theorem tailTrace_94997 : CollatzResearch.WordTrace tailWord_94997 prefixEnd_94997 48779121735270057500623 := by
  unfold tailWord_94997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464825236849568041035245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2309883491233045360690163 3464825236849568041035245)
  ·
    refine ⟨1299309463818588015388217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3464825236849568041035245 1299309463818588015388217)
    ·
      refine ⟨974482097863941011541163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1299309463818588015388217 974482097863941011541163)
      ·
        refine ⟨1461723146795911517311745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974482097863941011541163 1461723146795911517311745)
        ·
          refine ⟨1096292360096933637983809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461723146795911517311745 1096292360096933637983809)
          ·
            refine ⟨822219270072700228487857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096292360096933637983809 822219270072700228487857)
            ·
              refine ⟨616664452554525171365893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822219270072700228487857 616664452554525171365893)
              ·
                refine ⟨115624584853973469631105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616664452554525171365893 115624584853973469631105)
                ·
                  refine ⟨86718438640480102223329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115624584853973469631105 86718438640480102223329)
                  ·
                    refine ⟨65038828980360076667497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86718438640480102223329 65038828980360076667497)
                    ·
                      refine ⟨48779121735270057500623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65038828980360076667497 48779121735270057500623)
                      ·
                        rfl

theorem cell23_94997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_94997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_94997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_94997 prefixEnd_94997 := by exact prefixLift 94997
  have htrace : WordTrace (prefixWord ++ tailWord_94997) baseStart_94997 baseEnd_94997 := by
    simpa [prefixWord, tailWord_94997, baseEnd_94997] using wordTrace_append hprefix tailTrace_94997
  have hstable : (prefixWord ++ tailWord_94997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94997).length < 2 ^ (prefixWord ++ tailWord_94997).sum := by decide
  have hdescent : baseEnd_94997 < baseStart_94997 := by decide
  rcases family_descends (prefixWord ++ tailWord_94997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95013 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_95013 : Nat := 118140960795 + 95013 * 2 ^ 59
def prefixEnd_95013 : Nat := 4983230072969 + 3 ^ 40 * 95013 * 2
def baseEnd_95013 : Nat := 48787337425741994900549

theorem tailTrace_95013 : CollatzResearch.WordTrace tailWord_95013 prefixEnd_95013 48787337425741994900549 := by
  unfold tailWord_95013
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465408804791602773617693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2310272536527735182411795 3465408804791602773617693)
  ·
    refine ⟨1299528301796851040106635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3465408804791602773617693 1299528301796851040106635)
    ·
      refine ⟨1949292452695276560159953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299528301796851040106635 1949292452695276560159953)
      ·
        refine ⟨1461969339521457420119965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1949292452695276560159953 1461969339521457420119965)
        ·
          refine ⟨548238502320546532544987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1461969339521457420119965 548238502320546532544987)
          ·
            refine ⟨822357753480819798817481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548238502320546532544987 822357753480819798817481)
            ·
              refine ⟨616768315110614849113111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822357753480819798817481 616768315110614849113111)
              ·
                refine ⟨925152472665922273669667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616768315110614849113111 925152472665922273669667)
                ·
                  refine ⟨1387728708998883410504501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925152472665922273669667 1387728708998883410504501)
                  ·
                    refine ⟨130099566468645319734797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1387728708998883410504501 130099566468645319734797)
                    ·
                      refine ⟨48787337425741994900549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 130099566468645319734797 48787337425741994900549)
                      ·
                        rfl

theorem cell23_95013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_95013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95013 prefixEnd_95013 := by exact prefixLift 95013
  have htrace : WordTrace (prefixWord ++ tailWord_95013) baseStart_95013 baseEnd_95013 := by
    simpa [prefixWord, tailWord_95013, baseEnd_95013] using wordTrace_append hprefix tailTrace_95013
  have hstable : (prefixWord ++ tailWord_95013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95013).length < 2 ^ (prefixWord ++ tailWord_95013).sum := by decide
  have hdescent : baseEnd_95013 < baseStart_95013 := by decide
  rcases family_descends (prefixWord ++ tailWord_95013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
