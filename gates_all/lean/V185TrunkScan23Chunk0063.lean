import V185TrunkScan23Chunk0062

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_372098 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_372098 : Nat := 118140960795 + 372098 * 2 ^ 59
def prefixEnd_372098 : Nat := 4983230072969 + 3 ^ 40 * 372098 * 2
def baseEnd_372098 : Nat := 191065124576790398563759

theorem tailTrace_372098 : CollatzResearch.WordTrace tailWord_372098 prefixEnd_372098 191065124576790398563759 := by
  unfold tailWord_372098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392882251489992531023237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9047686003973313416061965 3392882251489992531023237)
  ·
    refine ⟨636165422154373599566857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3392882251489992531023237 636165422154373599566857)
    ·
      refine ⟨477124066615780199675143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636165422154373599566857 477124066615780199675143)
      ·
        refine ⟨715686099923670299512715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477124066615780199675143 715686099923670299512715)
        ·
          refine ⟨1073529149885505449269073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715686099923670299512715 1073529149885505449269073)
          ·
            refine ⟨805146862414129086951805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073529149885505449269073 805146862414129086951805)
            ·
              refine ⟨301930073405298407606927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805146862414129086951805 301930073405298407606927)
              ·
                refine ⟨452895110107947611410391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301930073405298407606927 452895110107947611410391)
                ·
                  refine ⟨679342665161921417115587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452895110107947611410391 679342665161921417115587)
                  ·
                    refine ⟨1019013997742882125673381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679342665161921417115587 1019013997742882125673381)
                    ·
                      refine ⟨191065124576790398563759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1019013997742882125673381 191065124576790398563759)
                      ·
                        rfl

theorem cell23_372098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_372098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372098 prefixEnd_372098 := by exact prefixLift 372098
  have htrace : WordTrace (prefixWord ++ tailWord_372098) baseStart_372098 baseEnd_372098 := by
    simpa [prefixWord, tailWord_372098, baseEnd_372098] using wordTrace_append hprefix tailTrace_372098
  have hstable : (prefixWord ++ tailWord_372098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372098).length < 2 ^ (prefixWord ++ tailWord_372098).sum := by decide
  have hdescent : baseEnd_372098 < baseStart_372098 := by decide
  rcases family_descends (prefixWord ++ tailWord_372098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372140 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_372140 : Nat := 118140960795 + 372140 * 2 ^ 59
def prefixEnd_372140 : Nat := 4983230072969 + 3 ^ 40 * 372140 * 2
def baseEnd_372140 : Nat := 191086690764279234238565

theorem tailTrace_372140 : CollatzResearch.WordTrace tailWord_372140 prefixEnd_372140 191086690764279234238565 := by
  unfold tailWord_372140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786530435903905648560937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9048707247871874198081249 6786530435903905648560937)
  ·
    refine ⟨5089897826927929236420703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6786530435903905648560937 5089897826927929236420703)
    ·
      refine ⟨7634846740391893854631055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5089897826927929236420703 7634846740391893854631055)
      ·
        refine ⟨11452270110587840781946583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634846740391893854631055 11452270110587840781946583)
        ·
          refine ⟨17178405165881761172919875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11452270110587840781946583 17178405165881761172919875)
          ·
            refine ⟨25767607748822641759379813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17178405165881761172919875 25767607748822641759379813)
            ·
              refine ⟨4831426452904245329883715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25767607748822641759379813 4831426452904245329883715)
              ·
                refine ⟨7247139679356367994825573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831426452904245329883715 7247139679356367994825573)
                ·
                  refine ⟨1358838689879318999029795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7247139679356367994825573 1358838689879318999029795)
                  ·
                    refine ⟨2038258034818978498544693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358838689879318999029795 2038258034818978498544693)
                    ·
                      refine ⟨191086690764279234238565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2038258034818978498544693 191086690764279234238565)
                      ·
                        rfl

theorem cell23_372140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_372140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372140 prefixEnd_372140 := by exact prefixLift 372140
  have htrace : WordTrace (prefixWord ++ tailWord_372140) baseStart_372140 baseEnd_372140 := by
    simpa [prefixWord, tailWord_372140, baseEnd_372140] using wordTrace_append hprefix tailTrace_372140
  have hstable : (prefixWord ++ tailWord_372140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372140).length < 2 ^ (prefixWord ++ tailWord_372140).sum := by decide
  have hdescent : baseEnd_372140 < baseStart_372140 := by decide
  rcases family_descends (prefixWord ++ tailWord_372140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372141 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_372141 : Nat := 118140960795 + 372141 * 2 ^ 59
def prefixEnd_372141 : Nat := 4983230072969 + 3 ^ 40 * 372141 * 2
def baseEnd_372141 : Nat := 191087204244933730326061

theorem tailTrace_372141 : CollatzResearch.WordTrace tailWord_372141 prefixEnd_372141 191087204244933730326061 := by
  unfold tailWord_372141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573097344804188467908277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9048731563202792311938851 13573097344804188467908277)
  ·
    refine ⟨1272477876075392668866401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13573097344804188467908277 1272477876075392668866401)
    ·
      refine ⟨954358407056544501649801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1272477876075392668866401 954358407056544501649801)
      ·
        refine ⟨715768805292408376237351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954358407056544501649801 715768805292408376237351)
        ·
          refine ⟨1073653207938612564356027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715768805292408376237351 1073653207938612564356027)
          ·
            refine ⟨1610479811907918846534041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073653207938612564356027 1610479811907918846534041)
            ·
              refine ⟨1207859858930939134900531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610479811907918846534041 1207859858930939134900531)
              ·
                refine ⟨1811789788396408702350797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207859858930939134900531 1811789788396408702350797)
                ·
                  refine ⟨679421170648653263381549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1811789788396408702350797 679421170648653263381549)
                  ·
                    refine ⟨254782938993244973768081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679421170648653263381549 254782938993244973768081)
                    ·
                      refine ⟨191087204244933730326061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254782938993244973768081 191087204244933730326061)
                      ·
                        rfl

theorem cell23_372141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_372141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372141 prefixEnd_372141 := by exact prefixLift 372141
  have htrace : WordTrace (prefixWord ++ tailWord_372141) baseStart_372141 baseEnd_372141 := by
    simpa [prefixWord, tailWord_372141, baseEnd_372141] using wordTrace_append hprefix tailTrace_372141
  have hstable : (prefixWord ++ tailWord_372141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372141).length < 2 ^ (prefixWord ++ tailWord_372141).sum := by decide
  have hdescent : baseEnd_372141 < baseStart_372141 := by decide
  rcases family_descends (prefixWord ++ tailWord_372141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372171 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 2, 2, 2]
def baseStart_372171 : Nat := 118140960795 + 372171 * 2 ^ 59
def prefixEnd_372171 : Nat := 4983230072969 + 3 ^ 40 * 372171 * 2
def baseEnd_372171 : Nat := 191102608664568612950923

theorem tailTrace_372171 : CollatzResearch.WordTrace tailWord_372171 prefixEnd_372171 191102608664568612950923 := by
  unfold tailWord_372171
  simp only [CollatzResearch.WordTrace]
  refine ⟨13574191534695503591500367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9049461023130335727666911 13574191534695503591500367)
  ·
    refine ⟨20361287302043255387250551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13574191534695503591500367 20361287302043255387250551)
    ·
      refine ⟨30541930953064883080875827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20361287302043255387250551 30541930953064883080875827)
      ·
        refine ⟨45812896429597324621313741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30541930953064883080875827 45812896429597324621313741)
        ·
          refine ⟨17179836161098996732992653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45812896429597324621313741 17179836161098996732992653)
          ·
            refine ⟨6442438560412123774872245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17179836161098996732992653 6442438560412123774872245)
            ·
              refine ⟨603978615038636603894273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6442438560412123774872245 603978615038636603894273)
              ·
                refine ⟨452983961278977452920705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603978615038636603894273 452983961278977452920705)
                ·
                  refine ⟨339737970959233089690529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452983961278977452920705 339737970959233089690529)
                  ·
                    refine ⟨254803478219424817267897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 339737970959233089690529 254803478219424817267897)
                    ·
                      refine ⟨191102608664568612950923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254803478219424817267897 191102608664568612950923)
                      ·
                        rfl

theorem cell23_372171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 2, 2].length) (baseStart_372171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372171 prefixEnd_372171 := by exact prefixLift 372171
  have htrace : WordTrace (prefixWord ++ tailWord_372171) baseStart_372171 baseEnd_372171 := by
    simpa [prefixWord, tailWord_372171, baseEnd_372171] using wordTrace_append hprefix tailTrace_372171
  have hstable : (prefixWord ++ tailWord_372171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372171).length < 2 ^ (prefixWord ++ tailWord_372171).sum := by decide
  have hdescent : baseEnd_372171 < baseStart_372171 := by decide
  rcases family_descends (prefixWord ++ tailWord_372171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372228 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 5]
def baseStart_372228 : Nat := 118140960795 + 372228 * 2 ^ 59
def prefixEnd_372228 : Nat := 4983230072969 + 3 ^ 40 * 372228 * 2
def baseEnd_372228 : Nat := 21236875229097209993129

theorem tailTrace_372228 : CollatzResearch.WordTrace tailWord_372228 prefixEnd_372228 21236875229097209993129 := by
  unfold tailWord_372228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6788135247744501163162669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9050846996992668217550225 6788135247744501163162669)
  ·
    refine ⟨2545550717904187936186001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6788135247744501163162669 2545550717904187936186001)
    ·
      refine ⟨1909163038428140952139501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2545550717904187936186001 1909163038428140952139501)
      ·
        refine ⟨715936139410552857052313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1909163038428140952139501 715936139410552857052313)
        ·
          refine ⟨536952104557914642789235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715936139410552857052313 536952104557914642789235)
          ·
            refine ⟨805428156836871964183853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536952104557914642789235 805428156836871964183853)
            ·
              refine ⟨302035558813826986568945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805428156836871964183853 302035558813826986568945)
              ·
                refine ⟨226526669110370239926709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302035558813826986568945 226526669110370239926709)
                ·
                  refine ⟨21236875229097209993129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226526669110370239926709 21236875229097209993129)
                  ·
                    rfl

theorem cell23_372228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_372228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372228 prefixEnd_372228 := by exact prefixLift 372228
  have htrace : WordTrace (prefixWord ++ tailWord_372228) baseStart_372228 baseEnd_372228 := by
    simpa [prefixWord, tailWord_372228, baseEnd_372228] using wordTrace_append hprefix tailTrace_372228
  have hstable : (prefixWord ++ tailWord_372228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372228).length < 2 ^ (prefixWord ++ tailWord_372228).sum := by decide
  have hdescent : baseEnd_372228 < baseStart_372228 := by decide
  rcases family_descends (prefixWord ++ tailWord_372228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372304 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2]
def baseStart_372304 : Nat := 118140960795 + 372304 * 2 ^ 59
def prefixEnd_372304 : Nat := 4983230072969 + 3 ^ 40 * 372304 * 2
def baseEnd_372304 : Nat := 191170901591616592587811

theorem tailTrace_372304 : CollatzResearch.WordTrace tailWord_372304 prefixEnd_372304 191170901591616592587811 := by
  unfold tailWord_372304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789521221606833653045983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9052694962142444870727977 6789521221606833653045983)
  ·
    refine ⟨10184281832410250479568975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6789521221606833653045983 10184281832410250479568975)
    ·
      refine ⟨15276422748615375719353463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10184281832410250479568975 15276422748615375719353463)
      ·
        refine ⟨22914634122923063579030195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15276422748615375719353463 22914634122923063579030195)
        ·
          refine ⟨34371951184384595368545293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22914634122923063579030195 34371951184384595368545293)
          ·
            refine ⟨12889481694144223263204485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34371951184384595368545293 12889481694144223263204485)
            ·
              refine ⟨2416777817652041861850841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12889481694144223263204485 2416777817652041861850841)
              ·
                refine ⟨1812583363239031396388131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2416777817652041861850841 1812583363239031396388131)
                ·
                  refine ⟨2718875044858547094582197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812583363239031396388131 2718875044858547094582197)
                  ·
                    refine ⟨254894535455488790117081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2718875044858547094582197 254894535455488790117081)
                    ·
                      refine ⟨191170901591616592587811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254894535455488790117081 191170901591616592587811)
                      ·
                        rfl

theorem cell23_372304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2].length) (baseStart_372304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372304 prefixEnd_372304 := by exact prefixLift 372304
  have htrace : WordTrace (prefixWord ++ tailWord_372304) baseStart_372304 baseEnd_372304 := by
    simpa [prefixWord, tailWord_372304, baseEnd_372304] using wordTrace_append hprefix tailTrace_372304
  have hstable : (prefixWord ++ tailWord_372304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372304).length < 2 ^ (prefixWord ++ tailWord_372304).sum := by decide
  have hdescent : baseEnd_372304 < baseStart_372304 := by decide
  rcases family_descends (prefixWord ++ tailWord_372304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372311 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_372311 : Nat := 118140960795 + 372311 * 2 ^ 59
def prefixEnd_372311 : Nat := 4983230072969 + 3 ^ 40 * 372311 * 2
def baseEnd_372311 : Nat := 191174495956198065200279

theorem tailTrace_372311 : CollatzResearch.WordTrace tailWord_372311 prefixEnd_372311 191174495956198065200279 := by
  unfold tailWord_372311
  simp only [CollatzResearch.WordTrace]
  refine ⟨13579297754188307501596787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052865169458871667731191 13579297754188307501596787)
  ·
    refine ⟨20368946631282461252395181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13579297754188307501596787 20368946631282461252395181)
    ·
      refine ⟨7638354986730922969648193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20368946631282461252395181 7638354986730922969648193)
      ·
        refine ⟨5728766240048192227236145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7638354986730922969648193 5728766240048192227236145)
        ·
          refine ⟨4296574680036144170427109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5728766240048192227236145 4296574680036144170427109)
          ·
            refine ⟨805607752506777031955083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4296574680036144170427109 805607752506777031955083)
            ·
              refine ⟨1208411628760165547932625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805607752506777031955083 1208411628760165547932625)
              ·
                refine ⟨906308721570124160949469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208411628760165547932625 906308721570124160949469)
                ·
                  refine ⟨339865770588796560356051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906308721570124160949469 339865770588796560356051)
                  ·
                    refine ⟨509798655883194840534077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 339865770588796560356051 509798655883194840534077)
                    ·
                      refine ⟨191174495956198065200279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 509798655883194840534077 191174495956198065200279)
                      ·
                        rfl

theorem cell23_372311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_372311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372311 prefixEnd_372311 := by exact prefixLift 372311
  have htrace : WordTrace (prefixWord ++ tailWord_372311) baseStart_372311 baseEnd_372311 := by
    simpa [prefixWord, tailWord_372311, baseEnd_372311] using wordTrace_append hprefix tailTrace_372311
  have hstable : (prefixWord ++ tailWord_372311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372311).length < 2 ^ (prefixWord ++ tailWord_372311).sum := by decide
  have hdescent : baseEnd_372311 < baseStart_372311 := by decide
  rcases family_descends (prefixWord ++ tailWord_372311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372337 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_372337 : Nat := 118140960795 + 372337 * 2 ^ 59
def prefixEnd_372337 : Nat := 4983230072969 + 3 ^ 40 * 372337 * 2
def baseEnd_372337 : Nat := 191187846453214963475159

theorem tailTrace_372337 : CollatzResearch.WordTrace tailWord_372337 prefixEnd_372337 191187846453214963475159 := by
  unfold tailWord_372337
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580246052094113942043265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9053497368062742628028843 13580246052094113942043265)
  ·
    refine ⟨10185184539070585456532449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13580246052094113942043265 10185184539070585456532449)
    ·
      refine ⟨7638888404302939092399337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10185184539070585456532449 7638888404302939092399337)
      ·
        refine ⟨5729166303227204319299503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7638888404302939092399337 5729166303227204319299503)
        ·
          refine ⟨8593749454840806478949255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729166303227204319299503 8593749454840806478949255)
          ·
            refine ⟨12890624182261209718423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8593749454840806478949255 12890624182261209718423883)
            ·
              refine ⟨19335936273391814577635825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12890624182261209718423883 19335936273391814577635825)
              ·
                refine ⟨14501952205043860933226869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19335936273391814577635825 14501952205043860933226869)
                ·
                  refine ⟨1359558019222861962490019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14501952205043860933226869 1359558019222861962490019)
                  ·
                    refine ⟨2039337028834292943735029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1359558019222861962490019 2039337028834292943735029)
                    ·
                      refine ⟨191187846453214963475159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2039337028834292943735029 191187846453214963475159)
                      ·
                        rfl

theorem cell23_372337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_372337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372337 prefixEnd_372337 := by exact prefixLift 372337
  have htrace : WordTrace (prefixWord ++ tailWord_372337) baseStart_372337 baseEnd_372337 := by
    simpa [prefixWord, tailWord_372337, baseEnd_372337] using wordTrace_append hprefix tailTrace_372337
  have hstable : (prefixWord ++ tailWord_372337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372337).length < 2 ^ (prefixWord ++ tailWord_372337).sum := by decide
  have hdescent : baseEnd_372337 < baseStart_372337 := by decide
  rcases family_descends (prefixWord ++ tailWord_372337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372347 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_372347 : Nat := 118140960795 + 372347 * 2 ^ 59
def prefixEnd_372347 : Nat := 4983230072969 + 3 ^ 40 * 372347 * 2
def baseEnd_372347 : Nat := 191192981259759924350113

theorem tailTrace_372347 : CollatzResearch.WordTrace tailWord_372347 prefixEnd_372347 191192981259759924350113 := by
  unfold tailWord_372347
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580610782057885649907295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9053740521371923766604863 13580610782057885649907295)
  ·
    refine ⟨20370916173086828474860943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13580610782057885649907295 20370916173086828474860943)
    ·
      refine ⟨30556374259630242712291415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20370916173086828474860943 30556374259630242712291415)
      ·
        refine ⟨45834561389445364068437123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30556374259630242712291415 45834561389445364068437123)
        ·
          refine ⟨68751842084168046102655685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45834561389445364068437123 68751842084168046102655685)
          ·
            refine ⟨12890970390781508644247941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68751842084168046102655685 12890970390781508644247941)
            ·
              refine ⟨2417056948271532870796489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12890970390781508644247941 2417056948271532870796489)
              ·
                refine ⟨1812792711203649653097367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417056948271532870796489 1812792711203649653097367)
                ·
                  refine ⟨2719189066805474479646051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812792711203649653097367 2719189066805474479646051)
                  ·
                    refine ⟨4078783600208211719469077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719189066805474479646051 4078783600208211719469077)
                    ·
                      refine ⟨191192981259759924350113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4078783600208211719469077 191192981259759924350113)
                      ·
                        rfl

theorem cell23_372347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_372347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372347 prefixEnd_372347 := by exact prefixLift 372347
  have htrace : WordTrace (prefixWord ++ tailWord_372347) baseStart_372347 baseEnd_372347 := by
    simpa [prefixWord, tailWord_372347, baseEnd_372347] using wordTrace_append hprefix tailTrace_372347
  have hstable : (prefixWord ++ tailWord_372347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372347).length < 2 ^ (prefixWord ++ tailWord_372347).sum := by decide
  have hdescent : baseEnd_372347 < baseStart_372347 := by decide
  rcases family_descends (prefixWord ++ tailWord_372347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372357 : List Nat := [1, 3, 1, 1, 4, 1, 2, 10]
def baseStart_372357 : Nat := 118140960795 + 372357 * 2 ^ 59
def prefixEnd_372357 : Nat := 4983230072969 + 3 ^ 40 * 372357 * 2
def baseEnd_372357 : Nat := 7081411706159440193521

theorem tailTrace_372357 : CollatzResearch.WordTrace tailWord_372357 prefixEnd_372357 7081411706159440193521 := by
  unfold tailWord_372357
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580975512021657357771325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9053983674681104905180883 13580975512021657357771325)
  ·
    refine ⟨5092865817008121509164247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13580975512021657357771325 5092865817008121509164247)
    ·
      refine ⟨7639298725512182263746371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5092865817008121509164247 7639298725512182263746371)
      ·
        refine ⟨11458948088268273395619557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639298725512182263746371 11458948088268273395619557)
        ·
          refine ⟨2148552766550301261678667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11458948088268273395619557 2148552766550301261678667)
          ·
            refine ⟨3222829149825451892518001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148552766550301261678667 3222829149825451892518001)
            ·
              refine ⟨2417121862369088919388501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222829149825451892518001 2417121862369088919388501)
              ·
                refine ⟨7081411706159440193521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2417121862369088919388501 7081411706159440193521)
                ·
                  rfl

theorem cell23_372357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 10].length) (baseStart_372357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372357 prefixEnd_372357 := by exact prefixLift 372357
  have htrace : WordTrace (prefixWord ++ tailWord_372357) baseStart_372357 baseEnd_372357 := by
    simpa [prefixWord, tailWord_372357, baseEnd_372357] using wordTrace_append hprefix tailTrace_372357
  have hstable : (prefixWord ++ tailWord_372357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372357).length < 2 ^ (prefixWord ++ tailWord_372357).sum := by decide
  have hdescent : baseEnd_372357 < baseStart_372357 := by decide
  rcases family_descends (prefixWord ++ tailWord_372357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372422 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_372422 : Nat := 118140960795 + 372422 * 2 ^ 59
def prefixEnd_372422 : Nat := 4983230072969 + 3 ^ 40 * 372422 * 2
def baseEnd_372422 : Nat := 191231492308847130912269

theorem tailTrace_372422 : CollatzResearch.WordTrace tailWord_372422 prefixEnd_372422 191231492308847130912269 := by
  unfold tailWord_372422
  simp only [CollatzResearch.WordTrace]
  refine ⟨424479570524567920590235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9055564171190782305925013 424479570524567920590235)
  ·
    refine ⟨636719355786851880885353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424479570524567920590235 636719355786851880885353)
    ·
      refine ⟨477539516840138910664015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636719355786851880885353 477539516840138910664015)
      ·
        refine ⟨716309275260208365996023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477539516840138910664015 716309275260208365996023)
        ·
          refine ⟨1074463912890312548994035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716309275260208365996023 1074463912890312548994035)
          ·
            refine ⟨1611695869335468823491053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074463912890312548994035 1611695869335468823491053)
            ·
              refine ⟨604385951000800808809145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1611695869335468823491053 604385951000800808809145)
              ·
                refine ⟨453289463250600606606859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604385951000800808809145 453289463250600606606859)
                ·
                  refine ⟨679934194875900909910289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453289463250600606606859 679934194875900909910289)
                  ·
                    refine ⟨509950646156925682432717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679934194875900909910289 509950646156925682432717)
                    ·
                      refine ⟨191231492308847130912269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 509950646156925682432717 191231492308847130912269)
                      ·
                        rfl

theorem cell23_372422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_372422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372422 prefixEnd_372422 := by exact prefixLift 372422
  have htrace : WordTrace (prefixWord ++ tailWord_372422) baseStart_372422 baseEnd_372422 := by
    simpa [prefixWord, tailWord_372422, baseEnd_372422] using wordTrace_append hprefix tailTrace_372422
  have hstable : (prefixWord ++ tailWord_372422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372422).length < 2 ^ (prefixWord ++ tailWord_372422).sum := by decide
  have hdescent : baseEnd_372422 < baseStart_372422 := by decide
  rcases family_descends (prefixWord ++ tailWord_372422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372441 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 3, 4, 2]
def baseStart_372441 : Nat := 118140960795 + 372441 * 2 ^ 59
def prefixEnd_372441 : Nat := 4983230072969 + 3 ^ 40 * 372441 * 2
def baseEnd_372441 : Nat := 191241248441282556574681

theorem tailTrace_372441 : CollatzResearch.WordTrace tailWord_372441 prefixEnd_372441 191241248441282556574681 := by
  unfold tailWord_372441
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584039243717339703829177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9056026162478226469219451 13584039243717339703829177)
  ·
    refine ⟨10188029432788004777871883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13584039243717339703829177 10188029432788004777871883)
    ·
      refine ⟨15282044149182007166807825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10188029432788004777871883 15282044149182007166807825)
      ·
        refine ⟨11461533111886505375105869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15282044149182007166807825 11461533111886505375105869)
        ·
          refine ⟨4298074916957439515664701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11461533111886505375105869 4298074916957439515664701)
          ·
            refine ⟨1611778093859039818374263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4298074916957439515664701 1611778093859039818374263)
            ·
              refine ⟨2417667140788559727561395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611778093859039818374263 2417667140788559727561395)
              ·
                refine ⟨3626500711182839591342093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417667140788559727561395 3626500711182839591342093)
                ·
                  refine ⟨1359937766693564846753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3626500711182839591342093 1359937766693564846753285)
                  ·
                    refine ⟨254988331255043408766241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359937766693564846753285 254988331255043408766241)
                    ·
                      refine ⟨191241248441282556574681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254988331255043408766241 191241248441282556574681)
                      ·
                        rfl

theorem cell23_372441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_372441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372441 prefixEnd_372441 := by exact prefixLift 372441
  have htrace : WordTrace (prefixWord ++ tailWord_372441) baseStart_372441 baseEnd_372441 := by
    simpa [prefixWord, tailWord_372441, baseEnd_372441] using wordTrace_append hprefix tailTrace_372441
  have hstable : (prefixWord ++ tailWord_372441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372441).length < 2 ^ (prefixWord ++ tailWord_372441).sum := by decide
  have hdescent : baseEnd_372441 < baseStart_372441 := by decide
  rcases family_descends (prefixWord ++ tailWord_372441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372458 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_372458 : Nat := 118140960795 + 372458 * 2 ^ 59
def prefixEnd_372458 : Nat := 4983230072969 + 3 ^ 40 * 372458 * 2
def baseEnd_372458 : Nat := 191249977612408990062103

theorem tailTrace_372458 : CollatzResearch.WordTrace tailWord_372458 prefixEnd_372458 191249977612408990062103 := by
  unfold tailWord_372458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396164821163937901799507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9056439523103834404798685 3396164821163937901799507)
  ·
    refine ⟨5094247231745906852699261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3396164821163937901799507 5094247231745906852699261)
    ·
      refine ⟨1910342711904715069762223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5094247231745906852699261 1910342711904715069762223)
      ·
        refine ⟨2865514067857072604643335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910342711904715069762223 2865514067857072604643335)
        ·
          refine ⟨4298271101785608906965003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865514067857072604643335 4298271101785608906965003)
          ·
            refine ⟨6447406652678413360447505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298271101785608906965003 6447406652678413360447505)
            ·
              refine ⟨4835554989508810020335629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447406652678413360447505 4835554989508810020335629)
              ·
                refine ⟨1813333121065803757625861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835554989508810020335629 1813333121065803757625861)
                ·
                  refine ⟨339999960199838204554849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813333121065803757625861 339999960199838204554849)
                  ·
                    refine ⟨254999970149878653416137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 339999960199838204554849 254999970149878653416137)
                    ·
                      refine ⟨191249977612408990062103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254999970149878653416137 191249977612408990062103)
                      ·
                        rfl

theorem cell23_372458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_372458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372458 prefixEnd_372458 := by exact prefixLift 372458
  have htrace : WordTrace (prefixWord ++ tailWord_372458) baseStart_372458 baseEnd_372458 := by
    simpa [prefixWord, tailWord_372458, baseEnd_372458] using wordTrace_append hprefix tailTrace_372458
  have hstable : (prefixWord ++ tailWord_372458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372458).length < 2 ^ (prefixWord ++ tailWord_372458).sum := by decide
  have hdescent : baseEnd_372458 < baseStart_372458 := by decide
  rcases family_descends (prefixWord ++ tailWord_372458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372461 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_372461 : Nat := 118140960795 + 372461 * 2 ^ 59
def prefixEnd_372461 : Nat := 4983230072969 + 3 ^ 40 * 372461 * 2
def baseEnd_372461 : Nat := 191251518054372478324589

theorem tailTrace_372461 : CollatzResearch.WordTrace tailWord_372461 prefixEnd_372461 191251518054372478324589 := by
  unfold tailWord_372461
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584768703644883119557237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9056512469096588746371491 13584768703644883119557237)
  ·
    refine ⟨1273572065966707792458491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13584768703644883119557237 1273572065966707792458491)
    ·
      refine ⟨1910358098950061688687737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273572065966707792458491 1910358098950061688687737)
      ·
        refine ⟨1432768574212546266515803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910358098950061688687737 1432768574212546266515803)
        ·
          refine ⟨2149152861318819399773705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432768574212546266515803 2149152861318819399773705)
          ·
            refine ⟨1611864645989114549830279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149152861318819399773705 1611864645989114549830279)
            ·
              refine ⟨2417796968983671824745419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611864645989114549830279 2417796968983671824745419)
              ·
                refine ⟨3626695453475507737118129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417796968983671824745419 3626695453475507737118129)
                ·
                  refine ⟨2720021590106630802838597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3626695453475507737118129 2720021590106630802838597)
                  ·
                    refine ⟨510004048144993275532237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720021590106630802838597 510004048144993275532237)
                    ·
                      refine ⟨191251518054372478324589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510004048144993275532237 191251518054372478324589)
                      ·
                        rfl

theorem cell23_372461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_372461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372461 prefixEnd_372461 := by exact prefixLift 372461
  have htrace : WordTrace (prefixWord ++ tailWord_372461) baseStart_372461 baseEnd_372461 := by
    simpa [prefixWord, tailWord_372461, baseEnd_372461] using wordTrace_append hprefix tailTrace_372461
  have hstable : (prefixWord ++ tailWord_372461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372461).length < 2 ^ (prefixWord ++ tailWord_372461).sum := by decide
  have hdescent : baseEnd_372461 < baseStart_372461 := by decide
  rcases family_descends (prefixWord ++ tailWord_372461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372468 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_372468 : Nat := 118140960795 + 372468 * 2 ^ 59
def prefixEnd_372468 : Nat := 4983230072969 + 3 ^ 40 * 372468 * 2
def baseEnd_372468 : Nat := 63751704139651316979019

theorem tailTrace_372468 : CollatzResearch.WordTrace tailWord_372468 prefixEnd_372468 63751704139651316979019 := by
  unfold tailWord_372468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792512007309761657531029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9056682676413015543374705 6792512007309761657531029)
  ·
    refine ⟨318399000342645077696767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6792512007309761657531029 318399000342645077696767)
    ·
      refine ⟨477598500513967616545151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318399000342645077696767 477598500513967616545151)
      ·
        refine ⟨716397750770951424817727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477598500513967616545151 716397750770951424817727)
        ·
          refine ⟨1074596626156427137226591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716397750770951424817727 1074596626156427137226591)
          ·
            refine ⟨1611894939234640705839887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074596626156427137226591 1611894939234640705839887)
            ·
              refine ⟨2417842408851961058759831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611894939234640705839887 2417842408851961058759831)
              ·
                refine ⟨3626763613277941588139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417842408851961058759831 3626763613277941588139747)
                ·
                  refine ⟨5440145419916912382209621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626763613277941588139747 5440145419916912382209621)
                  ·
                    refine ⟨63751704139651316979019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5440145419916912382209621 63751704139651316979019)
                    ·
                      rfl

theorem cell23_372468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_372468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372468 prefixEnd_372468 := by exact prefixLift 372468
  have htrace : WordTrace (prefixWord ++ tailWord_372468) baseStart_372468 baseEnd_372468 := by
    simpa [prefixWord, tailWord_372468, baseEnd_372468] using wordTrace_append hprefix tailTrace_372468
  have hstable : (prefixWord ++ tailWord_372468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372468).length < 2 ^ (prefixWord ++ tailWord_372468).sum := by decide
  have hdescent : baseEnd_372468 < baseStart_372468 := by decide
  rcases family_descends (prefixWord ++ tailWord_372468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372504 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_372504 : Nat := 118140960795 + 372504 * 2 ^ 59
def prefixEnd_372504 : Nat := 4983230072969 + 3 ^ 40 * 372504 * 2
def baseEnd_372504 : Nat := 191273597722515810086891

theorem tailTrace_372504 : CollatzResearch.WordTrace tailWord_372504 prefixEnd_372504 191273597722515810086891 := by
  unfold tailWord_372504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793168521244550731686283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9057558028326067642248377 6793168521244550731686283)
  ·
    refine ⟨10189752781866826097529425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793168521244550731686283 10189752781866826097529425)
    ·
      refine ⟨7642314586400119573147069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10189752781866826097529425 7642314586400119573147069)
      ·
        refine ⟨2865867969900044839930151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7642314586400119573147069 2865867969900044839930151)
        ·
          refine ⟨4298801954850067259895227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865867969900044839930151 4298801954850067259895227)
          ·
            refine ⟨6448202932275100889842841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298801954850067259895227 6448202932275100889842841)
            ·
              refine ⟨4836152199206325667382131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6448202932275100889842841 4836152199206325667382131)
              ·
                refine ⟨7254228298809488501073197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836152199206325667382131 7254228298809488501073197)
                ·
                  refine ⟨2720335612053558187902449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7254228298809488501073197 2720335612053558187902449)
                  ·
                    refine ⟨2040251709040168640926837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2720335612053558187902449 2040251709040168640926837)
                    ·
                      refine ⟨191273597722515810086891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2040251709040168640926837 191273597722515810086891)
                      ·
                        rfl

theorem cell23_372504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_372504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372504 prefixEnd_372504 := by exact prefixLift 372504
  have htrace : WordTrace (prefixWord ++ tailWord_372504) baseStart_372504 baseEnd_372504 := by
    simpa [prefixWord, tailWord_372504, baseEnd_372504] using wordTrace_append hprefix tailTrace_372504
  have hstable : (prefixWord ++ tailWord_372504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372504).length < 2 ^ (prefixWord ++ tailWord_372504).sum := by decide
  have hdescent : baseEnd_372504 < baseStart_372504 := by decide
  rcases family_descends (prefixWord ++ tailWord_372504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372551 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_372551 : Nat := 118140960795 + 372551 * 2 ^ 59
def prefixEnd_372551 : Nat := 4983230072969 + 3 ^ 40 * 372551 * 2
def baseEnd_372551 : Nat := 191297731313277126199175

theorem tailTrace_372551 : CollatzResearch.WordTrace tailWord_372551 prefixEnd_372551 191297731313277126199175 := by
  unfold tailWord_372551
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588051273318828490333507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9058700848879218993555671 13588051273318828490333507)
  ·
    refine ⟨20382076909978242735500261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13588051273318828490333507 20382076909978242735500261)
    ·
      refine ⟨3821639420620920512906299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20382076909978242735500261 3821639420620920512906299)
      ·
        refine ⟨5732459130931380769359449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821639420620920512906299 5732459130931380769359449)
        ·
          refine ⟨4299344348198535577019587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5732459130931380769359449 4299344348198535577019587)
          ·
            refine ⟨6449016522297803365529381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299344348198535577019587 6449016522297803365529381)
            ·
              refine ⟨1209190597930838131036759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6449016522297803365529381 1209190597930838131036759)
              ·
                refine ⟨1813785896896257196555139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209190597930838131036759 1813785896896257196555139)
                ·
                  refine ⟨2720678845344385794832709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813785896896257196555139 2720678845344385794832709)
                  ·
                    refine ⟨510127283502072336531133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720678845344385794832709 510127283502072336531133)
                    ·
                      refine ⟨191297731313277126199175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510127283502072336531133 191297731313277126199175)
                      ·
                        rfl

theorem cell23_372551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_372551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372551 prefixEnd_372551 := by exact prefixLift 372551
  have htrace : WordTrace (prefixWord ++ tailWord_372551) baseStart_372551 baseEnd_372551 := by
    simpa [prefixWord, tailWord_372551, baseEnd_372551] using wordTrace_append hprefix tailTrace_372551
  have hstable : (prefixWord ++ tailWord_372551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372551).length < 2 ^ (prefixWord ++ tailWord_372551).sum := by decide
  have hdescent : baseEnd_372551 < baseStart_372551 := by decide
  rcases family_descends (prefixWord ++ tailWord_372551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372554 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_372554 : Nat := 118140960795 + 372554 * 2 ^ 59
def prefixEnd_372554 : Nat := 4983230072969 + 3 ^ 40 * 372554 * 2
def baseEnd_372554 : Nat := 21255474639471179384629

theorem tailTrace_372554 : CollatzResearch.WordTrace tailWord_372554 prefixEnd_372554 21255474639471179384629 := by
  unfold tailWord_372554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397040173076990000673179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9058773794871973335128477 3397040173076990000673179)
  ·
    refine ⟨5095560259615485001009769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3397040173076990000673179 5095560259615485001009769)
    ·
      refine ⟨3821670194711613750757327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5095560259615485001009769 3821670194711613750757327)
      ·
        refine ⟨5732505292067420626135991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821670194711613750757327 5732505292067420626135991)
        ·
          refine ⟨8598757938101130939203987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732505292067420626135991 8598757938101130939203987)
          ·
            refine ⟨12898136907151696408805981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598757938101130939203987 12898136907151696408805981)
            ·
              refine ⟨4836801340181886153302243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12898136907151696408805981 4836801340181886153302243)
              ·
                refine ⟨7255202010272829229953365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836801340181886153302243 7255202010272829229953365)
                ·
                  refine ⟨21255474639471179384629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 7255202010272829229953365 21255474639471179384629)
                  ·
                    rfl

theorem cell23_372554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_372554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372554 prefixEnd_372554 := by exact prefixLift 372554
  have htrace : WordTrace (prefixWord ++ tailWord_372554) baseStart_372554 baseEnd_372554 := by
    simpa [prefixWord, tailWord_372554, baseEnd_372554] using wordTrace_append hprefix tailTrace_372554
  have hstable : (prefixWord ++ tailWord_372554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372554).length < 2 ^ (prefixWord ++ tailWord_372554).sum := by decide
  have hdescent : baseEnd_372554 < baseStart_372554 := by decide
  rcases family_descends (prefixWord ++ tailWord_372554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372588 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 6]
def baseStart_372588 : Nat := 118140960795 + 372588 * 2 ^ 59
def prefixEnd_372588 : Nat := 4983230072969 + 3 ^ 40 * 372588 * 2
def baseEnd_372588 : Nat := 21257414455277053492945

theorem tailTrace_372588 : CollatzResearch.WordTrace tailWord_372588 prefixEnd_372588 21257414455277053492945 := by
  unfold tailWord_372588
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794700387092391904715209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9059600516123189206286945 6794700387092391904715209)
  ·
    refine ⟨5096025290319293928536407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6794700387092391904715209 5096025290319293928536407)
    ·
      refine ⟨7644037935478940892804611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5096025290319293928536407 7644037935478940892804611)
      ·
        refine ⟨11466056903218411339206917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7644037935478940892804611 11466056903218411339206917)
        ·
          refine ⟨2149885669353452126101297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11466056903218411339206917 2149885669353452126101297)
          ·
            refine ⟨1612414252015089094575973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149885669353452126101297 1612414252015089094575973)
            ·
              refine ⟨302327672252829205232995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1612414252015089094575973 302327672252829205232995)
              ·
                refine ⟨453491508379243807849493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302327672252829205232995 453491508379243807849493)
                ·
                  refine ⟨21257414455277053492945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 453491508379243807849493 21257414455277053492945)
                  ·
                    rfl

theorem cell23_372588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_372588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372588 prefixEnd_372588 := by exact prefixLift 372588
  have htrace : WordTrace (prefixWord ++ tailWord_372588) baseStart_372588 baseEnd_372588 := by
    simpa [prefixWord, tailWord_372588, baseEnd_372588] using wordTrace_append hprefix tailTrace_372588
  have hstable : (prefixWord ++ tailWord_372588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372588).length < 2 ^ (prefixWord ++ tailWord_372588).sum := by decide
  have hdescent : baseEnd_372588 < baseStart_372588 := by decide
  rcases family_descends (prefixWord ++ tailWord_372588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372601 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_372601 : Nat := 118140960795 + 372601 * 2 ^ 59
def prefixEnd_372601 : Nat := 4983230072969 + 3 ^ 40 * 372601 * 2
def baseEnd_372601 : Nat := 63774468448667310191315

theorem tailTrace_372601 : CollatzResearch.WordTrace tailWord_372601 prefixEnd_372601 63774468448667310191315 := by
  unfold tailWord_372601
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589874923137687029653657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9059916615425124686435771 13589874923137687029653657)
  ·
    refine ⟨10192406192353265272240243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13589874923137687029653657 10192406192353265272240243)
    ·
      refine ⟨15288609288529897908360365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10192406192353265272240243 15288609288529897908360365)
      ·
        refine ⟨5733228483198711715635137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15288609288529897908360365 5733228483198711715635137)
        ·
          refine ⟨4299921362399033786726353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733228483198711715635137 4299921362399033786726353)
          ·
            refine ⟨3224941021799275340044765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299921362399033786726353 3224941021799275340044765)
            ·
              refine ⟨1209352883174728252516787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224941021799275340044765 1209352883174728252516787)
              ·
                refine ⟨1814029324762092378775181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209352883174728252516787 1814029324762092378775181)
                ·
                  refine ⟨680260996785784642040693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1814029324762092378775181 680260996785784642040693)
                  ·
                    refine ⟨63774468448667310191315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 680260996785784642040693 63774468448667310191315)
                    ·
                      rfl

theorem cell23_372601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_372601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372601 prefixEnd_372601 := by exact prefixLift 372601
  have htrace : WordTrace (prefixWord ++ tailWord_372601) baseStart_372601 baseEnd_372601 := by
    simpa [prefixWord, tailWord_372601, baseEnd_372601] using wordTrace_append hprefix tailTrace_372601
  have hstable : (prefixWord ++ tailWord_372601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372601).length < 2 ^ (prefixWord ++ tailWord_372601).sum := by decide
  have hdescent : baseEnd_372601 < baseStart_372601 := by decide
  rcases family_descends (prefixWord ++ tailWord_372601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372655 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 3, 2, 2]
def baseStart_372655 : Nat := 118140960795 + 372655 * 2 ^ 59
def prefixEnd_372655 : Nat := 4983230072969 + 3 ^ 40 * 372655 * 2
def baseEnd_372655 : Nat := 191351133301344719298697

theorem tailTrace_372655 : CollatzResearch.WordTrace tailWord_372655 prefixEnd_372655 191351133301344719298697 := by
  unfold tailWord_372655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591844464942054252119419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9061229643294702834746279 13591844464942054252119419)
  ·
    refine ⟨20387766697413081378179129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13591844464942054252119419 20387766697413081378179129)
    ·
      refine ⟨15290825023059811033634347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20387766697413081378179129 15290825023059811033634347)
      ·
        refine ⟨22936237534589716550451521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15290825023059811033634347 22936237534589716550451521)
        ·
          refine ⟨17202178150942287412838641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22936237534589716550451521 17202178150942287412838641)
          ·
            refine ⟨12901633613206715559628981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17202178150942287412838641 12901633613206715559628981)
            ·
              refine ⟨1209528151238129583715217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12901633613206715559628981 1209528151238129583715217)
              ·
                refine ⟨907146113428597187786413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209528151238129583715217 907146113428597187786413)
                ·
                  refine ⟨340179792535723945419905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907146113428597187786413 340179792535723945419905)
                  ·
                    refine ⟨255134844401792959064929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 340179792535723945419905 255134844401792959064929)
                    ·
                      refine ⟨191351133301344719298697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255134844401792959064929 191351133301344719298697)
                      ·
                        rfl

theorem cell23_372655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 2, 2].length) (baseStart_372655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372655 prefixEnd_372655 := by exact prefixLift 372655
  have htrace : WordTrace (prefixWord ++ tailWord_372655) baseStart_372655 baseEnd_372655 := by
    simpa [prefixWord, tailWord_372655, baseEnd_372655] using wordTrace_append hprefix tailTrace_372655
  have hstable : (prefixWord ++ tailWord_372655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372655).length < 2 ^ (prefixWord ++ tailWord_372655).sum := by decide
  have hdescent : baseEnd_372655 < baseStart_372655 := by decide
  rcases family_descends (prefixWord ++ tailWord_372655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372705 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_372705 : Nat := 118140960795 + 372705 * 2 ^ 59
def prefixEnd_372705 : Nat := 4983230072969 + 3 ^ 40 * 372705 * 2
def baseEnd_372705 : Nat := 191376807334069523673467

theorem tailTrace_372705 : CollatzResearch.WordTrace tailWord_372705 prefixEnd_372705 191376807334069523673467 := by
  unfold tailWord_372705
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593668114760912791439569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9062445409840608527626379 13593668114760912791439569)
  ·
    refine ⟨10195251086070684593579677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13593668114760912791439569 10195251086070684593579677)
    ·
      refine ⟨3823219157276506722592379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10195251086070684593579677 3823219157276506722592379)
      ·
        refine ⟨5734828735914760083888569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823219157276506722592379 5734828735914760083888569)
        ·
          refine ⟨4301121551936070062916427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5734828735914760083888569 4301121551936070062916427)
          ·
            refine ⟨6451682327904105094374641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301121551936070062916427 6451682327904105094374641)
            ·
              refine ⟨4838761745928078820780981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6451682327904105094374641 4838761745928078820780981)
              ·
                refine ⟨453633913680757389448217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4838761745928078820780981 453633913680757389448217)
                ·
                  refine ⟨340225435260568042086163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453633913680757389448217 340225435260568042086163)
                  ·
                    refine ⟨510338152890852063129245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340225435260568042086163 510338152890852063129245)
                    ·
                      refine ⟨191376807334069523673467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510338152890852063129245 191376807334069523673467)
                      ·
                        rfl

theorem cell23_372705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_372705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372705 prefixEnd_372705 := by exact prefixLift 372705
  have htrace : WordTrace (prefixWord ++ tailWord_372705) baseStart_372705 baseEnd_372705 := by
    simpa [prefixWord, tailWord_372705, baseEnd_372705] using wordTrace_append hprefix tailTrace_372705
  have hstable : (prefixWord ++ tailWord_372705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372705).length < 2 ^ (prefixWord ++ tailWord_372705).sum := by decide
  have hdescent : baseEnd_372705 < baseStart_372705 := by decide
  rcases family_descends (prefixWord ++ tailWord_372705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372718 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_372718 : Nat := 118140960795 + 372718 * 2 ^ 59
def prefixEnd_372718 : Nat := 4983230072969 + 3 ^ 40 * 372718 * 2
def baseEnd_372718 : Nat := 191383482582577972810907

theorem tailTrace_372718 : CollatzResearch.WordTrace tailWord_372718 prefixEnd_372718 191383482582577972810907 := by
  unfold tailWord_372718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699267782964227001457851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9062761509142544007775205 1699267782964227001457851)
  ·
    refine ⟨2548901674446340502186777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1699267782964227001457851 2548901674446340502186777)
    ·
      refine ⟨1911676255834755376640083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2548901674446340502186777 1911676255834755376640083)
      ·
        refine ⟨2867514383752133064960125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1911676255834755376640083 2867514383752133064960125)
        ·
          refine ⟨1075317893907049899360047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2867514383752133064960125 1075317893907049899360047)
          ·
            refine ⟨1612976840860574849040071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075317893907049899360047 1612976840860574849040071)
            ·
              refine ⟨2419465261290862273560107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612976840860574849040071 2419465261290862273560107)
              ·
                refine ⟨3629197891936293410340161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419465261290862273560107 3629197891936293410340161)
                ·
                  refine ⟨2721898418952220057755121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629197891936293410340161 2721898418952220057755121)
                  ·
                    refine ⟨2041423814214165043316341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721898418952220057755121 2041423814214165043316341)
                    ·
                      refine ⟨191383482582577972810907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2041423814214165043316341 191383482582577972810907)
                      ·
                        rfl

theorem cell23_372718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_372718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372718 prefixEnd_372718 := by exact prefixLift 372718
  have htrace : WordTrace (prefixWord ++ tailWord_372718) baseStart_372718 baseEnd_372718 := by
    simpa [prefixWord, tailWord_372718, baseEnd_372718] using wordTrace_append hprefix tailTrace_372718
  have hstable : (prefixWord ++ tailWord_372718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372718).length < 2 ^ (prefixWord ++ tailWord_372718).sum := by decide
  have hdescent : baseEnd_372718 < baseStart_372718 := by decide
  rcases family_descends (prefixWord ++ tailWord_372718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372731 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_372731 : Nat := 118140960795 + 372731 * 2 ^ 59
def prefixEnd_372731 : Nat := 4983230072969 + 3 ^ 40 * 372731 * 2
def baseEnd_372731 : Nat := 191390157831086421948347

theorem tailTrace_372731 : CollatzResearch.WordTrace tailWord_372731 prefixEnd_372731 191390157831086421948347 := by
  unfold tailWord_372731
  simp only [CollatzResearch.WordTrace]
  refine ⟨13594616412666719231886047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9063077608444479487924031 13594616412666719231886047)
  ·
    refine ⟨20391924619000078847829071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13594616412666719231886047 20391924619000078847829071)
    ·
      refine ⟨30587886928500118271743607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20391924619000078847829071 30587886928500118271743607)
      ·
        refine ⟨45881830392750177407615411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30587886928500118271743607 45881830392750177407615411)
        ·
          refine ⟨68822745589125266111423117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45881830392750177407615411 68822745589125266111423117)
          ·
            refine ⟨25808529595921974791783669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68822745589125266111423117 25808529595921974791783669)
            ·
              refine ⟨2419549649617685136729719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25808529595921974791783669 2419549649617685136729719)
              ·
                refine ⟨3629324474426527705094579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419549649617685136729719 3629324474426527705094579)
                ·
                  refine ⟨5443986711639791557641869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629324474426527705094579 5443986711639791557641869)
                  ·
                    refine ⟨2041495016864921834115701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5443986711639791557641869 2041495016864921834115701)
                    ·
                      refine ⟨191390157831086421948347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2041495016864921834115701 191390157831086421948347)
                      ·
                        rfl

theorem cell23_372731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_372731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372731 prefixEnd_372731 := by exact prefixLift 372731
  have htrace : WordTrace (prefixWord ++ tailWord_372731) baseStart_372731 baseEnd_372731 := by
    simpa [prefixWord, tailWord_372731, baseEnd_372731] using wordTrace_append hprefix tailTrace_372731
  have hstable : (prefixWord ++ tailWord_372731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372731).length < 2 ^ (prefixWord ++ tailWord_372731).sum := by decide
  have hdescent : baseEnd_372731 < baseStart_372731 := by decide
  rcases family_descends (prefixWord ++ tailWord_372731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372748 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_372748 : Nat := 118140960795 + 372748 * 2 ^ 59
def prefixEnd_372748 : Nat := 4983230072969 + 3 ^ 40 * 372748 * 2
def baseEnd_372748 : Nat := 191398887002212855435769

theorem tailTrace_372748 : CollatzResearch.WordTrace tailWord_372748 prefixEnd_372748 191398887002212855435769 := by
  unfold tailWord_372748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797618226802565567627449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9063490969070087423503265 6797618226802565567627449)
  ·
    refine ⟨5098213670101924175720587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6797618226802565567627449 5098213670101924175720587)
    ·
      refine ⟨7647320505152886263580881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5098213670101924175720587 7647320505152886263580881)
      ·
        refine ⟨5735490378864664697685661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7647320505152886263580881 5735490378864664697685661)
        ·
          refine ⟨2150808892074249261632123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5735490378864664697685661 2150808892074249261632123)
          ·
            refine ⟨3226213338111373892448185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150808892074249261632123 3226213338111373892448185)
            ·
              refine ⟨2419660003583530419336139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226213338111373892448185 2419660003583530419336139)
              ·
                refine ⟨3629490005375295629004209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419660003583530419336139 3629490005375295629004209)
                ·
                  refine ⟨2722117504031471721753157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629490005375295629004209 2722117504031471721753157)
                  ·
                    refine ⟨510397032005900947828717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722117504031471721753157 510397032005900947828717)
                    ·
                      refine ⟨191398887002212855435769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510397032005900947828717 191398887002212855435769)
                      ·
                        rfl

theorem cell23_372748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_372748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372748 prefixEnd_372748 := by exact prefixLift 372748
  have htrace : WordTrace (prefixWord ++ tailWord_372748) baseStart_372748 baseEnd_372748 := by
    simpa [prefixWord, tailWord_372748, baseEnd_372748] using wordTrace_append hprefix tailTrace_372748
  have hstable : (prefixWord ++ tailWord_372748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372748).length < 2 ^ (prefixWord ++ tailWord_372748).sum := by decide
  have hdescent : baseEnd_372748 < baseStart_372748 := by decide
  rcases family_descends (prefixWord ++ tailWord_372748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372756 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_372756 : Nat := 118140960795 + 372756 * 2 ^ 59
def prefixEnd_372756 : Nat := 4983230072969 + 3 ^ 40 * 372756 * 2
def baseEnd_372756 : Nat := 191402994847448824135733

theorem tailTrace_372756 : CollatzResearch.WordTrace tailWord_372756 prefixEnd_372756 191402994847448824135733 := by
  unfold tailWord_372756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797764118788074250773061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9063685491717432334364081 6797764118788074250773061)
  ·
    refine ⟨1274580772272763922019949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6797764118788074250773061 1274580772272763922019949)
    ·
      refine ⟨477967789602286470757481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1274580772272763922019949 477967789602286470757481)
      ·
        refine ⟨358475842201714853068111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477967789602286470757481 358475842201714853068111)
        ·
          refine ⟨537713763302572279602167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358475842201714853068111 537713763302572279602167)
          ·
            refine ⟨806570644953858419403251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537713763302572279602167 806570644953858419403251)
            ·
              refine ⟨1209855967430787629104877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806570644953858419403251 1209855967430787629104877)
              ·
                refine ⟨453695987786545360914329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209855967430787629104877 453695987786545360914329)
                ·
                  refine ⟨340271990839909020685747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453695987786545360914329 340271990839909020685747)
                  ·
                    refine ⟨510407986259863531028621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340271990839909020685747 510407986259863531028621)
                    ·
                      refine ⟨191402994847448824135733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510407986259863531028621 191402994847448824135733)
                      ·
                        rfl

theorem cell23_372756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_372756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372756 prefixEnd_372756 := by exact prefixLift 372756
  have htrace : WordTrace (prefixWord ++ tailWord_372756) baseStart_372756 baseEnd_372756 := by
    simpa [prefixWord, tailWord_372756, baseEnd_372756] using wordTrace_append hprefix tailTrace_372756
  have hstable : (prefixWord ++ tailWord_372756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372756).length < 2 ^ (prefixWord ++ tailWord_372756).sum := by decide
  have hdescent : baseEnd_372756 < baseStart_372756 := by decide
  rcases family_descends (prefixWord ++ tailWord_372756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372835 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4]
def baseStart_372835 : Nat := 118140960795 + 372835 * 2 ^ 59
def prefixEnd_372835 : Nat := 4983230072969 + 3 ^ 40 * 372835 * 2
def baseEnd_372835 : Nat := 191443559819154015047869

theorem tailTrace_372835 : CollatzResearch.WordTrace tailWord_372835 prefixEnd_372835 191443559819154015047869 := by
  unfold tailWord_372835
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598409604289944993671959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9065606402859963329114639 13598409604289944993671959)
  ·
    refine ⟨20397614406434917490507939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13598409604289944993671959 20397614406434917490507939)
    ·
      refine ⟨30596421609652376235761909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20397614406434917490507939 30596421609652376235761909)
      ·
        refine ⟨2868414525904910272102679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30596421609652376235761909 2868414525904910272102679)
        ·
          refine ⟨4302621788857365408154019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868414525904910272102679 4302621788857365408154019)
          ·
            refine ⟨6453932683286048112231029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302621788857365408154019 6453932683286048112231029)
            ·
              refine ⟨605056189058067010521659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6453932683286048112231029 605056189058067010521659)
              ·
                refine ⟨907584283587100515782489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605056189058067010521659 907584283587100515782489)
                ·
                  refine ⟨680688212690325386836867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907584283587100515782489 680688212690325386836867)
                  ·
                    refine ⟨1021032319035488080255301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680688212690325386836867 1021032319035488080255301)
                    ·
                      refine ⟨191443559819154015047869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1021032319035488080255301 191443559819154015047869)
                      ·
                        rfl

theorem cell23_372835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_372835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372835 prefixEnd_372835 := by exact prefixLift 372835
  have htrace : WordTrace (prefixWord ++ tailWord_372835) baseStart_372835 baseEnd_372835 := by
    simpa [prefixWord, tailWord_372835, baseEnd_372835] using wordTrace_append hprefix tailTrace_372835
  have hstable : (prefixWord ++ tailWord_372835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372835).length < 2 ^ (prefixWord ++ tailWord_372835).sum := by decide
  have hdescent : baseEnd_372835 < baseStart_372835 := by decide
  rcases family_descends (prefixWord ++ tailWord_372835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372845 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_372845 : Nat := 118140960795 + 372845 * 2 ^ 59
def prefixEnd_372845 : Nat := 4983230072969 + 3 ^ 40 * 372845 * 2
def baseEnd_372845 : Nat := 63816231541899658640941

theorem tailTrace_372845 : CollatzResearch.WordTrace tailWord_372845 prefixEnd_372845 63816231541899658640941 := by
  unfold tailWord_372845
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598774334253716701535989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9065849556169144467690659 13598774334253716701535989)
  ·
    refine ⟨1274885093836285940768999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13598774334253716701535989 1274885093836285940768999)
    ·
      refine ⟨1912327640754428911153499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274885093836285940768999 1912327640754428911153499)
      ·
        refine ⟨2868491461131643366730249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912327640754428911153499 2868491461131643366730249)
        ·
          refine ⟨2151368595848732525047687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868491461131643366730249 2151368595848732525047687)
          ·
            refine ⟨3227052893773098787571531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151368595848732525047687 3227052893773098787571531)
            ·
              refine ⟨4840579340659648181357297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227052893773098787571531 4840579340659648181357297)
              ·
                refine ⟨3630434505494736136017973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4840579340659648181357297 3630434505494736136017973)
                ·
                  refine ⟨340353234890131512751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3630434505494736136017973 340353234890131512751685)
                  ·
                    refine ⟨63816231541899658640941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340353234890131512751685 63816231541899658640941)
                    ·
                      rfl

theorem cell23_372845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_372845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372845 prefixEnd_372845 := by exact prefixLift 372845
  have htrace : WordTrace (prefixWord ++ tailWord_372845) baseStart_372845 baseEnd_372845 := by
    simpa [prefixWord, tailWord_372845, baseEnd_372845] using wordTrace_append hprefix tailTrace_372845
  have hstable : (prefixWord ++ tailWord_372845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372845).length < 2 ^ (prefixWord ++ tailWord_372845).sum := by decide
  have hdescent : baseEnd_372845 < baseStart_372845 := by decide
  rcases family_descends (prefixWord ++ tailWord_372845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372848 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_372848 : Nat := 118140960795 + 372848 * 2 ^ 59
def prefixEnd_372848 : Nat := 4983230072969 + 3 ^ 40 * 372848 * 2
def baseEnd_372848 : Nat := 191450235067662464185309

theorem tailTrace_372848 : CollatzResearch.WordTrace tailWord_372848 prefixEnd_372848 191450235067662464185309 := by
  unfold tailWord_372848
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799441876621424106947599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9065922502161898809263465 6799441876621424106947599)
  ·
    refine ⟨10199162814932136160421399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6799441876621424106947599 10199162814932136160421399)
    ·
      refine ⟨15298744222398204240632099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199162814932136160421399 15298744222398204240632099)
      ·
        refine ⟨22948116333597306360948149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15298744222398204240632099 22948116333597306360948149)
        ·
          refine ⟨2151385906274747471338889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22948116333597306360948149 2151385906274747471338889)
          ·
            refine ⟨1613539429706060603504167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151385906274747471338889 1613539429706060603504167)
            ·
              refine ⟨2420309144559090905256251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613539429706060603504167 2420309144559090905256251)
              ·
                refine ⟨3630463716838636357884377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420309144559090905256251 3630463716838636357884377)
                ·
                  refine ⟨2722847787628977268413283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630463716838636357884377 2722847787628977268413283)
                  ·
                    refine ⟨4084271681443465902619925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2722847787628977268413283 4084271681443465902619925)
                    ·
                      refine ⟨191450235067662464185309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4084271681443465902619925 191450235067662464185309)
                      ·
                        rfl

theorem cell23_372848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_372848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372848 prefixEnd_372848 := by exact prefixLift 372848
  have htrace : WordTrace (prefixWord ++ tailWord_372848) baseStart_372848 baseEnd_372848 := by
    simpa [prefixWord, tailWord_372848, baseEnd_372848] using wordTrace_append hprefix tailTrace_372848
  have hstable : (prefixWord ++ tailWord_372848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372848).length < 2 ^ (prefixWord ++ tailWord_372848).sum := by decide
  have hdescent : baseEnd_372848 < baseStart_372848 := by decide
  rcases family_descends (prefixWord ++ tailWord_372848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372908 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_372908 : Nat := 118140960795 + 372908 * 2 ^ 59
def prefixEnd_372908 : Nat := 4983230072969 + 3 ^ 40 * 372908 * 2
def baseEnd_372908 : Nat := 191481043906932229435033

theorem tailTrace_372908 : CollatzResearch.WordTrace tailWord_372908 prefixEnd_372908 191481043906932229435033 := by
  unfold tailWord_372908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800536066512739230539689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9067381422016985640719585 6800536066512739230539689)
  ·
    refine ⟨5100402049884554422904767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800536066512739230539689 5100402049884554422904767)
    ·
      refine ⟨7650603074826831634357151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100402049884554422904767 7650603074826831634357151)
      ·
        refine ⟨11475904612240247451535727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650603074826831634357151 11475904612240247451535727)
        ·
          refine ⟨17213856918360371177303591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475904612240247451535727 17213856918360371177303591)
          ·
            refine ⟨25820785377540556765955387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17213856918360371177303591 25820785377540556765955387)
            ·
              refine ⟨38731178066310835148933081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25820785377540556765955387 38731178066310835148933081)
              ·
                refine ⟨29048383549733126361699811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38731178066310835148933081 29048383549733126361699811)
                ·
                  refine ⟨43572575324599689542549717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29048383549733126361699811 43572575324599689542549717)
                  ·
                    refine ⟨1021232234170305223653509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43572575324599689542549717 1021232234170305223653509)
                    ·
                      refine ⟨191481043906932229435033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1021232234170305223653509 191481043906932229435033)
                      ·
                        rfl

theorem cell23_372908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_372908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372908 prefixEnd_372908 := by exact prefixLift 372908
  have htrace : WordTrace (prefixWord ++ tailWord_372908) baseStart_372908 baseEnd_372908 := by
    simpa [prefixWord, tailWord_372908, baseEnd_372908] using wordTrace_append hprefix tailTrace_372908
  have hstable : (prefixWord ++ tailWord_372908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372908).length < 2 ^ (prefixWord ++ tailWord_372908).sum := by decide
  have hdescent : baseEnd_372908 < baseStart_372908 := by decide
  rcases family_descends (prefixWord ++ tailWord_372908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372919 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_372919 : Nat := 118140960795 + 372919 * 2 ^ 59
def prefixEnd_372919 : Nat := 4983230072969 + 3 ^ 40 * 372919 * 2
def baseEnd_372919 : Nat := 191486692194131686397483

theorem tailTrace_372919 : CollatzResearch.WordTrace tailWord_372919 prefixEnd_372919 191486692194131686397483 := by
  unfold tailWord_372919
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601473335985627339729811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9067648890657084893153207 13601473335985627339729811)
  ·
    refine ⟨20402210003978441009594717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13601473335985627339729811 20402210003978441009594717)
    ·
      refine ⟨7650828751491915378598019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20402210003978441009594717 7650828751491915378598019)
      ·
        refine ⟨11476243127237873067897029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650828751491915378598019 11476243127237873067897029)
        ·
          refine ⟨2151795586357101200230693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11476243127237873067897029 2151795586357101200230693)
          ·
            refine ⟨403461672441956475043255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2151795586357101200230693 403461672441956475043255)
            ·
              refine ⟨605192508662934712564883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403461672441956475043255 605192508662934712564883)
              ·
                refine ⟨907788762994402068847325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605192508662934712564883 907788762994402068847325)
                ·
                  refine ⟨340420786122900775817747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907788762994402068847325 340420786122900775817747)
                  ·
                    refine ⟨510631179184351163726621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340420786122900775817747 510631179184351163726621)
                    ·
                      refine ⟨191486692194131686397483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510631179184351163726621 191486692194131686397483)
                      ·
                        rfl

theorem cell23_372919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_372919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372919 prefixEnd_372919 := by exact prefixLift 372919
  have htrace : WordTrace (prefixWord ++ tailWord_372919) baseStart_372919 baseEnd_372919 := by
    simpa [prefixWord, tailWord_372919, baseEnd_372919] using wordTrace_append hprefix tailTrace_372919
  have hstable : (prefixWord ++ tailWord_372919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372919).length < 2 ^ (prefixWord ++ tailWord_372919).sum := by decide
  have hdescent : baseEnd_372919 < baseStart_372919 := by decide
  rcases family_descends (prefixWord ++ tailWord_372919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372925 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_372925 : Nat := 118140960795 + 372925 * 2 ^ 59
def prefixEnd_372925 : Nat := 4983230072969 + 3 ^ 40 * 372925 * 2
def baseEnd_372925 : Nat := 191489773078058662922455

theorem tailTrace_372925 : CollatzResearch.WordTrace tailWord_372925 prefixEnd_372925 191489773078058662922455 := by
  unfold tailWord_372925
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601692173963890364448229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9067794782642593576298819 13601692173963890364448229)
  ·
    refine ⟨2550317282618229443334043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13601692173963890364448229 2550317282618229443334043)
    ·
      refine ⟨3825475923927344165001065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550317282618229443334043 3825475923927344165001065)
      ·
        refine ⟨2869106942945508123750799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3825475923927344165001065 2869106942945508123750799)
        ·
          refine ⟨4303660414418262185626199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869106942945508123750799 4303660414418262185626199)
          ·
            refine ⟨6455490621627393278439299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303660414418262185626199 6455490621627393278439299)
            ·
              refine ⟨9683235932441089917658949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455490621627393278439299 9683235932441089917658949)
              ·
                refine ⟨1815606737332704359561053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9683235932441089917658949 1815606737332704359561053)
                ·
                  refine ⟨680852526499764134835395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1815606737332704359561053 680852526499764134835395)
                  ·
                    refine ⟨1021278789749646202253093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680852526499764134835395 1021278789749646202253093)
                    ·
                      refine ⟨191489773078058662922455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1021278789749646202253093 191489773078058662922455)
                      ·
                        rfl

theorem cell23_372925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_372925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372925 prefixEnd_372925 := by exact prefixLift 372925
  have htrace : WordTrace (prefixWord ++ tailWord_372925) baseStart_372925 baseEnd_372925 := by
    simpa [prefixWord, tailWord_372925, baseEnd_372925] using wordTrace_append hprefix tailTrace_372925
  have hstable : (prefixWord ++ tailWord_372925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372925).length < 2 ^ (prefixWord ++ tailWord_372925).sum := by decide
  have hdescent : baseEnd_372925 < baseStart_372925 := by decide
  rcases family_descends (prefixWord ++ tailWord_372925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372926 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_372926 : Nat := 118140960795 + 372926 * 2 ^ 59
def prefixEnd_372926 : Nat := 4983230072969 + 3 ^ 40 * 372926 * 2
def baseEnd_372926 : Nat := 21276698506523684334439

theorem tailTrace_372926 : CollatzResearch.WordTrace tailWord_372926 prefixEnd_372926 21276698506523684334439 := by
  unfold tailWord_372926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700216080870033441904329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9067819097973511690156421 1700216080870033441904329)
  ·
    refine ⟨1275162060652525081428247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1700216080870033441904329 1275162060652525081428247)
    ·
      refine ⟨1912743090978787622142371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275162060652525081428247 1912743090978787622142371)
      ·
        refine ⟨2869114636468181433213557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912743090978787622142371 2869114636468181433213557)
        ·
          refine ⟨268979497168892009363771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2869114636468181433213557 268979497168892009363771)
          ·
            refine ⟨403469245753338014045657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268979497168892009363771 403469245753338014045657)
            ·
              refine ⟨302601934315003510534243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403469245753338014045657 302601934315003510534243)
              ·
                refine ⟨453902901472505265801365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302601934315003510534243 453902901472505265801365)
                ·
                  refine ⟨21276698506523684334439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 453902901472505265801365 21276698506523684334439)
                  ·
                    rfl

theorem cell23_372926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_372926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372926 prefixEnd_372926 := by exact prefixLift 372926
  have htrace : WordTrace (prefixWord ++ tailWord_372926) baseStart_372926 baseEnd_372926 := by
    simpa [prefixWord, tailWord_372926, baseEnd_372926] using wordTrace_append hprefix tailTrace_372926
  have hstable : (prefixWord ++ tailWord_372926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372926).length < 2 ^ (prefixWord ++ tailWord_372926).sum := by decide
  have hdescent : baseEnd_372926 < baseStart_372926 := by decide
  rcases family_descends (prefixWord ++ tailWord_372926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372942 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_372942 : Nat := 118140960795 + 372942 * 2 ^ 59
def prefixEnd_372942 : Nat := 4983230072969 + 3 ^ 40 * 372942 * 2
def baseEnd_372942 : Nat := 191498502249185096409877

theorem tailTrace_372942 : CollatzResearch.WordTrace tailWord_372942 prefixEnd_372942 191498502249185096409877 := by
  unfold tailWord_372942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700289026862787783477135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9068208143268201511878053 1700289026862787783477135)
  ·
    refine ⟨2550433540294181675215703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1700289026862787783477135 2550433540294181675215703)
    ·
      refine ⟨3825650310441272512823555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550433540294181675215703 3825650310441272512823555)
      ·
        refine ⟨5738475465661908769235333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825650310441272512823555 5738475465661908769235333)
        ·
          refine ⟨1075964149811607894231625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5738475465661908769235333 1075964149811607894231625)
          ·
            refine ⟨806973112358705920673719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075964149811607894231625 806973112358705920673719)
            ·
              refine ⟨1210459668538058881010579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806973112358705920673719 1210459668538058881010579)
              ·
                refine ⟨1815689502807088321515869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210459668538058881010579 1815689502807088321515869)
                ·
                  refine ⟨680883563552658120568451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1815689502807088321515869 680883563552658120568451)
                  ·
                    refine ⟨1021325345328987180852677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680883563552658120568451 1021325345328987180852677)
                    ·
                      refine ⟨191498502249185096409877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1021325345328987180852677 191498502249185096409877)
                      ·
                        rfl

theorem cell23_372942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_372942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372942 prefixEnd_372942 := by exact prefixLift 372942
  have htrace : WordTrace (prefixWord ++ tailWord_372942) baseStart_372942 baseEnd_372942 := by
    simpa [prefixWord, tailWord_372942, baseEnd_372942] using wordTrace_append hprefix tailTrace_372942
  have hstable : (prefixWord ++ tailWord_372942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372942).length < 2 ^ (prefixWord ++ tailWord_372942).sum := by decide
  have hdescent : baseEnd_372942 < baseStart_372942 := by decide
  rcases family_descends (prefixWord ++ tailWord_372942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372999 : List Nat := [1, 1, 4, 5, 1, 1, 3, 7]
def baseStart_372999 : Nat := 118140960795 + 372999 * 2 ^ 59
def prefixEnd_372999 : Nat := 4983230072969 + 3 ^ 40 * 372999 * 2
def baseEnd_372999 : Nat := 7093621135055236051745

theorem tailTrace_372999 : CollatzResearch.WordTrace tailWord_372999 prefixEnd_372999 7093621135055236051745 := by
  unfold tailWord_372999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604391175695801002642051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069594117130534001761367 13604391175695801002642051)
  ·
    refine ⟨20406586763543701503963077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13604391175695801002642051 20406586763543701503963077)
    ·
      refine ⟨3826235018164444031993077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20406586763543701503963077 3826235018164444031993077)
      ·
        refine ⟨358709532952916627999351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3826235018164444031993077 358709532952916627999351)
        ·
          refine ⟨538064299429374941999027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358709532952916627999351 538064299429374941999027)
          ·
            refine ⟨807096449144062412998541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538064299429374941999027 807096449144062412998541)
            ·
              refine ⟨302661168429023404874453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807096449144062412998541 302661168429023404874453)
              ·
                refine ⟨7093621135055236051745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 302661168429023404874453 7093621135055236051745)
                ·
                  rfl

theorem cell23_372999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 7].length) (baseStart_372999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372999 prefixEnd_372999 := by exact prefixLift 372999
  have htrace : WordTrace (prefixWord ++ tailWord_372999) baseStart_372999 baseEnd_372999 := by
    simpa [prefixWord, tailWord_372999, baseEnd_372999] using wordTrace_append hprefix tailTrace_372999
  have hstable : (prefixWord ++ tailWord_372999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372999).length < 2 ^ (prefixWord ++ tailWord_372999).sum := by decide
  have hdescent : baseEnd_372999 < baseStart_372999 := by decide
  rcases family_descends (prefixWord ++ tailWord_372999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373025 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_373025 : Nat := 118140960795 + 373025 * 2 ^ 59
def prefixEnd_373025 : Nat := 4983230072969 + 3 ^ 40 * 373025 * 2
def baseEnd_373025 : Nat := 63847040381169423890665

theorem tailTrace_373025 : CollatzResearch.WordTrace tailWord_373025 prefixEnd_373025 63847040381169423890665 := by
  unfold tailWord_373025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605339473601607443088529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9070226315734404962059019 13605339473601607443088529)
  ·
    refine ⟨10204004605201205582316397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13605339473601607443088529 10204004605201205582316397)
    ·
      refine ⟨3826501726950452093368649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10204004605201205582316397 3826501726950452093368649)
      ·
        refine ⟨2869876295212839070026487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3826501726950452093368649 2869876295212839070026487)
        ·
          refine ⟨4304814442819258605039731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869876295212839070026487 4304814442819258605039731)
          ·
            refine ⟨6457221664228887907559597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304814442819258605039731 6457221664228887907559597)
            ·
              refine ⟨2421458124085832965334849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6457221664228887907559597 2421458124085832965334849)
              ·
                refine ⟨1816093593064374724001137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421458124085832965334849 1816093593064374724001137)
                ·
                  refine ⟨1362070194798281043000853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816093593064374724001137 1362070194798281043000853)
                  ·
                    refine ⟨63847040381169423890665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1362070194798281043000853 63847040381169423890665)
                    ·
                      rfl

theorem cell23_373025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_373025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373025 prefixEnd_373025 := by exact prefixLift 373025
  have htrace : WordTrace (prefixWord ++ tailWord_373025) baseStart_373025 baseEnd_373025 := by
    simpa [prefixWord, tailWord_373025, baseEnd_373025] using wordTrace_append hprefix tailTrace_373025
  have hstable : (prefixWord ++ tailWord_373025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373025).length < 2 ^ (prefixWord ++ tailWord_373025).sum := by decide
  have hdescent : baseEnd_373025 < baseStart_373025 := by decide
  rcases family_descends (prefixWord ++ tailWord_373025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373026 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_373026 : Nat := 118140960795 + 373026 * 2 ^ 59
def prefixEnd_373026 : Nat := 4983230072969 + 3 ^ 40 * 373026 * 2
def baseEnd_373026 : Nat := 191541634624162767759491

theorem tailTrace_373026 : CollatzResearch.WordTrace tailWord_373026 prefixEnd_373026 191541634624162767759491 := by
  unfold tailWord_373026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401343986649496153468733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9070250631065323075916621 3401343986649496153468733)
  ·
    refine ⟨1275503994993561057550775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3401343986649496153468733 1275503994993561057550775)
    ·
      refine ⟨1913255992490341586326163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275503994993561057550775 1913255992490341586326163)
      ·
        refine ⟨2869883988735512379489245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913255992490341586326163 2869883988735512379489245)
        ·
          refine ⟨1076206495775817142308467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2869883988735512379489245 1076206495775817142308467)
          ·
            refine ⟨1614309743663725713462701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076206495775817142308467 1614309743663725713462701)
            ·
              refine ⟨605366153873897142548513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614309743663725713462701 605366153873897142548513)
              ·
                refine ⟨454024615405422856911385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605366153873897142548513 454024615405422856911385)
                ·
                  refine ⟨340518461554067142683539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454024615405422856911385 340518461554067142683539)
                  ·
                    refine ⟨510777692331100714025309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340518461554067142683539 510777692331100714025309)
                    ·
                      refine ⟨191541634624162767759491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 510777692331100714025309 191541634624162767759491)
                      ·
                        rfl

theorem cell23_373026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_373026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373026 prefixEnd_373026 := by exact prefixLift 373026
  have htrace : WordTrace (prefixWord ++ tailWord_373026) baseStart_373026 baseEnd_373026 := by
    simpa [prefixWord, tailWord_373026, baseEnd_373026] using wordTrace_append hprefix tailTrace_373026
  have hstable : (prefixWord ++ tailWord_373026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373026).length < 2 ^ (prefixWord ++ tailWord_373026).sum := by decide
  have hdescent : baseEnd_373026 < baseStart_373026 := by decide
  rcases family_descends (prefixWord ++ tailWord_373026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373055 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 7]
def baseStart_373055 : Nat := 118140960795 + 373055 * 2 ^ 59
def prefixEnd_373055 : Nat := 4983230072969 + 3 ^ 40 * 373055 * 2
def baseEnd_373055 : Nat := 21284058395904794921873

theorem tailTrace_373055 : CollatzResearch.WordTrace tailWord_373055 prefixEnd_373055 21284058395904794921873 := by
  unfold tailWord_373055
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606433663492922566680619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9070955775661948377787079 13606433663492922566680619)
  ·
    refine ⟨20409650495239383850020929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13606433663492922566680619 20409650495239383850020929)
    ·
      refine ⟨15307237871429537887515697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20409650495239383850020929 15307237871429537887515697)
      ·
        refine ⟨11480428403572153415636773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15307237871429537887515697 11480428403572153415636773)
        ·
          refine ⟨2152580325669778765431895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11480428403572153415636773 2152580325669778765431895)
          ·
            refine ⟨3228870488504668148147843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152580325669778765431895 3228870488504668148147843)
            ·
              refine ⟨4843305732757002222221765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228870488504668148147843 4843305732757002222221765)
              ·
                refine ⟨908119824891937916666581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4843305732757002222221765 908119824891937916666581)
                ·
                  refine ⟨21284058395904794921873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 908119824891937916666581 21284058395904794921873)
                  ·
                    rfl

theorem cell23_373055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 7].length) (baseStart_373055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373055 prefixEnd_373055 := by exact prefixLift 373055
  have htrace : WordTrace (prefixWord ++ tailWord_373055) baseStart_373055 baseEnd_373055 := by
    simpa [prefixWord, tailWord_373055, baseEnd_373055] using wordTrace_append hprefix tailTrace_373055
  have hstable : (prefixWord ++ tailWord_373055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373055).length < 2 ^ (prefixWord ++ tailWord_373055).sum := by decide
  have hdescent : baseEnd_373055 < baseStart_373055 := by decide
  rcases family_descends (prefixWord ++ tailWord_373055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373100 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_373100 : Nat := 118140960795 + 373100 * 2 ^ 59
def prefixEnd_373100 : Nat := 4983230072969 + 3 ^ 40 * 373100 * 2
def baseEnd_373100 : Nat := 191579632192595478234151

theorem tailTrace_373100 : CollatzResearch.WordTrace tailWord_373100 prefixEnd_373100 191579632192595478234151 := by
  unfold tailWord_373100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804037474164947626034377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9072049965553263501379169 6804037474164947626034377)
  ·
    refine ⟨5103028105623710719525783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6804037474164947626034377 5103028105623710719525783)
    ·
      refine ⟨7654542158435566079288675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103028105623710719525783 7654542158435566079288675)
      ·
        refine ⟨11481813237653349118933013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7654542158435566079288675 11481813237653349118933013)
        ·
          refine ⟨538209995515000739949985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11481813237653349118933013 538209995515000739949985)
          ·
            refine ⟨403657496636250554962489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538209995515000739949985 403657496636250554962489)
            ·
              refine ⟨302743122477187916221867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403657496636250554962489 302743122477187916221867)
              ·
                refine ⟨454114683715781874332801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302743122477187916221867 454114683715781874332801)
                ·
                  refine ⟨340586012786836405749601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454114683715781874332801 340586012786836405749601)
                  ·
                    refine ⟨255439509590127304312201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 340586012786836405749601 255439509590127304312201)
                    ·
                      refine ⟨191579632192595478234151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255439509590127304312201 191579632192595478234151)
                      ·
                        rfl

theorem cell23_373100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_373100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373100 prefixEnd_373100 := by exact prefixLift 373100
  have htrace : WordTrace (prefixWord ++ tailWord_373100) baseStart_373100 baseEnd_373100 := by
    simpa [prefixWord, tailWord_373100, baseEnd_373100] using wordTrace_append hprefix tailTrace_373100
  have hstable : (prefixWord ++ tailWord_373100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373100).length < 2 ^ (prefixWord ++ tailWord_373100).sum := by decide
  have hdescent : baseEnd_373100 < baseStart_373100 := by decide
  rcases family_descends (prefixWord ++ tailWord_373100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373140 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 5]
def baseStart_373140 : Nat := 118140960795 + 373140 * 2 ^ 59
def prefixEnd_373140 : Nat := 4983230072969 + 3 ^ 40 * 373140 * 2
def baseEnd_373140 : Nat := 21288907935419480192663

theorem tailTrace_373140 : CollatzResearch.WordTrace tailWord_373140 prefixEnd_373140 21288907935419480192663 := by
  unfold tailWord_373140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804766934092491041762437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9073022578789988055683249 6804766934092491041762437)
  ·
    refine ⟨1275893800142342070330457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6804766934092491041762437 1275893800142342070330457)
    ·
      refine ⟨956920350106756552747843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1275893800142342070330457 956920350106756552747843)
      ·
        refine ⟨1435380525160134829121765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956920350106756552747843 1435380525160134829121765)
        ·
          refine ⟨269133848467525280460331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1435380525160134829121765 269133848467525280460331)
          ·
            refine ⟨403700772701287920690497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269133848467525280460331 403700772701287920690497)
            ·
              refine ⟨302775579525965940517873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403700772701287920690497 302775579525965940517873)
              ·
                refine ⟨227081684644474455388405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302775579525965940517873 227081684644474455388405)
                ·
                  refine ⟨21288907935419480192663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227081684644474455388405 21288907935419480192663)
                  ·
                    rfl

theorem cell23_373140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_373140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373140 prefixEnd_373140 := by exact prefixLift 373140
  have htrace : WordTrace (prefixWord ++ tailWord_373140) baseStart_373140 baseEnd_373140 := by
    simpa [prefixWord, tailWord_373140, baseEnd_373140] using wordTrace_append hprefix tailTrace_373140
  have hstable : (prefixWord ++ tailWord_373140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373140).length < 2 ^ (prefixWord ++ tailWord_373140).sum := by decide
  have hdescent : baseEnd_373140 < baseStart_373140 := by decide
  rcases family_descends (prefixWord ++ tailWord_373140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373173 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_373173 : Nat := 118140960795 + 373173 * 2 ^ 59
def prefixEnd_373173 : Nat := 4983230072969 + 3 ^ 40 * 373173 * 2
def baseEnd_373173 : Nat := 191617116280373692621315

theorem tailTrace_373173 : CollatzResearch.WordTrace tailWord_373173 prefixEnd_373173 191617116280373692621315 := by
  unfold tailWord_373173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610737477065428719476173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9073824984710285812984115 13610737477065428719476173)
  ·
    refine ⟨5104026553899535769803565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13610737477065428719476173 5104026553899535769803565)
    ·
      refine ⟨1914009957712325913676337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5104026553899535769803565 1914009957712325913676337)
      ·
        refine ⟨1435507468284244435257253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1914009957712325913676337 1435507468284244435257253)
        ·
          refine ⟨269157650303295831610735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1435507468284244435257253 269157650303295831610735)
          ·
            refine ⟨403736475454943747416103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269157650303295831610735 403736475454943747416103)
            ·
              refine ⟨605604713182415621124155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403736475454943747416103 605604713182415621124155)
              ·
                refine ⟨908407069773623431686233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605604713182415621124155 908407069773623431686233)
                ·
                  refine ⟨681305302330217573764675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908407069773623431686233 681305302330217573764675)
                  ·
                    refine ⟨1021957953495326360647013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681305302330217573764675 1021957953495326360647013)
                    ·
                      refine ⟨191617116280373692621315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1021957953495326360647013 191617116280373692621315)
                      ·
                        rfl

theorem cell23_373173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_373173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373173 prefixEnd_373173 := by exact prefixLift 373173
  have htrace : WordTrace (prefixWord ++ tailWord_373173) baseStart_373173 baseEnd_373173 := by
    simpa [prefixWord, tailWord_373173, baseEnd_373173] using wordTrace_append hprefix tailTrace_373173
  have hstable : (prefixWord ++ tailWord_373173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373173).length < 2 ^ (prefixWord ++ tailWord_373173).sum := by decide
  have hdescent : baseEnd_373173 < baseStart_373173 := by decide
  rcases family_descends (prefixWord ++ tailWord_373173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373196 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 6]
def baseStart_373196 : Nat := 118140960795 + 373196 * 2 ^ 59
def prefixEnd_373196 : Nat := 4983230072969 + 3 ^ 40 * 373196 * 2
def baseEnd_373196 : Nat := 21292102926158566959301

theorem tailTrace_373196 : CollatzResearch.WordTrace tailWord_373196 prefixEnd_373196 21292102926158566959301 := by
  unfold tailWord_373196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805788177991051823781721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9074384237321402431708961 6805788177991051823781721)
  ·
    refine ⟨5104341133493288867836291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6805788177991051823781721 5104341133493288867836291)
    ·
      refine ⟨7656511700239933301754437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5104341133493288867836291 7656511700239933301754437)
      ·
        refine ⟨1435595943794987494078957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7656511700239933301754437 1435595943794987494078957)
        ·
          refine ⟨538348478923120310279609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1435595943794987494078957 538348478923120310279609)
          ·
            refine ⟨403761359192340232709707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538348478923120310279609 403761359192340232709707)
            ·
              refine ⟨605642038788510349064561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403761359192340232709707 605642038788510349064561)
              ·
                refine ⟨454231529091382761798421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605642038788510349064561 454231529091382761798421)
                ·
                  refine ⟨21292102926158566959301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 454231529091382761798421 21292102926158566959301)
                  ·
                    rfl

theorem cell23_373196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_373196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373196 prefixEnd_373196 := by exact prefixLift 373196
  have htrace : WordTrace (prefixWord ++ tailWord_373196) baseStart_373196 baseEnd_373196 := by
    simpa [prefixWord, tailWord_373196, baseEnd_373196] using wordTrace_append hprefix tailTrace_373196
  have hstable : (prefixWord ++ tailWord_373196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373196).length < 2 ^ (prefixWord ++ tailWord_373196).sum := by decide
  have hdescent : baseEnd_373196 < baseStart_373196 := by decide
  rcases family_descends (prefixWord ++ tailWord_373196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373199 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 4, 3, 2]
def baseStart_373199 : Nat := 118140960795 + 373199 * 2 ^ 59
def prefixEnd_373199 : Nat := 4983230072969 + 3 ^ 40 * 373199 * 2
def baseEnd_373199 : Nat := 191630466777390590896195

theorem tailTrace_373199 : CollatzResearch.WordTrace tailWord_373199 prefixEnd_373199 191630466777390590896195 := by
  unfold tailWord_373199
  simp only [CollatzResearch.WordTrace]
  refine ⟨13611685774971235159922651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9074457183314156773281767 13611685774971235159922651)
  ·
    refine ⟨20417528662456852739883977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13611685774971235159922651 20417528662456852739883977)
    ·
      refine ⟨15313146496842639554912983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20417528662456852739883977 15313146496842639554912983)
      ·
        refine ⟨22969719745263959332369475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15313146496842639554912983 22969719745263959332369475)
        ·
          refine ⟨34454579617895938998554213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22969719745263959332369475 34454579617895938998554213)
          ·
            refine ⟨6460233678355488562228915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34454579617895938998554213 6460233678355488562228915)
            ·
              refine ⟨9690350517533232843343373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460233678355488562228915 9690350517533232843343373)
              ·
                refine ⟨3633881444074962316253765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9690350517533232843343373 3633881444074962316253765)
                ·
                  refine ⟨681352770764055434297581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3633881444074962316253765 681352770764055434297581)
                  ·
                    refine ⟨255507289036520787861593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681352770764055434297581 255507289036520787861593)
                    ·
                      refine ⟨191630466777390590896195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255507289036520787861593 191630466777390590896195)
                      ·
                        rfl

theorem cell23_373199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3, 2].length) (baseStart_373199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373199 prefixEnd_373199 := by exact prefixLift 373199
  have htrace : WordTrace (prefixWord ++ tailWord_373199) baseStart_373199 baseEnd_373199 := by
    simpa [prefixWord, tailWord_373199, baseEnd_373199] using wordTrace_append hprefix tailTrace_373199
  have hstable : (prefixWord ++ tailWord_373199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373199).length < 2 ^ (prefixWord ++ tailWord_373199).sum := by decide
  have hdescent : baseEnd_373199 < baseStart_373199 := by decide
  rcases family_descends (prefixWord ++ tailWord_373199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373226 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_373226 : Nat := 118140960795 + 373226 * 2 ^ 59
def prefixEnd_373226 : Nat := 4983230072969 + 3 ^ 40 * 373226 * 2
def baseEnd_373226 : Nat := 63881443585020661752857

theorem tailTrace_373226 : CollatzResearch.WordTrace tailWord_373226 prefixEnd_373226 63881443585020661752857 := by
  unfold tailWord_373226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403167636468354692788883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9075113697248945847437021 3403167636468354692788883)
  ·
    refine ⟨5104751454702532039183325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3403167636468354692788883 5104751454702532039183325)
    ·
      refine ⟨1914281795513449514693747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5104751454702532039183325 1914281795513449514693747)
      ·
        refine ⟨2871422693270174272040621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914281795513449514693747 2871422693270174272040621)
        ·
          refine ⟨1076783509976315352015233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2871422693270174272040621 1076783509976315352015233)
          ·
            refine ⟨807587632482236514011425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076783509976315352015233 807587632482236514011425)
            ·
              refine ⟨605690724361677385508569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807587632482236514011425 605690724361677385508569)
              ·
                refine ⟨454268043271258039131427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605690724361677385508569 454268043271258039131427)
                ·
                  refine ⟨681402064906887058697141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454268043271258039131427 681402064906887058697141)
                  ·
                    refine ⟨63881443585020661752857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 681402064906887058697141 63881443585020661752857)
                    ·
                      rfl

theorem cell23_373226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_373226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373226 prefixEnd_373226 := by exact prefixLift 373226
  have htrace : WordTrace (prefixWord ++ tailWord_373226) baseStart_373226 baseEnd_373226 := by
    simpa [prefixWord, tailWord_373226, baseEnd_373226] using wordTrace_append hprefix tailTrace_373226
  have hstable : (prefixWord ++ tailWord_373226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373226).length < 2 ^ (prefixWord ++ tailWord_373226).sum := by decide
  have hdescent : baseEnd_373226 < baseStart_373226 := by decide
  rcases family_descends (prefixWord ++ tailWord_373226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373232 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_373232 : Nat := 118140960795 + 373232 * 2 ^ 59
def prefixEnd_373232 : Nat := 4983230072969 + 3 ^ 40 * 373232 * 2
def baseEnd_373232 : Nat := 191647411638988961783543

theorem tailTrace_373232 : CollatzResearch.WordTrace tailWord_373232 prefixEnd_373232 191647411638988961783543 := by
  unfold tailWord_373232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806444691925840897936975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9075259589234454530582633 6806444691925840897936975)
  ·
    refine ⟨10209667037888761346905463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806444691925840897936975 10209667037888761346905463)
    ·
      refine ⟨15314500556833142020358195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209667037888761346905463 15314500556833142020358195)
      ·
        refine ⟨22971750835249713030537293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15314500556833142020358195 22971750835249713030537293)
        ·
          refine ⟨8614406563218642386451485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22971750835249713030537293 8614406563218642386451485)
          ·
            refine ⟨3230402461206990894919307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8614406563218642386451485 3230402461206990894919307)
            ·
              refine ⟨4845603691810486342378961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230402461206990894919307 4845603691810486342378961)
              ·
                refine ⟨3634202768857864756784221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4845603691810486342378961 3634202768857864756784221)
                ·
                  refine ⟨1362826038321699283794083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3634202768857864756784221 1362826038321699283794083)
                  ·
                    refine ⟨2044239057482548925691125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362826038321699283794083 2044239057482548925691125)
                    ·
                      refine ⟨191647411638988961783543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2044239057482548925691125 191647411638988961783543)
                      ·
                        rfl

theorem cell23_373232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_373232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373232 prefixEnd_373232 := by exact prefixLift 373232
  have htrace : WordTrace (prefixWord ++ tailWord_373232) baseStart_373232 baseEnd_373232 := by
    simpa [prefixWord, tailWord_373232, baseEnd_373232] using wordTrace_append hprefix tailTrace_373232
  have hstable : (prefixWord ++ tailWord_373232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373232).length < 2 ^ (prefixWord ++ tailWord_373232).sum := by decide
  have hdescent : baseEnd_373232 < baseStart_373232 := by decide
  rcases family_descends (prefixWord ++ tailWord_373232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373249 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_373249 : Nat := 118140960795 + 373249 * 2 ^ 59
def prefixEnd_373249 : Nat := 4983230072969 + 3 ^ 40 * 373249 * 2
def baseEnd_373249 : Nat := 191656140810115395270965

theorem tailTrace_373249 : CollatzResearch.WordTrace tailWord_373249 prefixEnd_373249 191656140810115395270965 := by
  unfold tailWord_373249
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613509424790093699242801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9075672949860062466161867 13613509424790093699242801)
  ·
    refine ⟨10210132068592570274432101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13613509424790093699242801 10210132068592570274432101)
    ·
      refine ⟨1914399762861106926456019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10210132068592570274432101 1914399762861106926456019)
      ·
        refine ⟨2871599644291660389684029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914399762861106926456019 2871599644291660389684029)
        ·
          refine ⟨1076849866609372646131511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2871599644291660389684029 1076849866609372646131511)
          ·
            refine ⟨1615274799914058969197267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076849866609372646131511 1615274799914058969197267)
            ·
              refine ⟨2422912199871088453795901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615274799914058969197267 2422912199871088453795901)
              ·
                refine ⟨908592074951658170173463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2422912199871088453795901 908592074951658170173463)
                ·
                  refine ⟨1362888112427487255260195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908592074951658170173463 1362888112427487255260195)
                  ·
                    refine ⟨2044332168641230882890293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362888112427487255260195 2044332168641230882890293)
                    ·
                      refine ⟨191656140810115395270965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2044332168641230882890293 191656140810115395270965)
                      ·
                        rfl

theorem cell23_373249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_373249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373249 prefixEnd_373249 := by exact prefixLift 373249
  have htrace : WordTrace (prefixWord ++ tailWord_373249) baseStart_373249 baseEnd_373249 := by
    simpa [prefixWord, tailWord_373249, baseEnd_373249] using wordTrace_append hprefix tailTrace_373249
  have hstable : (prefixWord ++ tailWord_373249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373249).length < 2 ^ (prefixWord ++ tailWord_373249).sum := by decide
  have hdescent : baseEnd_373249 < baseStart_373249 := by decide
  rcases family_descends (prefixWord ++ tailWord_373249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373250 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_373250 : Nat := 118140960795 + 373250 * 2 ^ 59
def prefixEnd_373250 : Nat := 4983230072969 + 3 ^ 40 * 373250 * 2
def baseEnd_373250 : Nat := 191656654290769891358461

theorem tailTrace_373250 : CollatzResearch.WordTrace tailWord_373250 prefixEnd_373250 191656654290769891358461 := by
  unfold tailWord_373250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403386474446617717507301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9075697265190980580019469 3403386474446617717507301)
  ·
    refine ⟨638134963958740822032619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3403386474446617717507301 638134963958740822032619)
    ·
      refine ⟨957202445938111233048929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638134963958740822032619 957202445938111233048929)
      ·
        refine ⟨717901834453583424786697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 957202445938111233048929 717901834453583424786697)
        ·
          refine ⟨538426375840187568590023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717901834453583424786697 538426375840187568590023)
          ·
            refine ⟨807639563760281352885035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538426375840187568590023 807639563760281352885035)
            ·
              refine ⟨1211459345640422029327553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807639563760281352885035 1211459345640422029327553)
              ·
                refine ⟨908594509230316521995665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211459345640422029327553 908594509230316521995665)
                ·
                  refine ⟨681445881922737391496749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908594509230316521995665 681445881922737391496749)
                  ·
                    refine ⟨255542205721026521811281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681445881922737391496749 255542205721026521811281)
                    ·
                      refine ⟨191656654290769891358461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255542205721026521811281 191656654290769891358461)
                      ·
                        rfl

theorem cell23_373250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_373250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373250 prefixEnd_373250 := by exact prefixLift 373250
  have htrace : WordTrace (prefixWord ++ tailWord_373250) baseStart_373250 baseEnd_373250 := by
    simpa [prefixWord, tailWord_373250, baseEnd_373250] using wordTrace_append hprefix tailTrace_373250
  have hstable : (prefixWord ++ tailWord_373250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373250).length < 2 ^ (prefixWord ++ tailWord_373250).sum := by decide
  have hdescent : baseEnd_373250 < baseStart_373250 := by decide
  rcases family_descends (prefixWord ++ tailWord_373250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373279 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_373279 : Nat := 118140960795 + 373279 * 2 ^ 59
def prefixEnd_373279 : Nat := 4983230072969 + 3 ^ 40 * 373279 * 2
def baseEnd_373279 : Nat := 191671545229750277895827

theorem tailTrace_373279 : CollatzResearch.WordTrace tailWord_373279 prefixEnd_373279 191671545229750277895827 := by
  unfold tailWord_373279
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614603614681408822834891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9076402409787605881889927 13614603614681408822834891)
  ·
    refine ⟨20421905422022113234252337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13614603614681408822834891 20421905422022113234252337)
    ·
      refine ⟨15316429066516584925689253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20421905422022113234252337 15316429066516584925689253)
      ·
        refine ⟨2871830449971859673566735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15316429066516584925689253 2871830449971859673566735)
        ·
          refine ⟨4307745674957789510350103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871830449971859673566735 4307745674957789510350103)
          ·
            refine ⟨6461618512436684265525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307745674957789510350103 6461618512436684265525155)
            ·
              refine ⟨9692427768655026398287733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461618512436684265525155 9692427768655026398287733)
              ·
                refine ⟨908665103311408724839475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9692427768655026398287733 908665103311408724839475)
                ·
                  refine ⟨1362997654967113087259213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908665103311408724839475 1362997654967113087259213)
                  ·
                    refine ⟨511124120612667407722205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362997654967113087259213 511124120612667407722205)
                    ·
                      refine ⟨191671545229750277895827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511124120612667407722205 191671545229750277895827)
                      ·
                        rfl

theorem cell23_373279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_373279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373279 prefixEnd_373279 := by exact prefixLift 373279
  have htrace : WordTrace (prefixWord ++ tailWord_373279) baseStart_373279 baseEnd_373279 := by
    simpa [prefixWord, tailWord_373279, baseEnd_373279] using wordTrace_append hprefix tailTrace_373279
  have hstable : (prefixWord ++ tailWord_373279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373279).length < 2 ^ (prefixWord ++ tailWord_373279).sum := by decide
  have hdescent : baseEnd_373279 < baseStart_373279 := by decide
  rcases family_descends (prefixWord ++ tailWord_373279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373280 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4]
def baseStart_373280 : Nat := 118140960795 + 373280 * 2 ^ 59
def prefixEnd_373280 : Nat := 4983230072969 + 3 ^ 40 * 373280 * 2
def baseEnd_373280 : Nat := 191672058710404773983323

theorem tailTrace_373280 : CollatzResearch.WordTrace tailWord_373280 prefixEnd_373280 191672058710404773983323 := by
  unfold tailWord_373280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807320043838892996810647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9076426725118523995747529 6807320043838892996810647)
  ·
    refine ⟨10210980065758339495215971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6807320043838892996810647 10210980065758339495215971)
    ·
      refine ⟨15316470098637509242823957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10210980065758339495215971 15316470098637509242823957)
      ·
        refine ⟨717959535873633245757373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15316470098637509242823957 717959535873633245757373)
        ·
          refine ⟨269234825952612467159015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 717959535873633245757373 269234825952612467159015)
          ·
            refine ⟨403852238928918700738523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269234825952612467159015 403852238928918700738523)
            ·
              refine ⟨605778358393378051107785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403852238928918700738523 605778358393378051107785)
              ·
                refine ⟨454333768795033538330839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605778358393378051107785 454333768795033538330839)
                ·
                  refine ⟨681500653192550307496259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454333768795033538330839 681500653192550307496259)
                  ·
                    refine ⟨1022250979788825461244389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681500653192550307496259 1022250979788825461244389)
                    ·
                      refine ⟨191672058710404773983323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1022250979788825461244389 191672058710404773983323)
                      ·
                        rfl

theorem cell23_373280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_373280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373280 prefixEnd_373280 := by exact prefixLift 373280
  have htrace : WordTrace (prefixWord ++ tailWord_373280) baseStart_373280 baseEnd_373280 := by
    simpa [prefixWord, tailWord_373280, baseEnd_373280] using wordTrace_append hprefix tailTrace_373280
  have hstable : (prefixWord ++ tailWord_373280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373280).length < 2 ^ (prefixWord ++ tailWord_373280).sum := by decide
  have hdescent : baseEnd_373280 < baseStart_373280 := by decide
  rcases family_descends (prefixWord ++ tailWord_373280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373283 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 3]
def baseStart_373283 : Nat := 118140960795 + 373283 * 2 ^ 59
def prefixEnd_373283 : Nat := 4983230072969 + 3 ^ 40 * 373283 * 2
def baseEnd_373283 : Nat := 191673599152368262245809

theorem tailTrace_373283 : CollatzResearch.WordTrace tailWord_373283 prefixEnd_373283 191673599152368262245809 := by
  unfold tailWord_373283
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614749506666917505980503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9076499671111278337320335 13614749506666917505980503)
  ·
    refine ⟨20422124260000376258970755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13614749506666917505980503 20422124260000376258970755)
    ·
      refine ⟨30633186390000564388456133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20422124260000376258970755 30633186390000564388456133)
      ·
        refine ⟨5743722448125105822835525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30633186390000564388456133 5743722448125105822835525)
        ·
          refine ⟨1076947959023457341781661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5743722448125105822835525 1076947959023457341781661)
          ·
            refine ⟨403855484633796503168123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1076947959023457341781661 403855484633796503168123)
            ·
              refine ⟨605783226950694754752185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403855484633796503168123 605783226950694754752185)
              ·
                refine ⟨454337420213021066064139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605783226950694754752185 454337420213021066064139)
                ·
                  refine ⟨681506130319531599096209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454337420213021066064139 681506130319531599096209)
                  ·
                    refine ⟨511129597739648699322157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 681506130319531599096209 511129597739648699322157)
                    ·
                      refine ⟨191673599152368262245809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511129597739648699322157 191673599152368262245809)
                      ·
                        rfl

theorem cell23_373283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_373283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373283 prefixEnd_373283 := by exact prefixLift 373283
  have htrace : WordTrace (prefixWord ++ tailWord_373283) baseStart_373283 baseEnd_373283 := by
    simpa [prefixWord, tailWord_373283, baseEnd_373283] using wordTrace_append hprefix tailTrace_373283
  have hstable : (prefixWord ++ tailWord_373283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373283).length < 2 ^ (prefixWord ++ tailWord_373283).sum := by decide
  have hdescent : baseEnd_373283 < baseStart_373283 := by decide
  rcases family_descends (prefixWord ++ tailWord_373283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373292 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_373292 : Nat := 118140960795 + 373292 * 2 ^ 59
def prefixEnd_373292 : Nat := 4983230072969 + 3 ^ 40 * 373292 * 2
def baseEnd_373292 : Nat := 191678220478258727033267

theorem tailTrace_373292 : CollatzResearch.WordTrace tailWord_373292 prefixEnd_373292 191678220478258727033267 := by
  unfold tailWord_373292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807538881817156021529065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9076718509089541362038753 6807538881817156021529065)
  ·
    refine ⟨5105654161362867016146799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6807538881817156021529065 5105654161362867016146799)
    ·
      refine ⟨7658481242044300524220199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105654161362867016146799 7658481242044300524220199)
      ·
        refine ⟨11487721863066450786330299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658481242044300524220199 11487721863066450786330299)
        ·
          refine ⟨17231582794599676179495449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11487721863066450786330299 17231582794599676179495449)
          ·
            refine ⟨12923687095949757134621587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17231582794599676179495449 12923687095949757134621587)
            ·
              refine ⟨19385530643924635701932381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12923687095949757134621587 19385530643924635701932381)
              ·
                refine ⟨7269573991471738388224643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19385530643924635701932381 7269573991471738388224643)
                ·
                  refine ⟨10904360987207607582336965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7269573991471738388224643 10904360987207607582336965)
                  ·
                    refine ⟨2044567685101426421688181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10904360987207607582336965 2044567685101426421688181)
                    ·
                      refine ⟨191678220478258727033267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2044567685101426421688181 191678220478258727033267)
                      ·
                        rfl

theorem cell23_373292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_373292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373292 prefixEnd_373292 := by exact prefixLift 373292
  have htrace : WordTrace (prefixWord ++ tailWord_373292) baseStart_373292 baseEnd_373292 := by
    simpa [prefixWord, tailWord_373292, baseEnd_373292] using wordTrace_append hprefix tailTrace_373292
  have hstable : (prefixWord ++ tailWord_373292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373292).length < 2 ^ (prefixWord ++ tailWord_373292).sum := by decide
  have hdescent : baseEnd_373292 < baseStart_373292 := by decide
  rcases family_descends (prefixWord ++ tailWord_373292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373300 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_373300 : Nat := 118140960795 + 373300 * 2 ^ 59
def prefixEnd_373300 : Nat := 4983230072969 + 3 ^ 40 * 373300 * 2
def baseEnd_373300 : Nat := 191682328323494695733231

theorem tailTrace_373300 : CollatzResearch.WordTrace tailWord_373300 prefixEnd_373300 191682328323494695733231 := by
  unfold tailWord_373300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807684773802664704674677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9076913031736886272899569 6807684773802664704674677)
  ·
    refine ⟨638220447543999816063251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6807684773802664704674677 638220447543999816063251)
    ·
      refine ⟨957330671315999724094877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638220447543999816063251 957330671315999724094877)
      ·
        refine ⟨358999001743499896535579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 957330671315999724094877 358999001743499896535579)
        ·
          refine ⟨538498502615249844803369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358999001743499896535579 538498502615249844803369)
          ·
            refine ⟨403873876961437383602527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538498502615249844803369 403873876961437383602527)
            ·
              refine ⟨605810815442156075403791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403873876961437383602527 605810815442156075403791)
              ·
                refine ⟨908716223163234113105687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605810815442156075403791 908716223163234113105687)
                ·
                  refine ⟨1363074334744851169658531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908716223163234113105687 1363074334744851169658531)
                  ·
                    refine ⟨2044611502117276754487797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363074334744851169658531 2044611502117276754487797)
                    ·
                      refine ⟨191682328323494695733231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2044611502117276754487797 191682328323494695733231)
                      ·
                        rfl

theorem cell23_373300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_373300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373300 prefixEnd_373300 := by exact prefixLift 373300
  have htrace : WordTrace (prefixWord ++ tailWord_373300) baseStart_373300 baseEnd_373300 := by
    simpa [prefixWord, tailWord_373300, baseEnd_373300] using wordTrace_append hprefix tailTrace_373300
  have hstable : (prefixWord ++ tailWord_373300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373300).length < 2 ^ (prefixWord ++ tailWord_373300).sum := by decide
  have hdescent : baseEnd_373300 < baseStart_373300 := by decide
  rcases family_descends (prefixWord ++ tailWord_373300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373313 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_373313 : Nat := 118140960795 + 373313 * 2 ^ 59
def prefixEnd_373313 : Nat := 4983230072969 + 3 ^ 40 * 373313 * 2
def baseEnd_373313 : Nat := 191689003572003144870671

theorem tailTrace_373313 : CollatzResearch.WordTrace tailWord_373313 prefixEnd_373313 191689003572003144870671 := by
  unfold tailWord_373313
  simp only [CollatzResearch.WordTrace]
  refine ⟨13615843696558232629572593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077229131038821753048395 13615843696558232629572593)
  ·
    refine ⟨10211882772418674472179445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13615843696558232629572593 10211882772418674472179445)
    ·
      refine ⟨957364009914250731766823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10211882772418674472179445 957364009914250731766823)
      ·
        refine ⟨1436046014871376097650235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957364009914250731766823 1436046014871376097650235)
        ·
          refine ⟨2154069022307064146475353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436046014871376097650235 2154069022307064146475353)
          ·
            refine ⟨1615551766730298109856515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2154069022307064146475353 1615551766730298109856515)
            ·
              refine ⟨2423327650095447164784773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615551766730298109856515 2423327650095447164784773)
              ·
                refine ⟨454373934392896343397145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2423327650095447164784773 454373934392896343397145)
                ·
                  refine ⟨340780450794672257547859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454373934392896343397145 340780450794672257547859)
                  ·
                    refine ⟨511170676192008386321789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340780450794672257547859 511170676192008386321789)
                    ·
                      refine ⟨191689003572003144870671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511170676192008386321789 191689003572003144870671)
                      ·
                        rfl

theorem cell23_373313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_373313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373313 prefixEnd_373313 := by exact prefixLift 373313
  have htrace : WordTrace (prefixWord ++ tailWord_373313) baseStart_373313 baseEnd_373313 := by
    simpa [prefixWord, tailWord_373313, baseEnd_373313] using wordTrace_append hprefix tailTrace_373313
  have hstable : (prefixWord ++ tailWord_373313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373313).length < 2 ^ (prefixWord ++ tailWord_373313).sum := by decide
  have hdescent : baseEnd_373313 < baseStart_373313 := by decide
  rcases family_descends (prefixWord ++ tailWord_373313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373319 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_373319 : Nat := 118140960795 + 373319 * 2 ^ 59
def prefixEnd_373319 : Nat := 4983230072969 + 3 ^ 40 * 373319 * 2
def baseEnd_373319 : Nat := 191692084455930121395643

theorem tailTrace_373319 : CollatzResearch.WordTrace tailWord_373319 prefixEnd_373319 191692084455930121395643 := by
  unfold tailWord_373319
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616062534536495654291011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077375023024330436194007 13616062534536495654291011)
  ·
    refine ⟨20424093801804743481436517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13616062534536495654291011 20424093801804743481436517)
    ·
      refine ⟨3829517587838389402769347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20424093801804743481436517 3829517587838389402769347)
      ·
        refine ⟨5744276381757584104154021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829517587838389402769347 5744276381757584104154021)
        ·
          refine ⟨1077051821579547019528879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5744276381757584104154021 1077051821579547019528879)
          ·
            refine ⟨1615577732369320529293319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077051821579547019528879 1615577732369320529293319)
            ·
              refine ⟨2423366598553980793939979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615577732369320529293319 2423366598553980793939979)
              ·
                refine ⟨3635049897830971190909969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423366598553980793939979 3635049897830971190909969)
                ·
                  refine ⟨2726287423373228393182477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635049897830971190909969 2726287423373228393182477)
                  ·
                    refine ⟨1022357783764960647443429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726287423373228393182477 1022357783764960647443429)
                    ·
                      refine ⟨191692084455930121395643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1022357783764960647443429 191692084455930121395643)
                      ·
                        rfl

theorem cell23_373319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_373319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373319 prefixEnd_373319 := by exact prefixLift 373319
  have htrace : WordTrace (prefixWord ++ tailWord_373319) baseStart_373319 baseEnd_373319 := by
    simpa [prefixWord, tailWord_373319, baseEnd_373319] using wordTrace_append hprefix tailTrace_373319
  have hstable : (prefixWord ++ tailWord_373319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373319).length < 2 ^ (prefixWord ++ tailWord_373319).sum := by decide
  have hdescent : baseEnd_373319 < baseStart_373319 := by decide
  rcases family_descends (prefixWord ++ tailWord_373319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373329 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_373329 : Nat := 118140960795 + 373329 * 2 ^ 59
def prefixEnd_373329 : Nat := 4983230072969 + 3 ^ 40 * 373329 * 2
def baseEnd_373329 : Nat := 63899073087491694090199

theorem tailTrace_373329 : CollatzResearch.WordTrace tailWord_373329 prefixEnd_373329 63899073087491694090199 := by
  unfold tailWord_373329
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616427264500267362155041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077618176333511574770027 13616427264500267362155041)
  ·
    refine ⟨10212320448375200521616281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13616427264500267362155041 10212320448375200521616281)
    ·
      refine ⟨7659240336281400391212211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10212320448375200521616281 7659240336281400391212211)
      ·
        refine ⟨11488860504422100586818317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7659240336281400391212211 11488860504422100586818317)
        ·
          refine ⟨4308322689158287720056869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11488860504422100586818317 4308322689158287720056869)
          ·
            refine ⟨807810504217178947510663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4308322689158287720056869 807810504217178947510663)
            ·
              refine ⟨1211715756325768421265995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807810504217178947510663 1211715756325768421265995)
              ·
                refine ⟨1817573634488652631898993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211715756325768421265995 1817573634488652631898993)
                ·
                  refine ⟨1363180225866489473924245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817573634488652631898993 1363180225866489473924245)
                  ·
                    refine ⟨63899073087491694090199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1363180225866489473924245 63899073087491694090199)
                    ·
                      rfl

theorem cell23_373329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_373329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373329 prefixEnd_373329 := by exact prefixLift 373329
  have htrace : WordTrace (prefixWord ++ tailWord_373329) baseStart_373329 baseEnd_373329 := by
    simpa [prefixWord, tailWord_373329, baseEnd_373329] using wordTrace_append hprefix tailTrace_373329
  have hstable : (prefixWord ++ tailWord_373329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373329).length < 2 ^ (prefixWord ++ tailWord_373329).sum := by decide
  have hdescent : baseEnd_373329 < baseStart_373329 := by decide
  rcases family_descends (prefixWord ++ tailWord_373329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373336 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_373336 : Nat := 118140960795 + 373336 * 2 ^ 59
def prefixEnd_373336 : Nat := 4983230072969 + 3 ^ 40 * 373336 * 2
def baseEnd_373336 : Nat := 191700813627056554883065

theorem tailTrace_373336 : CollatzResearch.WordTrace tailWord_373336 prefixEnd_373336 191700813627056554883065 := by
  unfold tailWord_373336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808341287737453778829931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9077788383649938371773241 6808341287737453778829931)
  ·
    refine ⟨10212511931606180668244897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6808341287737453778829931 10212511931606180668244897)
    ·
      refine ⟨7659383948704635501183673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10212511931606180668244897 7659383948704635501183673)
      ·
        refine ⟨5744537961528476625887755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7659383948704635501183673 5744537961528476625887755)
        ·
          refine ⟨8616806942292714938831633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744537961528476625887755 8616806942292714938831633)
          ·
            refine ⟨6462605206719536204123725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8616806942292714938831633 6462605206719536204123725)
            ·
              refine ⟨2423476952519826076546397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6462605206719536204123725 2423476952519826076546397)
              ·
                refine ⟨908803857194934778704899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423476952519826076546397 908803857194934778704899)
                ·
                  refine ⟨1363205785792402168057349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908803857194934778704899 1363205785792402168057349)
                  ·
                    refine ⟨255601084836075406510753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1363205785792402168057349 255601084836075406510753)
                    ·
                      refine ⟨191700813627056554883065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255601084836075406510753 191700813627056554883065)
                      ·
                        rfl

theorem cell23_373336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_373336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373336 prefixEnd_373336 := by exact prefixLift 373336
  have htrace : WordTrace (prefixWord ++ tailWord_373336) baseStart_373336 baseEnd_373336 := by
    simpa [prefixWord, tailWord_373336, baseEnd_373336] using wordTrace_append hprefix tailTrace_373336
  have hstable : (prefixWord ++ tailWord_373336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373336).length < 2 ^ (prefixWord ++ tailWord_373336).sum := by decide
  have hdescent : baseEnd_373336 < baseStart_373336 := by decide
  rcases family_descends (prefixWord ++ tailWord_373336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373357 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_373357 : Nat := 118140960795 + 373357 * 2 ^ 59
def prefixEnd_373357 : Nat := 4983230072969 + 3 ^ 40 * 373357 * 2
def baseEnd_373357 : Nat := 191711596720800972720469

theorem tailTrace_373357 : CollatzResearch.WordTrace tailWord_373357 prefixEnd_373357 191711596720800972720469 := by
  unfold tailWord_373357
  simp only [CollatzResearch.WordTrace]
  refine ⟨13617448508398828144174325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9078299005599218762782883 13617448508398828144174325)
  ·
    refine ⟨1276635797662390138516343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13617448508398828144174325 1276635797662390138516343)
    ·
      refine ⟨1914953696493585207774515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276635797662390138516343 1914953696493585207774515)
      ·
        refine ⟨2872430544740377811661773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914953696493585207774515 2872430544740377811661773)
        ·
          refine ⟨1077161454277641679373165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2872430544740377811661773 1077161454277641679373165)
          ·
            refine ⟨403935545354115629764937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1077161454277641679373165 403935545354115629764937)
            ·
              refine ⟨302951659015586722323703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403935545354115629764937 302951659015586722323703)
              ·
                refine ⟨454427488523380083485555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302951659015586722323703 454427488523380083485555)
                ·
                  refine ⟨681641232785070125228333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454427488523380083485555 681641232785070125228333)
                  ·
                    refine ⟨255615462294401296960625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 681641232785070125228333 255615462294401296960625)
                    ·
                      refine ⟨191711596720800972720469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255615462294401296960625 191711596720800972720469)
                      ·
                        rfl

theorem cell23_373357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_373357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373357 prefixEnd_373357 := by exact prefixLift 373357
  have htrace : WordTrace (prefixWord ++ tailWord_373357) baseStart_373357 baseEnd_373357 := by
    simpa [prefixWord, tailWord_373357, baseEnd_373357] using wordTrace_append hprefix tailTrace_373357
  have hstable : (prefixWord ++ tailWord_373357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373357).length < 2 ^ (prefixWord ++ tailWord_373357).sum := by decide
  have hdescent : baseEnd_373357 < baseStart_373357 := by decide
  rcases family_descends (prefixWord ++ tailWord_373357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373376 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 5]
def baseStart_373376 : Nat := 118140960795 + 373376 * 2 ^ 59
def prefixEnd_373376 : Nat := 4983230072969 + 3 ^ 40 * 373376 * 2
def baseEnd_373376 : Nat := 21302372539248488709209

theorem tailTrace_373376 : CollatzResearch.WordTrace tailWord_373376 prefixEnd_373376 21302372539248488709209 := by
  unfold tailWord_373376
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809070747664997194557991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9078760996886662926077321 6809070747664997194557991)
  ·
    refine ⟨10213606121497495791836987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6809070747664997194557991 10213606121497495791836987)
    ·
      refine ⟨15320409182246243687755481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213606121497495791836987 15320409182246243687755481)
      ·
        refine ⟨11490306886684682765816611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15320409182246243687755481 11490306886684682765816611)
        ·
          refine ⟨17235460330027024148724917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11490306886684682765816611 17235460330027024148724917)
          ·
            refine ⟨1615824405940033513942961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17235460330027024148724917 1615824405940033513942961)
            ·
              refine ⟨1211868304455025135457221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615824405940033513942961 1211868304455025135457221)
              ·
                refine ⟨227225307085317212898229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1211868304455025135457221 227225307085317212898229)
                ·
                  refine ⟨21302372539248488709209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227225307085317212898229 21302372539248488709209)
                  ·
                    rfl

theorem cell23_373376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 5].length) (baseStart_373376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373376 prefixEnd_373376 := by exact prefixLift 373376
  have htrace : WordTrace (prefixWord ++ tailWord_373376) baseStart_373376 baseEnd_373376 := by
    simpa [prefixWord, tailWord_373376, baseEnd_373376] using wordTrace_append hprefix tailTrace_373376
  have hstable : (prefixWord ++ tailWord_373376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373376).length < 2 ^ (prefixWord ++ tailWord_373376).sum := by decide
  have hdescent : baseEnd_373376 < baseStart_373376 := by decide
  rcases family_descends (prefixWord ++ tailWord_373376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373406 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_373406 : Nat := 118140960795 + 373406 * 2 ^ 59
def prefixEnd_373406 : Nat := 4983230072969 + 3 ^ 40 * 373406 * 2
def baseEnd_373406 : Nat := 63912252424290427002581

theorem tailTrace_373406 : CollatzResearch.WordTrace tailWord_373406 prefixEnd_373406 63912252424290427002581 := by
  unfold tailWord_373406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702404460652663689088509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9079490456814206341805381 1702404460652663689088509)
  ·
    refine ⟨638401672744748883408191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1702404460652663689088509 638401672744748883408191)
    ·
      refine ⟨957602509117123325112287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638401672744748883408191 957602509117123325112287)
      ·
        refine ⟨1436403763675684987668431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957602509117123325112287 1436403763675684987668431)
        ·
          refine ⟨2154605645513527481502647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436403763675684987668431 2154605645513527481502647)
          ·
            refine ⟨3231908468270291222253971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154605645513527481502647 3231908468270291222253971)
            ·
              refine ⟨4847862702405436833380957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231908468270291222253971 4847862702405436833380957)
              ·
                refine ⟨1817948513402038812517859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4847862702405436833380957 1817948513402038812517859)
                ·
                  refine ⟨2726922770103058218776789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817948513402038812517859 2726922770103058218776789)
                  ·
                    refine ⟨63912252424290427002581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2726922770103058218776789 63912252424290427002581)
                    ·
                      rfl

theorem cell23_373406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_373406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373406 prefixEnd_373406 := by exact prefixLift 373406
  have htrace : WordTrace (prefixWord ++ tailWord_373406) baseStart_373406 baseEnd_373406 := by
    simpa [prefixWord, tailWord_373406, baseEnd_373406] using wordTrace_append hprefix tailTrace_373406
  have hstable : (prefixWord ++ tailWord_373406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373406).length < 2 ^ (prefixWord ++ tailWord_373406).sum := by decide
  have hdescent : baseEnd_373406 < baseStart_373406 := by decide
  rcases family_descends (prefixWord ++ tailWord_373406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373460 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_373460 : Nat := 118140960795 + 373460 * 2 ^ 59
def prefixEnd_373460 : Nat := 4983230072969 + 3 ^ 40 * 373460 * 2
def baseEnd_373460 : Nat := 191764485228214069732495

theorem tailTrace_373460 : CollatzResearch.WordTrace tailWord_373460 prefixEnd_373460 191764485228214069732495 := by
  unfold tailWord_373460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810602613512838367586917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9080803484683784490115889 6810602613512838367586917)
  ·
    refine ⟨1276987990033657193922547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6810602613512838367586917 1276987990033657193922547)
    ·
      refine ⟨1915481985050485790883821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276987990033657193922547 1915481985050485790883821)
      ·
        refine ⟨718305744393932171581433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1915481985050485790883821 718305744393932171581433)
        ·
          refine ⟨538729308295449128686075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718305744393932171581433 538729308295449128686075)
          ·
            refine ⟨808093962443173693029113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538729308295449128686075 808093962443173693029113)
            ·
              refine ⟨606070471832380269771835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808093962443173693029113 606070471832380269771835)
              ·
                refine ⟨909105707748570404657753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606070471832380269771835 909105707748570404657753)
                ·
                  refine ⟨681829280811427803493315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909105707748570404657753 681829280811427803493315)
                  ·
                    refine ⟨1022743921217141705239973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681829280811427803493315 1022743921217141705239973)
                    ·
                      refine ⟨191764485228214069732495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1022743921217141705239973 191764485228214069732495)
                      ·
                        rfl

theorem cell23_373460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_373460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373460 prefixEnd_373460 := by exact prefixLift 373460
  have htrace : WordTrace (prefixWord ++ tailWord_373460) baseStart_373460 baseEnd_373460 := by
    simpa [prefixWord, tailWord_373460, baseEnd_373460] using wordTrace_append hprefix tailTrace_373460
  have hstable : (prefixWord ++ tailWord_373460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373460).length < 2 ^ (prefixWord ++ tailWord_373460).sum := by decide
  have hdescent : baseEnd_373460 < baseStart_373460 := by decide
  rcases family_descends (prefixWord ++ tailWord_373460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373463 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_373463 : Nat := 118140960795 + 373463 * 2 ^ 59
def prefixEnd_373463 : Nat := 4983230072969 + 3 ^ 40 * 373463 * 2
def baseEnd_373463 : Nat := 191766025670177557994981

theorem tailTrace_373463 : CollatzResearch.WordTrace tailWord_373463 prefixEnd_373463 191766025670177557994981 := by
  unfold tailWord_373463
  simp only [CollatzResearch.WordTrace]
  refine ⟨13621314646014808247533043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9080876430676538831688695 13621314646014808247533043)
  ·
    refine ⟨20431971969022212371299565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13621314646014808247533043 20431971969022212371299565)
    ·
      refine ⟨7661989488383329639237337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20431971969022212371299565 7661989488383329639237337)
      ·
        refine ⟨5746492116287497229428003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7661989488383329639237337 5746492116287497229428003)
        ·
          refine ⟨8619738174431245844142005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5746492116287497229428003 8619738174431245844142005)
          ·
            refine ⟨808100453852929297888313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8619738174431245844142005 808100453852929297888313)
            ·
              refine ⟨606075340389696973416235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808100453852929297888313 606075340389696973416235)
              ·
                refine ⟨909113010584545460124353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606075340389696973416235 909113010584545460124353)
                ·
                  refine ⟨681834757938409095093265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909113010584545460124353 681834757938409095093265)
                  ·
                    refine ⟨511376068453806821319949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 681834757938409095093265 511376068453806821319949)
                    ·
                      refine ⟨191766025670177557994981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511376068453806821319949 191766025670177557994981)
                      ·
                        rfl

theorem cell23_373463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_373463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373463 prefixEnd_373463 := by exact prefixLift 373463
  have htrace : WordTrace (prefixWord ++ tailWord_373463) baseStart_373463 baseEnd_373463 := by
    simpa [prefixWord, tailWord_373463, baseEnd_373463] using wordTrace_append hprefix tailTrace_373463
  have hstable : (prefixWord ++ tailWord_373463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373463).length < 2 ^ (prefixWord ++ tailWord_373463).sum := by decide
  have hdescent : baseEnd_373463 < baseStart_373463 := by decide
  rcases family_descends (prefixWord ++ tailWord_373463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373487 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 1, 4]
def baseStart_373487 : Nat := 118140960795 + 373487 * 2 ^ 59
def prefixEnd_373487 : Nat := 4983230072969 + 3 ^ 40 * 373487 * 2
def baseEnd_373487 : Nat := 63926116401961821364957

theorem tailTrace_373487 : CollatzResearch.WordTrace tailWord_373487 prefixEnd_373487 63926116401961821364957 := by
  unfold tailWord_373487
  simp only [CollatzResearch.WordTrace]
  refine ⟨13622189997927860346406715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9081459998618573564271143 13622189997927860346406715)
  ·
    refine ⟨20433284996891790519610073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13622189997927860346406715 20433284996891790519610073)
    ·
      refine ⟨15324963747668842889707555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20433284996891790519610073 15324963747668842889707555)
      ·
        refine ⟨22987445621503264334561333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15324963747668842889707555 22987445621503264334561333)
        ·
          refine ⟨2155073027015931031365125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22987445621503264334561333 2155073027015931031365125)
          ·
            refine ⟨404076192565487068380961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2155073027015931031365125 404076192565487068380961)
            ·
              refine ⟨303057144424115301285721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404076192565487068380961 303057144424115301285721)
              ·
                refine ⟨227292858318086475964291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303057144424115301285721 227292858318086475964291)
                ·
                  refine ⟨340939287477129713946437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227292858318086475964291 340939287477129713946437)
                  ·
                    refine ⟨63926116401961821364957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 340939287477129713946437 63926116401961821364957)
                    ·
                      rfl

theorem cell23_373487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 4].length) (baseStart_373487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373487 prefixEnd_373487 := by exact prefixLift 373487
  have htrace : WordTrace (prefixWord ++ tailWord_373487) baseStart_373487 baseEnd_373487 := by
    simpa [prefixWord, tailWord_373487, baseEnd_373487] using wordTrace_append hprefix tailTrace_373487
  have hstable : (prefixWord ++ tailWord_373487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373487).length < 2 ^ (prefixWord ++ tailWord_373487).sum := by decide
  have hdescent : baseEnd_373487 < baseStart_373487 := by decide
  rcases family_descends (prefixWord ++ tailWord_373487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373560 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 2, 4]
def baseStart_373560 : Nat := 118140960795 + 373560 * 2 ^ 59
def prefixEnd_373560 : Nat := 4983230072969 + 3 ^ 40 * 373560 * 2
def baseEnd_373560 : Nat := 63938611097887892827345

theorem tailTrace_373560 : CollatzResearch.WordTrace tailWord_373560 prefixEnd_373560 63938611097887892827345 := by
  unfold tailWord_373560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812426263331696906907067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9083235017775595875876089 6812426263331696906907067)
  ·
    refine ⟨10218639394997545360360601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6812426263331696906907067 10218639394997545360360601)
    ·
      refine ⟨7663979546248159020270451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10218639394997545360360601 7663979546248159020270451)
      ·
        refine ⟨11495969319372238530405677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7663979546248159020270451 11495969319372238530405677)
        ·
          refine ⟨4310988494764589448902129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11495969319372238530405677 4310988494764589448902129)
          ·
            refine ⟨3233241371073442086676597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310988494764589448902129 3233241371073442086676597)
            ·
              refine ⟨303116378538135195625931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3233241371073442086676597 303116378538135195625931)
              ·
                refine ⟨454674567807202793438897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303116378538135195625931 454674567807202793438897)
                ·
                  refine ⟨341005925855402095079173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454674567807202793438897 341005925855402095079173)
                  ·
                    refine ⟨63938611097887892827345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341005925855402095079173 63938611097887892827345)
                    ·
                      rfl

theorem cell23_373560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_373560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373560 prefixEnd_373560 := by exact prefixLift 373560
  have htrace : WordTrace (prefixWord ++ tailWord_373560) baseStart_373560 baseEnd_373560 := by
    simpa [prefixWord, tailWord_373560, baseEnd_373560] using wordTrace_append hprefix tailTrace_373560
  have hstable : (prefixWord ++ tailWord_373560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373560).length < 2 ^ (prefixWord ++ tailWord_373560).sum := by decide
  have hdescent : baseEnd_373560 < baseStart_373560 := by decide
  rcases family_descends (prefixWord ++ tailWord_373560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373600 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3]
def baseStart_373600 : Nat := 118140960795 + 373600 * 2 ^ 59
def prefixEnd_373600 : Nat := 4983230072969 + 3 ^ 40 * 373600 * 2
def baseEnd_373600 : Nat := 191836372519843521981851

theorem tailTrace_373600 : CollatzResearch.WordTrace tailWord_373600 prefixEnd_373600 191836372519843521981851 := by
  unfold tailWord_373600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813155723259240322635127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9084207631012320430180169 6813155723259240322635127)
  ·
    refine ⟨10219733584888860483952691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6813155723259240322635127 10219733584888860483952691)
    ·
      refine ⟨15329600377333290725929037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10219733584888860483952691 15329600377333290725929037)
      ·
        refine ⟨5748600141499984022223389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15329600377333290725929037 5748600141499984022223389)
        ·
          refine ⟨2155725053062494008333771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5748600141499984022223389 2155725053062494008333771)
          ·
            refine ⟨3233587579593741012500657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155725053062494008333771 3233587579593741012500657)
            ·
              refine ⟨2425190684695305759375493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233587579593741012500657 2425190684695305759375493)
              ·
                refine ⟨454723253380369829882905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2425190684695305759375493 454723253380369829882905)
                ·
                  refine ⟨341042440035277372412179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454723253380369829882905 341042440035277372412179)
                  ·
                    refine ⟨511563660052916058618269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341042440035277372412179 511563660052916058618269)
                    ·
                      refine ⟨191836372519843521981851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511563660052916058618269 191836372519843521981851)
                      ·
                        rfl

theorem cell23_373600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_373600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373600 prefixEnd_373600 := by exact prefixLift 373600
  have htrace : WordTrace (prefixWord ++ tailWord_373600) baseStart_373600 baseEnd_373600 := by
    simpa [prefixWord, tailWord_373600, baseEnd_373600] using wordTrace_append hprefix tailTrace_373600
  have hstable : (prefixWord ++ tailWord_373600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373600).length < 2 ^ (prefixWord ++ tailWord_373600).sum := by decide
  have hdescent : baseEnd_373600 < baseStart_373600 := by decide
  rcases family_descends (prefixWord ++ tailWord_373600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373616 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_373616 : Nat := 118140960795 + 373616 * 2 ^ 59
def prefixEnd_373616 : Nat := 4983230072969 + 3 ^ 40 * 373616 * 2
def baseEnd_373616 : Nat := 63948196070105153127259

theorem tailTrace_373616 : CollatzResearch.WordTrace tailWord_373616 prefixEnd_373616 63948196070105153127259 := by
  unfold tailWord_373616
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813447507230257688926351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9084596676307010251901801 6813447507230257688926351)
  ·
    refine ⟨10220171260845386533389527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6813447507230257688926351 10220171260845386533389527)
    ·
      refine ⟨15330256891268079800084291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10220171260845386533389527 15330256891268079800084291)
      ·
        refine ⟨22995385336902119700126437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15330256891268079800084291 22995385336902119700126437)
        ·
          refine ⟨4311634750669147443773707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22995385336902119700126437 4311634750669147443773707)
          ·
            refine ⟨6467452126003721165660561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311634750669147443773707 6467452126003721165660561)
            ·
              refine ⟨4850589094502790874245421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467452126003721165660561 4850589094502790874245421)
              ·
                refine ⟨1818970910438546577842033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4850589094502790874245421 1818970910438546577842033)
                ·
                  refine ⟨1364228182828909933381525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818970910438546577842033 1364228182828909933381525)
                  ·
                    refine ⟨63948196070105153127259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1364228182828909933381525 63948196070105153127259)
                    ·
                      rfl

theorem cell23_373616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_373616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373616 prefixEnd_373616 := by exact prefixLift 373616
  have htrace : WordTrace (prefixWord ++ tailWord_373616) baseStart_373616 baseEnd_373616 := by
    simpa [prefixWord, tailWord_373616, baseEnd_373616] using wordTrace_append hprefix tailTrace_373616
  have hstable : (prefixWord ++ tailWord_373616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373616).length < 2 ^ (prefixWord ++ tailWord_373616).sum := by decide
  have hdescent : baseEnd_373616 < baseStart_373616 := by decide
  rcases family_descends (prefixWord ++ tailWord_373616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373617 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_373617 : Nat := 118140960795 + 373617 * 2 ^ 59
def prefixEnd_373617 : Nat := 4983230072969 + 3 ^ 40 * 373617 * 2
def baseEnd_373617 : Nat := 191845101690969955469273

theorem tailTrace_373617 : CollatzResearch.WordTrace tailWord_373617 prefixEnd_373617 191845101690969955469273 := by
  unfold tailWord_373617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13626931487456892548639105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9084620991637928365759403 13626931487456892548639105)
  ·
    refine ⟨10220198615592669411479329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13626931487456892548639105 10220198615592669411479329)
    ·
      refine ⟨7665148961694502058609497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10220198615592669411479329 7665148961694502058609497)
      ·
        refine ⟨5748861721270876543957123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7665148961694502058609497 5748861721270876543957123)
        ·
          refine ⟨8623292581906314815935685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748861721270876543957123 8623292581906314815935685)
          ·
            refine ⟨1616867359107434027987941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8623292581906314815935685 1616867359107434027987941)
            ·
              refine ⟨303162629832643880247739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1616867359107434027987941 303162629832643880247739)
              ·
                refine ⟨454743944748965820371609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303162629832643880247739 454743944748965820371609)
                ·
                  refine ⟨341057958561724365278707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454743944748965820371609 341057958561724365278707)
                  ·
                    refine ⟨511586937842586547918061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341057958561724365278707 511586937842586547918061)
                    ·
                      refine ⟨191845101690969955469273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511586937842586547918061 191845101690969955469273)
                      ·
                        rfl

theorem cell23_373617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_373617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373617 prefixEnd_373617 := by exact prefixLift 373617
  have htrace : WordTrace (prefixWord ++ tailWord_373617) baseStart_373617 baseEnd_373617 := by
    simpa [prefixWord, tailWord_373617, baseEnd_373617] using wordTrace_append hprefix tailTrace_373617
  have hstable : (prefixWord ++ tailWord_373617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373617).length < 2 ^ (prefixWord ++ tailWord_373617).sum := by decide
  have hdescent : baseEnd_373617 < baseStart_373617 := by decide
  rcases family_descends (prefixWord ++ tailWord_373617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373623 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_373623 : Nat := 118140960795 + 373623 * 2 ^ 59
def prefixEnd_373623 : Nat := 4983230072969 + 3 ^ 40 * 373623 * 2
def baseEnd_373623 : Nat := 191848182574896931994245

theorem tailTrace_373623 : CollatzResearch.WordTrace tailWord_373623 prefixEnd_373623 191848182574896931994245 := by
  unfold tailWord_373623
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627150325435155573357523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9084766883623437048905015 13627150325435155573357523)
  ·
    refine ⟨20440725488152733360036285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13627150325435155573357523 20440725488152733360036285)
    ·
      refine ⟨7665272058057275010013607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20440725488152733360036285 7665272058057275010013607)
      ·
        refine ⟨11497908087085912515020411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7665272058057275010013607 11497908087085912515020411)
        ·
          refine ⟨17246862130628868772530617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11497908087085912515020411 17246862130628868772530617)
          ·
            refine ⟨12935146597971651579397963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17246862130628868772530617 12935146597971651579397963)
            ·
              refine ⟨19402719896957477369096945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12935146597971651579397963 19402719896957477369096945)
              ·
                refine ⟨14552039922718108026822709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19402719896957477369096945 14552039922718108026822709)
                ·
                  refine ⟨1364253742754822627514629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14552039922718108026822709 1364253742754822627514629)
                  ·
                    refine ⟨255797576766529242658993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1364253742754822627514629 255797576766529242658993)
                    ·
                      refine ⟨191848182574896931994245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255797576766529242658993 191848182574896931994245)
                      ·
                        rfl

theorem cell23_373623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_373623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373623 prefixEnd_373623 := by exact prefixLift 373623
  have htrace : WordTrace (prefixWord ++ tailWord_373623) baseStart_373623 baseEnd_373623 := by
    simpa [prefixWord, tailWord_373623, baseEnd_373623] using wordTrace_append hprefix tailTrace_373623
  have hstable : (prefixWord ++ tailWord_373623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373623).length < 2 ^ (prefixWord ++ tailWord_373623).sum := by decide
  have hdescent : baseEnd_373623 < baseStart_373623 := by decide
  rcases family_descends (prefixWord ++ tailWord_373623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373634 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_373634 : Nat := 118140960795 + 373634 * 2 ^ 59
def prefixEnd_373634 : Nat := 4983230072969 + 3 ^ 40 * 373634 * 2
def baseEnd_373634 : Nat := 191853830862096388956695

theorem tailTrace_373634 : CollatzResearch.WordTrace tailWord_373634 prefixEnd_373634 191853830862096388956695 := by
  unfold tailWord_373634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406887882098826113001989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9085034352263536301338637 3406887882098826113001989)
  ·
    refine ⟨638791477893529896187873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3406887882098826113001989 638791477893529896187873)
    ·
      refine ⟨479093608420147422140905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638791477893529896187873 479093608420147422140905)
      ·
        refine ⟨359320206315110566605679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479093608420147422140905 359320206315110566605679)
        ·
          refine ⟨538980309472665849908519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359320206315110566605679 538980309472665849908519)
          ·
            refine ⟨808470464208998774862779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538980309472665849908519 808470464208998774862779)
            ·
              refine ⟨1212705696313498162294169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808470464208998774862779 1212705696313498162294169)
              ·
                refine ⟨909529272235123621720627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212705696313498162294169 909529272235123621720627)
                ·
                  refine ⟨1364293908352685432580941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909529272235123621720627 1364293908352685432580941)
                  ·
                    refine ⟨511610215632257037217853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364293908352685432580941 511610215632257037217853)
                    ·
                      refine ⟨191853830862096388956695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511610215632257037217853 191853830862096388956695)
                      ·
                        rfl

theorem cell23_373634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_373634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373634 prefixEnd_373634 := by exact prefixLift 373634
  have htrace : WordTrace (prefixWord ++ tailWord_373634) baseStart_373634 baseEnd_373634 := by
    simpa [prefixWord, tailWord_373634, baseEnd_373634] using wordTrace_append hprefix tailTrace_373634
  have hstable : (prefixWord ++ tailWord_373634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373634).length < 2 ^ (prefixWord ++ tailWord_373634).sum := by decide
  have hdescent : baseEnd_373634 < baseStart_373634 := by decide
  rcases family_descends (prefixWord ++ tailWord_373634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373640 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_373640 : Nat := 118140960795 + 373640 * 2 ^ 59
def prefixEnd_373640 : Nat := 4983230072969 + 3 ^ 40 * 373640 * 2
def baseEnd_373640 : Nat := 191856911746023365481667

theorem tailTrace_373640 : CollatzResearch.WordTrace tailWord_373640 prefixEnd_373640 191856911746023365481667 := by
  unfold tailWord_373640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813885183186783738363187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9085180244249044984484249 6813885183186783738363187)
  ·
    refine ⟨10220827774780175607544781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6813885183186783738363187 10220827774780175607544781)
    ·
      refine ⟨3832810415542565852829293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10220827774780175607544781 3832810415542565852829293)
      ·
        refine ⟨1437303905828462194810985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3832810415542565852829293 1437303905828462194810985)
        ·
          refine ⟨1077977929371346646108239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437303905828462194810985 1077977929371346646108239)
          ·
            refine ⟨1616966894057019969162359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077977929371346646108239 1616966894057019969162359)
            ·
              refine ⟨2425450341085529953743539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616966894057019969162359 2425450341085529953743539)
              ·
                refine ⟨3638175511628294930615309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425450341085529953743539 3638175511628294930615309)
                ·
                  refine ⟨1364315816860610598980741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3638175511628294930615309 1364315816860610598980741)
                  ·
                    refine ⟨255809215661364487308889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1364315816860610598980741 255809215661364487308889)
                    ·
                      refine ⟨191856911746023365481667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255809215661364487308889 191856911746023365481667)
                      ·
                        rfl

theorem cell23_373640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_373640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373640 prefixEnd_373640 := by exact prefixLift 373640
  have htrace : WordTrace (prefixWord ++ tailWord_373640) baseStart_373640 baseEnd_373640 := by
    simpa [prefixWord, tailWord_373640, baseEnd_373640] using wordTrace_append hprefix tailTrace_373640
  have hstable : (prefixWord ++ tailWord_373640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373640).length < 2 ^ (prefixWord ++ tailWord_373640).sum := by decide
  have hdescent : baseEnd_373640 < baseStart_373640 := by decide
  rcases family_descends (prefixWord ++ tailWord_373640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373673 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_373673 : Nat := 118140960795 + 373673 * 2 ^ 59
def prefixEnd_373673 : Nat := 4983230072969 + 3 ^ 40 * 373673 * 2
def baseEnd_373673 : Nat := 191873856607621736369015

theorem tailTrace_373673 : CollatzResearch.WordTrace tailWord_373673 prefixEnd_373673 191873856607621736369015 := by
  unfold tailWord_373673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13628973975254014112677673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9085982650169342741785115 13628973975254014112677673)
  ·
    refine ⟨10221730481440510584508255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13628973975254014112677673 10221730481440510584508255)
    ·
      refine ⟨15332595722160765876762383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10221730481440510584508255 15332595722160765876762383)
      ·
        refine ⟨22998893583241148815143575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332595722160765876762383 22998893583241148815143575)
        ·
          refine ⟨34498340374861723222715363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22998893583241148815143575 34498340374861723222715363)
          ·
            refine ⟨51747510562292584834073045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34498340374861723222715363 51747510562292584834073045)
            ·
              refine ⟨1212832278803732457048587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51747510562292584834073045 1212832278803732457048587)
              ·
                refine ⟨1819248418205598685572881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212832278803732457048587 1819248418205598685572881)
                ·
                  refine ⟨1364436313654199014179661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819248418205598685572881 1364436313654199014179661)
                  ·
                    refine ⟨511663617620324630317373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364436313654199014179661 511663617620324630317373)
                    ·
                      refine ⟨191873856607621736369015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511663617620324630317373 191873856607621736369015)
                      ·
                        rfl

theorem cell23_373673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_373673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373673 prefixEnd_373673 := by exact prefixLift 373673
  have htrace : WordTrace (prefixWord ++ tailWord_373673) baseStart_373673 baseEnd_373673 := by
    simpa [prefixWord, tailWord_373673, baseEnd_373673] using wordTrace_append hprefix tailTrace_373673
  have hstable : (prefixWord ++ tailWord_373673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373673).length < 2 ^ (prefixWord ++ tailWord_373673).sum := by decide
  have hdescent : baseEnd_373673 < baseStart_373673 := by decide
  rcases family_descends (prefixWord ++ tailWord_373673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373676 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_373676 : Nat := 118140960795 + 373676 * 2 ^ 59
def prefixEnd_373676 : Nat := 4983230072969 + 3 ^ 40 * 373676 * 2
def baseEnd_373676 : Nat := 63958465683195074877167

theorem tailTrace_373676 : CollatzResearch.WordTrace tailWord_373676 prefixEnd_373676 63958465683195074877167 := by
  unfold tailWord_373676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814541697121572812518441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9086055596162097083357921 6814541697121572812518441)
  ·
    refine ⟨5110906272841179609388831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6814541697121572812518441 5110906272841179609388831)
    ·
      refine ⟨7666359409261769414083247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5110906272841179609388831 7666359409261769414083247)
      ·
        refine ⟨11499539113892654121124871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666359409261769414083247 11499539113892654121124871)
        ·
          refine ⟨17249308670838981181687307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499539113892654121124871 17249308670838981181687307)
          ·
            refine ⟨25873963006258471772530961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249308670838981181687307 25873963006258471772530961)
            ·
              refine ⟨19405472254693853829398221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25873963006258471772530961 19405472254693853829398221)
              ·
                refine ⟨7277052095510195186024333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19405472254693853829398221 7277052095510195186024333)
                ·
                  refine ⟨2728894535816323194759125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7277052095510195186024333 2728894535816323194759125)
                  ·
                    refine ⟨63958465683195074877167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2728894535816323194759125 63958465683195074877167)
                    ·
                      rfl

theorem cell23_373676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_373676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373676 prefixEnd_373676 := by exact prefixLift 373676
  have htrace : WordTrace (prefixWord ++ tailWord_373676) baseStart_373676 baseEnd_373676 := by
    simpa [prefixWord, tailWord_373676, baseEnd_373676] using wordTrace_append hprefix tailTrace_373676
  have hstable : (prefixWord ++ tailWord_373676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373676).length < 2 ^ (prefixWord ++ tailWord_373676).sum := by decide
  have hdescent : baseEnd_373676 < baseStart_373676 := by decide
  rcases family_descends (prefixWord ++ tailWord_373676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373702 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_373702 : Nat := 118140960795 + 373702 * 2 ^ 59
def prefixEnd_373702 : Nat := 4983230072969 + 3 ^ 40 * 373702 * 2
def baseEnd_373702 : Nat := 191888747546602122906383

theorem tailTrace_373702 : CollatzResearch.WordTrace tailWord_373702 prefixEnd_373702 191888747546602122906383 := by
  unfold tailWord_373702
  simp only [CollatzResearch.WordTrace]
  refine ⟨425938490379654752046355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9086687794765968043655573 425938490379654752046355)
  ·
    refine ⟨638907735569482128069533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425938490379654752046355 638907735569482128069533)
    ·
      refine ⟨239590400838555798026075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 638907735569482128069533 239590400838555798026075)
      ·
        refine ⟨359385601257833697039113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239590400838555798026075 359385601257833697039113)
        ·
          refine ⟨269539200943375272779335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359385601257833697039113 269539200943375272779335)
          ·
            refine ⟨404308801415062909169003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269539200943375272779335 404308801415062909169003)
            ·
              refine ⟨606463202122594363753505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404308801415062909169003 606463202122594363753505)
              ·
                refine ⟨454847401591945772815129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606463202122594363753505 454847401591945772815129)
                ·
                  refine ⟨341135551193959329611347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454847401591945772815129 341135551193959329611347)
                  ·
                    refine ⟨511703326790938994417021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341135551193959329611347 511703326790938994417021)
                    ·
                      refine ⟨191888747546602122906383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511703326790938994417021 191888747546602122906383)
                      ·
                        rfl

theorem cell23_373702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_373702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373702 prefixEnd_373702 := by exact prefixLift 373702
  have htrace : WordTrace (prefixWord ++ tailWord_373702) baseStart_373702 baseEnd_373702 := by
    simpa [prefixWord, tailWord_373702, baseEnd_373702] using wordTrace_append hprefix tailTrace_373702
  have hstable : (prefixWord ++ tailWord_373702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373702).length < 2 ^ (prefixWord ++ tailWord_373702).sum := by decide
  have hdescent : baseEnd_373702 < baseStart_373702 := by decide
  rcases family_descends (prefixWord ++ tailWord_373702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373713 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_373713 : Nat := 118140960795 + 373713 * 2 ^ 59
def prefixEnd_373713 : Nat := 4983230072969 + 3 ^ 40 * 373713 * 2
def baseEnd_373713 : Nat := 191894395833801579868831

theorem tailTrace_373713 : CollatzResearch.WordTrace tailWord_373713 prefixEnd_373713 191894395833801579868831 := by
  unfold tailWord_373713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13630432895109100944133793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9086955263406067296089195 13630432895109100944133793)
  ·
    refine ⟨10222824671331825708100345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13630432895109100944133793 10222824671331825708100345)
    ·
      refine ⟨7667118503498869281075259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10222824671331825708100345 7667118503498869281075259)
      ·
        refine ⟨11500677755248303921612889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667118503498869281075259 11500677755248303921612889)
        ·
          refine ⟨8625508316436227941209667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11500677755248303921612889 8625508316436227941209667)
          ·
            refine ⟨12938262474654341911814501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8625508316436227941209667 12938262474654341911814501)
            ·
              refine ⟨2425924213997689108465219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12938262474654341911814501 2425924213997689108465219)
              ·
                refine ⟨3638886320996533662697829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425924213997689108465219 3638886320996533662697829)
                ·
                  refine ⟨682291185186850061755843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3638886320996533662697829 682291185186850061755843)
                  ·
                    refine ⟨1023436777780275092633765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 682291185186850061755843 1023436777780275092633765)
                    ·
                      refine ⟨191894395833801579868831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1023436777780275092633765 191894395833801579868831)
                      ·
                        rfl

theorem cell23_373713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_373713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373713 prefixEnd_373713 := by exact prefixLift 373713
  have htrace : WordTrace (prefixWord ++ tailWord_373713) baseStart_373713 baseEnd_373713 := by
    simpa [prefixWord, tailWord_373713, baseEnd_373713] using wordTrace_append hprefix tailTrace_373713
  have hstable : (prefixWord ++ tailWord_373713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373713).length < 2 ^ (prefixWord ++ tailWord_373713).sum := by decide
  have hdescent : baseEnd_373713 < baseStart_373713 := by decide
  rcases family_descends (prefixWord ++ tailWord_373713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373831 : List Nat := [1, 1, 4, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_373831 : Nat := 118140960795 + 373831 * 2 ^ 59
def prefixEnd_373831 : Nat := 4983230072969 + 3 ^ 40 * 373831 * 2
def baseEnd_373831 : Nat := 191954986551032118193289

theorem tailTrace_373831 : CollatzResearch.WordTrace tailWord_373831 prefixEnd_373831 191954986551032118193289 := by
  unfold tailWord_373831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634736708681607096929347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9089824472454404731286231 13634736708681607096929347)
  ·
    refine ⟨20452105063022410645394021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13634736708681607096929347 20452105063022410645394021)
    ·
      refine ⟨3834769699316701996011379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20452105063022410645394021 3834769699316701996011379)
      ·
        refine ⟨5752154548975052994017069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834769699316701996011379 5752154548975052994017069)
        ·
          refine ⟨2157057955865644872756401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5752154548975052994017069 2157057955865644872756401)
          ·
            refine ⟨1617793466899233654567301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157057955865644872756401 1617793466899233654567301)
            ·
              refine ⟨303336275043606310231369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1617793466899233654567301 303336275043606310231369)
              ·
                refine ⟨227502206282704732673527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303336275043606310231369 227502206282704732673527)
                ·
                  refine ⟨341253309424057099010291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227502206282704732673527 341253309424057099010291)
                  ·
                    refine ⟨511879964136085648515437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341253309424057099010291 511879964136085648515437)
                    ·
                      refine ⟨191954986551032118193289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 511879964136085648515437 191954986551032118193289)
                      ·
                        rfl

theorem cell23_373831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_373831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373831 prefixEnd_373831 := by exact prefixLift 373831
  have htrace : WordTrace (prefixWord ++ tailWord_373831) baseStart_373831 baseEnd_373831 := by
    simpa [prefixWord, tailWord_373831, baseEnd_373831] using wordTrace_append hprefix tailTrace_373831
  have hstable : (prefixWord ++ tailWord_373831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373831).length < 2 ^ (prefixWord ++ tailWord_373831).sum := by decide
  have hdescent : baseEnd_373831 < baseStart_373831 := by decide
  rcases family_descends (prefixWord ++ tailWord_373831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373833 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_373833 : Nat := 118140960795 + 373833 * 2 ^ 59
def prefixEnd_373833 : Nat := 4983230072969 + 3 ^ 40 * 373833 * 2
def baseEnd_373833 : Nat := 191956013512341110368279

theorem tailTrace_373833 : CollatzResearch.WordTrace tailWord_373833 prefixEnd_373833 191956013512341110368279 := by
  unfold tailWord_373833
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634809654674361438502153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9089873103116240959001435 13634809654674361438502153)
  ·
    refine ⟨10226107241005771078876615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13634809654674361438502153 10226107241005771078876615)
    ·
      refine ⟨15339160861508656618314923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10226107241005771078876615 15339160861508656618314923)
      ·
        refine ⟨23008741292262984927472385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15339160861508656618314923 23008741292262984927472385)
        ·
          refine ⟨17256555969197238695604289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23008741292262984927472385 17256555969197238695604289)
          ·
            refine ⟨12942416976897929021703217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17256555969197238695604289 12942416976897929021703217)
            ·
              refine ⟨9706812732673446766277413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12942416976897929021703217 9706812732673446766277413)
              ·
                refine ⟨1820027387376271268677015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9706812732673446766277413 1820027387376271268677015)
                ·
                  refine ⟨2730041081064406903015523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820027387376271268677015 2730041081064406903015523)
                  ·
                    refine ⟨4095061621596610354523285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730041081064406903015523 4095061621596610354523285)
                    ·
                      refine ⟨191956013512341110368279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4095061621596610354523285 191956013512341110368279)
                      ·
                        rfl

theorem cell23_373833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_373833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373833 prefixEnd_373833 := by exact prefixLift 373833
  have htrace : WordTrace (prefixWord ++ tailWord_373833) baseStart_373833 baseEnd_373833 := by
    simpa [prefixWord, tailWord_373833, baseEnd_373833] using wordTrace_append hprefix tailTrace_373833
  have hstable : (prefixWord ++ tailWord_373833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373833).length < 2 ^ (prefixWord ++ tailWord_373833).sum := by decide
  have hdescent : baseEnd_373833 < baseStart_373833 := by decide
  rcases family_descends (prefixWord ++ tailWord_373833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373837 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_373837 : Nat := 118140960795 + 373837 * 2 ^ 59
def prefixEnd_373837 : Nat := 4983230072969 + 3 ^ 40 * 373837 * 2
def baseEnd_373837 : Nat := 191958067434959094718261

theorem tailTrace_373837 : CollatzResearch.WordTrace tailWord_373837 prefixEnd_373837 191958067434959094718261 := by
  unfold tailWord_373837
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634955546659870121647765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9089970364439913414431843 13634955546659870121647765)
  ·
    refine ⟨639138541249681411952239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13634955546659870121647765 639138541249681411952239)
    ·
      refine ⟨958707811874522117928359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639138541249681411952239 958707811874522117928359)
      ·
        refine ⟨1438061717811783176892539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958707811874522117928359 1438061717811783176892539)
        ·
          refine ⟨2157092576717674765338809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438061717811783176892539 2157092576717674765338809)
          ·
            refine ⟨1617819432538256074004107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157092576717674765338809 1617819432538256074004107)
            ·
              refine ⟨2426729148807384111006161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617819432538256074004107 2426729148807384111006161)
              ·
                refine ⟨1820046861605538083254621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426729148807384111006161 1820046861605538083254621)
                ·
                  refine ⟨682517573102076781220483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1820046861605538083254621 682517573102076781220483)
                  ·
                    refine ⟨1023776359653115171830725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 682517573102076781220483 1023776359653115171830725)
                    ·
                      refine ⟨191958067434959094718261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1023776359653115171830725 191958067434959094718261)
                      ·
                        rfl

theorem cell23_373837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_373837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373837 prefixEnd_373837 := by exact prefixLift 373837
  have htrace : WordTrace (prefixWord ++ tailWord_373837) baseStart_373837 baseEnd_373837 := by
    simpa [prefixWord, tailWord_373837, baseEnd_373837] using wordTrace_append hprefix tailTrace_373837
  have hstable : (prefixWord ++ tailWord_373837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373837).length < 2 ^ (prefixWord ++ tailWord_373837).sum := by decide
  have hdescent : baseEnd_373837 < baseStart_373837 := by decide
  rcases family_descends (prefixWord ++ tailWord_373837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373871 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 1, 2, 2]
def baseStart_373871 : Nat := 118140960795 + 373871 * 2 ^ 59
def prefixEnd_373871 : Nat := 4983230072969 + 3 ^ 40 * 373871 * 2
def baseEnd_373871 : Nat := 191975525777211961693105

theorem tailTrace_373871 : CollatzResearch.WordTrace tailWord_373871 prefixEnd_373871 191975525777211961693105 := by
  unfold tailWord_373871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636195628536693928385467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9090797085691129285590311 13636195628536693928385467)
  ·
    refine ⟨20454293442805040892578201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13636195628536693928385467 20454293442805040892578201)
    ·
      refine ⟨15340720082103780669433651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20454293442805040892578201 15340720082103780669433651)
      ·
        refine ⟨23011080123155671004150477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15340720082103780669433651 23011080123155671004150477)
        ·
          refine ⟨8629155046183376626556429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23011080123155671004150477 8629155046183376626556429)
          ·
            refine ⟨3235933142318766234958661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8629155046183376626556429 3235933142318766234958661)
            ·
              refine ⟨606737464184768669054749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3235933142318766234958661 606737464184768669054749)
              ·
                refine ⟨227526549069288250895531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 606737464184768669054749 227526549069288250895531)
                ·
                  refine ⟨341289823603932376343297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227526549069288250895531 341289823603932376343297)
                  ·
                    refine ⟨255967367702949282257473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341289823603932376343297 255967367702949282257473)
                    ·
                      refine ⟨191975525777211961693105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 255967367702949282257473 191975525777211961693105)
                      ·
                        rfl

theorem cell23_373871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 2, 2].length) (baseStart_373871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373871 prefixEnd_373871 := by exact prefixLift 373871
  have htrace : WordTrace (prefixWord ++ tailWord_373871) baseStart_373871 baseEnd_373871 := by
    simpa [prefixWord, tailWord_373871, baseEnd_373871] using wordTrace_append hprefix tailTrace_373871
  have hstable : (prefixWord ++ tailWord_373871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373871).length < 2 ^ (prefixWord ++ tailWord_373871).sum := by decide
  have hdescent : baseEnd_373871 < baseStart_373871 := by decide
  rcases family_descends (prefixWord ++ tailWord_373871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373873 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_373873 : Nat := 118140960795 + 373873 * 2 ^ 59
def prefixEnd_373873 : Nat := 4983230072969 + 3 ^ 40 * 373873 * 2
def baseEnd_373873 : Nat := 63992184246173651289365

theorem tailTrace_373873 : CollatzResearch.WordTrace tailWord_373873 prefixEnd_373873 63992184246173651289365 := by
  unfold tailWord_373873
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636268574529448269958273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9090845716352965513305515 13636268574529448269958273)
  ·
    refine ⟨10227201430897086202468705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13636268574529448269958273 10227201430897086202468705)
    ·
      refine ⟨7670401073172814651851529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10227201430897086202468705 7670401073172814651851529)
      ·
        refine ⟨5752800804879610988888647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7670401073172814651851529 5752800804879610988888647)
        ·
          refine ⟨8629201207319416483332971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752800804879610988888647 8629201207319416483332971)
          ·
            refine ⟨12943801810979124724999457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629201207319416483332971 12943801810979124724999457)
            ·
              refine ⟨9707851358234343543749593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12943801810979124724999457 9707851358234343543749593)
              ·
                refine ⟨7280888518675757657812195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9707851358234343543749593 7280888518675757657812195)
                ·
                  refine ⟨10921332778013636486718293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7280888518675757657812195 10921332778013636486718293)
                  ·
                    refine ⟨63992184246173651289365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 10921332778013636486718293 63992184246173651289365)
                    ·
                      rfl

theorem cell23_373873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_373873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373873 prefixEnd_373873 := by exact prefixLift 373873
  have htrace : WordTrace (prefixWord ++ tailWord_373873) baseStart_373873 baseEnd_373873 := by
    simpa [prefixWord, tailWord_373873, baseEnd_373873] using wordTrace_append hprefix tailTrace_373873
  have hstable : (prefixWord ++ tailWord_373873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373873).length < 2 ^ (prefixWord ++ tailWord_373873).sum := by decide
  have hdescent : baseEnd_373873 < baseStart_373873 := by decide
  rcases family_descends (prefixWord ++ tailWord_373873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373877 : List Nat := [1, 3, 4, 3, 1, 1, 10]
def baseStart_373877 : Nat := 118140960795 + 373877 * 2 ^ 59
def prefixEnd_373877 : Nat := 4983230072969 + 3 ^ 40 * 373877 * 2
def baseEnd_373877 : Nat := 2370106255075789360717

theorem tailTrace_373877 : CollatzResearch.WordTrace tailWord_373877 prefixEnd_373877 2370106255075789360717 := by
  unfold tailWord_373877
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636414466514956953103885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9090942977676637968735923 13636414466514956953103885)
  ·
    refine ⟨5113655424943108857413957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13636414466514956953103885 5113655424943108857413957)
    ·
      refine ⟨958810392176832910765117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5113655424943108857413957 958810392176832910765117)
      ·
        refine ⟨359553897066312341536919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 958810392176832910765117 359553897066312341536919)
        ·
          refine ⟨539330845599468512305379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359553897066312341536919 539330845599468512305379)
          ·
            refine ⟨808996268399202768458069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539330845599468512305379 808996268399202768458069)
            ·
              refine ⟨2370106255075789360717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 808996268399202768458069 2370106255075789360717)
              ·
                rfl

theorem cell23_373877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 10].length) (baseStart_373877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373877 prefixEnd_373877 := by exact prefixLift 373877
  have htrace : WordTrace (prefixWord ++ tailWord_373877) baseStart_373877 baseEnd_373877 := by
    simpa [prefixWord, tailWord_373877, baseEnd_373877] using wordTrace_append hprefix tailTrace_373877
  have hstable : (prefixWord ++ tailWord_373877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373877).length < 2 ^ (prefixWord ++ tailWord_373877).sum := by decide
  have hdescent : baseEnd_373877 < baseStart_373877 := by decide
  rcases family_descends (prefixWord ++ tailWord_373877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373881 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 2, 4]
def baseStart_373881 : Nat := 118140960795 + 373881 * 2 ^ 59
def prefixEnd_373881 : Nat := 4983230072969 + 3 ^ 40 * 373881 * 2
def baseEnd_373881 : Nat := 63993553527918974189353

theorem tailTrace_373881 : CollatzResearch.WordTrace tailWord_373881 prefixEnd_373881 63993553527918974189353 := by
  unfold tailWord_373881
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636560358500465636249497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9091040239000310424166331 13636560358500465636249497)
  ·
    refine ⟨10227420268875349227187123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13636560358500465636249497 10227420268875349227187123)
    ·
      refine ⟨15341130403313023840780685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10227420268875349227187123 15341130403313023840780685)
      ·
        refine ⟨5752923901242383940292757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15341130403313023840780685 5752923901242383940292757)
        ·
          refine ⟨269668307870736747201223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5752923901242383940292757 269668307870736747201223)
          ·
            refine ⟨404502461806105120801835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269668307870736747201223 404502461806105120801835)
            ·
              refine ⟨606753692709157681202753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404502461806105120801835 606753692709157681202753)
              ·
                refine ⟨455065269531868260902065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606753692709157681202753 455065269531868260902065)
                ·
                  refine ⟨341298952148901195676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455065269531868260902065 341298952148901195676549)
                  ·
                    refine ⟨63993553527918974189353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341298952148901195676549 63993553527918974189353)
                    ·
                      rfl

theorem cell23_373881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_373881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373881 prefixEnd_373881 := by exact prefixLift 373881
  have htrace : WordTrace (prefixWord ++ tailWord_373881) baseStart_373881 baseEnd_373881 := by
    simpa [prefixWord, tailWord_373881, baseEnd_373881] using wordTrace_append hprefix tailTrace_373881
  have hstable : (prefixWord ++ tailWord_373881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373881).length < 2 ^ (prefixWord ++ tailWord_373881).sum := by decide
  have hdescent : baseEnd_373881 < baseStart_373881 := by decide
  rcases family_descends (prefixWord ++ tailWord_373881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373903 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 8]
def baseStart_373903 : Nat := 118140960795 + 373903 * 2 ^ 59
def prefixEnd_373903 : Nat := 4983230072969 + 3 ^ 40 * 373903 * 2
def baseEnd_373903 : Nat := 63997319052718612164319

theorem tailTrace_373903 : CollatzResearch.WordTrace tailWord_373903 prefixEnd_373903 63997319052718612164319 := by
  unfold tailWord_373903
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637362764420763393550363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9091575176280508929033575 13637362764420763393550363)
  ·
    refine ⟨20456044146631145090325545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13637362764420763393550363 20456044146631145090325545)
    ·
      refine ⟨15342033109973358817744159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20456044146631145090325545 15342033109973358817744159)
      ·
        refine ⟨23013049664960038226616239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342033109973358817744159 23013049664960038226616239)
        ·
          refine ⟨34519574497440057339924359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23013049664960038226616239 34519574497440057339924359)
          ·
            refine ⟨51779361746160086009886539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34519574497440057339924359 51779361746160086009886539)
            ·
              refine ⟨77669042619240129014829809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51779361746160086009886539 77669042619240129014829809)
              ·
                refine ⟨58251781964430096761122357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77669042619240129014829809 58251781964430096761122357)
                ·
                  refine ⟨5461104559165321571355221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58251781964430096761122357 5461104559165321571355221)
                  ·
                    refine ⟨63997319052718612164319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5461104559165321571355221 63997319052718612164319)
                    ·
                      rfl

theorem cell23_373903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_373903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373903 prefixEnd_373903 := by exact prefixLift 373903
  have htrace : WordTrace (prefixWord ++ tailWord_373903) baseStart_373903 baseEnd_373903 := by
    simpa [prefixWord, tailWord_373903, baseEnd_373903] using wordTrace_append hprefix tailTrace_373903
  have hstable : (prefixWord ++ tailWord_373903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373903).length < 2 ^ (prefixWord ++ tailWord_373903).sum := by decide
  have hdescent : baseEnd_373903 < baseStart_373903 := by decide
  rcases family_descends (prefixWord ++ tailWord_373903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373922 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_373922 : Nat := 118140960795 + 373922 * 2 ^ 59
def prefixEnd_373922 : Nat := 4983230072969 + 3 ^ 40 * 373922 * 2
def baseEnd_373922 : Nat := 192001713290591262155371

theorem tailTrace_373922 : CollatzResearch.WordTrace tailWord_373922 prefixEnd_373922 192001713290591262155371 := by
  unfold tailWord_373922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409513937837982409623005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9092037167567953092328013 3409513937837982409623005)
  ·
    refine ⟨1278567726689243403608627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3409513937837982409623005 1278567726689243403608627)
    ·
      refine ⟨1917851590033865105412941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278567726689243403608627 1917851590033865105412941)
      ·
        refine ⟨719194346262699414529853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1917851590033865105412941 719194346262699414529853)
        ·
          refine ⟨269697879848512280448695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 719194346262699414529853 269697879848512280448695)
          ·
            refine ⟨404546819772768420673043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269697879848512280448695 404546819772768420673043)
            ·
              refine ⟨606820229659152631009565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404546819772768420673043 606820229659152631009565)
              ·
                refine ⟨227557586122182236628587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 606820229659152631009565 227557586122182236628587)
                ·
                  refine ⟨341336379183273354942881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227557586122182236628587 341336379183273354942881)
                  ·
                    refine ⟨256002284387455016207161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341336379183273354942881 256002284387455016207161)
                    ·
                      refine ⟨192001713290591262155371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256002284387455016207161 192001713290591262155371)
                      ·
                        rfl

theorem cell23_373922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_373922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_373922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_373922 prefixEnd_373922 := by exact prefixLift 373922
  have htrace : WordTrace (prefixWord ++ tailWord_373922) baseStart_373922 baseEnd_373922 := by
    simpa [prefixWord, tailWord_373922, baseEnd_373922] using wordTrace_append hprefix tailTrace_373922
  have hstable : (prefixWord ++ tailWord_373922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373922).length < 2 ^ (prefixWord ++ tailWord_373922).sum := by decide
  have hdescent : baseEnd_373922 < baseStart_373922 := by decide
  rcases family_descends (prefixWord ++ tailWord_373922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374000 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_374000 : Nat := 118140960795 + 374000 * 2 ^ 59
def prefixEnd_374000 : Nat := 4983230072969 + 3 ^ 40 * 374000 * 2
def baseEnd_374000 : Nat := 192041764781641956980011

theorem tailTrace_374000 : CollatzResearch.WordTrace tailWord_374000 prefixEnd_374000 192041764781641956980011 := by
  unfold tailWord_374000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820450322534674479915727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9093933763379565973220969 6820450322534674479915727)
  ·
    refine ⟨10230675483802011719873591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6820450322534674479915727 10230675483802011719873591)
    ·
      refine ⟨15346013225703017579810387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230675483802011719873591 15346013225703017579810387)
      ·
        refine ⟨23019019838554526369715581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346013225703017579810387 23019019838554526369715581)
        ·
          refine ⟨8632132439457947388643343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23019019838554526369715581 8632132439457947388643343)
          ·
            refine ⟨12948198659186921082965015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8632132439457947388643343 12948198659186921082965015)
            ·
              refine ⟨19422297988780381624447523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12948198659186921082965015 19422297988780381624447523)
              ·
                refine ⟨29133446983170572436671285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19422297988780381624447523 29133446983170572436671285)
                ·
                  refine ⟨2731260654672241165937933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29133446983170572436671285 2731260654672241165937933)
                  ·
                    refine ⟨1024222745502090437226725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731260654672241165937933 1024222745502090437226725)
                    ·
                      refine ⟨192041764781641956980011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1024222745502090437226725 192041764781641956980011)
                      ·
                        rfl

theorem cell23_374000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_374000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374000 prefixEnd_374000 := by exact prefixLift 374000
  have htrace : WordTrace (prefixWord ++ tailWord_374000) baseStart_374000 baseEnd_374000 := by
    simpa [prefixWord, tailWord_374000, baseEnd_374000] using wordTrace_append hprefix tailTrace_374000
  have hstable : (prefixWord ++ tailWord_374000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374000).length < 2 ^ (prefixWord ++ tailWord_374000).sum := by decide
  have hdescent : baseEnd_374000 < baseStart_374000 := by decide
  rcases family_descends (prefixWord ++ tailWord_374000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374027 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 5, 4]
def baseStart_374027 : Nat := 118140960795 + 374027 * 2 ^ 59
def prefixEnd_374027 : Nat := 4983230072969 + 3 ^ 40 * 374027 * 2
def baseEnd_374027 : Nat := 64018542919771117114129

theorem tailTrace_374027 : CollatzResearch.WordTrace tailWord_374027 prefixEnd_374027 64018542919771117114129 := by
  unfold tailWord_374027
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641885415971532571064335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9094590277314355047376223 13641885415971532571064335)
  ·
    refine ⟨20462828123957298856596503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13641885415971532571064335 20462828123957298856596503)
    ·
      refine ⟨30694242185935948284894755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20462828123957298856596503 30694242185935948284894755)
      ·
        refine ⟨46041363278903922427342133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30694242185935948284894755 46041363278903922427342133)
        ·
          refine ⟨4316377807397242727563325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46041363278903922427342133 4316377807397242727563325)
          ·
            refine ⟨1618641677773966022836247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4316377807397242727563325 1618641677773966022836247)
            ·
              refine ⟨2427962516660949034254371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618641677773966022836247 2427962516660949034254371)
              ·
                refine ⟨3641943774991423551381557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427962516660949034254371 3641943774991423551381557)
                ·
                  refine ⟨341432228905445957942021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641943774991423551381557 341432228905445957942021)
                  ·
                    refine ⟨64018542919771117114129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341432228905445957942021 64018542919771117114129)
                    ·
                      rfl

theorem cell23_374027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 4].length) (baseStart_374027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374027 prefixEnd_374027 := by exact prefixLift 374027
  have htrace : WordTrace (prefixWord ++ tailWord_374027) baseStart_374027 baseEnd_374027 := by
    simpa [prefixWord, tailWord_374027, baseEnd_374027] using wordTrace_append hprefix tailTrace_374027
  have hstable : (prefixWord ++ tailWord_374027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374027).length < 2 ^ (prefixWord ++ tailWord_374027).sum := by decide
  have hdescent : baseEnd_374027 < baseStart_374027 := by decide
  rcases family_descends (prefixWord ++ tailWord_374027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374061 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_374061 : Nat := 118140960795 + 374061 * 2 ^ 59
def prefixEnd_374061 : Nat := 4983230072969 + 3 ^ 40 * 374061 * 2
def baseEnd_374061 : Nat := 64024362367188739439077

theorem tailTrace_374061 : CollatzResearch.WordTrace tailWord_374061 prefixEnd_374061 64024362367188739439077 := by
  unfold tailWord_374061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13643125497848356377802037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9095416998565570918534691 13643125497848356377802037)
  ·
    refine ⟨1279043015423283410418941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13643125497848356377802037 1279043015423283410418941)
    ·
      refine ⟨479641130783731278907103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1279043015423283410418941 479641130783731278907103)
      ·
        refine ⟨719461696175596918360655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479641130783731278907103 719461696175596918360655)
        ·
          refine ⟨1079192544263395377540983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719461696175596918360655 1079192544263395377540983)
          ·
            refine ⟨1618788816395093066311475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079192544263395377540983 1618788816395093066311475)
            ·
              refine ⟨2428183224592639599467213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618788816395093066311475 2428183224592639599467213)
              ·
                refine ⟨910568709222239849800205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2428183224592639599467213 910568709222239849800205)
                ·
                  refine ⟨341463265958339943675077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910568709222239849800205 341463265958339943675077)
                  ·
                    refine ⟨64024362367188739439077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341463265958339943675077 64024362367188739439077)
                    ·
                      rfl

theorem cell23_374061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_374061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374061 prefixEnd_374061 := by exact prefixLift 374061
  have htrace : WordTrace (prefixWord ++ tailWord_374061) baseStart_374061 baseEnd_374061 := by
    simpa [prefixWord, tailWord_374061, baseEnd_374061] using wordTrace_append hprefix tailTrace_374061
  have hstable : (prefixWord ++ tailWord_374061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374061).length < 2 ^ (prefixWord ++ tailWord_374061).sum := by decide
  have hdescent : baseEnd_374061 < baseStart_374061 := by decide
  rcases family_descends (prefixWord ++ tailWord_374061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374074 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_374074 : Nat := 118140960795 + 374074 * 2 ^ 59
def prefixEnd_374074 : Nat := 4983230072969 + 3 ^ 40 * 374074 * 2
def baseEnd_374074 : Nat := 21342195816674963050519

theorem tailTrace_374074 : CollatzResearch.WordTrace tailWord_374074 prefixEnd_374074 21342195816674963050519 := by
  unfold tailWord_374074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410899911700314899506319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9095733097867506398683517 3410899911700314899506319)
  ·
    refine ⟨5116349867550472349259479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3410899911700314899506319 5116349867550472349259479)
    ·
      refine ⟨7674524801325708523889219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5116349867550472349259479 7674524801325708523889219)
      ·
        refine ⟨11511787201988562785833829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674524801325708523889219 11511787201988562785833829)
        ·
          refine ⟨2158460100372855522343843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11511787201988562785833829 2158460100372855522343843)
          ·
            refine ⟨3237690150559283283515765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158460100372855522343843 3237690150559283283515765)
            ·
              refine ⟨303533451614932807829603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3237690150559283283515765 303533451614932807829603)
              ·
                refine ⟨455300177422399211744405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303533451614932807829603 455300177422399211744405)
                ·
                  refine ⟨21342195816674963050519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 455300177422399211744405 21342195816674963050519)
                  ·
                    rfl

theorem cell23_374074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_374074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374074 prefixEnd_374074 := by exact prefixLift 374074
  have htrace : WordTrace (prefixWord ++ tailWord_374074) baseStart_374074 baseEnd_374074 := by
    simpa [prefixWord, tailWord_374074, baseEnd_374074] using wordTrace_append hprefix tailTrace_374074
  have hstable : (prefixWord ++ tailWord_374074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374074).length < 2 ^ (prefixWord ++ tailWord_374074).sum := by decide
  have hdescent : baseEnd_374074 < baseStart_374074 := by decide
  rcases family_descends (prefixWord ++ tailWord_374074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374094 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_374094 : Nat := 118140960795 + 374094 * 2 ^ 59
def prefixEnd_374094 : Nat := 4983230072969 + 3 ^ 40 * 374094 * 2
def baseEnd_374094 : Nat := 192090031963164589204579

theorem tailTrace_374094 : CollatzResearch.WordTrace tailWord_374094 prefixEnd_374094 192090031963164589204579 := by
  unfold tailWord_374094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705541138341100376719167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9096219404485868675835557 1705541138341100376719167)
  ·
    refine ⟨2558311707511650565078751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705541138341100376719167 2558311707511650565078751)
    ·
      refine ⟨3837467561267475847618127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558311707511650565078751 3837467561267475847618127)
      ·
        refine ⟨5756201341901213771427191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837467561267475847618127 5756201341901213771427191)
        ·
          refine ⟨8634302012851820657140787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756201341901213771427191 8634302012851820657140787)
          ·
            refine ⟨12951453019277730985711181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8634302012851820657140787 12951453019277730985711181)
            ·
              refine ⟨4856794882229149119641693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12951453019277730985711181 4856794882229149119641693)
              ·
                refine ⟨1821298080835930919865635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4856794882229149119641693 1821298080835930919865635)
                ·
                  refine ⟨2731947121253896379798453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821298080835930919865635 2731947121253896379798453)
                  ·
                    refine ⟨256120042617552785606105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2731947121253896379798453 256120042617552785606105)
                    ·
                      refine ⟨192090031963164589204579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256120042617552785606105 192090031963164589204579)
                      ·
                        rfl

theorem cell23_374094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_374094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374094 prefixEnd_374094 := by exact prefixLift 374094
  have htrace : WordTrace (prefixWord ++ tailWord_374094) baseStart_374094 baseEnd_374094 := by
    simpa [prefixWord, tailWord_374094, baseEnd_374094] using wordTrace_append hprefix tailTrace_374094
  have hstable : (prefixWord ++ tailWord_374094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374094).length < 2 ^ (prefixWord ++ tailWord_374094).sum := by decide
  have hdescent : baseEnd_374094 < baseStart_374094 := by decide
  rcases family_descends (prefixWord ++ tailWord_374094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374127 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_374127 : Nat := 118140960795 + 374127 * 2 ^ 59
def prefixEnd_374127 : Nat := 4983230072969 + 3 ^ 40 * 374127 * 2
def baseEnd_374127 : Nat := 192106976824762960091927

theorem tailTrace_374127 : CollatzResearch.WordTrace tailWord_374127 prefixEnd_374127 192106976824762960091927 := by
  unfold tailWord_374127
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645532715609249649704635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9097021810406166433136423 13645532715609249649704635)
  ·
    refine ⟨20468299073413874474556953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13645532715609249649704635 20468299073413874474556953)
    ·
      refine ⟨15351224305060405855917715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20468299073413874474556953 15351224305060405855917715)
      ·
        refine ⟨23026836457590608783876573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15351224305060405855917715 23026836457590608783876573)
        ·
          refine ⟨8635063671596478293953715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23026836457590608783876573 8635063671596478293953715)
          ·
            refine ⟨12952595507394717440930573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635063671596478293953715 12952595507394717440930573)
            ·
              refine ⟨4857223315273019040348965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12952595507394717440930573 4857223315273019040348965)
              ·
                refine ⟨910729371613691070065431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4857223315273019040348965 910729371613691070065431)
                ·
                  refine ⟨1366094057420536605098147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910729371613691070065431 1366094057420536605098147)
                  ·
                    refine ⟨2049141086130804907647221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366094057420536605098147 2049141086130804907647221)
                    ·
                      refine ⟨192106976824762960091927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2049141086130804907647221 192106976824762960091927)
                      ·
                        rfl

theorem cell23_374127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_374127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374127 prefixEnd_374127 := by exact prefixLift 374127
  have htrace : WordTrace (prefixWord ++ tailWord_374127) baseStart_374127 baseEnd_374127 := by
    simpa [prefixWord, tailWord_374127, baseEnd_374127] using wordTrace_append hprefix tailTrace_374127
  have hstable : (prefixWord ++ tailWord_374127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374127).length < 2 ^ (prefixWord ++ tailWord_374127).sum := by decide
  have hdescent : baseEnd_374127 < baseStart_374127 := by decide
  rcases family_descends (prefixWord ++ tailWord_374127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374137 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_374137 : Nat := 118140960795 + 374137 * 2 ^ 59
def prefixEnd_374137 : Nat := 4983230072969 + 3 ^ 40 * 374137 * 2
def baseEnd_374137 : Nat := 192112111631307920966881

theorem tailTrace_374137 : CollatzResearch.WordTrace tailWord_374137 prefixEnd_374137 192112111631307920966881 := by
  unfold tailWord_374137
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645897445573021357568665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9097264963715347571712443 13645897445573021357568665)
  ·
    refine ⟨10234423084179766018176499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13645897445573021357568665 10234423084179766018176499)
    ·
      refine ⟨15351634626269649027264749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10234423084179766018176499 15351634626269649027264749)
      ·
        refine ⟨5756862984851118385224281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15351634626269649027264749 5756862984851118385224281)
        ·
          refine ⟨4317647238638338788918211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756862984851118385224281 4317647238638338788918211)
          ·
            refine ⟨6476470857957508183377317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317647238638338788918211 6476470857957508183377317)
            ·
              refine ⟨1214338285867032784383247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6476470857957508183377317 1214338285867032784383247)
              ·
                refine ⟨1821507428800549176574871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214338285867032784383247 1821507428800549176574871)
                ·
                  refine ⟨2732261143200823764862307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821507428800549176574871 2732261143200823764862307)
                  ·
                    refine ⟨4098391714801235647293461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732261143200823764862307 4098391714801235647293461)
                    ·
                      refine ⟨192112111631307920966881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4098391714801235647293461 192112111631307920966881)
                      ·
                        rfl

theorem cell23_374137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_374137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374137 prefixEnd_374137 := by exact prefixLift 374137
  have htrace : WordTrace (prefixWord ++ tailWord_374137) baseStart_374137 baseEnd_374137 := by
    simpa [prefixWord, tailWord_374137, baseEnd_374137] using wordTrace_append hprefix tailTrace_374137
  have hstable : (prefixWord ++ tailWord_374137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374137).length < 2 ^ (prefixWord ++ tailWord_374137).sum := by decide
  have hdescent : baseEnd_374137 < baseStart_374137 := by decide
  rcases family_descends (prefixWord ++ tailWord_374137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374141 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_374141 : Nat := 118140960795 + 374141 * 2 ^ 59
def prefixEnd_374141 : Nat := 4983230072969 + 3 ^ 40 * 374141 * 2
def baseEnd_374141 : Nat := 192114165553925905316863

theorem tailTrace_374141 : CollatzResearch.WordTrace tailWord_374141 prefixEnd_374141 192114165553925905316863 := by
  unfold tailWord_374141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646043337558530040714277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9097362225039020027142851 13646043337558530040714277)
  ·
    refine ⟨2558633125792224382633927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13646043337558530040714277 2558633125792224382633927)
    ·
      refine ⟨3837949688688336573950891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558633125792224382633927 3837949688688336573950891)
      ·
        refine ⟨5756924533032504860926337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837949688688336573950891 5756924533032504860926337)
        ·
          refine ⟨4317693399774378645694753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756924533032504860926337 4317693399774378645694753)
          ·
            refine ⟨3238270049830783984271065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317693399774378645694753 3238270049830783984271065)
            ·
              refine ⟨2428702537373087988203299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3238270049830783984271065 2428702537373087988203299)
              ·
                refine ⟨3643053806059631982304949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428702537373087988203299 3643053806059631982304949)
                ·
                  refine ⟨341536294318090498341089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3643053806059631982304949 341536294318090498341089)
                  ·
                    refine ⟨256152220738567873755817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341536294318090498341089 256152220738567873755817)
                    ·
                      refine ⟨192114165553925905316863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256152220738567873755817 192114165553925905316863)
                      ·
                        rfl

theorem cell23_374141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_374141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374141 prefixEnd_374141 := by exact prefixLift 374141
  have htrace : WordTrace (prefixWord ++ tailWord_374141) baseStart_374141 baseEnd_374141 := by
    simpa [prefixWord, tailWord_374141, baseEnd_374141] using wordTrace_append hprefix tailTrace_374141
  have hstable : (prefixWord ++ tailWord_374141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374141).length < 2 ^ (prefixWord ++ tailWord_374141).sum := by decide
  have hdescent : baseEnd_374141 < baseStart_374141 := by decide
  rcases family_descends (prefixWord ++ tailWord_374141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374147 : List Nat := [1, 1, 1, 3, 5, 1, 2, 9]
def baseStart_374147 : Nat := 118140960795 + 374147 * 2 ^ 59
def prefixEnd_374147 : Nat := 4983230072969 + 3 ^ 40 * 374147 * 2
def baseEnd_374147 : Nat := 7115453571772328957105

theorem tailTrace_374147 : CollatzResearch.WordTrace tailWord_374147 prefixEnd_374147 7115453571772328957105 := by
  unfold tailWord_374147
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646262175536793065432695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9097508117024528710288463 13646262175536793065432695)
  ·
    refine ⟨20469393263305189598149043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13646262175536793065432695 20469393263305189598149043)
    ·
      refine ⟨30704089894957784397223565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20469393263305189598149043 30704089894957784397223565)
      ·
        refine ⟨11514033710609169148958837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30704089894957784397223565 11514033710609169148958837)
        ·
          refine ⟨1079440660369609607714891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11514033710609169148958837 1079440660369609607714891)
          ·
            refine ⟨1619160990554414411572337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079440660369609607714891 1619160990554414411572337)
            ·
              refine ⟨1214370742915810808679253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619160990554414411572337 1214370742915810808679253)
              ·
                refine ⟨7115453571772328957105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1214370742915810808679253 7115453571772328957105)
                ·
                  rfl

theorem cell23_374147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 9].length) (baseStart_374147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374147 prefixEnd_374147 := by exact prefixLift 374147
  have htrace : WordTrace (prefixWord ++ tailWord_374147) baseStart_374147 baseEnd_374147 := by
    simpa [prefixWord, tailWord_374147, baseEnd_374147] using wordTrace_append hprefix tailTrace_374147
  have hstable : (prefixWord ++ tailWord_374147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374147).length < 2 ^ (prefixWord ++ tailWord_374147).sum := by decide
  have hdescent : baseEnd_374147 < baseStart_374147 := by decide
  rcases family_descends (prefixWord ++ tailWord_374147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374168 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_374168 : Nat := 118140960795 + 374168 * 2 ^ 59
def prefixEnd_374168 : Nat := 4983230072969 + 3 ^ 40 * 374168 * 2
def baseEnd_374168 : Nat := 64042676510532433226413

theorem tailTrace_374168 : CollatzResearch.WordTrace tailWord_374168 prefixEnd_374168 64042676510532433226413 := by
  unfold tailWord_374168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823514054230356825973579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9098018738973809101298105 6823514054230356825973579)
  ·
    refine ⟨10235271081345535238960369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6823514054230356825973579 10235271081345535238960369)
    ·
      refine ⟨7676453311009151429220277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10235271081345535238960369 7676453311009151429220277)
      ·
        refine ⟨719667497907107946489401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7676453311009151429220277 719667497907107946489401)
        ·
          refine ⟨539750623430330959867051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719667497907107946489401 539750623430330959867051)
          ·
            refine ⟨809625935145496439800577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539750623430330959867051 809625935145496439800577)
            ·
              refine ⟨607219451359122329850433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809625935145496439800577 607219451359122329850433)
              ·
                refine ⟨455414588519341747387825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607219451359122329850433 455414588519341747387825)
                ·
                  refine ⟨341560941389506310540869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455414588519341747387825 341560941389506310540869)
                  ·
                    refine ⟨64042676510532433226413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341560941389506310540869 64042676510532433226413)
                    ·
                      rfl

theorem cell23_374168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_374168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374168 prefixEnd_374168 := by exact prefixLift 374168
  have htrace : WordTrace (prefixWord ++ tailWord_374168) baseStart_374168 baseEnd_374168 := by
    simpa [prefixWord, tailWord_374168, baseEnd_374168] using wordTrace_append hprefix tailTrace_374168
  have hstable : (prefixWord ++ tailWord_374168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374168).length < 2 ^ (prefixWord ++ tailWord_374168).sum := by decide
  have hdescent : baseEnd_374168 < baseStart_374168 := by decide
  rcases family_descends (prefixWord ++ tailWord_374168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374175 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 1, 2, 2]
def baseStart_374175 : Nat := 118140960795 + 374175 * 2 ^ 59
def prefixEnd_374175 : Nat := 4983230072969 + 3 ^ 40 * 374175 * 2
def baseEnd_374175 : Nat := 192131623896178772291707

theorem tailTrace_374175 : CollatzResearch.WordTrace tailWord_374175 prefixEnd_374175 192131623896178772291707 := by
  unfold tailWord_374175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13647283419435353847451979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9098188946290235898301319 13647283419435353847451979)
  ·
    refine ⟨20470925129153030771177969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13647283419435353847451979 20470925129153030771177969)
    ·
      refine ⟨15353193846864773078383477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20470925129153030771177969 15353193846864773078383477)
      ·
        refine ⟨1439361923143572476098451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15353193846864773078383477 1439361923143572476098451)
        ·
          refine ⟨2159042884715358714147677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439361923143572476098451 2159042884715358714147677)
          ·
            refine ⟨809641081768259517805379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2159042884715358714147677 809641081768259517805379)
            ·
              refine ⟨1214461622652389276708069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809641081768259517805379 1214461622652389276708069)
              ·
                refine ⟨227711554247322989382763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1214461622652389276708069 227711554247322989382763)
                ·
                  refine ⟨341567331370984484074145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227711554247322989382763 341567331370984484074145)
                  ·
                    refine ⟨256175498528238363055609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341567331370984484074145 256175498528238363055609)
                    ·
                      refine ⟨192131623896178772291707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256175498528238363055609 192131623896178772291707)
                      ·
                        rfl

theorem cell23_374175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_374175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374175 prefixEnd_374175 := by exact prefixLift 374175
  have htrace : WordTrace (prefixWord ++ tailWord_374175) baseStart_374175 baseEnd_374175 := by
    simpa [prefixWord, tailWord_374175, baseEnd_374175] using wordTrace_append hprefix tailTrace_374175
  have hstable : (prefixWord ++ tailWord_374175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374175).length < 2 ^ (prefixWord ++ tailWord_374175).sum := by decide
  have hdescent : baseEnd_374175 < baseStart_374175 := by decide
  rcases family_descends (prefixWord ++ tailWord_374175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374217 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_374217 : Nat := 118140960795 + 374217 * 2 ^ 59
def prefixEnd_374217 : Nat := 4983230072969 + 3 ^ 40 * 374217 * 2
def baseEnd_374217 : Nat := 192153190083667607966513

theorem tailTrace_374217 : CollatzResearch.WordTrace tailWord_374217 prefixEnd_374217 192153190083667607966513 := by
  unfold tailWord_374217
  simp only [CollatzResearch.WordTrace]
  refine ⟨13648815285283195020480905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9099210190188796680320603 13648815285283195020480905)
  ·
    refine ⟨10236611463962396265360679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13648815285283195020480905 10236611463962396265360679)
    ·
      refine ⟨15354917195943594398041019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10236611463962396265360679 15354917195943594398041019)
      ·
        refine ⟨23032375793915391597061529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15354917195943594398041019 23032375793915391597061529)
        ·
          refine ⟨17274281845436543697796147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23032375793915391597061529 17274281845436543697796147)
          ·
            refine ⟨25911422768154815546694221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17274281845436543697796147 25911422768154815546694221)
            ·
              refine ⟨9716783538058055830010333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25911422768154815546694221 9716783538058055830010333)
              ·
                refine ⟨3643793826771770936253875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9716783538058055830010333 3643793826771770936253875)
                ·
                  refine ⟨5465690740157656404380813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643793826771770936253875 5465690740157656404380813)
                  ·
                    refine ⟨2049634027559121151642805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5465690740157656404380813 2049634027559121151642805)
                    ·
                      refine ⟨192153190083667607966513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2049634027559121151642805 192153190083667607966513)
                      ·
                        rfl

theorem cell23_374217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_374217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374217 prefixEnd_374217 := by exact prefixLift 374217
  have htrace : WordTrace (prefixWord ++ tailWord_374217) baseStart_374217 baseEnd_374217 := by
    simpa [prefixWord, tailWord_374217, baseEnd_374217] using wordTrace_append hprefix tailTrace_374217
  have hstable : (prefixWord ++ tailWord_374217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374217).length < 2 ^ (prefixWord ++ tailWord_374217).sum := by decide
  have hdescent : baseEnd_374217 < baseStart_374217 := by decide
  rcases family_descends (prefixWord ++ tailWord_374217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374218 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_374218 : Nat := 118140960795 + 374218 * 2 ^ 59
def prefixEnd_374218 : Nat := 4983230072969 + 3 ^ 40 * 374218 * 2
def baseEnd_374218 : Nat := 192153703564322104054009

theorem tailTrace_374218 : CollatzResearch.WordTrace tailWord_374218 prefixEnd_374218 192153703564322104054009 := by
  unfold tailWord_374218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412212939569893047816827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9099234505519714794178205 3412212939569893047816827)
  ·
    refine ⟨5118319409354839571725241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412212939569893047816827 5118319409354839571725241)
    ·
      refine ⟨3838739557016129678793931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118319409354839571725241 3838739557016129678793931)
      ·
        refine ⟨5758109335524194518190897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838739557016129678793931 5758109335524194518190897)
        ·
          refine ⟨4318582001643145888643173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758109335524194518190897 4318582001643145888643173)
          ·
            refine ⟨809734125308089854120595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4318582001643145888643173 809734125308089854120595)
            ·
              refine ⟨1214601187962134781180893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809734125308089854120595 1214601187962134781180893)
              ·
                refine ⟨455475445485800542942835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214601187962134781180893 455475445485800542942835)
                ·
                  refine ⟨683213168228700814414253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455475445485800542942835 683213168228700814414253)
                  ·
                    refine ⟨256204938085762805405345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 683213168228700814414253 256204938085762805405345)
                    ·
                      refine ⟨192153703564322104054009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256204938085762805405345 192153703564322104054009)
                      ·
                        rfl

theorem cell23_374218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_374218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374218 prefixEnd_374218 := by exact prefixLift 374218
  have htrace : WordTrace (prefixWord ++ tailWord_374218) baseStart_374218 baseEnd_374218 := by
    simpa [prefixWord, tailWord_374218, baseEnd_374218] using wordTrace_append hprefix tailTrace_374218
  have hstable : (prefixWord ++ tailWord_374218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374218).length < 2 ^ (prefixWord ++ tailWord_374218).sum := by decide
  have hdescent : baseEnd_374218 < baseStart_374218 := by decide
  rcases family_descends (prefixWord ++ tailWord_374218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374227 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_374227 : Nat := 118140960795 + 374227 * 2 ^ 59
def prefixEnd_374227 : Nat := 4983230072969 + 3 ^ 40 * 374227 * 2
def baseEnd_374227 : Nat := 192158324890212568841467

theorem tailTrace_374227 : CollatzResearch.WordTrace tailWord_374227 prefixEnd_374227 192158324890212568841467 := by
  unfold tailWord_374227
  simp only [CollatzResearch.WordTrace]
  refine ⟨13649180015246966728344935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9099453343497977818896623 13649180015246966728344935)
  ·
    refine ⟨20473770022870450092517403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13649180015246966728344935 20473770022870450092517403)
    ·
      refine ⟨30710655034305675138776105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20473770022870450092517403 30710655034305675138776105)
      ·
        refine ⟨23032991275729256354082079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30710655034305675138776105 23032991275729256354082079)
        ·
          refine ⟨34549486913593884531123119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23032991275729256354082079 34549486913593884531123119)
          ·
            refine ⟨51824230370390826796684679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34549486913593884531123119 51824230370390826796684679)
            ·
              refine ⟨77736345555586240195027019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51824230370390826796684679 77736345555586240195027019)
              ·
                refine ⟨116604518333379360292540529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77736345555586240195027019 116604518333379360292540529)
                ·
                  refine ⟨87453388750034520219405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116604518333379360292540529 87453388750034520219405397)
                  ·
                    refine ⟨1024844399414467033821157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87453388750034520219405397 1024844399414467033821157)
                    ·
                      refine ⟨192158324890212568841467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1024844399414467033821157 192158324890212568841467)
                      ·
                        rfl

theorem cell23_374227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_374227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374227 prefixEnd_374227 := by exact prefixLift 374227
  have htrace : WordTrace (prefixWord ++ tailWord_374227) baseStart_374227 baseEnd_374227 := by
    simpa [prefixWord, tailWord_374227, baseEnd_374227] using wordTrace_append hprefix tailTrace_374227
  have hstable : (prefixWord ++ tailWord_374227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374227).length < 2 ^ (prefixWord ++ tailWord_374227).sum := by decide
  have hdescent : baseEnd_374227 < baseStart_374227 := by decide
  rcases family_descends (prefixWord ++ tailWord_374227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374254 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_374254 : Nat := 118140960795 + 374254 * 2 ^ 59
def prefixEnd_374254 : Nat := 4983230072969 + 3 ^ 40 * 374254 * 2
def baseEnd_374254 : Nat := 21352465429764884800427

theorem tailTrace_374254 : CollatzResearch.WordTrace tailWord_374254 prefixEnd_374254 21352465429764884800427 := by
  unfold tailWord_374254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706270598268643792447227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9100109857432766893051877 1706270598268643792447227)
  ·
    refine ⟨2559405897402965688670841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706270598268643792447227 2559405897402965688670841)
    ·
      refine ⟨1919554423052224266503131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2559405897402965688670841 1919554423052224266503131)
      ·
        refine ⟨2879331634578336399754697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919554423052224266503131 2879331634578336399754697)
        ·
          refine ⟨2159498725933752299816023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2879331634578336399754697 2159498725933752299816023)
          ·
            refine ⟨3239248088900628449724035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159498725933752299816023 3239248088900628449724035)
            ·
              refine ⟨4858872133350942674586053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239248088900628449724035 4858872133350942674586053)
              ·
                refine ⟨911038525003301751484885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4858872133350942674586053 911038525003301751484885)
                ·
                  refine ⟨21352465429764884800427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 911038525003301751484885 21352465429764884800427)
                  ·
                    rfl

theorem cell23_374254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_374254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374254 prefixEnd_374254 := by exact prefixLift 374254
  have htrace : WordTrace (prefixWord ++ tailWord_374254) baseStart_374254 baseEnd_374254 := by
    simpa [prefixWord, tailWord_374254, baseEnd_374254] using wordTrace_append hprefix tailTrace_374254
  have hstable : (prefixWord ++ tailWord_374254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374254).length < 2 ^ (prefixWord ++ tailWord_374254).sum := by decide
  have hdescent : baseEnd_374254 < baseStart_374254 := by decide
  rcases family_descends (prefixWord ++ tailWord_374254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374318 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_374318 : Nat := 118140960795 + 374318 * 2 ^ 59
def prefixEnd_374318 : Nat := 4983230072969 + 3 ^ 40 * 374318 * 2
def baseEnd_374318 : Nat := 64068350543257237601183

theorem tailTrace_374318 : CollatzResearch.WordTrace tailWord_374318 prefixEnd_374318 64068350543257237601183 := by
  unfold tailWord_374318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706562382239661158738451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9101666038611526179938405 1706562382239661158738451)
  ·
    refine ⟨2559843573359491738107677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706562382239661158738451 2559843573359491738107677)
    ·
      refine ⟨959941340009809401790379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2559843573359491738107677 959941340009809401790379)
      ·
        refine ⟨1439912010014714102685569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959941340009809401790379 1439912010014714102685569)
        ·
          refine ⟨1079934007511035577014177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439912010014714102685569 1079934007511035577014177)
          ·
            refine ⟨809950505633276682760633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079934007511035577014177 809950505633276682760633)
            ·
              refine ⟨607462879224957512070475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809950505633276682760633 607462879224957512070475)
              ·
                refine ⟨911194318837436268105713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607462879224957512070475 911194318837436268105713)
                ·
                  refine ⟨683395739128077201079285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911194318837436268105713 683395739128077201079285)
                  ·
                    refine ⟨64068350543257237601183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 683395739128077201079285 64068350543257237601183)
                    ·
                      rfl

theorem cell23_374318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_374318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374318 prefixEnd_374318 := by exact prefixLift 374318
  have htrace : WordTrace (prefixWord ++ tailWord_374318) baseStart_374318 baseEnd_374318 := by
    simpa [prefixWord, tailWord_374318, baseEnd_374318] using wordTrace_append hprefix tailTrace_374318
  have hstable : (prefixWord ++ tailWord_374318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374318).length < 2 ^ (prefixWord ++ tailWord_374318).sum := by decide
  have hdescent : baseEnd_374318 < baseStart_374318 := by decide
  rcases family_descends (prefixWord ++ tailWord_374318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374321 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_374321 : Nat := 118140960795 + 374321 * 2 ^ 59
def prefixEnd_374321 : Nat := 4983230072969 + 3 ^ 40 * 374321 * 2
def baseEnd_374321 : Nat := 192206592071735201066035

theorem tailTrace_374321 : CollatzResearch.WordTrace tailWord_374321 prefixEnd_374321 192206592071735201066035 := by
  unfold tailWord_374321
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652608476906420782266817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9101738984604280521511211 13652608476906420782266817)
  ·
    refine ⟨10239456357679815586700113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13652608476906420782266817 10239456357679815586700113)
    ·
      refine ⟨7679592268259861690025085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10239456357679815586700113 7679592268259861690025085)
      ·
        refine ⟨2879847100597448133759407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7679592268259861690025085 2879847100597448133759407)
        ·
          refine ⟨4319770650896172200639111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879847100597448133759407 4319770650896172200639111)
          ·
            refine ⟨6479655976344258300958667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319770650896172200639111 6479655976344258300958667)
            ·
              refine ⟨9719483964516387451438001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479655976344258300958667 9719483964516387451438001)
              ·
                refine ⟨7289612973387290588578501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9719483964516387451438001 7289612973387290588578501)
                ·
                  refine ⟨1366802432510116985358469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7289612973387290588578501 1366802432510116985358469)
                  ·
                    refine ⟨256275456095646934754713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366802432510116985358469 256275456095646934754713)
                    ·
                      refine ⟨192206592071735201066035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256275456095646934754713 192206592071735201066035)
                      ·
                        rfl

theorem cell23_374321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_374321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374321 prefixEnd_374321 := by exact prefixLift 374321
  have htrace : WordTrace (prefixWord ++ tailWord_374321) baseStart_374321 baseEnd_374321 := by
    simpa [prefixWord, tailWord_374321, baseEnd_374321] using wordTrace_append hprefix tailTrace_374321
  have hstable : (prefixWord ++ tailWord_374321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374321).length < 2 ^ (prefixWord ++ tailWord_374321).sum := by decide
  have hdescent : baseEnd_374321 < baseStart_374321 := by decide
  rcases family_descends (prefixWord ++ tailWord_374321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374341 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_374341 : Nat := 118140960795 + 374341 * 2 ^ 59
def prefixEnd_374341 : Nat := 4983230072969 + 3 ^ 40 * 374341 * 2
def baseEnd_374341 : Nat := 192216861684825122815943

theorem tailTrace_374341 : CollatzResearch.WordTrace tailWord_374341 prefixEnd_374341 192216861684825122815943 := by
  unfold tailWord_374341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653337936833964197994877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9102225291222642798663251 13653337936833964197994877)
  ·
    refine ⟨5120001726312736574248079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13653337936833964197994877 5120001726312736574248079)
    ·
      refine ⟨7680002589469104861372119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120001726312736574248079 7680002589469104861372119)
      ·
        refine ⟨11520003884203657292058179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680002589469104861372119 11520003884203657292058179)
        ·
          refine ⟨17280005826305485938087269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520003884203657292058179 17280005826305485938087269)
          ·
            refine ⟨3240001092432278613391363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17280005826305485938087269 3240001092432278613391363)
            ·
              refine ⟨4860001638648417920087045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240001092432278613391363 4860001638648417920087045)
              ·
                refine ⟨911250307246578360016321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4860001638648417920087045 911250307246578360016321)
                ·
                  refine ⟨683437730434933770012241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911250307246578360016321 683437730434933770012241)
                  ·
                    refine ⟨512578297826200327509181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683437730434933770012241 512578297826200327509181)
                    ·
                      refine ⟨192216861684825122815943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 512578297826200327509181 192216861684825122815943)
                      ·
                        rfl

theorem cell23_374341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_374341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374341 prefixEnd_374341 := by exact prefixLift 374341
  have htrace : WordTrace (prefixWord ++ tailWord_374341) baseStart_374341 baseEnd_374341 := by
    simpa [prefixWord, tailWord_374341, baseEnd_374341] using wordTrace_append hprefix tailTrace_374341
  have hstable : (prefixWord ++ tailWord_374341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374341).length < 2 ^ (prefixWord ++ tailWord_374341).sum := by decide
  have hdescent : baseEnd_374341 < baseStart_374341 := by decide
  rcases family_descends (prefixWord ++ tailWord_374341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374382 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_374382 : Nat := 118140960795 + 374382 * 2 ^ 59
def prefixEnd_374382 : Nat := 4983230072969 + 3 ^ 40 * 374382 * 2
def baseEnd_374382 : Nat := 64079304797219820801085

theorem tailTrace_374382 : CollatzResearch.WordTrace tailWord_374382 prefixEnd_374382 64079304797219820801085 := by
  unfold tailWord_374382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706854166210678525029675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9103222219790285466824933 1706854166210678525029675)
  ·
    refine ⟨2560281249316017787544513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706854166210678525029675 2560281249316017787544513)
    ·
      refine ⟨1920210936987013340658385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560281249316017787544513 1920210936987013340658385)
      ·
        refine ⟨1440158202740260005493789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920210936987013340658385 1440158202740260005493789)
        ·
          refine ⟨540059326027597502060171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1440158202740260005493789 540059326027597502060171)
          ·
            refine ⟨810088989041396253090257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540059326027597502060171 810088989041396253090257)
            ·
              refine ⟨607566741781047189817693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810088989041396253090257 607566741781047189817693)
              ·
                refine ⟨227837528167892696181635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607566741781047189817693 227837528167892696181635)
                ·
                  refine ⟨341756292251839044272453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227837528167892696181635 341756292251839044272453)
                  ·
                    refine ⟨64079304797219820801085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341756292251839044272453 64079304797219820801085)
                    ·
                      rfl

theorem cell23_374382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_374382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374382 prefixEnd_374382 := by exact prefixLift 374382
  have htrace : WordTrace (prefixWord ++ tailWord_374382) baseStart_374382 baseEnd_374382 := by
    simpa [prefixWord, tailWord_374382, baseEnd_374382] using wordTrace_append hprefix tailTrace_374382
  have hstable : (prefixWord ++ tailWord_374382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374382).length < 2 ^ (prefixWord ++ tailWord_374382).sum := by decide
  have hdescent : baseEnd_374382 < baseStart_374382 := by decide
  rcases family_descends (prefixWord ++ tailWord_374382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374405 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 1, 1, 3]
def baseStart_374405 : Nat := 118140960795 + 374405 * 2 ^ 59
def prefixEnd_374405 : Nat := 4983230072969 + 3 ^ 40 * 374405 * 2
def baseEnd_374405 : Nat := 192249724446712872415649

theorem tailTrace_374405 : CollatzResearch.WordTrace tailWord_374405 prefixEnd_374405 192249724446712872415649 := by
  unfold tailWord_374405
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655672208602103128324669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9103781472401402085549779 13655672208602103128324669)
  ·
    refine ⟨5120877078225788673121751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13655672208602103128324669 5120877078225788673121751)
    ·
      refine ⟨7681315617338683009682627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120877078225788673121751 7681315617338683009682627)
      ·
        refine ⟨11521973426008024514523941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681315617338683009682627 11521973426008024514523941)
        ·
          refine ⟨2160370017376504596473239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11521973426008024514523941 2160370017376504596473239)
          ·
            refine ⟨3240555026064756894709859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160370017376504596473239 3240555026064756894709859)
            ·
              refine ⟨4860832539097135342064789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240555026064756894709859 4860832539097135342064789)
              ·
                refine ⟨227851525270178219159287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4860832539097135342064789 227851525270178219159287)
                ·
                  refine ⟨341777287905267328738931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227851525270178219159287 341777287905267328738931)
                  ·
                    refine ⟨512665931857900993108397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341777287905267328738931 512665931857900993108397)
                    ·
                      refine ⟨192249724446712872415649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 512665931857900993108397 192249724446712872415649)
                      ·
                        rfl

theorem cell23_374405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_374405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374405 prefixEnd_374405 := by exact prefixLift 374405
  have htrace : WordTrace (prefixWord ++ tailWord_374405) baseStart_374405 baseEnd_374405 := by
    simpa [prefixWord, tailWord_374405, baseEnd_374405] using wordTrace_append hprefix tailTrace_374405
  have hstable : (prefixWord ++ tailWord_374405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374405).length < 2 ^ (prefixWord ++ tailWord_374405).sum := by decide
  have hdescent : baseEnd_374405 < baseStart_374405 := by decide
  rcases family_descends (prefixWord ++ tailWord_374405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374448 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_374448 : Nat := 118140960795 + 374448 * 2 ^ 59
def prefixEnd_374448 : Nat := 4983230072969 + 3 ^ 40 * 374448 * 2
def baseEnd_374448 : Nat := 192271804114856204177951

theorem tailTrace_374448 : CollatzResearch.WordTrace tailWord_374448 prefixEnd_374448 192271804114856204177951 := by
  unfold tailWord_374448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828620273723160736069999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9104827031630880981426665 6828620273723160736069999)
  ·
    refine ⟨10242930410584741104104999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6828620273723160736069999 10242930410584741104104999)
    ·
      refine ⟨15364395615877111656157499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242930410584741104104999 15364395615877111656157499)
      ·
        refine ⟨23046593423815667484236249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15364395615877111656157499 23046593423815667484236249)
        ·
          refine ⟨17284945067861750613177187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23046593423815667484236249 17284945067861750613177187)
          ·
            refine ⟨25927417601792625919765781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17284945067861750613177187 25927417601792625919765781)
            ·
              refine ⟨1215347700084029339989021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25927417601792625919765781 1215347700084029339989021)
              ·
                refine ⟨455755387531511002495883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1215347700084029339989021 455755387531511002495883)
                ·
                  refine ⟨683633081297266503743825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455755387531511002495883 683633081297266503743825)
                  ·
                    refine ⟨512724810972949877807869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683633081297266503743825 512724810972949877807869)
                    ·
                      refine ⟨192271804114856204177951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 512724810972949877807869 192271804114856204177951)
                      ·
                        rfl

theorem cell23_374448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_374448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374448 prefixEnd_374448 := by exact prefixLift 374448
  have htrace : WordTrace (prefixWord ++ tailWord_374448) baseStart_374448 baseEnd_374448 := by
    simpa [prefixWord, tailWord_374448, baseEnd_374448] using wordTrace_append hprefix tailTrace_374448
  have hstable : (prefixWord ++ tailWord_374448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374448).length < 2 ^ (prefixWord ++ tailWord_374448).sum := by decide
  have hdescent : baseEnd_374448 < baseStart_374448 := by decide
  rcases family_descends (prefixWord ++ tailWord_374448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374462 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_374462 : Nat := 118140960795 + 374462 * 2 ^ 59
def prefixEnd_374462 : Nat := 4983230072969 + 3 ^ 40 * 374462 * 2
def baseEnd_374462 : Nat := 192278992844019149402887

theorem tailTrace_374462 : CollatzResearch.WordTrace tailWord_374462 prefixEnd_374462 192278992844019149402887 := by
  unfold tailWord_374462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707218896174450232893705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9105167446263734575433093 1707218896174450232893705)
  ·
    refine ⟨1280414172130837674670279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1707218896174450232893705 1280414172130837674670279)
    ·
      refine ⟨1920621258196256512005419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280414172130837674670279 1920621258196256512005419)
      ·
        refine ⟨2880931887294384768008129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920621258196256512005419 2880931887294384768008129)
        ·
          refine ⟨2160698915470788576006097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880931887294384768008129 2160698915470788576006097)
          ·
            refine ⟨1620524186603091432004573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160698915470788576006097 1620524186603091432004573)
            ·
              refine ⟨607696569976159287001715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1620524186603091432004573 607696569976159287001715)
              ·
                refine ⟨911544854964238930502573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607696569976159287001715 911544854964238930502573)
                ·
                  refine ⟨341829320611589598938465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911544854964238930502573 341829320611589598938465)
                  ·
                    refine ⟨256371990458692199203849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341829320611589598938465 256371990458692199203849)
                    ·
                      refine ⟨192278992844019149402887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256371990458692199203849 192278992844019149402887)
                      ·
                        rfl

theorem cell23_374462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_374462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374462 prefixEnd_374462 := by exact prefixLift 374462
  have htrace : WordTrace (prefixWord ++ tailWord_374462) baseStart_374462 baseEnd_374462 := by
    simpa [prefixWord, tailWord_374462, baseEnd_374462] using wordTrace_append hprefix tailTrace_374462
  have hstable : (prefixWord ++ tailWord_374462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374462).length < 2 ^ (prefixWord ++ tailWord_374462).sum := by decide
  have hdescent : baseEnd_374462 < baseStart_374462 := by decide
  rcases family_descends (prefixWord ++ tailWord_374462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374478 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_374478 : Nat := 118140960795 + 374478 * 2 ^ 59
def prefixEnd_374478 : Nat := 4983230072969 + 3 ^ 40 * 374478 * 2
def baseEnd_374478 : Nat := 192287208534491086802813

theorem tailTrace_374478 : CollatzResearch.WordTrace tailWord_374478 prefixEnd_374478 192287208534491086802813 := by
  unfold tailWord_374478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707291842167204574466511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9105556491558424397154725 1707291842167204574466511)
  ·
    refine ⟨2560937763250806861699767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1707291842167204574466511 2560937763250806861699767)
    ·
      refine ⟨3841406644876210292549651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560937763250806861699767 3841406644876210292549651)
      ·
        refine ⟨5762109967314315438824477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841406644876210292549651 5762109967314315438824477)
        ·
          refine ⟨2160791237742868289559179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5762109967314315438824477 2160791237742868289559179)
          ·
            refine ⟨3241186856614302434338769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160791237742868289559179 3241186856614302434338769)
            ·
              refine ⟨2430890142460726825754077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241186856614302434338769 2430890142460726825754077)
              ·
                refine ⟨911583803422772559657779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430890142460726825754077 911583803422772559657779)
                ·
                  refine ⟨1367375705134158839486669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911583803422772559657779 1367375705134158839486669)
                  ·
                    refine ⟨512765889425309564807501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367375705134158839486669 512765889425309564807501)
                    ·
                      refine ⟨192287208534491086802813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 512765889425309564807501 192287208534491086802813)
                      ·
                        rfl

theorem cell23_374478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_374478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374478 prefixEnd_374478 := by exact prefixLift 374478
  have htrace : WordTrace (prefixWord ++ tailWord_374478) baseStart_374478 baseEnd_374478 := by
    simpa [prefixWord, tailWord_374478, baseEnd_374478] using wordTrace_append hprefix tailTrace_374478
  have hstable : (prefixWord ++ tailWord_374478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374478).length < 2 ^ (prefixWord ++ tailWord_374478).sum := by decide
  have hdescent : baseEnd_374478 < baseStart_374478 := by decide
  rcases family_descends (prefixWord ++ tailWord_374478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374482 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_374482 : Nat := 118140960795 + 374482 * 2 ^ 59
def prefixEnd_374482 : Nat := 4983230072969 + 3 ^ 40 * 374482 * 2
def baseEnd_374482 : Nat := 192289262457109071152795

theorem tailTrace_374482 : CollatzResearch.WordTrace tailWord_374482 prefixEnd_374482 192289262457109071152795 := by
  unfold tailWord_374482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414620157330786319719425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9105653752882096852585133 3414620157330786319719425)
  ·
    refine ⟨2560965117998089739789569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3414620157330786319719425 2560965117998089739789569)
    ·
      refine ⟨1920723838498567304842177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560965117998089739789569 1920723838498567304842177)
      ·
        refine ⟨1440542878873925478631633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920723838498567304842177 1440542878873925478631633)
        ·
          refine ⟨1080407159155444108973725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440542878873925478631633 1080407159155444108973725)
          ·
            refine ⟨405152684683291540865147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1080407159155444108973725 405152684683291540865147)
            ·
              refine ⟨607729027024937311297721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405152684683291540865147 607729027024937311297721)
              ·
                refine ⟨455796770268702983473291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607729027024937311297721 455796770268702983473291)
                ·
                  refine ⟨683695155403054475209937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455796770268702983473291 683695155403054475209937)
                  ·
                    refine ⟨512771366552290856407453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683695155403054475209937 512771366552290856407453)
                    ·
                      refine ⟨192289262457109071152795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 512771366552290856407453 192289262457109071152795)
                      ·
                        rfl

theorem cell23_374482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_374482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374482 prefixEnd_374482 := by exact prefixLift 374482
  have htrace : WordTrace (prefixWord ++ tailWord_374482) baseStart_374482 baseEnd_374482 := by
    simpa [prefixWord, tailWord_374482, baseEnd_374482] using wordTrace_append hprefix tailTrace_374482
  have hstable : (prefixWord ++ tailWord_374482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374482).length < 2 ^ (prefixWord ++ tailWord_374482).sum := by decide
  have hdescent : baseEnd_374482 < baseStart_374482 := by decide
  rcases family_descends (prefixWord ++ tailWord_374482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374511 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 2, 6]
def baseStart_374511 : Nat := 118140960795 + 374511 * 2 ^ 59
def prefixEnd_374511 : Nat := 4983230072969 + 3 ^ 40 * 374511 * 2
def baseEnd_374511 : Nat := 64101384465363152563387

theorem tailTrace_374511 : CollatzResearch.WordTrace tailWord_374511 prefixEnd_374511 64101384465363152563387 := by
  unfold tailWord_374511
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659538346218083231683387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9106358897478722154455591 13659538346218083231683387)
  ·
    refine ⟨20489307519327124847525081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659538346218083231683387 20489307519327124847525081)
    ·
      refine ⟨15366980639495343635643811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20489307519327124847525081 15366980639495343635643811)
      ·
        refine ⟨23050470959243015453465717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15366980639495343635643811 23050470959243015453465717)
        ·
          refine ⟨2160981652429032698762411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23050470959243015453465717 2160981652429032698762411)
          ·
            refine ⟨3241472478643549048143617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160981652429032698762411 3241472478643549048143617)
            ·
              refine ⟨2431104358982661786107713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241472478643549048143617 2431104358982661786107713)
              ·
                refine ⟨1823328269236996339580785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431104358982661786107713 1823328269236996339580785)
                ·
                  refine ⟨1367496201927747254685589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1823328269236996339580785 1367496201927747254685589)
                  ·
                    refine ⟨64101384465363152563387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1367496201927747254685589 64101384465363152563387)
                    ·
                      rfl

theorem cell23_374511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_374511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374511 prefixEnd_374511 := by exact prefixLift 374511
  have htrace : WordTrace (prefixWord ++ tailWord_374511) baseStart_374511 baseEnd_374511 := by
    simpa [prefixWord, tailWord_374511, baseEnd_374511] using wordTrace_append hprefix tailTrace_374511
  have hstable : (prefixWord ++ tailWord_374511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374511).length < 2 ^ (prefixWord ++ tailWord_374511).sum := by decide
  have hdescent : baseEnd_374511 < baseStart_374511 := by decide
  rcases family_descends (prefixWord ++ tailWord_374511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374518 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_374518 : Nat := 118140960795 + 374518 * 2 ^ 59
def prefixEnd_374518 : Nat := 4983230072969 + 3 ^ 40 * 374518 * 2
def baseEnd_374518 : Nat := 192307747760670930302629

theorem tailTrace_374518 : CollatzResearch.WordTrace tailWord_374518 prefixEnd_374518 192307747760670930302629 := by
  unfold tailWord_374518
  simp only [CollatzResearch.WordTrace]
  refine ⟨853737103574545214199263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9106529104795148951458805 853737103574545214199263)
  ·
    refine ⟨1280605655361817821298895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853737103574545214199263 1280605655361817821298895)
    ·
      refine ⟨1920908483042726731948343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280605655361817821298895 1920908483042726731948343)
      ·
        refine ⟨2881362724564090097922515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920908483042726731948343 2881362724564090097922515)
        ·
          refine ⟨4322044086846135146883773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881362724564090097922515 4322044086846135146883773)
          ·
            refine ⟨1620766532567300680081415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4322044086846135146883773 1620766532567300680081415)
            ·
              refine ⟨2431149798850951020122123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620766532567300680081415 2431149798850951020122123)
              ·
                refine ⟨3646724698276426530183185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431149798850951020122123 3646724698276426530183185)
                ·
                  refine ⟨2735043523707319897637389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646724698276426530183185 2735043523707319897637389)
                  ·
                    refine ⟨1025641321390244961614021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735043523707319897637389 1025641321390244961614021)
                    ·
                      refine ⟨192307747760670930302629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1025641321390244961614021 192307747760670930302629)
                      ·
                        rfl

theorem cell23_374518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_374518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374518 prefixEnd_374518 := by exact prefixLift 374518
  have htrace : WordTrace (prefixWord ++ tailWord_374518) baseStart_374518 baseEnd_374518 := by
    simpa [prefixWord, tailWord_374518, baseEnd_374518] using wordTrace_append hprefix tailTrace_374518
  have hstable : (prefixWord ++ tailWord_374518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374518).length < 2 ^ (prefixWord ++ tailWord_374518).sum := by decide
  have hdescent : baseEnd_374518 < baseStart_374518 := by decide
  rcases family_descends (prefixWord ++ tailWord_374518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374531 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_374531 : Nat := 118140960795 + 374531 * 2 ^ 59
def prefixEnd_374531 : Nat := 4983230072969 + 3 ^ 40 * 374531 * 2
def baseEnd_374531 : Nat := 192314423009179379440069

theorem tailTrace_374531 : CollatzResearch.WordTrace tailWord_374531 prefixEnd_374531 192314423009179379440069 := by
  unfold tailWord_374531
  simp only [CollatzResearch.WordTrace]
  refine ⟨13660267806145626647411447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9106845204097084431607631 13660267806145626647411447)
  ·
    refine ⟨20490401709218439971117171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13660267806145626647411447 20490401709218439971117171)
    ·
      refine ⟨30735602563827659956675757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20490401709218439971117171 30735602563827659956675757)
      ·
        refine ⟨11525850961435372483753409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30735602563827659956675757 11525850961435372483753409)
        ·
          refine ⟨8644388221076529362815057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11525850961435372483753409 8644388221076529362815057)
          ·
            refine ⟨6483291165807397022111293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8644388221076529362815057 6483291165807397022111293)
            ·
              refine ⟨2431234187177773883291735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6483291165807397022111293 2431234187177773883291735)
              ·
                refine ⟨3646851280766660824937603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431234187177773883291735 3646851280766660824937603)
                ·
                  refine ⟨5470276921149991237406405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646851280766660824937603 5470276921149991237406405)
                  ·
                    refine ⟨1025676922715623357013701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470276921149991237406405 1025676922715623357013701)
                    ·
                      refine ⟨192314423009179379440069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1025676922715623357013701 192314423009179379440069)
                      ·
                        rfl

theorem cell23_374531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_374531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374531 prefixEnd_374531 := by exact prefixLift 374531
  have htrace : WordTrace (prefixWord ++ tailWord_374531) baseStart_374531 baseEnd_374531 := by
    simpa [prefixWord, tailWord_374531, baseEnd_374531] using wordTrace_append hprefix tailTrace_374531
  have hstable : (prefixWord ++ tailWord_374531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374531).length < 2 ^ (prefixWord ++ tailWord_374531).sum := by decide
  have hdescent : baseEnd_374531 < baseStart_374531 := by decide
  rcases family_descends (prefixWord ++ tailWord_374531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374601 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_374601 : Nat := 118140960795 + 374601 * 2 ^ 59
def prefixEnd_374601 : Nat := 4983230072969 + 3 ^ 40 * 374601 * 2
def baseEnd_374601 : Nat := 64116788884998035188249

theorem tailTrace_374601 : CollatzResearch.WordTrace tailWord_374601 prefixEnd_374601 64116788884998035188249 := by
  unfold tailWord_374601
  simp only [CollatzResearch.WordTrace]
  refine ⟨13662820915892028602459657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9108547277261352401639771 13662820915892028602459657)
  ·
    refine ⟨10247115686919021451844743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13662820915892028602459657 10247115686919021451844743)
    ·
      refine ⟨15370673530378532177767115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247115686919021451844743 15370673530378532177767115)
      ·
        refine ⟨23056010295567798266650673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370673530378532177767115 23056010295567798266650673)
        ·
          refine ⟨17292007721675848699988005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23056010295567798266650673 17292007721675848699988005)
          ·
            refine ⟨3242251447814221631247751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17292007721675848699988005 3242251447814221631247751)
            ·
              refine ⟨4863377171721332446871627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242251447814221631247751 4863377171721332446871627)
              ·
                refine ⟨7295065757581998670307441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863377171721332446871627 7295065757581998670307441)
                ·
                  refine ⟨5471299318186499002730581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295065757581998670307441 5471299318186499002730581)
                  ·
                    refine ⟨64116788884998035188249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5471299318186499002730581 64116788884998035188249)
                    ·
                      rfl

theorem cell23_374601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_374601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374601 prefixEnd_374601 := by exact prefixLift 374601
  have htrace : WordTrace (prefixWord ++ tailWord_374601) baseStart_374601 baseEnd_374601 := by
    simpa [prefixWord, tailWord_374601, baseEnd_374601] using wordTrace_append hprefix tailTrace_374601
  have hstable : (prefixWord ++ tailWord_374601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374601).length < 2 ^ (prefixWord ++ tailWord_374601).sum := by decide
  have hdescent : baseEnd_374601 < baseStart_374601 := by decide
  rcases family_descends (prefixWord ++ tailWord_374601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374605 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_374605 : Nat := 118140960795 + 374605 * 2 ^ 59
def prefixEnd_374605 : Nat := 4983230072969 + 3 ^ 40 * 374605 * 2
def baseEnd_374605 : Nat := 64117473525870696638243

theorem tailTrace_374605 : CollatzResearch.WordTrace tailWord_374605 prefixEnd_374605 64117473525870696638243 := by
  unfold tailWord_374605
  simp only [CollatzResearch.WordTrace]
  refine ⟨13662966807877537285605269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9108644538585024857070179 13662966807877537285605269)
  ·
    refine ⟨640451569119259560262747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13662966807877537285605269 640451569119259560262747)
    ·
      refine ⟨960677353678889340394121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640451569119259560262747 960677353678889340394121)
      ·
        refine ⟨720508015259167005295591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960677353678889340394121 720508015259167005295591)
        ·
          refine ⟨1080762022888750507943387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720508015259167005295591 1080762022888750507943387)
          ·
            refine ⟨1621143034333125761915081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080762022888750507943387 1621143034333125761915081)
            ·
              refine ⟨1215857275749844321436311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621143034333125761915081 1215857275749844321436311)
              ·
                refine ⟨1823785913624766482154467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215857275749844321436311 1823785913624766482154467)
                ·
                  refine ⟨2735678870437149723231701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823785913624766482154467 2735678870437149723231701)
                  ·
                    refine ⟨64117473525870696638243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2735678870437149723231701 64117473525870696638243)
                    ·
                      rfl

theorem cell23_374605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_374605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374605 prefixEnd_374605 := by exact prefixLift 374605
  have htrace : WordTrace (prefixWord ++ tailWord_374605) baseStart_374605 baseEnd_374605 := by
    simpa [prefixWord, tailWord_374605, baseEnd_374605] using wordTrace_append hprefix tailTrace_374605
  have hstable : (prefixWord ++ tailWord_374605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374605).length < 2 ^ (prefixWord ++ tailWord_374605).sum := by decide
  have hdescent : baseEnd_374605 < baseStart_374605 := by decide
  rcases family_descends (prefixWord ++ tailWord_374605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374608 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_374608 : Nat := 118140960795 + 374608 * 2 ^ 59
def prefixEnd_374608 : Nat := 4983230072969 + 3 ^ 40 * 374608 * 2
def baseEnd_374608 : Nat := 192353961019575578177215

theorem tailTrace_374608 : CollatzResearch.WordTrace tailWord_374608 prefixEnd_374608 192353961019575578177215 := by
  unfold tailWord_374608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6831538113433334398982239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9108717484577779198642985 6831538113433334398982239)
  ·
    refine ⟨10247307170150001598473359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6831538113433334398982239 10247307170150001598473359)
    ·
      refine ⟨15370960755225002397710039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247307170150001598473359 15370960755225002397710039)
      ·
        refine ⟨23056441132837503596565059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370960755225002397710039 23056441132837503596565059)
        ·
          refine ⟨34584661699256255394847589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23056441132837503596565059 34584661699256255394847589)
          ·
            refine ⟨6484624068610547886533923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34584661699256255394847589 6484624068610547886533923)
            ·
              refine ⟨9726936102915821829800885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484624068610547886533923 9726936102915821829800885)
              ·
                refine ⟨911900259648358296543833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9726936102915821829800885 911900259648358296543833)
                ·
                  refine ⟨683925194736268722407875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911900259648358296543833 683925194736268722407875)
                  ·
                    refine ⟨1025887792104403083611813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683925194736268722407875 1025887792104403083611813)
                    ·
                      refine ⟨192353961019575578177215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1025887792104403083611813 192353961019575578177215)
                      ·
                        rfl

theorem cell23_374608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_374608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374608 prefixEnd_374608 := by exact prefixLift 374608
  have htrace : WordTrace (prefixWord ++ tailWord_374608) baseStart_374608 baseEnd_374608 := by
    simpa [prefixWord, tailWord_374608, baseEnd_374608] using wordTrace_append hprefix tailTrace_374608
  have hstable : (prefixWord ++ tailWord_374608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374608).length < 2 ^ (prefixWord ++ tailWord_374608).sum := by decide
  have hdescent : baseEnd_374608 < baseStart_374608 := by decide
  rcases family_descends (prefixWord ++ tailWord_374608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374611 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_374611 : Nat := 118140960795 + 374611 * 2 ^ 59
def prefixEnd_374611 : Nat := 4983230072969 + 3 ^ 40 * 374611 * 2
def baseEnd_374611 : Nat := 192355501461539066439701

theorem tailTrace_374611 : CollatzResearch.WordTrace tailWord_374611 prefixEnd_374611 192355501461539066439701 := by
  unfold tailWord_374611
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663185645855800310323687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9108790430570533540215791 13663185645855800310323687)
  ·
    refine ⟨20494778468783700465485531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663185645855800310323687 20494778468783700465485531)
    ·
      refine ⟨30742167703175550698228297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20494778468783700465485531 30742167703175550698228297)
      ·
        refine ⟨23056625777381663023671223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30742167703175550698228297 23056625777381663023671223)
        ·
          refine ⟨34584938666072494535506835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23056625777381663023671223 34584938666072494535506835)
          ·
            refine ⟨51877407999108741803260253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34584938666072494535506835 51877407999108741803260253)
            ·
              refine ⟨19454027999665778176222595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51877407999108741803260253 19454027999665778176222595)
              ·
                refine ⟨29181041999498667264333893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19454027999665778176222595 29181041999498667264333893)
                ·
                  refine ⟨5471445374906000112062605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29181041999498667264333893 5471445374906000112062605)
                  ·
                    refine ⟨2051792015589750042023477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5471445374906000112062605 2051792015589750042023477)
                    ·
                      refine ⟨192355501461539066439701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2051792015589750042023477 192355501461539066439701)
                      ·
                        rfl

theorem cell23_374611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_374611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374611 prefixEnd_374611 := by exact prefixLift 374611
  have htrace : WordTrace (prefixWord ++ tailWord_374611) baseStart_374611 baseEnd_374611 := by
    simpa [prefixWord, tailWord_374611, baseEnd_374611] using wordTrace_append hprefix tailTrace_374611
  have hstable : (prefixWord ++ tailWord_374611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374611).length < 2 ^ (prefixWord ++ tailWord_374611).sum := by decide
  have hdescent : baseEnd_374611 < baseStart_374611 := by decide
  rcases family_descends (prefixWord ++ tailWord_374611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374645 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_374645 : Nat := 118140960795 + 374645 * 2 ^ 59
def prefixEnd_374645 : Nat := 4983230072969 + 3 ^ 40 * 374645 * 2
def baseEnd_374645 : Nat := 192372959803791933414545

theorem tailTrace_374645 : CollatzResearch.WordTrace tailWord_374645 prefixEnd_374645 192372959803791933414545 := by
  unfold tailWord_374645
  simp only [CollatzResearch.WordTrace]
  refine ⟨13664425727732624117061389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9109617151821749411374259 13664425727732624117061389)
  ·
    refine ⟨5124159647899734043898021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13664425727732624117061389 5124159647899734043898021)
    ·
      refine ⟨960779933981200133230879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5124159647899734043898021 960779933981200133230879)
      ·
        refine ⟨1441169900971800199846319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960779933981200133230879 1441169900971800199846319)
        ·
          refine ⟨2161754851457700299769479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441169900971800199846319 2161754851457700299769479)
          ·
            refine ⟨3242632277186550449654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161754851457700299769479 3242632277186550449654219)
            ·
              refine ⟨4863948415779825674481329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242632277186550449654219 4863948415779825674481329)
              ·
                refine ⟨3647961311834869255860997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863948415779825674481329 3647961311834869255860997)
                ·
                  refine ⟨683992745969037985473937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3647961311834869255860997 683992745969037985473937)
                  ·
                    refine ⟨512994559476778489105453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683992745969037985473937 512994559476778489105453)
                    ·
                      refine ⟨192372959803791933414545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 512994559476778489105453 192372959803791933414545)
                      ·
                        rfl

theorem cell23_374645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_374645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374645 prefixEnd_374645 := by exact prefixLift 374645
  have htrace : WordTrace (prefixWord ++ tailWord_374645) baseStart_374645 baseEnd_374645 := by
    simpa [prefixWord, tailWord_374645, baseEnd_374645] using wordTrace_append hprefix tailTrace_374645
  have hstable : (prefixWord ++ tailWord_374645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374645).length < 2 ^ (prefixWord ++ tailWord_374645).sum := by decide
  have hdescent : baseEnd_374645 < baseStart_374645 := by decide
  rcases family_descends (prefixWord ++ tailWord_374645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374695 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 3, 5]
def baseStart_374695 : Nat := 118140960795 + 374695 * 2 ^ 59
def prefixEnd_374695 : Nat := 4983230072969 + 3 ^ 40 * 374695 * 2
def baseEnd_374695 : Nat := 64132877945505579263105

theorem tailTrace_374695 : CollatzResearch.WordTrace tailWord_374695 prefixEnd_374695 64132877945505579263105 := by
  unfold tailWord_374695
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666249377551482656381539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9110832918367655104254359 13666249377551482656381539)
  ·
    refine ⟨20499374066327223984572309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13666249377551482656381539 20499374066327223984572309)
    ·
      refine ⟨960908159359088624276827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20499374066327223984572309 960908159359088624276827)
      ·
        refine ⟨1441362239038632936415241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960908159359088624276827 1441362239038632936415241)
        ·
          refine ⟨1081021679278974702311431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441362239038632936415241 1081021679278974702311431)
          ·
            refine ⟨1621532518918462053467147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081021679278974702311431 1621532518918462053467147)
            ·
              refine ⟨2432298778377693080200721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621532518918462053467147 2432298778377693080200721)
              ·
                refine ⟨1824224083783269810150541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432298778377693080200721 1824224083783269810150541)
                ·
                  refine ⟨684084031418726178806453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1824224083783269810150541 684084031418726178806453)
                  ·
                    refine ⟨64132877945505579263105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 684084031418726178806453 64132877945505579263105)
                    ·
                      rfl

theorem cell23_374695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_374695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374695 prefixEnd_374695 := by exact prefixLift 374695
  have htrace : WordTrace (prefixWord ++ tailWord_374695) baseStart_374695 baseEnd_374695 := by
    simpa [prefixWord, tailWord_374695, baseEnd_374695] using wordTrace_append hprefix tailTrace_374695
  have hstable : (prefixWord ++ tailWord_374695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374695).length < 2 ^ (prefixWord ++ tailWord_374695).sum := by decide
  have hdescent : baseEnd_374695 < baseStart_374695 := by decide
  rcases family_descends (prefixWord ++ tailWord_374695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374732 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_374732 : Nat := 118140960795 + 374732 * 2 ^ 59
def prefixEnd_374732 : Nat := 4983230072969 + 3 ^ 40 * 374732 * 2
def baseEnd_374732 : Nat := 192417632620733093026645

theorem tailTrace_374732 : CollatzResearch.WordTrace tailWord_374732 prefixEnd_374732 192417632620733093026645 := by
  unfold tailWord_374732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6833799439208718987739225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9111732585611625316985633 6833799439208718987739225)
  ·
    refine ⟨5125349579406539240804419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6833799439208718987739225 5125349579406539240804419)
    ·
      refine ⟨7688024369109808861206629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5125349579406539240804419 7688024369109808861206629)
      ·
        refine ⟨1441504569208089161476243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7688024369109808861206629 1441504569208089161476243)
        ·
          refine ⟨2162256853812133742214365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441504569208089161476243 2162256853812133742214365)
          ·
            refine ⟨810846320179550153330387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2162256853812133742214365 810846320179550153330387)
            ·
              refine ⟨1216269480269325229995581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810846320179550153330387 1216269480269325229995581)
              ·
                refine ⟨456101055100996961248343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216269480269325229995581 456101055100996961248343)
                ·
                  refine ⟨684151582651495441872515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456101055100996961248343 684151582651495441872515)
                  ·
                    refine ⟨1026227373977243162808773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684151582651495441872515 1026227373977243162808773)
                    ·
                      refine ⟨192417632620733093026645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1026227373977243162808773 192417632620733093026645)
                      ·
                        rfl

theorem cell23_374732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_374732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374732 prefixEnd_374732 := by exact prefixLift 374732
  have htrace : WordTrace (prefixWord ++ tailWord_374732) baseStart_374732 baseEnd_374732 := by
    simpa [prefixWord, tailWord_374732, baseEnd_374732] using wordTrace_append hprefix tailTrace_374732
  have hstable : (prefixWord ++ tailWord_374732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374732).length < 2 ^ (prefixWord ++ tailWord_374732).sum := by decide
  have hdescent : baseEnd_374732 < baseStart_374732 := by decide
  rcases family_descends (prefixWord ++ tailWord_374732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374759 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 1, 6]
def baseStart_374759 : Nat := 118140960795 + 374759 * 2 ^ 59
def prefixEnd_374759 : Nat := 4983230072969 + 3 ^ 40 * 374759 * 2
def baseEnd_374759 : Nat := 64143832199468162463007

theorem tailTrace_374759 : CollatzResearch.WordTrace tailWord_374759 prefixEnd_374759 64143832199468162463007 := by
  unfold tailWord_374759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13668583649319621586711331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9112389099546414391140887 13668583649319621586711331)
  ·
    refine ⟨20502875473979432380066997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13668583649319621586711331 20502875473979432380066997)
    ·
      refine ⟨1922144575685571785631281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20502875473979432380066997 1922144575685571785631281)
      ·
        refine ⟨1441608431764178839223461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1922144575685571785631281 1441608431764178839223461)
        ·
          refine ⟨270301580955783532354399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1441608431764178839223461 270301580955783532354399)
          ·
            refine ⟨405452371433675298531599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270301580955783532354399 405452371433675298531599)
            ·
              refine ⟨608178557150512947797399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405452371433675298531599 608178557150512947797399)
              ·
                refine ⟨912267835725769421696099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608178557150512947797399 912267835725769421696099)
                ·
                  refine ⟨1368401753588654132544149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912267835725769421696099 1368401753588654132544149)
                  ·
                    refine ⟨64143832199468162463007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1368401753588654132544149 64143832199468162463007)
                    ·
                      rfl

theorem cell23_374759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_374759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374759 prefixEnd_374759 := by exact prefixLift 374759
  have htrace : WordTrace (prefixWord ++ tailWord_374759) baseStart_374759 baseEnd_374759 := by
    simpa [prefixWord, tailWord_374759, baseEnd_374759] using wordTrace_append hprefix tailTrace_374759
  have hstable : (prefixWord ++ tailWord_374759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374759).length < 2 ^ (prefixWord ++ tailWord_374759).sum := by decide
  have hdescent : baseEnd_374759 < baseStart_374759 := by decide
  rcases family_descends (prefixWord ++ tailWord_374759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374768 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_374768 : Nat := 118140960795 + 374768 * 2 ^ 59
def prefixEnd_374768 : Nat := 4983230072969 + 3 ^ 40 * 374768 * 2
def baseEnd_374768 : Nat := 64145372641431650725493

theorem tailTrace_374768 : CollatzResearch.WordTrace tailWord_374768 prefixEnd_374768 64145372641431650725493 := by
  unfold tailWord_374768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6834455953143508061894479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9112607937524677415859305 6834455953143508061894479)
  ·
    refine ⟨10251683929715262092841719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6834455953143508061894479 10251683929715262092841719)
    ·
      refine ⟨15377525894572893139262579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10251683929715262092841719 15377525894572893139262579)
      ·
        refine ⟨23066288841859339708893869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15377525894572893139262579 23066288841859339708893869)
        ·
          refine ⟨8649858315697252390835201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23066288841859339708893869 8649858315697252390835201)
          ·
            refine ⟨6487393736772939293126401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8649858315697252390835201 6487393736772939293126401)
            ·
              refine ⟨4865545302579704469844801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487393736772939293126401 4865545302579704469844801)
              ·
                refine ⟨3649158976934778352383601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865545302579704469844801 3649158976934778352383601)
                ·
                  refine ⟨2736869232701083764287701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649158976934778352383601 2736869232701083764287701)
                  ·
                    refine ⟨64145372641431650725493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2736869232701083764287701 64145372641431650725493)
                    ·
                      rfl

theorem cell23_374768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_374768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374768 prefixEnd_374768 := by exact prefixLift 374768
  have htrace : WordTrace (prefixWord ++ tailWord_374768) baseStart_374768 baseEnd_374768 := by
    simpa [prefixWord, tailWord_374768, baseEnd_374768] using wordTrace_append hprefix tailTrace_374768
  have hstable : (prefixWord ++ tailWord_374768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374768).length < 2 ^ (prefixWord ++ tailWord_374768).sum := by decide
  have hdescent : baseEnd_374768 < baseStart_374768 := by decide
  rcases family_descends (prefixWord ++ tailWord_374768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374769 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_374769 : Nat := 118140960795 + 374769 * 2 ^ 59
def prefixEnd_374769 : Nat := 4983230072969 + 3 ^ 40 * 374769 * 2
def baseEnd_374769 : Nat := 192436631404949448263975

theorem tailTrace_374769 : CollatzResearch.WordTrace tailWord_374769 prefixEnd_374769 192436631404949448263975 := by
  unfold tailWord_374769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13668948379283393294575361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9112632252855595529716907 13668948379283393294575361)
  ·
    refine ⟨10251711284462544970931521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13668948379283393294575361 10251711284462544970931521)
    ·
      refine ⟨7688783463346908728198641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10251711284462544970931521 7688783463346908728198641)
      ·
        refine ⟨5766587597510181546148981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7688783463346908728198641 5766587597510181546148981)
        ·
          refine ⟨540617587266579519951467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5766587597510181546148981 540617587266579519951467)
          ·
            refine ⟨810926380899869279927201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540617587266579519951467 810926380899869279927201)
            ·
              refine ⟨608194785674901959945401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810926380899869279927201 608194785674901959945401)
              ·
                refine ⟨456146089256176469959051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608194785674901959945401 456146089256176469959051)
                ·
                  refine ⟨684219133884264704938577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456146089256176469959051 684219133884264704938577)
                  ·
                    refine ⟨513164350413198528703933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 684219133884264704938577 513164350413198528703933)
                    ·
                      refine ⟨192436631404949448263975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 513164350413198528703933 192436631404949448263975)
                      ·
                        rfl

theorem cell23_374769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_374769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374769 prefixEnd_374769 := by exact prefixLift 374769
  have htrace : WordTrace (prefixWord ++ tailWord_374769) baseStart_374769 baseEnd_374769 := by
    simpa [prefixWord, tailWord_374769, baseEnd_374769] using wordTrace_append hprefix tailTrace_374769
  have hstable : (prefixWord ++ tailWord_374769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374769).length < 2 ^ (prefixWord ++ tailWord_374769).sum := by decide
  have hdescent : baseEnd_374769 < baseStart_374769 := by decide
  rcases family_descends (prefixWord ++ tailWord_374769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_374775 : Nat := 118140960795 + 374775 * 2 ^ 59
def prefixEnd_374775 : Nat := 4983230072969 + 3 ^ 40 * 374775 * 2
def baseEnd_374775 : Nat := 192439712288876424788947

theorem tailTrace_374775 : CollatzResearch.WordTrace tailWord_374775 prefixEnd_374775 192439712288876424788947 := by
  unfold tailWord_374775
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669167217261656319293779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9112778144841104212862519 13669167217261656319293779)
  ·
    refine ⟨20503750825892484478940669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13669167217261656319293779 20503750825892484478940669)
    ·
      refine ⟨7688906559709681679602751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20503750825892484478940669 7688906559709681679602751)
      ·
        refine ⟨11533359839564522519404127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688906559709681679602751 11533359839564522519404127)
        ·
          refine ⟨17300039759346783779106191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533359839564522519404127 17300039759346783779106191)
          ·
            refine ⟨25950059639020175668659287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17300039759346783779106191 25950059639020175668659287)
            ·
              refine ⟨38925089458530263502988931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25950059639020175668659287 38925089458530263502988931)
              ·
                refine ⟨58387634187795395254483397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38925089458530263502988931 58387634187795395254483397)
                ·
                  refine ⟨10947681410211636610215637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58387634187795395254483397 10947681410211636610215637)
                  ·
                    refine ⟨256586283051835233051929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10947681410211636610215637 256586283051835233051929)
                    ·
                      refine ⟨192439712288876424788947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256586283051835233051929 192439712288876424788947)
                      ·
                        rfl

theorem cell23_374775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_374775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374775 prefixEnd_374775 := by exact prefixLift 374775
  have htrace : WordTrace (prefixWord ++ tailWord_374775) baseStart_374775 baseEnd_374775 := by
    simpa [prefixWord, tailWord_374775, baseEnd_374775] using wordTrace_append hprefix tailTrace_374775
  have hstable : (prefixWord ++ tailWord_374775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374775).length < 2 ^ (prefixWord ++ tailWord_374775).sum := by decide
  have hdescent : baseEnd_374775 < baseStart_374775 := by decide
  rcases family_descends (prefixWord ++ tailWord_374775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374826 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_374826 : Nat := 118140960795 + 374826 * 2 ^ 59
def prefixEnd_374826 : Nat := 4983230072969 + 3 ^ 40 * 374826 * 2
def baseEnd_374826 : Nat := 192465899802255725251213

theorem tailTrace_374826 : CollatzResearch.WordTrace tailWord_374826 prefixEnd_374826 192465899802255725251213 := by
  unfold tailWord_374826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417756835019223007350083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9114018226717928019600221 3417756835019223007350083)
  ·
    refine ⟨5126635252528834511025125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417756835019223007350083 5126635252528834511025125)
    ·
      refine ⟨961244109849156470817211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5126635252528834511025125 961244109849156470817211)
      ·
        refine ⟨1441866164773734706225817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961244109849156470817211 1441866164773734706225817)
        ·
          refine ⟨1081399623580301029669363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441866164773734706225817 1081399623580301029669363)
          ·
            refine ⟨1622099435370451544504045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081399623580301029669363 1622099435370451544504045)
            ·
              refine ⟨608287288263919329189017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1622099435370451544504045 608287288263919329189017)
              ·
                refine ⟨456215466197939496891763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608287288263919329189017 456215466197939496891763)
                ·
                  refine ⟨684323199296909245337645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456215466197939496891763 684323199296909245337645)
                  ·
                    refine ⟨256621199736340967001617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684323199296909245337645 256621199736340967001617)
                    ·
                      refine ⟨192465899802255725251213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256621199736340967001617 192465899802255725251213)
                      ·
                        rfl

theorem cell23_374826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_374826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374826 prefixEnd_374826 := by exact prefixLift 374826
  have htrace : WordTrace (prefixWord ++ tailWord_374826) baseStart_374826 baseEnd_374826 := by
    simpa [prefixWord, tailWord_374826, baseEnd_374826] using wordTrace_append hprefix tailTrace_374826
  have hstable : (prefixWord ++ tailWord_374826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374826).length < 2 ^ (prefixWord ++ tailWord_374826).sum := by decide
  have hdescent : baseEnd_374826 < baseStart_374826 := by decide
  rcases family_descends (prefixWord ++ tailWord_374826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374872 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_374872 : Nat := 118140960795 + 374872 * 2 ^ 59
def prefixEnd_374872 : Nat := 4983230072969 + 3 ^ 40 * 374872 * 2
def baseEnd_374872 : Nat := 192489519912362545276001

theorem tailTrace_374872 : CollatzResearch.WordTrace tailWord_374872 prefixEnd_374872 192489519912362545276001 := by
  unfold tailWord_374872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836352548955120942787435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9115136731940161257049913 6836352548955120942787435)
  ·
    refine ⟨10254528823432681414181153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836352548955120942787435 10254528823432681414181153)
    ·
      refine ⟨7690896617574511060635865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10254528823432681414181153 7690896617574511060635865)
      ·
        refine ⟨5768172463180883295476899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7690896617574511060635865 5768172463180883295476899)
        ·
          refine ⟨8652258694771324943215349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768172463180883295476899 8652258694771324943215349)
          ·
            refine ⟨811149252634811713426439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8652258694771324943215349 811149252634811713426439)
            ·
              refine ⟨1216723878952217570139659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811149252634811713426439 1216723878952217570139659)
              ·
                refine ⟨1825085818428326355209489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216723878952217570139659 1825085818428326355209489)
                ·
                  refine ⟨1368814363821244766407117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825085818428326355209489 1368814363821244766407117)
                  ·
                    refine ⟨513305386432966787402669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368814363821244766407117 513305386432966787402669)
                    ·
                      refine ⟨192489519912362545276001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 513305386432966787402669 192489519912362545276001)
                      ·
                        rfl

theorem cell23_374872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_374872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374872 prefixEnd_374872 := by exact prefixLift 374872
  have htrace : WordTrace (prefixWord ++ tailWord_374872) baseStart_374872 baseEnd_374872 := by
    simpa [prefixWord, tailWord_374872, baseEnd_374872] using wordTrace_append hprefix tailTrace_374872
  have hstable : (prefixWord ++ tailWord_374872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374872).length < 2 ^ (prefixWord ++ tailWord_374872).sum := by decide
  have hdescent : baseEnd_374872 < baseStart_374872 := by decide
  rcases family_descends (prefixWord ++ tailWord_374872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374892 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_374892 : Nat := 118140960795 + 374892 * 2 ^ 59
def prefixEnd_374892 : Nat := 4983230072969 + 3 ^ 40 * 374892 * 2
def baseEnd_374892 : Nat := 64166596508484155675303

theorem tailTrace_374892 : CollatzResearch.WordTrace tailWord_374892 prefixEnd_374892 64166596508484155675303 := by
  unfold tailWord_374892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836717278918892650651465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9115623038558523534201953 6836717278918892650651465)
  ·
    refine ⟨5127537959189169487988599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6836717278918892650651465 5127537959189169487988599)
    ·
      refine ⟨7691306938783754231982899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127537959189169487988599 7691306938783754231982899)
      ·
        refine ⟨11536960408175631347974349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691306938783754231982899 11536960408175631347974349)
        ·
          refine ⟨4326360153065861755490381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11536960408175631347974349 4326360153065861755490381)
          ·
            refine ⟨1622385057399698158308893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4326360153065861755490381 1622385057399698158308893)
            ·
              refine ⟨608394396524886809365835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1622385057399698158308893 608394396524886809365835)
              ·
                refine ⟨912591594787330214048753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608394396524886809365835 912591594787330214048753)
                ·
                  refine ⟨684443696090497660536565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912591594787330214048753 684443696090497660536565)
                  ·
                    refine ⟨64166596508484155675303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 684443696090497660536565 64166596508484155675303)
                    ·
                      rfl

theorem cell23_374892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_374892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374892 prefixEnd_374892 := by exact prefixLift 374892
  have htrace : WordTrace (prefixWord ++ tailWord_374892) baseStart_374892 baseEnd_374892 := by
    simpa [prefixWord, tailWord_374892, baseEnd_374892] using wordTrace_append hprefix tailTrace_374892
  have hstable : (prefixWord ++ tailWord_374892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374892).length < 2 ^ (prefixWord ++ tailWord_374892).sum := by decide
  have hdescent : baseEnd_374892 < baseStart_374892 := by decide
  rcases family_descends (prefixWord ++ tailWord_374892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374975 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_374975 : Nat := 118140960795 + 374975 * 2 ^ 59
def prefixEnd_374975 : Nat := 4983230072969 + 3 ^ 40 * 374975 * 2
def baseEnd_374975 : Nat := 192542408419775642288027

theorem tailTrace_374975 : CollatzResearch.WordTrace tailWord_374975 prefixEnd_374975 192542408419775642288027 := by
  unfold tailWord_374975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676461816537090476574379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9117641211024726984382919 13676461816537090476574379)
  ·
    refine ⟨20514692724805635714861569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13676461816537090476574379 20514692724805635714861569)
    ·
      refine ⟨15386019543604226786146177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20514692724805635714861569 15386019543604226786146177)
      ·
        refine ⟨11539514657703170089609633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15386019543604226786146177 11539514657703170089609633)
        ·
          refine ⟨8654635993277377567207225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11539514657703170089609633 8654635993277377567207225)
          ·
            refine ⟨6490976994958033175405419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8654635993277377567207225 6490976994958033175405419)
            ·
              refine ⟨9736465492437049763108129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490976994958033175405419 9736465492437049763108129)
              ·
                refine ⟨7302349119327787322331097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9736465492437049763108129 7302349119327787322331097)
                ·
                  refine ⟨5476761839495840491748323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302349119327787322331097 5476761839495840491748323)
                  ·
                    refine ⟨8215142759243760737622485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476761839495840491748323 8215142759243760737622485)
                    ·
                      refine ⟨192542408419775642288027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8215142759243760737622485 192542408419775642288027)
                      ·
                        rfl

theorem cell23_374975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_374975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_374975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_374975 prefixEnd_374975 := by exact prefixLift 374975
  have htrace : WordTrace (prefixWord ++ tailWord_374975) baseStart_374975 baseEnd_374975 := by
    simpa [prefixWord, tailWord_374975, baseEnd_374975] using wordTrace_append hprefix tailTrace_374975
  have hstable : (prefixWord ++ tailWord_374975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374975).length < 2 ^ (prefixWord ++ tailWord_374975).sum := by decide
  have hdescent : baseEnd_374975 < baseStart_374975 := by decide
  rcases family_descends (prefixWord ++ tailWord_374975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375016 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 1, 5]
def baseStart_375016 : Nat := 118140960795 + 375016 * 2 ^ 59
def prefixEnd_375016 : Nat := 4983230072969 + 3 ^ 40 * 375016 * 2
def baseEnd_375016 : Nat := 64187820375536660625113

theorem tailTrace_375016 : CollatzResearch.WordTrace tailWord_375016 prefixEnd_375016 64187820375536660625113 := by
  unfold tailWord_375016
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838978604694277239408451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9118638139592369652544601 6838978604694277239408451)
  ·
    refine ⟨10258467907041415859112677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838978604694277239408451 10258467907041415859112677)
    ·
      refine ⟨1923462732570265473583627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10258467907041415859112677 1923462732570265473583627)
      ·
        refine ⟨2885194098855398210375441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923462732570265473583627 2885194098855398210375441)
        ·
          refine ⟨2163895574141548657781581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2885194098855398210375441 2163895574141548657781581)
          ·
            refine ⟨811460840303080746668093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2163895574141548657781581 811460840303080746668093)
            ·
              refine ⟨304297815113655280000535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 811460840303080746668093 304297815113655280000535)
              ·
                refine ⟨456446722670482920000803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304297815113655280000535 456446722670482920000803)
                ·
                  refine ⟨684670084005724380001205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456446722670482920000803 684670084005724380001205)
                  ·
                    refine ⟨64187820375536660625113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 684670084005724380001205 64187820375536660625113)
                    ·
                      rfl

theorem cell23_375016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_375016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375016 prefixEnd_375016 := by exact prefixLift 375016
  have htrace : WordTrace (prefixWord ++ tailWord_375016) baseStart_375016 baseEnd_375016 := by
    simpa [prefixWord, tailWord_375016, baseEnd_375016] using wordTrace_append hprefix tailTrace_375016
  have hstable : (prefixWord ++ tailWord_375016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375016).length < 2 ^ (prefixWord ++ tailWord_375016).sum := by decide
  have hdescent : baseEnd_375016 < baseStart_375016 := by decide
  rcases family_descends (prefixWord ++ tailWord_375016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375030 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_375030 : Nat := 118140960795 + 375030 * 2 ^ 59
def prefixEnd_375030 : Nat := 4983230072969 + 3 ^ 40 * 375030 * 2
def baseEnd_375030 : Nat := 192570649855772927100275

theorem tailTrace_375030 : CollatzResearch.WordTrace tailWord_375030 prefixEnd_375030 192570649855772927100275 := by
  unfold tailWord_375030
  simp only [CollatzResearch.WordTrace]
  refine ⟨854904239458614679364159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9118978554225223246551029 854904239458614679364159)
  ·
    refine ⟨1282356359187922019046239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 854904239458614679364159 1282356359187922019046239)
    ·
      refine ⟨1923534538781883028569359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282356359187922019046239 1923534538781883028569359)
      ·
        refine ⟨2885301808172824542854039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923534538781883028569359 2885301808172824542854039)
        ·
          refine ⟨4327952712259236814281059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885301808172824542854039 4327952712259236814281059)
          ·
            refine ⟨6491929068388855221421589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327952712259236814281059 6491929068388855221421589)
            ·
              refine ⟨304309175080727588504137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6491929068388855221421589 304309175080727588504137)
              ·
                refine ⟨228231881310545691378103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304309175080727588504137 228231881310545691378103)
                ·
                  refine ⟨342347821965818537067155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228231881310545691378103 342347821965818537067155)
                  ·
                    refine ⟨513521732948727805600733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 342347821965818537067155 513521732948727805600733)
                    ·
                      refine ⟨192570649855772927100275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 513521732948727805600733 192570649855772927100275)
                      ·
                        rfl

theorem cell23_375030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_375030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375030 prefixEnd_375030 := by exact prefixLift 375030
  have htrace : WordTrace (prefixWord ++ tailWord_375030) baseStart_375030 baseEnd_375030 := by
    simpa [prefixWord, tailWord_375030, baseEnd_375030] using wordTrace_append hprefix tailTrace_375030
  have hstable : (prefixWord ++ tailWord_375030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375030).length < 2 ^ (prefixWord ++ tailWord_375030).sum := by decide
  have hdescent : baseEnd_375030 < baseStart_375030 := by decide
  rcases family_descends (prefixWord ++ tailWord_375030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375049 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_375049 : Nat := 118140960795 + 375049 * 2 ^ 59
def prefixEnd_375049 : Nat := 4983230072969 + 3 ^ 40 * 375049 * 2
def baseEnd_375049 : Nat := 192580405988208352762687

theorem tailTrace_375049 : CollatzResearch.WordTrace tailWord_375049 prefixEnd_375049 192580405988208352762687 := by
  unfold tailWord_375049
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679160818269001114768201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9119440545512667409845467 13679160818269001114768201)
  ·
    refine ⟨10259370613701750836076151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13679160818269001114768201 10259370613701750836076151)
    ·
      refine ⟨15389055920552626254114227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10259370613701750836076151 15389055920552626254114227)
      ·
        refine ⟨23083583880828939381171341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15389055920552626254114227 23083583880828939381171341)
        ·
          refine ⟨8656343955310852267939253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23083583880828939381171341 8656343955310852267939253)
          ·
            refine ⟨811532245810392400119305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8656343955310852267939253 811532245810392400119305)
            ·
              refine ⟨608649184357794300089479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811532245810392400119305 608649184357794300089479)
              ·
                refine ⟨912973776536691450134219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608649184357794300089479 912973776536691450134219)
                ·
                  refine ⟨1369460664805037175201329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912973776536691450134219 1369460664805037175201329)
                  ·
                    refine ⟨1027095498603777881400997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1369460664805037175201329 1027095498603777881400997)
                    ·
                      refine ⟨192580405988208352762687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1027095498603777881400997 192580405988208352762687)
                      ·
                        rfl

theorem cell23_375049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_375049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375049 prefixEnd_375049 := by exact prefixLift 375049
  have htrace : WordTrace (prefixWord ++ tailWord_375049) baseStart_375049 baseEnd_375049 := by
    simpa [prefixWord, tailWord_375049, baseEnd_375049] using wordTrace_append hprefix tailTrace_375049
  have hstable : (prefixWord ++ tailWord_375049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375049).length < 2 ^ (prefixWord ++ tailWord_375049).sum := by decide
  have hdescent : baseEnd_375049 < baseStart_375049 := by decide
  rcases family_descends (prefixWord ++ tailWord_375049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375070 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_375070 : Nat := 118140960795 + 375070 * 2 ^ 59
def prefixEnd_375070 : Nat := 4983230072969 + 3 ^ 40 * 375070 * 2
def baseEnd_375070 : Nat := 192591189081952770600091

theorem tailTrace_375070 : CollatzResearch.WordTrace tailWord_375070 prefixEnd_375070 192591189081952770600091 := by
  unfold tailWord_375070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709990843899115212660333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9119951167461947800855109 1709990843899115212660333)
  ·
    refine ⟨641246566462168204747625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1709990843899115212660333 641246566462168204747625)
    ·
      refine ⟨480934924846626153560719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 641246566462168204747625 480934924846626153560719)
      ·
        refine ⟨721402387269939230341079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480934924846626153560719 721402387269939230341079)
        ·
          refine ⟨1082103580904908845511619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721402387269939230341079 1082103580904908845511619)
          ·
            refine ⟨1623155371357363268267429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082103580904908845511619 1623155371357363268267429)
            ·
              refine ⟨304341632129505612800143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1623155371357363268267429 304341632129505612800143)
              ·
                refine ⟨456512448194258419200215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304341632129505612800143 456512448194258419200215)
                ·
                  refine ⟨684768672291387628800323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456512448194258419200215 684768672291387628800323)
                  ·
                    refine ⟨1027153008437081443200485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684768672291387628800323 1027153008437081443200485)
                    ·
                      refine ⟨192591189081952770600091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1027153008437081443200485 192591189081952770600091)
                      ·
                        rfl

theorem cell23_375070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_375070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375070 prefixEnd_375070 := by exact prefixLift 375070
  have htrace : WordTrace (prefixWord ++ tailWord_375070) baseStart_375070 baseEnd_375070 := by
    simpa [prefixWord, tailWord_375070, baseEnd_375070] using wordTrace_append hprefix tailTrace_375070
  have hstable : (prefixWord ++ tailWord_375070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375070).length < 2 ^ (prefixWord ++ tailWord_375070).sum := by decide
  have hdescent : baseEnd_375070 < baseStart_375070 := by decide
  rcases family_descends (prefixWord ++ tailWord_375070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375080 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 2, 4]
def baseStart_375080 : Nat := 118140960795 + 375080 * 2 ^ 59
def prefixEnd_375080 : Nat := 4983230072969 + 3 ^ 40 * 375080 * 2
def baseEnd_375080 : Nat := 64198774629499243825015

theorem tailTrace_375080 : CollatzResearch.WordTrace tailWord_375080 prefixEnd_375080 64198774629499243825015 := by
  unfold tailWord_375080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840145740578346704573347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9120194320771128939431129 6840145740578346704573347)
  ·
    refine ⟨10260218610867520056860021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6840145740578346704573347 10260218610867520056860021)
    ·
      refine ⟨961895494768830005330627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10260218610867520056860021 961895494768830005330627)
      ·
        refine ⟨1442843242153245007995941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961895494768830005330627 1442843242153245007995941)
        ·
          refine ⟨270533107903733438999239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1442843242153245007995941 270533107903733438999239)
          ·
            refine ⟨405799661855600158498859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270533107903733438999239 405799661855600158498859)
            ·
              refine ⟨608699492783400237748289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405799661855600158498859 608699492783400237748289)
              ·
                refine ⟨456524619587550178311217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608699492783400237748289 456524619587550178311217)
                ·
                  refine ⟨342393464690662633733413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456524619587550178311217 342393464690662633733413)
                  ·
                    refine ⟨64198774629499243825015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342393464690662633733413 64198774629499243825015)
                    ·
                      rfl

theorem cell23_375080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_375080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375080 prefixEnd_375080 := by exact prefixLift 375080
  have htrace : WordTrace (prefixWord ++ tailWord_375080) baseStart_375080 baseEnd_375080 := by
    simpa [prefixWord, tailWord_375080, baseEnd_375080] using wordTrace_append hprefix tailTrace_375080
  have hstable : (prefixWord ++ tailWord_375080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375080).length < 2 ^ (prefixWord ++ tailWord_375080).sum := by decide
  have hdescent : baseEnd_375080 < baseStart_375080 := by decide
  rcases family_descends (prefixWord ++ tailWord_375080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375103 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 2, 1, 3]
def baseStart_375103 : Nat := 118140960795 + 375103 * 2 ^ 59
def prefixEnd_375103 : Nat := 4983230072969 + 3 ^ 40 * 375103 * 2
def baseEnd_375103 : Nat := 192608133943551141487439

theorem tailTrace_375103 : CollatzResearch.WordTrace tailWord_375103 prefixEnd_375103 192608133943551141487439 := by
  unfold tailWord_375103
  simp only [CollatzResearch.WordTrace]
  refine ⟨13681130360073368337233963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9120753573382245558155975 13681130360073368337233963)
  ·
    refine ⟨20521695540110052505850945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13681130360073368337233963 20521695540110052505850945)
    ·
      refine ⟨15391271655082539379388209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20521695540110052505850945 15391271655082539379388209)
      ·
        refine ⟨11543453741311904534541157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15391271655082539379388209 11543453741311904534541157)
        ·
          refine ⟨2164397576495982100226467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11543453741311904534541157 2164397576495982100226467)
          ·
            refine ⟨3246596364743973150339701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164397576495982100226467 3246596364743973150339701)
            ·
              refine ⟨304368409194747482844347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3246596364743973150339701 304368409194747482844347)
              ·
                refine ⟨456552613792121224266521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304368409194747482844347 456552613792121224266521)
                ·
                  refine ⟨342414460344090918199891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456552613792121224266521 342414460344090918199891)
                  ·
                    refine ⟨513621690516136377299837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 342414460344090918199891 513621690516136377299837)
                    ·
                      refine ⟨192608133943551141487439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 513621690516136377299837 192608133943551141487439)
                      ·
                        rfl

theorem cell23_375103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_375103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375103 prefixEnd_375103 := by exact prefixLift 375103
  have htrace : WordTrace (prefixWord ++ tailWord_375103) baseStart_375103 baseEnd_375103 := by
    simpa [prefixWord, tailWord_375103, baseEnd_375103] using wordTrace_append hprefix tailTrace_375103
  have hstable : (prefixWord ++ tailWord_375103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375103).length < 2 ^ (prefixWord ++ tailWord_375103).sum := by decide
  have hdescent : baseEnd_375103 < baseStart_375103 := by decide
  rcases family_descends (prefixWord ++ tailWord_375103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375143 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_375143 : Nat := 118140960795 + 375143 * 2 ^ 59
def prefixEnd_375143 : Nat := 4983230072969 + 3 ^ 40 * 375143 * 2
def baseEnd_375143 : Nat := 192628673169730984987255

theorem tailTrace_375143 : CollatzResearch.WordTrace tailWord_375143 prefixEnd_375143 192628673169730984987255 := by
  unfold tailWord_375143
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682589279928455168690083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9121726186618970112460055 13682589279928455168690083)
  ·
    refine ⟨20523883919892682753035125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13682589279928455168690083 20523883919892682753035125)
    ·
      refine ⟨1924114117489939008097043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20523883919892682753035125 1924114117489939008097043)
      ·
        refine ⟨2886171176234908512145565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924114117489939008097043 2886171176234908512145565)
        ·
          refine ⟨1082314191088090692054587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2886171176234908512145565 1082314191088090692054587)
          ·
            refine ⟨1623471286632136038081881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082314191088090692054587 1623471286632136038081881)
            ·
              refine ⟨1217603464974102028561411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623471286632136038081881 1217603464974102028561411)
              ·
                refine ⟨1826405197461153042842117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217603464974102028561411 1826405197461153042842117)
                ·
                  refine ⟨342450974523966195532897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826405197461153042842117 342450974523966195532897)
                  ·
                    refine ⟨256838230892974646649673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342450974523966195532897 256838230892974646649673)
                    ·
                      refine ⟨192628673169730984987255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256838230892974646649673 192628673169730984987255)
                      ·
                        rfl

theorem cell23_375143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_375143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375143 prefixEnd_375143 := by exact prefixLift 375143
  have htrace : WordTrace (prefixWord ++ tailWord_375143) baseStart_375143 baseEnd_375143 := by
    simpa [prefixWord, tailWord_375143, baseEnd_375143] using wordTrace_append hprefix tailTrace_375143
  have hstable : (prefixWord ++ tailWord_375143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375143).length < 2 ^ (prefixWord ++ tailWord_375143).sum := by decide
  have hdescent : baseEnd_375143 < baseStart_375143 := by decide
  rcases family_descends (prefixWord ++ tailWord_375143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375179 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 2, 5]
def baseStart_375179 : Nat := 118140960795 + 375179 * 2 ^ 59
def prefixEnd_375179 : Nat := 4983230072969 + 3 ^ 40 * 375179 * 2
def baseEnd_375179 : Nat := 64215719491097614712363

theorem tailTrace_375179 : CollatzResearch.WordTrace tailWord_375179 prefixEnd_375179 64215719491097614712363 := by
  unfold tailWord_375179
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683902307798033317000591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9122601538532022211333727 13683902307798033317000591)
  ·
    refine ⟨20525853461697049975500887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13683902307798033317000591 20525853461697049975500887)
    ·
      refine ⟨30788780192545574963251331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20525853461697049975500887 30788780192545574963251331)
      ·
        refine ⟨46183170288818362444876997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30788780192545574963251331 46183170288818362444876997)
        ·
          refine ⟨8659344429153442958414437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46183170288818362444876997 8659344429153442958414437)
          ·
            refine ⟨1623627080466270554702707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8659344429153442958414437 1623627080466270554702707)
            ·
              refine ⟨2435440620699405832054061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623627080466270554702707 2435440620699405832054061)
              ·
                refine ⟨913290232762277187020273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2435440620699405832054061 913290232762277187020273)
                ·
                  refine ⟨684967674571707890265205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913290232762277187020273 684967674571707890265205)
                  ·
                    refine ⟨64215719491097614712363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 684967674571707890265205 64215719491097614712363)
                    ·
                      rfl

theorem cell23_375179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 5].length) (baseStart_375179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375179 prefixEnd_375179 := by exact prefixLift 375179
  have htrace : WordTrace (prefixWord ++ tailWord_375179) baseStart_375179 baseEnd_375179 := by
    simpa [prefixWord, tailWord_375179, baseEnd_375179] using wordTrace_append hprefix tailTrace_375179
  have hstable : (prefixWord ++ tailWord_375179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375179).length < 2 ^ (prefixWord ++ tailWord_375179).sum := by decide
  have hdescent : baseEnd_375179 < baseStart_375179 := by decide
  rcases family_descends (prefixWord ++ tailWord_375179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375209 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_375209 : Nat := 118140960795 + 375209 * 2 ^ 59
def prefixEnd_375209 : Nat := 4983230072969 + 3 ^ 40 * 375209 * 2
def baseEnd_375209 : Nat := 64220854297642575587317

theorem tailTrace_375209 : CollatzResearch.WordTrace tailWord_375209 prefixEnd_375209 64220854297642575587317 := by
  unfold tailWord_375209
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684996497689348440592681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9123330998459565627061787 13684996497689348440592681)
  ·
    refine ⟨10263747373267011330444511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13684996497689348440592681 10263747373267011330444511)
    ·
      refine ⟨15395621059900516995666767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10263747373267011330444511 15395621059900516995666767)
      ·
        refine ⟨23093431589850775493500151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15395621059900516995666767 23093431589850775493500151)
        ·
          refine ⟨34640147384776163240250227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23093431589850775493500151 34640147384776163240250227)
          ·
            refine ⟨51960221077164244860375341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34640147384776163240250227 51960221077164244860375341)
            ·
              refine ⟨19485082903936591822640753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51960221077164244860375341 19485082903936591822640753)
              ·
                refine ⟨14613812177952443866980565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19485082903936591822640753 14613812177952443866980565)
                ·
                  refine ⟨342511222920760403132357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14613812177952443866980565 342511222920760403132357)
                  ·
                    refine ⟨64220854297642575587317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342511222920760403132357 64220854297642575587317)
                    ·
                      rfl

theorem cell23_375209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_375209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375209 prefixEnd_375209 := by exact prefixLift 375209
  have htrace : WordTrace (prefixWord ++ tailWord_375209) baseStart_375209 baseEnd_375209 := by
    simpa [prefixWord, tailWord_375209, baseEnd_375209] using wordTrace_append hprefix tailTrace_375209
  have hstable : (prefixWord ++ tailWord_375209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375209).length < 2 ^ (prefixWord ++ tailWord_375209).sum := by decide
  have hdescent : baseEnd_375209 < baseStart_375209 := by decide
  rcases family_descends (prefixWord ++ tailWord_375209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375249 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_375249 : Nat := 118140960795 + 375249 * 2 ^ 59
def prefixEnd_375249 : Nat := 4983230072969 + 3 ^ 40 * 375249 * 2
def baseEnd_375249 : Nat := 192683102119107570261767

theorem tailTrace_375249 : CollatzResearch.WordTrace tailWord_375249 prefixEnd_375249 192683102119107570261767 := by
  unfold tailWord_375249
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686455417544435272048801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9124303611696290181365867 13686455417544435272048801)
  ·
    refine ⟨10264841563158326454036601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13686455417544435272048801 10264841563158326454036601)
    ·
      refine ⟨7698631172368744840527451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10264841563158326454036601 7698631172368744840527451)
      ·
        refine ⟨11547946758553117260791177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7698631172368744840527451 11547946758553117260791177)
        ·
          refine ⟨8660960068914837945593383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547946758553117260791177 8660960068914837945593383)
          ·
            refine ⟨12991440103372256918390075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660960068914837945593383 12991440103372256918390075)
            ·
              refine ⟨19487160155058385377585113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12991440103372256918390075 19487160155058385377585113)
              ·
                refine ⟨14615370116293789033188835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19487160155058385377585113 14615370116293789033188835)
                ·
                  refine ⟨21923055174440683549783253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14615370116293789033188835 21923055174440683549783253)
                  ·
                    refine ⟨513821605650953520698045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21923055174440683549783253 513821605650953520698045)
                    ·
                      refine ⟨192683102119107570261767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 513821605650953520698045 192683102119107570261767)
                      ·
                        rfl

theorem cell23_375249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_375249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375249 prefixEnd_375249 := by exact prefixLift 375249
  have htrace : WordTrace (prefixWord ++ tailWord_375249) baseStart_375249 baseEnd_375249 := by
    simpa [prefixWord, tailWord_375249, baseEnd_375249] using wordTrace_append hprefix tailTrace_375249
  have hstable : (prefixWord ++ tailWord_375249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375249).length < 2 ^ (prefixWord ++ tailWord_375249).sum := by decide
  have hdescent : baseEnd_375249 < baseStart_375249 := by decide
  rcases family_descends (prefixWord ++ tailWord_375249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375276 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_375276 : Nat := 118140960795 + 375276 * 2 ^ 59
def prefixEnd_375276 : Nat := 4983230072969 + 3 ^ 40 * 375276 * 2
def baseEnd_375276 : Nat := 192696966096778964624143

theorem tailTrace_375276 : CollatzResearch.WordTrace tailWord_375276 prefixEnd_375276 192696966096778964624143 := by
  unfold tailWord_375276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843720094223309441640841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9124960125631079255521121 6843720094223309441640841)
  ·
    refine ⟨5132790070667482081230631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6843720094223309441640841 5132790070667482081230631)
    ·
      refine ⟨7699185106001223121845947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132790070667482081230631 7699185106001223121845947)
      ·
        refine ⟨11548777659001834682768921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699185106001223121845947 11548777659001834682768921)
        ·
          refine ⟨8661583244251376012076691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11548777659001834682768921 8661583244251376012076691)
          ·
            refine ⟨12992374866377064018115037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8661583244251376012076691 12992374866377064018115037)
            ·
              refine ⟨4872140574891399006793139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12992374866377064018115037 4872140574891399006793139)
              ·
                refine ⟨7308210862337098510189709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872140574891399006793139 7308210862337098510189709)
                ·
                  refine ⟨2740579073376411941321141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7308210862337098510189709 2740579073376411941321141)
                  ·
                    refine ⟨256929288129038619498857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2740579073376411941321141 256929288129038619498857)
                    ·
                      refine ⟨192696966096778964624143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256929288129038619498857 192696966096778964624143)
                      ·
                        rfl

theorem cell23_375276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_375276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375276 prefixEnd_375276 := by exact prefixLift 375276
  have htrace : WordTrace (prefixWord ++ tailWord_375276) baseStart_375276 baseEnd_375276 := by
    simpa [prefixWord, tailWord_375276, baseEnd_375276] using wordTrace_append hprefix tailTrace_375276
  have hstable : (prefixWord ++ tailWord_375276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375276).length < 2 ^ (prefixWord ++ tailWord_375276).sum := by decide
  have hdescent : baseEnd_375276 < baseStart_375276 := by decide
  rcases family_descends (prefixWord ++ tailWord_375276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375293 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_375293 : Nat := 118140960795 + 375293 * 2 ^ 59
def prefixEnd_375293 : Nat := 4983230072969 + 3 ^ 40 * 375293 * 2
def baseEnd_375293 : Nat := 192705695267905398111565

theorem tailTrace_375293 : CollatzResearch.WordTrace tailWord_375293 prefixEnd_375293 192705695267905398111565 := by
  unfold tailWord_375293
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688060229385030786650533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9125373486256687191100355 13688060229385030786650533)
  ·
    refine ⟨2566511293009693272496975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13688060229385030786650533 2566511293009693272496975)
    ·
      refine ⟨3849766939514539908745463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566511293009693272496975 3849766939514539908745463)
      ·
        refine ⟨5774650409271809863118195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849766939514539908745463 5774650409271809863118195)
        ·
          refine ⟨8661975613907714794677293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774650409271809863118195 8661975613907714794677293)
          ·
            refine ⟨3248240855215393048003985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8661975613907714794677293 3248240855215393048003985)
            ·
              refine ⟨2436180641411544786002989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248240855215393048003985 2436180641411544786002989)
              ·
                refine ⟨913567740529329294751121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2436180641411544786002989 913567740529329294751121)
                ·
                  refine ⟨685175805396996971063341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913567740529329294751121 685175805396996971063341)
                  ·
                    refine ⟨256940927023873864148753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685175805396996971063341 256940927023873864148753)
                    ·
                      refine ⟨192705695267905398111565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256940927023873864148753 192705695267905398111565)
                      ·
                        rfl

theorem cell23_375293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_375293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375293 prefixEnd_375293 := by exact prefixLift 375293
  have htrace : WordTrace (prefixWord ++ tailWord_375293) baseStart_375293 baseEnd_375293 := by
    simpa [prefixWord, tailWord_375293, baseEnd_375293] using wordTrace_append hprefix tailTrace_375293
  have hstable : (prefixWord ++ tailWord_375293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375293).length < 2 ^ (prefixWord ++ tailWord_375293).sum := by decide
  have hdescent : baseEnd_375293 < baseStart_375293 := by decide
  rcases family_descends (prefixWord ++ tailWord_375293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375299 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 3, 6]
def baseStart_375299 : Nat := 118140960795 + 375299 * 2 ^ 59
def prefixEnd_375299 : Nat := 4983230072969 + 3 ^ 40 * 375299 * 2
def baseEnd_375299 : Nat := 64236258717277458212179

theorem tailTrace_375299 : CollatzResearch.WordTrace tailWord_375299 prefixEnd_375299 64236258717277458212179 := by
  unfold tailWord_375299
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688279067363293811368951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9125519378242195874245967 13688279067363293811368951)
  ·
    refine ⟨20532418601044940717053427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13688279067363293811368951 20532418601044940717053427)
    ·
      refine ⟨30798627901567411075580141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20532418601044940717053427 30798627901567411075580141)
      ·
        refine ⟨11549485463087779153342553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30798627901567411075580141 11549485463087779153342553)
        ·
          refine ⟨8662114097315834365006915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11549485463087779153342553 8662114097315834365006915)
          ·
            refine ⟨12993171145973751547510373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662114097315834365006915 12993171145973751547510373)
            ·
              refine ⟨2436219589870078415158195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12993171145973751547510373 2436219589870078415158195)
              ·
                refine ⟨3654329384805117622737293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436219589870078415158195 3654329384805117622737293)
                ·
                  refine ⟨1370373519301919108526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3654329384805117622737293 1370373519301919108526485)
                  ·
                    refine ⟨64236258717277458212179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1370373519301919108526485 64236258717277458212179)
                    ·
                      rfl

theorem cell23_375299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_375299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375299 prefixEnd_375299 := by exact prefixLift 375299
  have htrace : WordTrace (prefixWord ++ tailWord_375299) baseStart_375299 baseEnd_375299 := by
    simpa [prefixWord, tailWord_375299, baseEnd_375299] using wordTrace_append hprefix tailTrace_375299
  have hstable : (prefixWord ++ tailWord_375299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375299).length < 2 ^ (prefixWord ++ tailWord_375299).sum := by decide
  have hdescent : baseEnd_375299 < baseStart_375299 := by decide
  rcases family_descends (prefixWord ++ tailWord_375299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375310 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_375310 : Nat := 118140960795 + 375310 * 2 ^ 59
def prefixEnd_375310 : Nat := 4983230072969 + 3 ^ 40 * 375310 * 2
def baseEnd_375310 : Nat := 192714424439031831598987

theorem tailTrace_375310 : CollatzResearch.WordTrace tailWord_375310 prefixEnd_375310 192714424439031831598987 := by
  unfold tailWord_375310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711085033790430336252423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9125786846882295126679589 1711085033790430336252423)
  ·
    refine ⟨2566627550685645504378635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711085033790430336252423 2566627550685645504378635)
    ·
      refine ⟨3849941326028468256567953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566627550685645504378635 3849941326028468256567953)
      ·
        refine ⟨2887455994521351192425965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3849941326028468256567953 2887455994521351192425965)
        ·
          refine ⟨1082795997945506697159737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2887455994521351192425965 1082795997945506697159737)
          ·
            refine ⟨812096998459130022869803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082795997945506697159737 812096998459130022869803)
            ·
              refine ⟨1218145497688695034304705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812096998459130022869803 1218145497688695034304705)
              ·
                refine ⟨913609123266521275728529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218145497688695034304705 913609123266521275728529)
                ·
                  refine ⟨685206842449890956796397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913609123266521275728529 685206842449890956796397)
                  ·
                    refine ⟨256952565918709108798649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685206842449890956796397 256952565918709108798649)
                    ·
                      refine ⟨192714424439031831598987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256952565918709108798649 192714424439031831598987)
                      ·
                        rfl

theorem cell23_375310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_375310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375310 prefixEnd_375310 := by exact prefixLift 375310
  have htrace : WordTrace (prefixWord ++ tailWord_375310) baseStart_375310 baseEnd_375310 := by
    simpa [prefixWord, tailWord_375310, baseEnd_375310] using wordTrace_append hprefix tailTrace_375310
  have hstable : (prefixWord ++ tailWord_375310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375310).length < 2 ^ (prefixWord ++ tailWord_375310).sum := by decide
  have hdescent : baseEnd_375310 < baseStart_375310 := by decide
  rcases family_descends (prefixWord ++ tailWord_375310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375317 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_375317 : Nat := 118140960795 + 375317 * 2 ^ 59
def prefixEnd_375317 : Nat := 4983230072969 + 3 ^ 40 * 375317 * 2
def baseEnd_375317 : Nat := 192718018803613304211455

theorem tailTrace_375317 : CollatzResearch.WordTrace tailWord_375317 prefixEnd_375317 192718018803613304211455 := by
  unfold tailWord_375317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688935581298082885524205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9125957054198721923682803 13688935581298082885524205)
  ·
    refine ⟨5133350842986781082071577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13688935581298082885524205 5133350842986781082071577)
    ·
      refine ⟨3850013132240085811553683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5133350842986781082071577 3850013132240085811553683)
      ·
        refine ⟨5775019698360128717330525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850013132240085811553683 5775019698360128717330525)
        ·
          refine ⟨2165632386885048268998947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5775019698360128717330525 2165632386885048268998947)
          ·
            refine ⟨3248448580327572403498421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165632386885048268998947 3248448580327572403498421)
            ·
              refine ⟨304542054405709912827977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3248448580327572403498421 304542054405709912827977)
              ·
                refine ⟨228406540804282434620983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304542054405709912827977 228406540804282434620983)
                ·
                  refine ⟨342609811206423651931475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228406540804282434620983 342609811206423651931475)
                  ·
                    refine ⟨513914716809635477897213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 342609811206423651931475 513914716809635477897213)
                    ·
                      refine ⟨192718018803613304211455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 513914716809635477897213 192718018803613304211455)
                      ·
                        rfl

theorem cell23_375317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_375317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375317 prefixEnd_375317 := by exact prefixLift 375317
  have htrace : WordTrace (prefixWord ++ tailWord_375317) baseStart_375317 baseEnd_375317 := by
    simpa [prefixWord, tailWord_375317, baseEnd_375317] using wordTrace_append hprefix tailTrace_375317
  have hstable : (prefixWord ++ tailWord_375317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375317).length < 2 ^ (prefixWord ++ tailWord_375317).sum := by decide
  have hdescent : baseEnd_375317 < baseStart_375317 := by decide
  rcases family_descends (prefixWord ++ tailWord_375317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375369 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_375369 : Nat := 118140960795 + 375369 * 2 ^ 59
def prefixEnd_375369 : Nat := 4983230072969 + 3 ^ 40 * 375369 * 2
def baseEnd_375369 : Nat := 192744719797647100761215

theorem tailTrace_375369 : CollatzResearch.WordTrace tailWord_375369 prefixEnd_375369 192744719797647100761215 := by
  unfold tailWord_375369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690832177109695766417161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9127221451406463844278107 13690832177109695766417161)
  ·
    refine ⟨10268124132832271824812871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13690832177109695766417161 10268124132832271824812871)
    ·
      refine ⟨15402186199248407737219307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10268124132832271824812871 15402186199248407737219307)
      ·
        refine ⟨23103279298872611605828961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15402186199248407737219307 23103279298872611605828961)
        ·
          refine ⟨17327459474154458704371721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23103279298872611605828961 17327459474154458704371721)
          ·
            refine ⟨12995594605615844028278791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17327459474154458704371721 12995594605615844028278791)
            ·
              refine ⟨19493391908423766042418187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12995594605615844028278791 19493391908423766042418187)
              ·
                refine ⟨29240087862635649063627281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19493391908423766042418187 29240087862635649063627281)
                ·
                  refine ⟨21930065896976736797720461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29240087862635649063627281 21930065896976736797720461)
                  ·
                    refine ⟨8223774711366276299145173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21930065896976736797720461 8223774711366276299145173)
                    ·
                      refine ⟨192744719797647100761215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8223774711366276299145173 192744719797647100761215)
                      ·
                        rfl

theorem cell23_375369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_375369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375369 prefixEnd_375369 := by exact prefixLift 375369
  have htrace : WordTrace (prefixWord ++ tailWord_375369) baseStart_375369 baseEnd_375369 := by
    simpa [prefixWord, tailWord_375369, baseEnd_375369] using wordTrace_append hprefix tailTrace_375369
  have hstable : (prefixWord ++ tailWord_375369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375369).length < 2 ^ (prefixWord ++ tailWord_375369).sum := by decide
  have hdescent : baseEnd_375369 < baseStart_375369 := by decide
  rcases family_descends (prefixWord ++ tailWord_375369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375374 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_375374 : Nat := 118140960795 + 375374 * 2 ^ 59
def prefixEnd_375374 : Nat := 4983230072969 + 3 ^ 40 * 375374 * 2
def baseEnd_375374 : Nat := 192747287200919581198693

theorem tailTrace_375374 : CollatzResearch.WordTrace tailWord_375374 prefixEnd_375374 192747287200919581198693 := by
  unfold tailWord_375374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711376817761447702543647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9127343028061054413566117 1711376817761447702543647)
  ·
    refine ⟨2567065226642171553815471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711376817761447702543647 2567065226642171553815471)
    ·
      refine ⟨3850597839963257330723207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567065226642171553815471 3850597839963257330723207)
      ·
        refine ⟨5775896759944885996084811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850597839963257330723207 5775896759944885996084811)
        ·
          refine ⟨8663845139917328994127217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775896759944885996084811 8663845139917328994127217)
          ·
            refine ⟨6497883854937996745595413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663845139917328994127217 6497883854937996745595413)
            ·
              refine ⟨304588305700218597449785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6497883854937996745595413 304588305700218597449785)
              ·
                refine ⟨228441229275163948087339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304588305700218597449785 228441229275163948087339)
                ·
                  refine ⟨342661843912745922131009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228441229275163948087339 342661843912745922131009)
                  ·
                    refine ⟨256996382934559441598257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342661843912745922131009 256996382934559441598257)
                    ·
                      refine ⟨192747287200919581198693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 256996382934559441598257 192747287200919581198693)
                      ·
                        rfl

theorem cell23_375374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_375374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375374 prefixEnd_375374 := by exact prefixLift 375374
  have htrace : WordTrace (prefixWord ++ tailWord_375374) baseStart_375374 baseEnd_375374 := by
    simpa [prefixWord, tailWord_375374, baseEnd_375374] using wordTrace_append hprefix tailTrace_375374
  have hstable : (prefixWord ++ tailWord_375374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375374).length < 2 ^ (prefixWord ++ tailWord_375374).sum := by decide
  have hdescent : baseEnd_375374 < baseStart_375374 := by decide
  rcases family_descends (prefixWord ++ tailWord_375374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375383 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_375383 : Nat := 118140960795 + 375383 * 2 ^ 59
def prefixEnd_375383 : Nat := 4983230072969 + 3 ^ 40 * 375383 * 2
def baseEnd_375383 : Nat := 192751908526810045986151

theorem tailTrace_375383 : CollatzResearch.WordTrace tailWord_375383 prefixEnd_375383 192751908526810045986151 := by
  unfold tailWord_375383
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691342799058976157426803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9127561866039317438284535 13691342799058976157426803)
  ·
    refine ⟨20537014198588464236140205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691342799058976157426803 20537014198588464236140205)
    ·
      refine ⟨7701380324470674088552577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20537014198588464236140205 7701380324470674088552577)
      ·
        refine ⟨5776035243353005566414433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7701380324470674088552577 5776035243353005566414433)
        ·
          refine ⟨4332026432514754174810825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5776035243353005566414433 4332026432514754174810825)
          ·
            refine ⟨3249019824386065631108119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332026432514754174810825 3249019824386065631108119)
            ·
              refine ⟨4873529736579098446662179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249019824386065631108119 4873529736579098446662179)
              ·
                refine ⟨7310294604868647669993269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873529736579098446662179 7310294604868647669993269)
                ·
                  refine ⟨685340119206435719061869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7310294604868647669993269 685340119206435719061869)
                  ·
                    refine ⟨257002544702413394648201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685340119206435719061869 257002544702413394648201)
                    ·
                      refine ⟨192751908526810045986151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 257002544702413394648201 192751908526810045986151)
                      ·
                        rfl

theorem cell23_375383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_375383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375383 prefixEnd_375383 := by exact prefixLift 375383
  have htrace : WordTrace (prefixWord ++ tailWord_375383) baseStart_375383 baseEnd_375383 := by
    simpa [prefixWord, tailWord_375383, baseEnd_375383] using wordTrace_append hprefix tailTrace_375383
  have hstable : (prefixWord ++ tailWord_375383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375383).length < 2 ^ (prefixWord ++ tailWord_375383).sum := by decide
  have hdescent : baseEnd_375383 < baseStart_375383 := by decide
  rcases family_descends (prefixWord ++ tailWord_375383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375396 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_375396 : Nat := 118140960795 + 375396 * 2 ^ 59
def prefixEnd_375396 : Nat := 4983230072969 + 3 ^ 40 * 375396 * 2
def baseEnd_375396 : Nat := 192758583775318495123591

theorem tailTrace_375396 : CollatzResearch.WordTrace tailWord_375396 prefixEnd_375396 192758583775318495123591 := by
  unfold tailWord_375396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845908474005939688825021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9127877965341252918433361 6845908474005939688825021)
  ·
    refine ⟨2567215677752227383309383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6845908474005939688825021 2567215677752227383309383)
    ·
      refine ⟨3850823516628341074964075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567215677752227383309383 3850823516628341074964075)
      ·
        refine ⟨5776235274942511612446113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850823516628341074964075 5776235274942511612446113)
        ·
          refine ⟨4332176456206883709334585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5776235274942511612446113 4332176456206883709334585)
          ·
            refine ⟨3249132342155162782000939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332176456206883709334585 3249132342155162782000939)
            ·
              refine ⟨4873698513232744173001409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249132342155162782000939 4873698513232744173001409)
              ·
                refine ⟨3655273884924558129751057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873698513232744173001409 3655273884924558129751057)
                ·
                  refine ⟨2741455413693418597313293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655273884924558129751057 2741455413693418597313293)
                  ·
                    refine ⟨1028045780135031973992485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741455413693418597313293 1028045780135031973992485)
                    ·
                      refine ⟨192758583775318495123591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1028045780135031973992485 192758583775318495123591)
                      ·
                        rfl

theorem cell23_375396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_375396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375396 prefixEnd_375396 := by exact prefixLift 375396
  have htrace : WordTrace (prefixWord ++ tailWord_375396) baseStart_375396 baseEnd_375396 := by
    simpa [prefixWord, tailWord_375396, baseEnd_375396] using wordTrace_append hprefix tailTrace_375396
  have hstable : (prefixWord ++ tailWord_375396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375396).length < 2 ^ (prefixWord ++ tailWord_375396).sum := by decide
  have hdescent : baseEnd_375396 < baseStart_375396 := by decide
  rcases family_descends (prefixWord ++ tailWord_375396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_375416 : Nat := 118140960795 + 375416 * 2 ^ 59
def prefixEnd_375416 : Nat := 4983230072969 + 3 ^ 40 * 375416 * 2
def baseEnd_375416 : Nat := 192768853388408416873499

theorem tailTrace_375416 : CollatzResearch.WordTrace tailWord_375416 prefixEnd_375416 192768853388408416873499 := by
  unfold tailWord_375416
  simp only [CollatzResearch.WordTrace]
  refine ⟨6846273203969711396689051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9128364271959615195585401 6846273203969711396689051)
  ·
    refine ⟨10269409805954567095033577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6846273203969711396689051 10269409805954567095033577)
    ·
      refine ⟨7702057354465925321275183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10269409805954567095033577 7702057354465925321275183)
      ·
        refine ⟨11553086031698887981912775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7702057354465925321275183 11553086031698887981912775)
        ·
          refine ⟨17329629047548331972869163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553086031698887981912775 17329629047548331972869163)
          ·
            refine ⟨25994443571322497959303745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17329629047548331972869163 25994443571322497959303745)
            ·
              refine ⟨19495832678491873469477809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25994443571322497959303745 19495832678491873469477809)
              ·
                refine ⟨14621874508868905102108357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19495832678491873469477809 14621874508868905102108357)
                ·
                  refine ⟨2741601470412919706645317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14621874508868905102108357 2741601470412919706645317)
                  ·
                    refine ⟨514050275702422444995997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741601470412919706645317 514050275702422444995997)
                    ·
                      refine ⟨192768853388408416873499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 514050275702422444995997 192768853388408416873499)
                      ·
                        rfl

theorem cell23_375416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_375416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375416 prefixEnd_375416 := by exact prefixLift 375416
  have htrace : WordTrace (prefixWord ++ tailWord_375416) baseStart_375416 baseEnd_375416 := by
    simpa [prefixWord, tailWord_375416, baseEnd_375416] using wordTrace_append hprefix tailTrace_375416
  have hstable : (prefixWord ++ tailWord_375416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375416).length < 2 ^ (prefixWord ++ tailWord_375416).sum := by decide
  have hdescent : baseEnd_375416 < baseStart_375416 := by decide
  rcases family_descends (prefixWord ++ tailWord_375416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375417 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 1, 3, 2]
def baseStart_375417 : Nat := 118140960795 + 375417 * 2 ^ 59
def prefixEnd_375417 : Nat := 4983230072969 + 3 ^ 40 * 375417 * 2
def baseEnd_375417 : Nat := 192769366869062912960995

theorem tailTrace_375417 : CollatzResearch.WordTrace tailWord_375417 prefixEnd_375417 192769366869062912960995 := by
  unfold tailWord_375417
  simp only [CollatzResearch.WordTrace]
  refine ⟨13692582880935799964164505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9128388587290533309443003 13692582880935799964164505)
  ·
    refine ⟨10269437160701849973123379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13692582880935799964164505 10269437160701849973123379)
    ·
      refine ⟨15404155741052774959685069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10269437160701849973123379 15404155741052774959685069)
      ·
        refine ⟨5776558402894790609881901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15404155741052774959685069 5776558402894790609881901)
        ·
          refine ⟨2166209401085546478705713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5776558402894790609881901 2166209401085546478705713)
          ·
            refine ⟨1624657050814159859029285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2166209401085546478705713 1624657050814159859029285)
            ·
              refine ⟨304623197027654973567991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1624657050814159859029285 304623197027654973567991)
              ·
                refine ⟨456934795541482460351987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304623197027654973567991 456934795541482460351987)
                ·
                  refine ⟨685402193312223690527981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456934795541482460351987 685402193312223690527981)
                  ·
                    refine ⟨257025822492083883947993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 685402193312223690527981 257025822492083883947993)
                    ·
                      refine ⟨192769366869062912960995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 257025822492083883947993 192769366869062912960995)
                      ·
                        rfl

theorem cell23_375417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_375417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375417 prefixEnd_375417 := by exact prefixLift 375417
  have htrace : WordTrace (prefixWord ++ tailWord_375417) baseStart_375417 baseEnd_375417 := by
    simpa [prefixWord, tailWord_375417, baseEnd_375417] using wordTrace_append hprefix tailTrace_375417
  have hstable : (prefixWord ++ tailWord_375417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375417).length < 2 ^ (prefixWord ++ tailWord_375417).sum := by decide
  have hdescent : baseEnd_375417 < baseStart_375417 := by decide
  rcases family_descends (prefixWord ++ tailWord_375417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375513 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_375513 : Nat := 118140960795 + 375513 * 2 ^ 59
def prefixEnd_375513 : Nat := 4983230072969 + 3 ^ 40 * 375513 * 2
def baseEnd_375513 : Nat := 64272887003964845786851

theorem tailTrace_375513 : CollatzResearch.WordTrace tailWord_375513 prefixEnd_375513 64272887003964845786851 := by
  unfold tailWord_375513
  simp only [CollatzResearch.WordTrace]
  refine ⟨13696084288588008359659193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9130722859058672239772795 13696084288588008359659193)
  ·
    refine ⟨10272063216441006269744395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13696084288588008359659193 10272063216441006269744395)
    ·
      refine ⟨15408094824661509404616593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10272063216441006269744395 15408094824661509404616593)
      ·
        refine ⟨11556071118496132053462445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15408094824661509404616593 11556071118496132053462445)
        ·
          refine ⟨4333526669436049520048417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11556071118496132053462445 4333526669436049520048417)
          ·
            refine ⟨3250145002077037140036313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333526669436049520048417 3250145002077037140036313)
            ·
              refine ⟨2437608751557777855027235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250145002077037140036313 2437608751557777855027235)
              ·
                refine ⟨3656413127336666782540853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437608751557777855027235 3656413127336666782540853)
                ·
                  refine ⟨342788730687812510863205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3656413127336666782540853 342788730687812510863205)
                  ·
                    refine ⟨64272887003964845786851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342788730687812510863205 64272887003964845786851)
                    ·
                      rfl

theorem cell23_375513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_375513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375513 prefixEnd_375513 := by exact prefixLift 375513
  have htrace : WordTrace (prefixWord ++ tailWord_375513) baseStart_375513 baseEnd_375513 := by
    simpa [prefixWord, tailWord_375513, baseEnd_375513] using wordTrace_append hprefix tailTrace_375513
  have hstable : (prefixWord ++ tailWord_375513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375513).length < 2 ^ (prefixWord ++ tailWord_375513).sum := by decide
  have hdescent : baseEnd_375513 < baseStart_375513 := by decide
  rcases family_descends (prefixWord ++ tailWord_375513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375533 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_375533 : Nat := 118140960795 + 375533 * 2 ^ 59
def prefixEnd_375533 : Nat := 4983230072969 + 3 ^ 40 * 375533 * 2
def baseEnd_375533 : Nat := 192828930624984459110461

theorem tailTrace_375533 : CollatzResearch.WordTrace tailWord_375533 prefixEnd_375533 192828930624984459110461 := by
  unfold tailWord_375533
  simp only [CollatzResearch.WordTrace]
  refine ⟨13696813748515551775387253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9131209165677034516924835 13696813748515551775387253)
  ·
    refine ⟨1284076288923332978942555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13696813748515551775387253 1284076288923332978942555)
    ·
      refine ⟨1926114433384999468413833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284076288923332978942555 1926114433384999468413833)
      ·
        refine ⟨1444585825038749601310375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926114433384999468413833 1444585825038749601310375)
        ·
          refine ⟨2166878737558124401965563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444585825038749601310375 2166878737558124401965563)
          ·
            refine ⟨3250318106337186602948345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166878737558124401965563 3250318106337186602948345)
            ·
              refine ⟨2437738579752889952211259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250318106337186602948345 2437738579752889952211259)
              ·
                refine ⟨3656607869629334928316889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437738579752889952211259 3656607869629334928316889)
                ·
                  refine ⟨2742455902222001196237667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656607869629334928316889 2742455902222001196237667)
                  ·
                    refine ⟨4113683853333001794356501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742455902222001196237667 4113683853333001794356501)
                    ·
                      refine ⟨192828930624984459110461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4113683853333001794356501 192828930624984459110461)
                      ·
                        rfl

theorem cell23_375533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_375533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375533 prefixEnd_375533 := by exact prefixLift 375533
  have htrace : WordTrace (prefixWord ++ tailWord_375533) baseStart_375533 baseEnd_375533 := by
    simpa [prefixWord, tailWord_375533, baseEnd_375533] using wordTrace_append hprefix tailTrace_375533
  have hstable : (prefixWord ++ tailWord_375533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375533).length < 2 ^ (prefixWord ++ tailWord_375533).sum := by decide
  have hdescent : baseEnd_375533 < baseStart_375533 := by decide
  rcases family_descends (prefixWord ++ tailWord_375533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375553 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_375553 : Nat := 118140960795 + 375553 * 2 ^ 59
def prefixEnd_375553 : Nat := 4983230072969 + 3 ^ 40 * 375553 * 2
def baseEnd_375553 : Nat := 192839200238074380860369

theorem tailTrace_375553 : CollatzResearch.WordTrace tailWord_375553 prefixEnd_375553 192839200238074380860369 := by
  unfold tailWord_375553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13697543208443095191115313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9131695472295396794076875 13697543208443095191115313)
  ·
    refine ⟨10273157406332321393336485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13697543208443095191115313 10273157406332321393336485)
    ·
      refine ⟨1926217013687310261250591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10273157406332321393336485 1926217013687310261250591)
      ·
        refine ⟨2889325520530965391875887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926217013687310261250591 2889325520530965391875887)
        ·
          refine ⟨4333988280796448087813831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889325520530965391875887 4333988280796448087813831)
          ·
            refine ⟨6500982421194672131720747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333988280796448087813831 6500982421194672131720747)
            ·
              refine ⟨9751473631792008197581121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500982421194672131720747 9751473631792008197581121)
              ·
                refine ⟨7313605223844006148185841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9751473631792008197581121 7313605223844006148185841)
                ·
                  refine ⟨5485203917883004611139381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313605223844006148185841 5485203917883004611139381)
                  ·
                    refine ⟨514237867301531682294317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5485203917883004611139381 514237867301531682294317)
                    ·
                      refine ⟨192839200238074380860369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 514237867301531682294317 192839200238074380860369)
                      ·
                        rfl

theorem cell23_375553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_375553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375553 prefixEnd_375553 := by exact prefixLift 375553
  have htrace : WordTrace (prefixWord ++ tailWord_375553) baseStart_375553 baseEnd_375553 := by
    simpa [prefixWord, tailWord_375553, baseEnd_375553] using wordTrace_append hprefix tailTrace_375553
  have hstable : (prefixWord ++ tailWord_375553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375553).length < 2 ^ (prefixWord ++ tailWord_375553).sum := by decide
  have hdescent : baseEnd_375553 < baseStart_375553 := by decide
  rcases family_descends (prefixWord ++ tailWord_375553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375573 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_375573 : Nat := 118140960795 + 375573 * 2 ^ 59
def prefixEnd_375573 : Nat := 4983230072969 + 3 ^ 40 * 375573 * 2
def baseEnd_375573 : Nat := 64283156617054767536759

theorem tailTrace_375573 : CollatzResearch.WordTrace tailWord_375573 prefixEnd_375573 64283156617054767536759 := by
  unfold tailWord_375573
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698272668370638606843373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9132181778913759071228915 13698272668370638606843373)
  ·
    refine ⟨5136852250638989477566265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13698272668370638606843373 5136852250638989477566265)
    ·
      refine ⟨3852639187979242108174699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5136852250638989477566265 3852639187979242108174699)
      ·
        refine ⟨5778958781968863162262049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852639187979242108174699 5778958781968863162262049)
        ·
          refine ⟨4334219086476647371696537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5778958781968863162262049 4334219086476647371696537)
          ·
            refine ⟨3250664314857485528772403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334219086476647371696537 3250664314857485528772403)
            ·
              refine ⟨4875996472286228293158605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250664314857485528772403 4875996472286228293158605)
              ·
                refine ⟨1828498677107335609934477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4875996472286228293158605 1828498677107335609934477)
                ·
                  refine ⟨685687003915250853725429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1828498677107335609934477 685687003915250853725429)
                  ·
                    refine ⟨64283156617054767536759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 685687003915250853725429 64283156617054767536759)
                    ·
                      rfl

theorem cell23_375573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_375573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375573 prefixEnd_375573 := by exact prefixLift 375573
  have htrace : WordTrace (prefixWord ++ tailWord_375573) baseStart_375573 baseEnd_375573 := by
    simpa [prefixWord, tailWord_375573, baseEnd_375573] using wordTrace_append hprefix tailTrace_375573
  have hstable : (prefixWord ++ tailWord_375573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375573).length < 2 ^ (prefixWord ++ tailWord_375573).sum := by decide
  have hdescent : baseEnd_375573 < baseStart_375573 := by decide
  rcases family_descends (prefixWord ++ tailWord_375573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375581 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_375581 : Nat := 118140960795 + 375581 * 2 ^ 59
def prefixEnd_375581 : Nat := 4983230072969 + 3 ^ 40 * 375581 * 2
def baseEnd_375581 : Nat := 64284525898800090436747

theorem tailTrace_375581 : CollatzResearch.WordTrace tailWord_375581 prefixEnd_375581 64284525898800090436747 := by
  unfold tailWord_375581
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698564452341655973134597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9132376301561103982089731 13698564452341655973134597)
  ·
    refine ⟨2568480834814060494962737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13698564452341655973134597 2568480834814060494962737)
    ·
      refine ⟨1926360626110545371222053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2568480834814060494962737 1926360626110545371222053)
      ·
        refine ⟨361192617395727257104135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1926360626110545371222053 361192617395727257104135)
        ·
          refine ⟨541788926093590885656203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361192617395727257104135 541788926093590885656203)
          ·
            refine ⟨812683389140386328484305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541788926093590885656203 812683389140386328484305)
            ·
              refine ⟨609512541855289746363229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812683389140386328484305 609512541855289746363229)
              ·
                refine ⟨228567203195733654886211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609512541855289746363229 228567203195733654886211)
                ·
                  refine ⟨342850804793600482329317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228567203195733654886211 342850804793600482329317)
                  ·
                    refine ⟨64284525898800090436747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342850804793600482329317 64284525898800090436747)
                    ·
                      rfl

theorem cell23_375581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_375581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375581 prefixEnd_375581 := by exact prefixLift 375581
  have htrace : WordTrace (prefixWord ++ tailWord_375581) baseStart_375581 baseEnd_375581 := by
    simpa [prefixWord, tailWord_375581, baseEnd_375581] using wordTrace_append hprefix tailTrace_375581
  have hstable : (prefixWord ++ tailWord_375581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375581).length < 2 ^ (prefixWord ++ tailWord_375581).sum := by decide
  have hdescent : baseEnd_375581 < baseStart_375581 := by decide
  rcases family_descends (prefixWord ++ tailWord_375581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375594 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_375594 : Nat := 118140960795 + 375594 * 2 ^ 59
def prefixEnd_375594 : Nat := 4983230072969 + 3 ^ 40 * 375594 * 2
def baseEnd_375594 : Nat := 21428916993878746716409

theorem tailTrace_375594 : CollatzResearch.WordTrace tailWord_375594 prefixEnd_375594 21428916993878746716409 := by
  unfold tailWord_375594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424759650323639798339459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9132692400863039462238557 3424759650323639798339459)
  ·
    refine ⟨5137139475485459697509189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3424759650323639798339459 5137139475485459697509189)
    ·
      refine ⟨963213651653523693282973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5137139475485459697509189 963213651653523693282973)
      ·
        refine ⟨361205119370071384981115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 963213651653523693282973 361205119370071384981115)
        ·
          refine ⟨541807679055107077471673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361205119370071384981115 541807679055107077471673)
          ·
            refine ⟨406355759291330308103755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541807679055107077471673 406355759291330308103755)
            ·
              refine ⟨609533638936995462155633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406355759291330308103755 609533638936995462155633)
              ·
                refine ⟨457150229202746596616725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609533638936995462155633 457150229202746596616725)
                ·
                  refine ⟨21428916993878746716409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 457150229202746596616725 21428916993878746716409)
                  ·
                    rfl

theorem cell23_375594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_375594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375594 prefixEnd_375594 := by exact prefixLift 375594
  have htrace : WordTrace (prefixWord ++ tailWord_375594) baseStart_375594 baseEnd_375594 := by
    simpa [prefixWord, tailWord_375594, baseEnd_375594] using wordTrace_append hprefix tailTrace_375594
  have hstable : (prefixWord ++ tailWord_375594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375594).length < 2 ^ (prefixWord ++ tailWord_375594).sum := by decide
  have hdescent : baseEnd_375594 < baseStart_375594 := by decide
  rcases family_descends (prefixWord ++ tailWord_375594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375630 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_375630 : Nat := 118140960795 + 375630 * 2 ^ 59
def prefixEnd_375630 : Nat := 4983230072969 + 3 ^ 40 * 375630 * 2
def baseEnd_375630 : Nat := 192878738248470579597515

theorem tailTrace_375630 : CollatzResearch.WordTrace tailWord_375630 prefixEnd_375630 192878738248470579597515 := by
  unfold tailWord_375630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712543953645517167708543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9133567752776091561112229 1712543953645517167708543)
  ·
    refine ⟨2568815930468275751562815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1712543953645517167708543 2568815930468275751562815)
    ·
      refine ⟨3853223895702413627344223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568815930468275751562815 3853223895702413627344223)
      ·
        refine ⟨5779835843553620441016335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853223895702413627344223 5779835843553620441016335)
        ·
          refine ⟨8669753765330430661524503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779835843553620441016335 8669753765330430661524503)
          ·
            refine ⟨13004630647995645992286755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669753765330430661524503 13004630647995645992286755)
            ·
              refine ⟨19506945971993468988430133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13004630647995645992286755 19506945971993468988430133)
              ·
                refine ⟨1828776184874387717665325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19506945971993468988430133 1828776184874387717665325)
                ·
                  refine ⟨685791069327895394124497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1828776184874387717665325 685791069327895394124497)
                  ·
                    refine ⟨514343301995921545593373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685791069327895394124497 514343301995921545593373)
                    ·
                      refine ⟨192878738248470579597515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 514343301995921545593373 192878738248470579597515)
                      ·
                        rfl

theorem cell23_375630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_375630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375630 prefixEnd_375630 := by exact prefixLift 375630
  have htrace : WordTrace (prefixWord ++ tailWord_375630) baseStart_375630 baseEnd_375630 := by
    simpa [prefixWord, tailWord_375630, baseEnd_375630] using wordTrace_append hprefix tailTrace_375630
  have hstable : (prefixWord ++ tailWord_375630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375630).length < 2 ^ (prefixWord ++ tailWord_375630).sum := by decide
  have hdescent : baseEnd_375630 < baseStart_375630 := by decide
  rcases family_descends (prefixWord ++ tailWord_375630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375678 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_375678 : Nat := 118140960795 + 375678 * 2 ^ 59
def prefixEnd_375678 : Nat := 4983230072969 + 3 ^ 40 * 375678 * 2
def baseEnd_375678 : Nat := 192903385319886391797295

theorem tailTrace_375678 : CollatzResearch.WordTrace tailWord_375678 prefixEnd_375678 192903385319886391797295 := by
  unfold tailWord_375678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712762791623780192426961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9134734888660161026277125 1712762791623780192426961)
  ·
    refine ⟨1284572093717835144320221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1712762791623780192426961 1284572093717835144320221)
    ·
      refine ⟨481714535144188179120083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1284572093717835144320221 481714535144188179120083)
      ·
        refine ⟨722571802716282268680125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481714535144188179120083 722571802716282268680125)
        ·
          refine ⟨270964426018605850755047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722571802716282268680125 270964426018605850755047)
          ·
            refine ⟨406446639027908776132571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270964426018605850755047 406446639027908776132571)
            ·
              refine ⟨609669958541863164198857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406446639027908776132571 609669958541863164198857)
              ·
                refine ⟨457252468906397373149143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609669958541863164198857 457252468906397373149143)
                ·
                  refine ⟨685878703359596059723715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457252468906397373149143 685878703359596059723715)
                  ·
                    refine ⟨1028818055039394089585573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 685878703359596059723715 1028818055039394089585573)
                    ·
                      refine ⟨192903385319886391797295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1028818055039394089585573 192903385319886391797295)
                      ·
                        rfl

theorem cell23_375678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_375678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375678 prefixEnd_375678 := by exact prefixLift 375678
  have htrace : WordTrace (prefixWord ++ tailWord_375678) baseStart_375678 baseEnd_375678 := by
    simpa [prefixWord, tailWord_375678, baseEnd_375678] using wordTrace_append hprefix tailTrace_375678
  have hstable : (prefixWord ++ tailWord_375678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375678).length < 2 ^ (prefixWord ++ tailWord_375678).sum := by decide
  have hdescent : baseEnd_375678 < baseStart_375678 := by decide
  rcases family_descends (prefixWord ++ tailWord_375678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375877 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_375877 : Nat := 118140960795 + 375877 * 2 ^ 59
def prefixEnd_375877 : Nat := 4983230072969 + 3 ^ 40 * 375877 * 2
def baseEnd_375877 : Nat := 64335189323377037736293

theorem tailTrace_375877 : CollatzResearch.WordTrace tailWord_375877 prefixEnd_375877 64335189323377037736293 := by
  unfold tailWord_375877
  simp only [CollatzResearch.WordTrace]
  refine ⟨13709360459269298525909885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9139573639512865683939923 13709360459269298525909885)
  ·
    refine ⟨5141010172225986947216207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13709360459269298525909885 5141010172225986947216207)
    ·
      refine ⟨7711515258338980420824311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5141010172225986947216207 7711515258338980420824311)
      ·
        refine ⟨11567272887508470631236467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711515258338980420824311 11567272887508470631236467)
        ·
          refine ⟨17350909331262705946854701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11567272887508470631236467 17350909331262705946854701)
          ·
            refine ⟨6506590999223514730070513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17350909331262705946854701 6506590999223514730070513)
            ·
              refine ⟨4879943249417636047552885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6506590999223514730070513 4879943249417636047552885)
              ·
                refine ⟨457494679632903379458083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4879943249417636047552885 457494679632903379458083)
                ·
                  refine ⟨686242019449355069187125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457494679632903379458083 686242019449355069187125)
                  ·
                    refine ⟨64335189323377037736293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 686242019449355069187125 64335189323377037736293)
                    ·
                      rfl

theorem cell23_375877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_375877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375877 prefixEnd_375877 := by exact prefixLift 375877
  have htrace : WordTrace (prefixWord ++ tailWord_375877) baseStart_375877 baseEnd_375877 := by
    simpa [prefixWord, tailWord_375877, baseEnd_375877] using wordTrace_append hprefix tailTrace_375877
  have hstable : (prefixWord ++ tailWord_375877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375877).length < 2 ^ (prefixWord ++ tailWord_375877).sum := by decide
  have hdescent : baseEnd_375877 < baseStart_375877 := by decide
  rcases family_descends (prefixWord ++ tailWord_375877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375885 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_375885 : Nat := 118140960795 + 375885 * 2 ^ 59
def prefixEnd_375885 : Nat := 4983230072969 + 3 ^ 40 * 375885 * 2
def baseEnd_375885 : Nat := 64336558605122360636281

theorem tailTrace_375885 : CollatzResearch.WordTrace tailWord_375885 prefixEnd_375885 64336558605122360636281 := by
  unfold tailWord_375885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13709652243240315892201109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9139768162160210594800739 13709652243240315892201109)
  ·
    refine ⟨642639948901889807446927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13709652243240315892201109 642639948901889807446927)
    ·
      refine ⟨963959923352834711170391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642639948901889807446927 963959923352834711170391)
      ·
        refine ⟨1445939885029252066755587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963959923352834711170391 1445939885029252066755587)
        ·
          refine ⟨2168909827543878100133381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445939885029252066755587 2168909827543878100133381)
          ·
            refine ⟨406670592664477143775009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2168909827543878100133381 406670592664477143775009)
            ·
              refine ⟨305002944498357857831257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406670592664477143775009 305002944498357857831257)
              ·
                refine ⟨228752208373768393373443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305002944498357857831257 228752208373768393373443)
                ·
                  refine ⟨343128312560652590060165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228752208373768393373443 343128312560652590060165)
                  ·
                    refine ⟨64336558605122360636281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343128312560652590060165 64336558605122360636281)
                    ·
                      rfl

theorem cell23_375885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_375885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375885 prefixEnd_375885 := by exact prefixLift 375885
  have htrace : WordTrace (prefixWord ++ tailWord_375885) baseStart_375885 baseEnd_375885 := by
    simpa [prefixWord, tailWord_375885, baseEnd_375885] using wordTrace_append hprefix tailTrace_375885
  have hstable : (prefixWord ++ tailWord_375885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375885).length < 2 ^ (prefixWord ++ tailWord_375885).sum := by decide
  have hdescent : baseEnd_375885 < baseStart_375885 := by decide
  rcases family_descends (prefixWord ++ tailWord_375885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375907 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 6, 4]
def baseStart_375907 : Nat := 118140960795 + 375907 * 2 ^ 59
def prefixEnd_375907 : Nat := 4983230072969 + 3 ^ 40 * 375907 * 2
def baseEnd_375907 : Nat := 64340324129921998611247

theorem tailTrace_375907 : CollatzResearch.WordTrace tailWord_375907 prefixEnd_375907 64340324129921998611247 := by
  unfold tailWord_375907
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710454649160613649501975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9140303099440409099667983 13710454649160613649501975)
  ·
    refine ⟨20565681973740920474252963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13710454649160613649501975 20565681973740920474252963)
    ·
      refine ⟨30848522960611380711379445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20565681973740920474252963 30848522960611380711379445)
      ·
        refine ⟨2892049027557316941691823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30848522960611380711379445 2892049027557316941691823)
        ·
          refine ⟨4338073541335975412537735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892049027557316941691823 4338073541335975412537735)
          ·
            refine ⟨6507110312003963118806603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338073541335975412537735 6507110312003963118806603)
            ·
              refine ⟨9760665468005944678209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507110312003963118806603 9760665468005944678209905)
              ·
                refine ⟨7320499101004458508657429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760665468005944678209905 7320499101004458508657429)
                ·
                  refine ⟨343148395359583992593317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7320499101004458508657429 343148395359583992593317)
                  ·
                    refine ⟨64340324129921998611247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343148395359583992593317 64340324129921998611247)
                    ·
                      rfl

theorem cell23_375907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 4].length) (baseStart_375907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375907 prefixEnd_375907 := by exact prefixLift 375907
  have htrace : WordTrace (prefixWord ++ tailWord_375907) baseStart_375907 baseEnd_375907 := by
    simpa [prefixWord, tailWord_375907, baseEnd_375907] using wordTrace_append hprefix tailTrace_375907
  have hstable : (prefixWord ++ tailWord_375907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375907).length < 2 ^ (prefixWord ++ tailWord_375907).sum := by decide
  have hdescent : baseEnd_375907 < baseStart_375907 := by decide
  rcases family_descends (prefixWord ++ tailWord_375907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375914 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_375914 : Nat := 118140960795 + 375914 * 2 ^ 59
def prefixEnd_375914 : Nat := 4983230072969 + 3 ^ 40 * 375914 * 2
def baseEnd_375914 : Nat := 193024566754347468446209

theorem tailTrace_375914 : CollatzResearch.WordTrace tailWord_375914 prefixEnd_375914 193024566754347468446209 := by
  unfold tailWord_375914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427677490033813461251699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9140473306756835896671197 3427677490033813461251699)
  ·
    refine ⟨5141516235050720191877549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3427677490033813461251699 5141516235050720191877549)
    ·
      refine ⟨1928068588144020071954081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5141516235050720191877549 1928068588144020071954081)
      ·
        refine ⟨1446051441108015053965561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1928068588144020071954081 1446051441108015053965561)
        ·
          refine ⟨1084538580831011290474171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446051441108015053965561 1084538580831011290474171)
          ·
            refine ⟨1626807871246516935711257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084538580831011290474171 1626807871246516935711257)
            ·
              refine ⟨1220105903434887701783443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626807871246516935711257 1220105903434887701783443)
              ·
                refine ⟨1830158855152331552675165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220105903434887701783443 1830158855152331552675165)
                ·
                  refine ⟨686309570682124332253187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1830158855152331552675165 686309570682124332253187)
                  ·
                    refine ⟨1029464356023186498379781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 686309570682124332253187 1029464356023186498379781)
                    ·
                      refine ⟨193024566754347468446209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1029464356023186498379781 193024566754347468446209)
                      ·
                        rfl

theorem cell23_375914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_375914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375914 prefixEnd_375914 := by exact prefixLift 375914
  have htrace : WordTrace (prefixWord ++ tailWord_375914) baseStart_375914 baseEnd_375914 := by
    simpa [prefixWord, tailWord_375914, baseEnd_375914] using wordTrace_append hprefix tailTrace_375914
  have hstable : (prefixWord ++ tailWord_375914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375914).length < 2 ^ (prefixWord ++ tailWord_375914).sum := by decide
  have hdescent : baseEnd_375914 < baseStart_375914 := by decide
  rcases family_descends (prefixWord ++ tailWord_375914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375918 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_375918 : Nat := 118140960795 + 375918 * 2 ^ 59
def prefixEnd_375918 : Nat := 4983230072969 + 3 ^ 40 * 375918 * 2
def baseEnd_375918 : Nat := 193026620676965452796191

theorem tailTrace_375918 : CollatzResearch.WordTrace tailWord_375918 prefixEnd_375918 193026620676965452796191 := by
  unfold tailWord_375918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713856981515095316019051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9140570568080508352101605 1713856981515095316019051)
  ·
    refine ⟨2570785472272642974028577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1713856981515095316019051 2570785472272642974028577)
    ·
      refine ⟨1928089104204482230521433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2570785472272642974028577 1928089104204482230521433)
      ·
        refine ⟨1446066828153361672891075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1928089104204482230521433 1446066828153361672891075)
        ·
          refine ⟨2169100242230042509336613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446066828153361672891075 2169100242230042509336613)
          ·
            refine ⟨406706295418132970500615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2169100242230042509336613 406706295418132970500615)
            ·
              refine ⟨610059443127199455750923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406706295418132970500615 610059443127199455750923)
              ·
                refine ⟨915089164690799183626385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610059443127199455750923 915089164690799183626385)
                ·
                  refine ⟨686316873518099387719789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915089164690799183626385 686316873518099387719789)
                  ·
                    refine ⟨257368827569287270394921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686316873518099387719789 257368827569287270394921)
                    ·
                      refine ⟨193026620676965452796191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 257368827569287270394921 193026620676965452796191)
                      ·
                        rfl

theorem cell23_375918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_375918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375918 prefixEnd_375918 := by exact prefixLift 375918
  have htrace : WordTrace (prefixWord ++ tailWord_375918) baseStart_375918 baseEnd_375918 := by
    simpa [prefixWord, tailWord_375918, baseEnd_375918] using wordTrace_append hprefix tailTrace_375918
  have hstable : (prefixWord ++ tailWord_375918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375918).length < 2 ^ (prefixWord ++ tailWord_375918).sum := by decide
  have hdescent : baseEnd_375918 < baseStart_375918 := by decide
  rcases family_descends (prefixWord ++ tailWord_375918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375927 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_375927 : Nat := 118140960795 + 375927 * 2 ^ 59
def prefixEnd_375927 : Nat := 4983230072969 + 3 ^ 40 * 375927 * 2
def baseEnd_375927 : Nat := 193031242002855917583649

theorem tailTrace_375927 : CollatzResearch.WordTrace tailWord_375927 prefixEnd_375927 193031242002855917583649 := by
  unfold tailWord_375927
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711184109088157065230035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9140789406058771376820023 13711184109088157065230035)
  ·
    refine ⟨20566776163632235597845053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711184109088157065230035 20566776163632235597845053)
    ·
      refine ⟨7712541061362088349191895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20566776163632235597845053 7712541061362088349191895)
      ·
        refine ⟨11568811592043132523787843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7712541061362088349191895 11568811592043132523787843)
        ·
          refine ⟨17353217388064698785681765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11568811592043132523787843 17353217388064698785681765)
          ·
            refine ⟨3253728260262131022315331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17353217388064698785681765 3253728260262131022315331)
            ·
              refine ⟨4880592390393196533472997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253728260262131022315331 4880592390393196533472997)
              ·
                refine ⟨915111073198724350026187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4880592390393196533472997 915111073198724350026187)
                ·
                  refine ⟨1372666609798086525039281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915111073198724350026187 1372666609798086525039281)
                  ·
                    refine ⟨1029499957348564893779461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372666609798086525039281 1029499957348564893779461)
                    ·
                      refine ⟨193031242002855917583649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1029499957348564893779461 193031242002855917583649)
                      ·
                        rfl

theorem cell23_375927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_375927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375927 prefixEnd_375927 := by exact prefixLift 375927
  have htrace : WordTrace (prefixWord ++ tailWord_375927) baseStart_375927 baseEnd_375927 := by
    simpa [prefixWord, tailWord_375927, baseEnd_375927] using wordTrace_append hprefix tailTrace_375927
  have hstable : (prefixWord ++ tailWord_375927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375927).length < 2 ^ (prefixWord ++ tailWord_375927).sum := by decide
  have hdescent : baseEnd_375927 < baseStart_375927 := by decide
  rcases family_descends (prefixWord ++ tailWord_375927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375937 : List Nat := [1, 2, 4, 2, 2, 2, 10]
def baseStart_375937 : Nat := 118140960795 + 375937 * 2 ^ 59
def prefixEnd_375937 : Nat := 4983230072969 + 3 ^ 40 * 375937 * 2
def baseEnd_375937 : Nat := 2383165145795072573563

theorem tailTrace_375937 : CollatzResearch.WordTrace tailWord_375937 prefixEnd_375937 2383165145795072573563 := by
  unfold tailWord_375937
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711548839051928773094065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9141032559367952515396043 13711548839051928773094065)
  ·
    refine ⟨10283661629288946579820549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13711548839051928773094065 10283661629288946579820549)
    ·
      refine ⟨1928186555491677483716353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10283661629288946579820549 1928186555491677483716353)
      ·
        refine ⟨1446139916618758112787265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1928186555491677483716353 1446139916618758112787265)
        ·
          refine ⟨1084604937464068584590449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1446139916618758112787265 1084604937464068584590449)
          ·
            refine ⟨813453703098051438442837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084604937464068584590449 813453703098051438442837)
            ·
              refine ⟨2383165145795072573563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 813453703098051438442837 2383165145795072573563)
              ·
                rfl

theorem cell23_375937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 10].length) (baseStart_375937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375937 prefixEnd_375937 := by exact prefixLift 375937
  have htrace : WordTrace (prefixWord ++ tailWord_375937) baseStart_375937 baseEnd_375937 := by
    simpa [prefixWord, tailWord_375937, baseEnd_375937] using wordTrace_append hprefix tailTrace_375937
  have hstable : (prefixWord ++ tailWord_375937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375937).length < 2 ^ (prefixWord ++ tailWord_375937).sum := by decide
  have hdescent : baseEnd_375937 < baseStart_375937 := by decide
  rcases family_descends (prefixWord ++ tailWord_375937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375947 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3]
def baseStart_375947 : Nat := 118140960795 + 375947 * 2 ^ 59
def prefixEnd_375947 : Nat := 4983230072969 + 3 ^ 40 * 375947 * 2
def baseEnd_375947 : Nat := 193041511615945839333557

theorem tailTrace_375947 : CollatzResearch.WordTrace tailWord_375947 prefixEnd_375947 193041511615945839333557 := by
  unfold tailWord_375947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711913569015700480958095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9141275712677133653972063 13711913569015700480958095)
  ·
    refine ⟨20567870353523550721437143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711913569015700480958095 20567870353523550721437143)
    ·
      refine ⟨30851805530285326082155715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20567870353523550721437143 30851805530285326082155715)
      ·
        refine ⟨46277708295427989123233573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30851805530285326082155715 46277708295427989123233573)
        ·
          refine ⟨8677070305392747960606295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46277708295427989123233573 8677070305392747960606295)
          ·
            refine ⟨13015605458089121940909443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677070305392747960606295 13015605458089121940909443)
            ·
              refine ⟨19523408187133682911364165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015605458089121940909443 19523408187133682911364165)
              ·
                refine ⟨3660639035087565545880781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19523408187133682911364165 3660639035087565545880781)
                ·
                  refine ⟨1372739638157837079705293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3660639035087565545880781 1372739638157837079705293)
                  ·
                    refine ⟨514777364309188904889485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372739638157837079705293 514777364309188904889485)
                    ·
                      refine ⟨193041511615945839333557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 514777364309188904889485 193041511615945839333557)
                      ·
                        rfl

theorem cell23_375947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 3].length) (baseStart_375947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375947 prefixEnd_375947 := by exact prefixLift 375947
  have htrace : WordTrace (prefixWord ++ tailWord_375947) baseStart_375947 baseEnd_375947 := by
    simpa [prefixWord, tailWord_375947, baseEnd_375947] using wordTrace_append hprefix tailTrace_375947
  have hstable : (prefixWord ++ tailWord_375947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375947).length < 2 ^ (prefixWord ++ tailWord_375947).sum := by decide
  have hdescent : baseEnd_375947 < baseStart_375947 := by decide
  rcases family_descends (prefixWord ++ tailWord_375947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375991 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_375991 : Nat := 118140960795 + 375991 * 2 ^ 59
def prefixEnd_375991 : Nat := 4983230072969 + 3 ^ 40 * 375991 * 2
def baseEnd_375991 : Nat := 193064104764743667183355

theorem tailTrace_375991 : CollatzResearch.WordTrace tailWord_375991 prefixEnd_375991 193064104764743667183355 := by
  unfold tailWord_375991
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713518380856295995559827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9142345587237530663706551 13713518380856295995559827)
  ·
    refine ⟨20570277571284443993339741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13713518380856295995559827 20570277571284443993339741)
    ·
      refine ⟨7713854089231666497502403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20570277571284443993339741 7713854089231666497502403)
      ·
        refine ⟨11570781133847499746253605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713854089231666497502403 11570781133847499746253605)
        ·
          refine ⟨2169521462596406202422551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11570781133847499746253605 2169521462596406202422551)
          ·
            refine ⟨3254282193894609303633827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169521462596406202422551 3254282193894609303633827)
            ·
              refine ⟨4881423290841913955450741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254282193894609303633827 4881423290841913955450741)
              ·
                refine ⟨457633433516429433323507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4881423290841913955450741 457633433516429433323507)
                ·
                  refine ⟨686450150274644149985261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457633433516429433323507 686450150274644149985261)
                  ·
                    refine ⟨257418806352991556244473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686450150274644149985261 257418806352991556244473)
                    ·
                      refine ⟨193064104764743667183355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 257418806352991556244473 193064104764743667183355)
                      ·
                        rfl

theorem cell23_375991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_375991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375991 prefixEnd_375991 := by exact prefixLift 375991
  have htrace : WordTrace (prefixWord ++ tailWord_375991) baseStart_375991 baseEnd_375991 := by
    simpa [prefixWord, tailWord_375991, baseEnd_375991] using wordTrace_append hprefix tailTrace_375991
  have hstable : (prefixWord ++ tailWord_375991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375991).length < 2 ^ (prefixWord ++ tailWord_375991).sum := by decide
  have hdescent : baseEnd_375991 < baseStart_375991 := by decide
  rcases family_descends (prefixWord ++ tailWord_375991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375997 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_375997 : Nat := 118140960795 + 375997 * 2 ^ 59
def prefixEnd_375997 : Nat := 4983230072969 + 3 ^ 40 * 375997 * 2
def baseEnd_375997 : Nat := 64355728549556881236109

theorem tailTrace_375997 : CollatzResearch.WordTrace tailWord_375997 prefixEnd_375997 64355728549556881236109 := by
  unfold tailWord_375997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713737218834559020278245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9142491479223039346852163 13713737218834559020278245)
  ·
    refine ⟨2571325728531479816302171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13713737218834559020278245 2571325728531479816302171)
    ·
      refine ⟨3856988592797219724453257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571325728531479816302171 3856988592797219724453257)
      ·
        refine ⟨2892741444597914793339943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856988592797219724453257 2892741444597914793339943)
        ·
          refine ⟨4339112166896872190009915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892741444597914793339943 4339112166896872190009915)
          ·
            refine ⟨6508668250345308285014873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339112166896872190009915 6508668250345308285014873)
            ·
              refine ⟨4881501187758981213761155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508668250345308285014873 4881501187758981213761155)
              ·
                refine ⟨7322251781638471820641733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881501187758981213761155 7322251781638471820641733)
                ·
                  refine ⟨1372922209057213466370325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7322251781638471820641733 1372922209057213466370325)
                  ·
                    refine ⟨64355728549556881236109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1372922209057213466370325 64355728549556881236109)
                    ·
                      rfl

theorem cell23_375997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_375997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_375997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_375997 prefixEnd_375997 := by exact prefixLift 375997
  have htrace : WordTrace (prefixWord ++ tailWord_375997) baseStart_375997 baseEnd_375997 := by
    simpa [prefixWord, tailWord_375997, baseEnd_375997] using wordTrace_append hprefix tailTrace_375997
  have hstable : (prefixWord ++ tailWord_375997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375997).length < 2 ^ (prefixWord ++ tailWord_375997).sum := by decide
  have hdescent : baseEnd_375997 < baseStart_375997 := by decide
  rcases family_descends (prefixWord ++ tailWord_375997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376017 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_376017 : Nat := 118140960795 + 376017 * 2 ^ 59
def prefixEnd_376017 : Nat := 4983230072969 + 3 ^ 40 * 376017 * 2
def baseEnd_376017 : Nat := 193077455261760565458235

theorem tailTrace_376017 : CollatzResearch.WordTrace tailWord_376017 prefixEnd_376017 193077455261760565458235 := by
  unfold tailWord_376017
  simp only [CollatzResearch.WordTrace]
  refine ⟨13714466678762102436006305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9142977785841401624004203 13714466678762102436006305)
  ·
    refine ⟨10285850009071576827004729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13714466678762102436006305 10285850009071576827004729)
    ·
      refine ⟨7714387506803682620253547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10285850009071576827004729 7714387506803682620253547)
      ·
        refine ⟨11571581260205523930380321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714387506803682620253547 11571581260205523930380321)
        ·
          refine ⟨8678685945154142947785241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11571581260205523930380321 8678685945154142947785241)
          ·
            refine ⟨6509014458865607210838931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8678685945154142947785241 6509014458865607210838931)
            ·
              refine ⟨9763521688298410816258397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509014458865607210838931 9763521688298410816258397)
              ·
                refine ⟨3661320633111904056096899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9763521688298410816258397 3661320633111904056096899)
                ·
                  refine ⟨5491980949667856084145349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661320633111904056096899 5491980949667856084145349)
                  ·
                    refine ⟨1029746428062723015777253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491980949667856084145349 1029746428062723015777253)
                    ·
                      refine ⟨193077455261760565458235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1029746428062723015777253 193077455261760565458235)
                      ·
                        rfl

theorem cell23_376017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_376017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376017 prefixEnd_376017 := by exact prefixLift 376017
  have htrace : WordTrace (prefixWord ++ tailWord_376017) baseStart_376017 baseEnd_376017 := by
    simpa [prefixWord, tailWord_376017, baseEnd_376017] using wordTrace_append hprefix tailTrace_376017
  have hstable : (prefixWord ++ tailWord_376017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376017).length < 2 ^ (prefixWord ++ tailWord_376017).sum := by decide
  have hdescent : baseEnd_376017 < baseStart_376017 := by decide
  rcases family_descends (prefixWord ++ tailWord_376017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376144 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_376144 : Nat := 118140960795 + 376144 * 2 ^ 59
def prefixEnd_376144 : Nat := 4983230072969 + 3 ^ 40 * 376144 * 2
def baseEnd_376144 : Nat := 193142667304881568570151

theorem tailTrace_376144 : CollatzResearch.WordTrace tailWord_376144 prefixEnd_376144 193142667304881568570151 := by
  unfold tailWord_376144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859549374651001562939743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9146065832868002083919657 6859549374651001562939743)
  ·
    refine ⟨10289324061976502344409615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859549374651001562939743 10289324061976502344409615)
    ·
      refine ⟨15433986092964753516614423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10289324061976502344409615 15433986092964753516614423)
      ·
        refine ⟨23150979139447130274921635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15433986092964753516614423 23150979139447130274921635)
        ·
          refine ⟨34726468709170695412382453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23150979139447130274921635 34726468709170695412382453)
          ·
            refine ⟨3255606441484752694910855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34726468709170695412382453 3255606441484752694910855)
            ·
              refine ⟨4883409662227129042366283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255606441484752694910855 4883409662227129042366283)
              ·
                refine ⟨7325114493340693563549425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883409662227129042366283 7325114493340693563549425)
                ·
                  refine ⟨5493835870005520172662069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7325114493340693563549425 5493835870005520172662069)
                  ·
                    refine ⟨515047112813017516187069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5493835870005520172662069 515047112813017516187069)
                    ·
                      refine ⟨193142667304881568570151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515047112813017516187069 193142667304881568570151)
                      ·
                        rfl

theorem cell23_376144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_376144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376144 prefixEnd_376144 := by exact prefixLift 376144
  have htrace : WordTrace (prefixWord ++ tailWord_376144) baseStart_376144 baseEnd_376144 := by
    simpa [prefixWord, tailWord_376144, baseEnd_376144] using wordTrace_append hprefix tailTrace_376144
  have hstable : (prefixWord ++ tailWord_376144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376144).length < 2 ^ (prefixWord ++ tailWord_376144).sum := by decide
  have hdescent : baseEnd_376144 < baseStart_376144 := by decide
  rcases family_descends (prefixWord ++ tailWord_376144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376161 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_376161 : Nat := 118140960795 + 376161 * 2 ^ 59
def prefixEnd_376161 : Nat := 4983230072969 + 3 ^ 40 * 376161 * 2
def baseEnd_376161 : Nat := 193151396476008002057573

theorem tailTrace_376161 : CollatzResearch.WordTrace tailWord_376161 prefixEnd_376161 193151396476008002057573 := by
  unfold tailWord_376161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13719718790240415029248337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9146479193493610019498891 13719718790240415029248337)
  ·
    refine ⟨10289789092680311271936253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13719718790240415029248337 10289789092680311271936253)
    ·
      refine ⟨3858670909755116726976095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10289789092680311271936253 3858670909755116726976095)
      ·
        refine ⟨5788006364632675090464143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858670909755116726976095 5788006364632675090464143)
        ·
          refine ⟨8682009546949012635696215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788006364632675090464143 8682009546949012635696215)
          ·
            refine ⟨13023014320423518953544323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682009546949012635696215 13023014320423518953544323)
            ·
              refine ⟨19534521480635278430316485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023014320423518953544323 19534521480635278430316485)
              ·
                refine ⟨3662722777619114705684341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19534521480635278430316485 3662722777619114705684341)
                ·
                  refine ⟨343380260401792003657907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662722777619114705684341 343380260401792003657907)
                  ·
                    refine ⟨515070390602688005486861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343380260401792003657907 515070390602688005486861)
                    ·
                      refine ⟨193151396476008002057573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515070390602688005486861 193151396476008002057573)
                      ·
                        rfl

theorem cell23_376161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_376161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376161 prefixEnd_376161 := by exact prefixLift 376161
  have htrace : WordTrace (prefixWord ++ tailWord_376161) baseStart_376161 baseEnd_376161 := by
    simpa [prefixWord, tailWord_376161, baseEnd_376161] using wordTrace_append hprefix tailTrace_376161
  have hstable : (prefixWord ++ tailWord_376161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376161).length < 2 ^ (prefixWord ++ tailWord_376161).sum := by decide
  have hdescent : baseEnd_376161 < baseStart_376161 := by decide
  rcases family_descends (prefixWord ++ tailWord_376161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376231 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_376231 : Nat := 118140960795 + 376231 * 2 ^ 59
def prefixEnd_376231 : Nat := 4983230072969 + 3 ^ 40 * 376231 * 2
def baseEnd_376231 : Nat := 193187340121822728182251

theorem tailTrace_376231 : CollatzResearch.WordTrace tailWord_376231 prefixEnd_376231 193187340121822728182251 := by
  unfold tailWord_376231
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722271899986816984296547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9148181266657877989531031 13722271899986816984296547)
  ·
    refine ⟨20583407849980225476444821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13722271899986816984296547 20583407849980225476444821)
    ·
      refine ⟨964847242967823069208351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20583407849980225476444821 964847242967823069208351)
      ·
        refine ⟨1447270864451734603812527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964847242967823069208351 1447270864451734603812527)
        ·
          refine ⟨2170906296677601905718791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447270864451734603812527 2170906296677601905718791)
          ·
            refine ⟨3256359445016402858578187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170906296677601905718791 3256359445016402858578187)
            ·
              refine ⟨4884539167524604287867281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256359445016402858578187 4884539167524604287867281)
              ·
                refine ⟨3663404375643453215900461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884539167524604287867281 3663404375643453215900461)
                ·
                  refine ⟨1373776640866294955962673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3663404375643453215900461 1373776640866294955962673)
                  ·
                    refine ⟨1030332480649721216972005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373776640866294955962673 1030332480649721216972005)
                    ·
                      refine ⟨193187340121822728182251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1030332480649721216972005 193187340121822728182251)
                      ·
                        rfl

theorem cell23_376231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_376231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376231 prefixEnd_376231 := by exact prefixLift 376231
  have htrace : WordTrace (prefixWord ++ tailWord_376231) baseStart_376231 baseEnd_376231 := by
    simpa [prefixWord, tailWord_376231, baseEnd_376231] using wordTrace_append hprefix tailTrace_376231
  have hstable : (prefixWord ++ tailWord_376231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376231).length < 2 ^ (prefixWord ++ tailWord_376231).sum := by decide
  have hdescent : baseEnd_376231 < baseStart_376231 := by decide
  rcases family_descends (prefixWord ++ tailWord_376231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376252 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_376252 : Nat := 118140960795 + 376252 * 2 ^ 59
def prefixEnd_376252 : Nat := 4983230072969 + 3 ^ 40 * 376252 * 2
def baseEnd_376252 : Nat := 193198123215567146019655

theorem tailTrace_376252 : CollatzResearch.WordTrace tailWord_376252 prefixEnd_376252 193198123215567146019655 := by
  unfold tailWord_376252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861518916455368785405505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9148691888607158380540673 6861518916455368785405505)
  ·
    refine ⟨5146139187341526589054129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6861518916455368785405505 5146139187341526589054129)
    ·
      refine ⟨3859604390506144941790597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5146139187341526589054129 3859604390506144941790597)
      ·
        refine ⟨723675823219902176585737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3859604390506144941790597 723675823219902176585737)
        ·
          refine ⟨542756867414926632439303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723675823219902176585737 542756867414926632439303)
          ·
            refine ⟨814135301122389948658955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542756867414926632439303 814135301122389948658955)
            ·
              refine ⟨1221202951683584922988433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814135301122389948658955 1221202951683584922988433)
              ·
                refine ⟨915902213762688692241325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221202951683584922988433 915902213762688692241325)
                ·
                  refine ⟨343463330161008259590497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915902213762688692241325 343463330161008259590497)
                  ·
                    refine ⟨257597497620756194692873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 343463330161008259590497 257597497620756194692873)
                    ·
                      refine ⟨193198123215567146019655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 257597497620756194692873 193198123215567146019655)
                      ·
                        rfl

theorem cell23_376252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_376252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376252 prefixEnd_376252 := by exact prefixLift 376252
  have htrace : WordTrace (prefixWord ++ tailWord_376252) baseStart_376252 baseEnd_376252 := by
    simpa [prefixWord, tailWord_376252, baseEnd_376252] using wordTrace_append hprefix tailTrace_376252
  have hstable : (prefixWord ++ tailWord_376252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376252).length < 2 ^ (prefixWord ++ tailWord_376252).sum := by decide
  have hdescent : baseEnd_376252 < baseStart_376252 := by decide
  rcases family_descends (prefixWord ++ tailWord_376252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376268 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_376268 : Nat := 118140960795 + 376268 * 2 ^ 59
def prefixEnd_376268 : Nat := 4983230072969 + 3 ^ 40 * 376268 * 2
def baseEnd_376268 : Nat := 193206338906039083419581

theorem tailTrace_376268 : CollatzResearch.WordTrace tailWord_376268 prefixEnd_376268 193206338906039083419581 := by
  unfold tailWord_376268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861810700426386151696729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9149080933901848202262305 6861810700426386151696729)
  ·
    refine ⟨5146358025319789613772547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6861810700426386151696729 5146358025319789613772547)
    ·
      refine ⟨7719537037979684420658821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5146358025319789613772547 7719537037979684420658821)
      ·
        refine ⟨1447413194621190828873529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7719537037979684420658821 1447413194621190828873529)
        ·
          refine ⟨1085559895965893121655147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447413194621190828873529 1085559895965893121655147)
          ·
            refine ⟨1628339843948839682482721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085559895965893121655147 1628339843948839682482721)
            ·
              refine ⟨1221254882961629761862041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628339843948839682482721 1221254882961629761862041)
              ·
                refine ⟨915941162221222321396531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221254882961629761862041 915941162221222321396531)
                ·
                  refine ⟨1373911743331833482094797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915941162221222321396531 1373911743331833482094797)
                  ·
                    refine ⟨515216903749437555785549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373911743331833482094797 515216903749437555785549)
                    ·
                      refine ⟨193206338906039083419581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515216903749437555785549 193206338906039083419581)
                      ·
                        rfl

theorem cell23_376268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_376268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376268 prefixEnd_376268 := by exact prefixLift 376268
  have htrace : WordTrace (prefixWord ++ tailWord_376268) baseStart_376268 baseEnd_376268 := by
    simpa [prefixWord, tailWord_376268, baseEnd_376268] using wordTrace_append hprefix tailTrace_376268
  have hstable : (prefixWord ++ tailWord_376268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376268).length < 2 ^ (prefixWord ++ tailWord_376268).sum := by decide
  have hdescent : baseEnd_376268 < baseStart_376268 := by decide
  rcases family_descends (prefixWord ++ tailWord_376268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376285 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_376285 : Nat := 118140960795 + 376285 * 2 ^ 59
def prefixEnd_376285 : Nat := 4983230072969 + 3 ^ 40 * 376285 * 2
def baseEnd_376285 : Nat := 193215068077165516907003

theorem tailTrace_376285 : CollatzResearch.WordTrace tailWord_376285 prefixEnd_376285 193215068077165516907003 := by
  unfold tailWord_376285
  simp only [CollatzResearch.WordTrace]
  refine ⟨13724241441791184206762309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9149494294527456137841539 13724241441791184206762309)
  ·
    refine ⟨2573295270335847038767933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13724241441791184206762309 2573295270335847038767933)
    ·
      refine ⟨964985726375942639537975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2573295270335847038767933 964985726375942639537975)
      ·
        refine ⟨1447478589563913959306963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964985726375942639537975 1447478589563913959306963)
        ·
          refine ⟨2171217884345870938960445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447478589563913959306963 2171217884345870938960445)
          ·
            refine ⟨814206706629701602110167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171217884345870938960445 814206706629701602110167)
            ·
              refine ⟨1221310059944552403165251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814206706629701602110167 1221310059944552403165251)
              ·
                refine ⟨1831965089916828604747877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221310059944552403165251 1831965089916828604747877)
                ·
                  refine ⟨343493454359405363390227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831965089916828604747877 343493454359405363390227)
                  ·
                    refine ⟨515240181539108045085341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343493454359405363390227 515240181539108045085341)
                    ·
                      refine ⟨193215068077165516907003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515240181539108045085341 193215068077165516907003)
                      ·
                        rfl

theorem cell23_376285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_376285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376285 prefixEnd_376285 := by exact prefixLift 376285
  have htrace : WordTrace (prefixWord ++ tailWord_376285) baseStart_376285 baseEnd_376285 := by
    simpa [prefixWord, tailWord_376285, baseEnd_376285] using wordTrace_append hprefix tailTrace_376285
  have hstable : (prefixWord ++ tailWord_376285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376285).length < 2 ^ (prefixWord ++ tailWord_376285).sum := by decide
  have hdescent : baseEnd_376285 < baseStart_376285 := by decide
  rcases family_descends (prefixWord ++ tailWord_376285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376302 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_376302 : Nat := 118140960795 + 376302 * 2 ^ 59
def prefixEnd_376302 : Nat := 4983230072969 + 3 ^ 40 * 376302 * 2
def baseEnd_376302 : Nat := 193223797248291950394425

theorem tailTrace_376302 : CollatzResearch.WordTrace tailWord_376302 prefixEnd_376302 193223797248291950394425 := by
  unfold tailWord_376302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715607685341199513766395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9149907655153064073420773 1715607685341199513766395)
  ·
    refine ⟨2573411528011799270649593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715607685341199513766395 2573411528011799270649593)
    ·
      refine ⟨1930058646008849452987195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2573411528011799270649593 1930058646008849452987195)
      ·
        refine ⟨2895087969013274179480793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1930058646008849452987195 2895087969013274179480793)
        ·
          refine ⟨2171315976759955634610595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895087969013274179480793 2171315976759955634610595)
          ·
            refine ⟨3256973965139933451915893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171315976759955634610595 3256973965139933451915893)
            ·
              refine ⟨305341309231868761117115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3256973965139933451915893 305341309231868761117115)
              ·
                refine ⟨458011963847803141675673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305341309231868761117115 458011963847803141675673)
                ·
                  refine ⟨343508972885852356256755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458011963847803141675673 343508972885852356256755)
                  ·
                    refine ⟨515263459328778534385133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343508972885852356256755 515263459328778534385133)
                    ·
                      refine ⟨193223797248291950394425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515263459328778534385133 193223797248291950394425)
                      ·
                        rfl

theorem cell23_376302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_376302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376302 prefixEnd_376302 := by exact prefixLift 376302
  have htrace : WordTrace (prefixWord ++ tailWord_376302) baseStart_376302 baseEnd_376302 := by
    simpa [prefixWord, tailWord_376302, baseEnd_376302] using wordTrace_append hprefix tailTrace_376302
  have hstable : (prefixWord ++ tailWord_376302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376302).length < 2 ^ (prefixWord ++ tailWord_376302).sum := by decide
  have hdescent : baseEnd_376302 < baseStart_376302 := by decide
  rcases family_descends (prefixWord ++ tailWord_376302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376378 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_376378 : Nat := 118140960795 + 376378 * 2 ^ 59
def prefixEnd_376378 : Nat := 4983230072969 + 3 ^ 40 * 376378 * 2
def baseEnd_376378 : Nat := 64420940592677884348025

theorem tailTrace_376378 : CollatzResearch.WordTrace tailWord_376378 prefixEnd_376378 64420940592677884348025 := by
  unfold tailWord_376378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431908357613565272474447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9151755620302840726598525 3431908357613565272474447)
  ·
    refine ⟨5147862536420347908711671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3431908357613565272474447 5147862536420347908711671)
    ·
      refine ⟨7721793804630521863067507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5147862536420347908711671 7721793804630521863067507)
      ·
        refine ⟨11582690706945782794601261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7721793804630521863067507 11582690706945782794601261)
        ·
          refine ⟨4343509015104668547975473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11582690706945782794601261 4343509015104668547975473)
          ·
            refine ⟨3257631761328501410981605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4343509015104668547975473 3257631761328501410981605)
            ·
              refine ⟨610805955249094014559051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3257631761328501410981605 610805955249094014559051)
              ·
                refine ⟨916208932873641021838577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610805955249094014559051 916208932873641021838577)
                ·
                  refine ⟨687156699655230766378933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916208932873641021838577 687156699655230766378933)
                  ·
                    refine ⟨64420940592677884348025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687156699655230766378933 64420940592677884348025)
                    ·
                      rfl

theorem cell23_376378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_376378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376378 prefixEnd_376378 := by exact prefixLift 376378
  have htrace : WordTrace (prefixWord ++ tailWord_376378) baseStart_376378 baseEnd_376378 := by
    simpa [prefixWord, tailWord_376378, baseEnd_376378] using wordTrace_append hprefix tailTrace_376378
  have hstable : (prefixWord ++ tailWord_376378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376378).length < 2 ^ (prefixWord ++ tailWord_376378).sum := by decide
  have hdescent : baseEnd_376378 < baseStart_376378 := by decide
  rcases family_descends (prefixWord ++ tailWord_376378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376401 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_376401 : Nat := 118140960795 + 376401 * 2 ^ 59
def prefixEnd_376401 : Nat := 4983230072969 + 3 ^ 40 * 376401 * 2
def baseEnd_376401 : Nat := 193274631833087063056469

theorem tailTrace_376401 : CollatzResearch.WordTrace tailWord_376401 prefixEnd_376401 193274631833087063056469 := by
  unfold tailWord_376401
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728472309370936017985057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9152314872913957345323371 13728472309370936017985057)
  ·
    refine ⟨10296354232028202013488793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13728472309370936017985057 10296354232028202013488793)
    ·
      refine ⟨7722265674021151510116595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10296354232028202013488793 7722265674021151510116595)
      ·
        refine ⟨11583398511031727265174893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722265674021151510116595 11583398511031727265174893)
        ·
          refine ⟨4343774441636897724440585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11583398511031727265174893 4343774441636897724440585)
          ·
            refine ⟨3257830831227673293330439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4343774441636897724440585 3257830831227673293330439)
            ·
              refine ⟨4886746246841509939995659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257830831227673293330439 4886746246841509939995659)
              ·
                refine ⟨7330119370262264909993489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4886746246841509939995659 7330119370262264909993489)
                ·
                  refine ⟨5497589527696698682495117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7330119370262264909993489 5497589527696698682495117)
                  ·
                    refine ⟨2061596072886262005935669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5497589527696698682495117 2061596072886262005935669)
                    ·
                      refine ⟨193274631833087063056469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2061596072886262005935669 193274631833087063056469)
                      ·
                        rfl

theorem cell23_376401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_376401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376401 prefixEnd_376401 := by exact prefixLift 376401
  have htrace : WordTrace (prefixWord ++ tailWord_376401) baseStart_376401 baseEnd_376401 := by
    simpa [prefixWord, tailWord_376401, baseEnd_376401] using wordTrace_append hprefix tailTrace_376401
  have hstable : (prefixWord ++ tailWord_376401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376401).length < 2 ^ (prefixWord ++ tailWord_376401).sum := by decide
  have hdescent : baseEnd_376401 < baseStart_376401 := by decide
  rcases family_descends (prefixWord ++ tailWord_376401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376408 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_376408 : Nat := 118140960795 + 376408 * 2 ^ 59
def prefixEnd_376408 : Nat := 4983230072969 + 3 ^ 40 * 376408 * 2
def baseEnd_376408 : Nat := 64426075399222845222979

theorem tailTrace_376408 : CollatzResearch.WordTrace tailWord_376408 prefixEnd_376408 64426075399222845222979 := by
  unfold tailWord_376408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864363810172788106744939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9152485080230384142326585 6864363810172788106744939)
  ·
    refine ⟨10296545715259182160117409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6864363810172788106744939 10296545715259182160117409)
    ·
      refine ⟨7722409286444386620088057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10296545715259182160117409 7722409286444386620088057)
      ·
        refine ⟨5791806964833289965066043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7722409286444386620088057 5791806964833289965066043)
        ·
          refine ⟨8687710447249934947599065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791806964833289965066043 8687710447249934947599065)
          ·
            refine ⟨6515782835437451210699299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8687710447249934947599065 6515782835437451210699299)
            ·
              refine ⟨9773674253156176816048949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515782835437451210699299 9773674253156176816048949)
              ·
                refine ⟨916281961233391576504589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9773674253156176816048949 916281961233391576504589)
                ·
                  refine ⟨343605735462521841189221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916281961233391576504589 343605735462521841189221)
                  ·
                    refine ⟨64426075399222845222979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 343605735462521841189221 64426075399222845222979)
                    ·
                      rfl

theorem cell23_376408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_376408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376408 prefixEnd_376408 := by exact prefixLift 376408
  have htrace : WordTrace (prefixWord ++ tailWord_376408) baseStart_376408 baseEnd_376408 := by
    simpa [prefixWord, tailWord_376408, baseEnd_376408] using wordTrace_append hprefix tailTrace_376408
  have hstable : (prefixWord ++ tailWord_376408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376408).length < 2 ^ (prefixWord ++ tailWord_376408).sum := by decide
  have hdescent : baseEnd_376408 < baseStart_376408 := by decide
  rcases family_descends (prefixWord ++ tailWord_376408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376455 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 6]
def baseStart_376455 : Nat := 118140960795 + 376455 * 2 ^ 59
def prefixEnd_376455 : Nat := 4983230072969 + 3 ^ 40 * 376455 * 2
def baseEnd_376455 : Nat := 21478039976492205753469

theorem tailTrace_376455 : CollatzResearch.WordTrace tailWord_376455 prefixEnd_376455 21478039976492205753469 := by
  unfold tailWord_376455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730441851175303240450819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9153627900783535493633879 13730441851175303240450819)
  ·
    refine ⟨20595662776762954860676229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13730441851175303240450819 20595662776762954860676229)
    ·
      refine ⟨3861686770643054036376793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20595662776762954860676229 3861686770643054036376793)
      ·
        refine ⟨2896265077982290527282595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3861686770643054036376793 2896265077982290527282595)
        ·
          refine ⟨4344397616973435790923893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896265077982290527282595 4344397616973435790923893)
          ·
            refine ⟨407287276591259605399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4344397616973435790923893 407287276591259605399115)
            ·
              refine ⟨610930914886889408098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407287276591259605399115 610930914886889408098673)
              ·
                refine ⟨458198186165167056074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610930914886889408098673 458198186165167056074005)
                ·
                  refine ⟨21478039976492205753469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 458198186165167056074005 21478039976492205753469)
                  ·
                    rfl

theorem cell23_376455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 6].length) (baseStart_376455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376455 prefixEnd_376455 := by exact prefixLift 376455
  have htrace : WordTrace (prefixWord ++ tailWord_376455) baseStart_376455 baseEnd_376455 := by
    simpa [prefixWord, tailWord_376455, baseEnd_376455] using wordTrace_append hprefix tailTrace_376455
  have hstable : (prefixWord ++ tailWord_376455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376455).length < 2 ^ (prefixWord ++ tailWord_376455).sum := by decide
  have hdescent : baseEnd_376455 < baseStart_376455 := by decide
  rcases family_descends (prefixWord ++ tailWord_376455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376458 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_376458 : Nat := 118140960795 + 376458 * 2 ^ 59
def prefixEnd_376458 : Nat := 4983230072969 + 3 ^ 40 * 376458 * 2
def baseEnd_376458 : Nat := 193303900230393340043707

theorem tailTrace_376458 : CollatzResearch.WordTrace tailWord_376458 prefixEnd_376458 193303900230393340043707 := by
  unfold tailWord_376458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432637817541108688202507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9153700846776289835206685 3432637817541108688202507)
  ·
    refine ⟨5148956726311663032303761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432637817541108688202507 5148956726311663032303761)
    ·
      refine ⟨3861717544733747274227821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5148956726311663032303761 3861717544733747274227821)
      ·
        refine ⟨1448144079275155227835433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3861717544733747274227821 1448144079275155227835433)
        ·
          refine ⟨1086108059456366420876575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448144079275155227835433 1086108059456366420876575)
          ·
            refine ⟨1629162089184549631314863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086108059456366420876575 1629162089184549631314863)
            ·
              refine ⟨2443743133776824446972295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629162089184549631314863 2443743133776824446972295)
              ·
                refine ⟨3665614700665236670458443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443743133776824446972295 3665614700665236670458443)
                ·
                  refine ⟨5498422050997855005687665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665614700665236670458443 5498422050997855005687665)
                  ·
                    refine ⟨4123816538248391254265749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498422050997855005687665 4123816538248391254265749)
                    ·
                      refine ⟨193303900230393340043707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4123816538248391254265749 193303900230393340043707)
                      ·
                        rfl

theorem cell23_376458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_376458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376458 prefixEnd_376458 := by exact prefixLift 376458
  have htrace : WordTrace (prefixWord ++ tailWord_376458) baseStart_376458 baseEnd_376458 := by
    simpa [prefixWord, tailWord_376458, baseEnd_376458] using wordTrace_append hprefix tailTrace_376458
  have hstable : (prefixWord ++ tailWord_376458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376458).length < 2 ^ (prefixWord ++ tailWord_376458).sum := by decide
  have hdescent : baseEnd_376458 < baseStart_376458 := by decide
  rcases family_descends (prefixWord ++ tailWord_376458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376498 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_376498 : Nat := 118140960795 + 376498 * 2 ^ 59
def prefixEnd_376498 : Nat := 4983230072969 + 3 ^ 40 * 376498 * 2
def baseEnd_376498 : Nat := 64441479818857727847841

theorem tailTrace_376498 : CollatzResearch.WordTrace tailWord_376498 prefixEnd_376498 64441479818857727847841 := by
  unfold tailWord_376498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433002547504880396066537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9154673460013014389510765 3433002547504880396066537)
  ·
    refine ⟨2574751910628660297049903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3433002547504880396066537 2574751910628660297049903)
    ·
      refine ⟨3862127865942990445574855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574751910628660297049903 3862127865942990445574855)
      ·
        refine ⟨5793191798914485668362283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862127865942990445574855 5793191798914485668362283)
        ·
          refine ⟨8689787698371728502543425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793191798914485668362283 8689787698371728502543425)
          ·
            refine ⟨6517340773778796376907569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8689787698371728502543425 6517340773778796376907569)
            ·
              refine ⟨4888005580334097282680677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6517340773778796376907569 4888005580334097282680677)
              ·
                refine ⟨916501046312643240502627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4888005580334097282680677 916501046312643240502627)
                ·
                  refine ⟨1374751569468964860753941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916501046312643240502627 1374751569468964860753941)
                  ·
                    refine ⟨64441479818857727847841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1374751569468964860753941 64441479818857727847841)
                    ·
                      rfl

theorem cell23_376498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_376498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376498 prefixEnd_376498 := by exact prefixLift 376498
  have htrace : WordTrace (prefixWord ++ tailWord_376498) baseStart_376498 baseEnd_376498 := by
    simpa [prefixWord, tailWord_376498, baseEnd_376498] using wordTrace_append hprefix tailTrace_376498
  have hstable : (prefixWord ++ tailWord_376498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376498).length < 2 ^ (prefixWord ++ tailWord_376498).sum := by decide
  have hdescent : baseEnd_376498 < baseStart_376498 := by decide
  rcases family_descends (prefixWord ++ tailWord_376498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376505 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_376505 : Nat := 118140960795 + 376505 * 2 ^ 59
def prefixEnd_376505 : Nat := 4983230072969 + 3 ^ 40 * 376505 * 2
def baseEnd_376505 : Nat := 193328033821154656155991

theorem tailTrace_376505 : CollatzResearch.WordTrace tailWord_376505 prefixEnd_376505 193328033821154656155991 := by
  unfold tailWord_376505
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732265500994161779770969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9154843667329441186513979 13732265500994161779770969)
  ·
    refine ⟨10299199125745621334828227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13732265500994161779770969 10299199125745621334828227)
    ·
      refine ⟨15448798688618432002242341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299199125745621334828227 15448798688618432002242341)
      ·
        refine ⟨2896649754115956000420439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15448798688618432002242341 2896649754115956000420439)
        ·
          refine ⟨4344974631173934000630659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896649754115956000420439 4344974631173934000630659)
          ·
            refine ⟨6517461946760901000945989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344974631173934000630659 6517461946760901000945989)
            ·
              refine ⟨1222024115017668937677373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6517461946760901000945989 1222024115017668937677373)
              ·
                refine ⟨458259043131625851629015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1222024115017668937677373 458259043131625851629015)
                ·
                  refine ⟨687388564697438777443523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458259043131625851629015 687388564697438777443523)
                  ·
                    refine ⟨1031082847046158166165285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 687388564697438777443523 1031082847046158166165285)
                    ·
                      refine ⟨193328033821154656155991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1031082847046158166165285 193328033821154656155991)
                      ·
                        rfl

theorem cell23_376505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_376505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376505 prefixEnd_376505 := by exact prefixLift 376505
  have htrace : WordTrace (prefixWord ++ tailWord_376505) baseStart_376505 baseEnd_376505 := by
    simpa [prefixWord, tailWord_376505, baseEnd_376505] using wordTrace_append hprefix tailTrace_376505
  have hstable : (prefixWord ++ tailWord_376505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376505).length < 2 ^ (prefixWord ++ tailWord_376505).sum := by decide
  have hdescent : baseEnd_376505 < baseStart_376505 := by decide
  rcases family_descends (prefixWord ++ tailWord_376505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376516 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_376516 : Nat := 118140960795 + 376516 * 2 ^ 59
def prefixEnd_376516 : Nat := 4983230072969 + 3 ^ 40 * 376516 * 2
def baseEnd_376516 : Nat := 193333682108354113118441

theorem tailTrace_376516 : CollatzResearch.WordTrace tailWord_376516 prefixEnd_376516 193333682108354113118441 := by
  unfold tailWord_376516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866333351977155329210701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9155111135969540438947601 6866333351977155329210701)
  ·
    refine ⟨2574875006991433248454013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6866333351977155329210701 2574875006991433248454013)
    ·
      refine ⟨965578127621787468170255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2574875006991433248454013 965578127621787468170255)
      ·
        refine ⟨1448367191432681202255383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965578127621787468170255 1448367191432681202255383)
        ·
          refine ⟨2172550787149021803383075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448367191432681202255383 2172550787149021803383075)
          ·
            refine ⟨3258826180723532705074613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172550787149021803383075 3258826180723532705074613)
            ·
              refine ⟨305514954442831191100745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3258826180723532705074613 305514954442831191100745)
              ·
                refine ⟨229136215832123393325559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305514954442831191100745 229136215832123393325559)
                ·
                  refine ⟨343704323748185089988339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229136215832123393325559 343704323748185089988339)
                  ·
                    refine ⟨515556485622277634982509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343704323748185089988339 515556485622277634982509)
                    ·
                      refine ⟨193333682108354113118441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515556485622277634982509 193333682108354113118441)
                      ·
                        rfl

theorem cell23_376516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_376516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376516 prefixEnd_376516 := by exact prefixLift 376516
  have htrace : WordTrace (prefixWord ++ tailWord_376516) baseStart_376516 baseEnd_376516 := by
    simpa [prefixWord, tailWord_376516, baseEnd_376516] using wordTrace_append hprefix tailTrace_376516
  have hstable : (prefixWord ++ tailWord_376516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376516).length < 2 ^ (prefixWord ++ tailWord_376516).sum := by decide
  have hdescent : baseEnd_376516 < baseStart_376516 := by decide
  rcases family_descends (prefixWord ++ tailWord_376516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376555 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 3]
def baseStart_376555 : Nat := 118140960795 + 376555 * 2 ^ 59
def prefixEnd_376555 : Nat := 4983230072969 + 3 ^ 40 * 376555 * 2
def baseEnd_376555 : Nat := 193353707853879460530761

theorem tailTrace_376555 : CollatzResearch.WordTrace tailWord_376555 prefixEnd_376555 193353707853879460530761 := by
  unfold tailWord_376555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13734089150813020319091119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9156059433875346879394079 13734089150813020319091119)
  ·
    refine ⟨20601133726219530478636679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13734089150813020319091119 20601133726219530478636679)
    ·
      refine ⟨30901700589329295717955019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20601133726219530478636679 30901700589329295717955019)
      ·
        refine ⟨46352550883993943576932529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30901700589329295717955019 46352550883993943576932529)
        ·
          refine ⟨34764413162995457682699397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46352550883993943576932529 34764413162995457682699397)
          ·
            refine ⟨6518327468061648315506137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34764413162995457682699397 6518327468061648315506137)
            ·
              refine ⟨4888745601046236236629603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518327468061648315506137 4888745601046236236629603)
              ·
                refine ⟨7333118401569354354944405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888745601046236236629603 7333118401569354354944405)
                ·
                  refine ⟨343739925073563485388019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7333118401569354354944405 343739925073563485388019)
                  ·
                    refine ⟨515609887610345228082029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343739925073563485388019 515609887610345228082029)
                    ·
                      refine ⟨193353707853879460530761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515609887610345228082029 193353707853879460530761)
                      ·
                        rfl

theorem cell23_376555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 3].length) (baseStart_376555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376555 prefixEnd_376555 := by exact prefixLift 376555
  have htrace : WordTrace (prefixWord ++ tailWord_376555) baseStart_376555 baseEnd_376555 := by
    simpa [prefixWord, tailWord_376555, baseEnd_376555] using wordTrace_append hprefix tailTrace_376555
  have hstable : (prefixWord ++ tailWord_376555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376555).length < 2 ^ (prefixWord ++ tailWord_376555).sum := by decide
  have hdescent : baseEnd_376555 < baseStart_376555 := by decide
  rcases family_descends (prefixWord ++ tailWord_376555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376588 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_376588 : Nat := 118140960795 + 376588 * 2 ^ 59
def prefixEnd_376588 : Nat := 4983230072969 + 3 ^ 40 * 376588 * 2
def baseEnd_376588 : Nat := 64456884238492610472703

theorem tailTrace_376588 : CollatzResearch.WordTrace tailWord_376588 prefixEnd_376588 64456884238492610472703 := by
  unfold tailWord_376588
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867646379846733477521209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9156861839795644636694945 6867646379846733477521209)
  ·
    refine ⟨5150734784885050108140907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6867646379846733477521209 5150734784885050108140907)
    ·
      refine ⟨7726102177327575162211361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150734784885050108140907 7726102177327575162211361)
      ·
        refine ⟨5794576632995681371658521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7726102177327575162211361 5794576632995681371658521)
        ·
          refine ⟨4345932474746761028743891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794576632995681371658521 4345932474746761028743891)
          ·
            refine ⟨6518898712120141543115837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345932474746761028743891 6518898712120141543115837)
            ·
              refine ⟨2444587017045053078668439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6518898712120141543115837 2444587017045053078668439)
              ·
                refine ⟨3666880525567579618002659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444587017045053078668439 3666880525567579618002659)
                ·
                  refine ⟨5500320788351369427003989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666880525567579618002659 5500320788351369427003989)
                  ·
                    refine ⟨64456884238492610472703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5500320788351369427003989 64456884238492610472703)
                    ·
                      rfl

theorem cell23_376588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_376588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376588 prefixEnd_376588 := by exact prefixLift 376588
  have htrace : WordTrace (prefixWord ++ tailWord_376588) baseStart_376588 baseEnd_376588 := by
    simpa [prefixWord, tailWord_376588, baseEnd_376588] using wordTrace_append hprefix tailTrace_376588
  have hstable : (prefixWord ++ tailWord_376588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376588).length < 2 ^ (prefixWord ++ tailWord_376588).sum := by decide
  have hdescent : baseEnd_376588 < baseStart_376588 := by decide
  rcases family_descends (prefixWord ++ tailWord_376588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376596 : List Nat := [2, 4, 4, 1, 1, 1, 3, 7]
def baseStart_376596 : Nat := 118140960795 + 376596 * 2 ^ 59
def prefixEnd_376596 : Nat := 4983230072969 + 3 ^ 40 * 376596 * 2
def baseEnd_376596 : Nat := 7162028168915325930299

theorem tailTrace_376596 : CollatzResearch.WordTrace tailWord_376596 prefixEnd_376596 7162028168915325930299 := by
  unfold tailWord_376596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867792271832242160666821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9157056362442989547555761 6867792271832242160666821)
  ·
    refine ⟨1287711050968545405125029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6867792271832242160666821 1287711050968545405125029)
    ·
      refine ⟨241445822056602263460943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1287711050968545405125029 241445822056602263460943)
      ·
        refine ⟨362168733084903395191415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241445822056602263460943 362168733084903395191415)
        ·
          refine ⟨543253099627355092787123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362168733084903395191415 543253099627355092787123)
          ·
            refine ⟨814879649441032639180685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543253099627355092787123 814879649441032639180685)
            ·
              refine ⟨305579868540387239692757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 814879649441032639180685 305579868540387239692757)
              ·
                refine ⟨7162028168915325930299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 305579868540387239692757 7162028168915325930299)
                ·
                  rfl

theorem cell23_376596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 7].length) (baseStart_376596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376596 prefixEnd_376596 := by exact prefixLift 376596
  have htrace : WordTrace (prefixWord ++ tailWord_376596) baseStart_376596 baseEnd_376596 := by
    simpa [prefixWord, tailWord_376596, baseEnd_376596] using wordTrace_append hprefix tailTrace_376596
  have hstable : (prefixWord ++ tailWord_376596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376596).length < 2 ^ (prefixWord ++ tailWord_376596).sum := by decide
  have hdescent : baseEnd_376596 < baseStart_376596 := by decide
  rcases family_descends (prefixWord ++ tailWord_376596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376616 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_376616 : Nat := 118140960795 + 376616 * 2 ^ 59
def prefixEnd_376616 : Nat := 4983230072969 + 3 ^ 40 * 376616 * 2
def baseEnd_376616 : Nat := 193385030173803721867981

theorem tailTrace_376616 : CollatzResearch.WordTrace tailWord_376616 prefixEnd_376616 193385030173803721867981 := by
  unfold tailWord_376616
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868157001796013868530851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9157542669061351824707801 6868157001796013868530851)
  ·
    refine ⟨10302235502694020802796277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6868157001796013868530851 10302235502694020802796277)
    ·
      refine ⟨965834578377564450262151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10302235502694020802796277 965834578377564450262151)
      ·
        refine ⟨1448751867566346675393227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965834578377564450262151 1448751867566346675393227)
        ·
          refine ⟨2173127801349520013089841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448751867566346675393227 2173127801349520013089841)
          ·
            refine ⟨1629845851012140009817381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173127801349520013089841 1629845851012140009817381)
            ·
              refine ⟨305596097064776251840759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1629845851012140009817381 305596097064776251840759)
              ·
                refine ⟨458394145597164377761139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305596097064776251840759 458394145597164377761139)
                ·
                  refine ⟨687591218395746566641709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458394145597164377761139 687591218395746566641709)
                  ·
                    refine ⟨257846706898404962490641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687591218395746566641709 257846706898404962490641)
                    ·
                      refine ⟨193385030173803721867981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 257846706898404962490641 193385030173803721867981)
                      ·
                        rfl

theorem cell23_376616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_376616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376616 prefixEnd_376616 := by exact prefixLift 376616
  have htrace : WordTrace (prefixWord ++ tailWord_376616) baseStart_376616 baseEnd_376616 := by
    simpa [prefixWord, tailWord_376616, baseEnd_376616] using wordTrace_append hprefix tailTrace_376616
  have hstable : (prefixWord ++ tailWord_376616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376616).length < 2 ^ (prefixWord ++ tailWord_376616).sum := by decide
  have hdescent : baseEnd_376616 < baseStart_376616 := by decide
  rcases family_descends (prefixWord ++ tailWord_376616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376625 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_376625 : Nat := 118140960795 + 376625 * 2 ^ 59
def prefixEnd_376625 : Nat := 4983230072969 + 3 ^ 40 * 376625 * 2
def baseEnd_376625 : Nat := 193389651499694186655439

theorem tailTrace_376625 : CollatzResearch.WordTrace tailWord_376625 prefixEnd_376625 193389651499694186655439 := by
  unfold tailWord_376625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13736642260559422274139329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9157761507039614849426219 13736642260559422274139329)
  ·
    refine ⟨10302481695419566705604497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13736642260559422274139329 10302481695419566705604497)
    ·
      refine ⟨7726861271564675029203373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10302481695419566705604497 7726861271564675029203373)
      ·
        refine ⟨2897572976836753135951265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7726861271564675029203373 2897572976836753135951265)
        ·
          refine ⟨2173179732627564851963449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897572976836753135951265 2173179732627564851963449)
          ·
            refine ⟨1629884799470673638972587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173179732627564851963449 1629884799470673638972587)
            ·
              refine ⟨2444827199206010458458881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629884799470673638972587 2444827199206010458458881)
              ·
                refine ⟨1833620399404507843844161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444827199206010458458881 1833620399404507843844161)
                ·
                  refine ⟨1375215299553380882883121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833620399404507843844161 1375215299553380882883121)
                  ·
                    refine ⟨1031411474665035662162341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375215299553380882883121 1031411474665035662162341)
                    ·
                      refine ⟨193389651499694186655439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1031411474665035662162341 193389651499694186655439)
                      ·
                        rfl

theorem cell23_376625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_376625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376625 prefixEnd_376625 := by exact prefixLift 376625
  have htrace : WordTrace (prefixWord ++ tailWord_376625) baseStart_376625 baseEnd_376625 := by
    simpa [prefixWord, tailWord_376625, baseEnd_376625] using wordTrace_append hprefix tailTrace_376625
  have hstable : (prefixWord ++ tailWord_376625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376625).length < 2 ^ (prefixWord ++ tailWord_376625).sum := by decide
  have hdescent : baseEnd_376625 < baseStart_376625 := by decide
  rcases family_descends (prefixWord ++ tailWord_376625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376645 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_376645 : Nat := 118140960795 + 376645 * 2 ^ 59
def prefixEnd_376645 : Nat := 4983230072969 + 3 ^ 40 * 376645 * 2
def baseEnd_376645 : Nat := 193399921112784108405347

theorem tailTrace_376645 : CollatzResearch.WordTrace tailWord_376645 prefixEnd_376645 193399921112784108405347 := by
  unfold tailWord_376645
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737371720486965689867389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9158247813657977126578259 13737371720486965689867389)
  ·
    refine ⟨5151514395182612133700271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13737371720486965689867389 5151514395182612133700271)
    ·
      refine ⟨7727271592773918200550407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151514395182612133700271 7727271592773918200550407)
      ·
        refine ⟨11590907389160877300825611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7727271592773918200550407 11590907389160877300825611)
        ·
          refine ⟨17386361083741315951238417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11590907389160877300825611 17386361083741315951238417)
          ·
            refine ⟨13039770812805986963428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17386361083741315951238417 13039770812805986963428813)
            ·
              refine ⟨4889914054802245111285805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13039770812805986963428813 4889914054802245111285805)
              ·
                refine ⟨1833717770550841916732177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889914054802245111285805 1833717770550841916732177)
                ·
                  refine ⟨1375288327913131437549133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833717770550841916732177 1375288327913131437549133)
                  ·
                    refine ⟨515733122967424289080925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375288327913131437549133 515733122967424289080925)
                    ·
                      refine ⟨193399921112784108405347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515733122967424289080925 193399921112784108405347)
                      ·
                        rfl

theorem cell23_376645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_376645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376645 prefixEnd_376645 := by exact prefixLift 376645
  have htrace : WordTrace (prefixWord ++ tailWord_376645) baseStart_376645 baseEnd_376645 := by
    simpa [prefixWord, tailWord_376645, baseEnd_376645] using wordTrace_append hprefix tailTrace_376645
  have hstable : (prefixWord ++ tailWord_376645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376645).length < 2 ^ (prefixWord ++ tailWord_376645).sum := by decide
  have hdescent : baseEnd_376645 < baseStart_376645 := by decide
  rcases family_descends (prefixWord ++ tailWord_376645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376665 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_376665 : Nat := 118140960795 + 376665 * 2 ^ 59
def prefixEnd_376665 : Nat := 4983230072969 + 3 ^ 40 * 376665 * 2
def baseEnd_376665 : Nat := 64470063575291343385085

theorem tailTrace_376665 : CollatzResearch.WordTrace tailWord_376665 prefixEnd_376665 64470063575291343385085 := by
  unfold tailWord_376665
  simp only [CollatzResearch.WordTrace]
  refine ⟨13738101180414509105595449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9158734120276339403730299 13738101180414509105595449)
  ·
    refine ⟨10303575885310881829196587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13738101180414509105595449 10303575885310881829196587)
    ·
      refine ⟨15455363827966322743794881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10303575885310881829196587 15455363827966322743794881)
      ·
        refine ⟨11591522870974742057846161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15455363827966322743794881 11591522870974742057846161)
        ·
          refine ⟨8693642153231056543384621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11591522870974742057846161 8693642153231056543384621)
          ·
            refine ⟨3260115807461646203769233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8693642153231056543384621 3260115807461646203769233)
            ·
              refine ⟨2445086855596234652826925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260115807461646203769233 2445086855596234652826925)
              ·
                refine ⟨916907570848587994810097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2445086855596234652826925 916907570848587994810097)
                ·
                  refine ⟨687680678136440996107573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916907570848587994810097 687680678136440996107573)
                  ·
                    refine ⟨64470063575291343385085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687680678136440996107573 64470063575291343385085)
                    ·
                      rfl

theorem cell23_376665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_376665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376665 prefixEnd_376665 := by exact prefixLift 376665
  have htrace : WordTrace (prefixWord ++ tailWord_376665) baseStart_376665 baseEnd_376665 := by
    simpa [prefixWord, tailWord_376665, baseEnd_376665] using wordTrace_append hprefix tailTrace_376665
  have hstable : (prefixWord ++ tailWord_376665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376665).length < 2 ^ (prefixWord ++ tailWord_376665).sum := by decide
  have hdescent : baseEnd_376665 < baseStart_376665 := by decide
  rcases family_descends (prefixWord ++ tailWord_376665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376686 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_376686 : Nat := 118140960795 + 376686 * 2 ^ 59
def prefixEnd_376686 : Nat := 4983230072969 + 3 ^ 40 * 376686 * 2
def baseEnd_376686 : Nat := 21491219313290938665851

theorem tailTrace_376686 : CollatzResearch.WordTrace tailWord_376686 prefixEnd_376686 21491219313290938665851 := by
  unfold tailWord_376686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717358389167303711513739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9159244742225619794739941 1717358389167303711513739)
  ·
    refine ⟨2576037583750955567270609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717358389167303711513739 2576037583750955567270609)
    ·
      refine ⟨1932028187813216675452957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576037583750955567270609 1932028187813216675452957)
      ·
        refine ⟨724510570429956253294859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1932028187813216675452957 724510570429956253294859)
        ·
          refine ⟨1086765855644934379942289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724510570429956253294859 1086765855644934379942289)
          ·
            refine ⟨815074391733700784956717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086765855644934379942289 815074391733700784956717)
            ·
              refine ⟨305652896900137794358769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815074391733700784956717 305652896900137794358769)
              ·
                refine ⟨229239672675103345769077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305652896900137794358769 229239672675103345769077)
                ·
                  refine ⟨21491219313290938665851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229239672675103345769077 21491219313290938665851)
                  ·
                    rfl

theorem cell23_376686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_376686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376686 prefixEnd_376686 := by exact prefixLift 376686
  have htrace : WordTrace (prefixWord ++ tailWord_376686) baseStart_376686 baseEnd_376686 := by
    simpa [prefixWord, tailWord_376686, baseEnd_376686] using wordTrace_append hprefix tailTrace_376686
  have hstable : (prefixWord ++ tailWord_376686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376686).length < 2 ^ (prefixWord ++ tailWord_376686).sum := by decide
  have hdescent : baseEnd_376686 < baseStart_376686 := by decide
  rcases family_descends (prefixWord ++ tailWord_376686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376752 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3]
def baseStart_376752 : Nat := 118140960795 + 376752 * 2 ^ 59
def prefixEnd_376752 : Nat := 4983230072969 + 3 ^ 40 * 376752 * 2
def baseEnd_376752 : Nat := 193454863542815189767355

theorem tailTrace_376752 : CollatzResearch.WordTrace tailWord_376752 prefixEnd_376752 193454863542815189767355 := by
  unfold tailWord_376752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870637165549661482006255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9160849554066215309341673 6870637165549661482006255)
  ·
    refine ⟨10305955748324492223009383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6870637165549661482006255 10305955748324492223009383)
    ·
      refine ⟨15458933622486738334514075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10305955748324492223009383 15458933622486738334514075)
      ·
        refine ⟨23188400433730107501771113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15458933622486738334514075 23188400433730107501771113)
        ·
          refine ⟨17391300325297580626328335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23188400433730107501771113 17391300325297580626328335)
          ·
            refine ⟨26086950487946370939492503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17391300325297580626328335 26086950487946370939492503)
            ·
              refine ⟨39130425731919556409238755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26086950487946370939492503 39130425731919556409238755)
              ·
                refine ⟨58695638597879334613858133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39130425731919556409238755 58695638597879334613858133)
                ·
                  refine ⟨343919757409449226253075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58695638597879334613858133 343919757409449226253075)
                  ·
                    refine ⟨515879636114173839379613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343919757409449226253075 515879636114173839379613)
                    ·
                      refine ⟨193454863542815189767355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515879636114173839379613 193454863542815189767355)
                      ·
                        rfl

theorem cell23_376752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_376752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376752 prefixEnd_376752 := by exact prefixLift 376752
  have htrace : WordTrace (prefixWord ++ tailWord_376752) baseStart_376752 baseEnd_376752 := by
    simpa [prefixWord, tailWord_376752, baseEnd_376752] using wordTrace_append hprefix tailTrace_376752
  have hstable : (prefixWord ++ tailWord_376752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376752).length < 2 ^ (prefixWord ++ tailWord_376752).sum := by decide
  have hdescent : baseEnd_376752 < baseStart_376752 := by decide
  rcases family_descends (prefixWord ++ tailWord_376752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376755 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 5, 5]
def baseStart_376755 : Nat := 118140960795 + 376755 * 2 ^ 59
def prefixEnd_376755 : Nat := 4983230072969 + 3 ^ 40 * 376755 * 2
def baseEnd_376755 : Nat := 64485467994926226009947

theorem tailTrace_376755 : CollatzResearch.WordTrace tailWord_376755 prefixEnd_376755 64485467994926226009947 := by
  unfold tailWord_376755
  simp only [CollatzResearch.WordTrace]
  refine ⟨13741383750088454476371719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9160922500058969650914479 13741383750088454476371719)
  ·
    refine ⟨20612075625132681714557579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13741383750088454476371719 20612075625132681714557579)
    ·
      refine ⟨30918113437699022571836369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20612075625132681714557579 30918113437699022571836369)
      ·
        refine ⟨23188585078274266928877277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30918113437699022571836369 23188585078274266928877277)
        ·
          refine ⟨8695719404352850098328979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23188585078274266928877277 8695719404352850098328979)
          ·
            refine ⟨13043579106529275147493469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8695719404352850098328979 13043579106529275147493469)
            ·
              refine ⟨4891342164948478180310051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13043579106529275147493469 4891342164948478180310051)
              ·
                refine ⟨7337013247422717270465077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4891342164948478180310051 7337013247422717270465077)
                ·
                  refine ⟨687844991945879744106101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7337013247422717270465077 687844991945879744106101)
                  ·
                    refine ⟨64485467994926226009947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687844991945879744106101 64485467994926226009947)
                    ·
                      rfl

theorem cell23_376755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 5].length) (baseStart_376755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376755 prefixEnd_376755 := by exact prefixLift 376755
  have htrace : WordTrace (prefixWord ++ tailWord_376755) baseStart_376755 baseEnd_376755 := by
    simpa [prefixWord, tailWord_376755, baseEnd_376755] using wordTrace_append hprefix tailTrace_376755
  have hstable : (prefixWord ++ tailWord_376755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376755).length < 2 ^ (prefixWord ++ tailWord_376755).sum := by decide
  have hdescent : baseEnd_376755 < baseStart_376755 := by decide
  rcases family_descends (prefixWord ++ tailWord_376755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376785 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_376785 : Nat := 118140960795 + 376785 * 2 ^ 59
def prefixEnd_376785 : Nat := 4983230072969 + 3 ^ 40 * 376785 * 2
def baseEnd_376785 : Nat := 64490602801471186884901

theorem tailTrace_376785 : CollatzResearch.WordTrace tailWord_376785 prefixEnd_376785 64490602801471186884901 := by
  unfold tailWord_376785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742477939979769599963809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9161651959986513066642539 13742477939979769599963809)
  ·
    refine ⟨10306858454984827199972857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13742477939979769599963809 10306858454984827199972857)
    ·
      refine ⟨7730143841238620399979643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10306858454984827199972857 7730143841238620399979643)
      ·
        refine ⟨11595215761857930599969465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730143841238620399979643 11595215761857930599969465)
        ·
          refine ⟨8696411821393447949977099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11595215761857930599969465 8696411821393447949977099)
          ·
            refine ⟨13044617732090171924965649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696411821393447949977099 13044617732090171924965649)
            ·
              refine ⟨9783463299067628943724237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13044617732090171924965649 9783463299067628943724237)
              ·
                refine ⟨3668798737150360853896589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9783463299067628943724237 3668798737150360853896589)
                ·
                  refine ⟨1375799526431385320211221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3668798737150360853896589 1375799526431385320211221)
                  ·
                    refine ⟨64490602801471186884901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1375799526431385320211221 64490602801471186884901)
                    ·
                      rfl

theorem cell23_376785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_376785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376785 prefixEnd_376785 := by exact prefixLift 376785
  have htrace : WordTrace (prefixWord ++ tailWord_376785) baseStart_376785 baseEnd_376785 := by
    simpa [prefixWord, tailWord_376785, baseEnd_376785] using wordTrace_append hprefix tailTrace_376785
  have hstable : (prefixWord ++ tailWord_376785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376785).length < 2 ^ (prefixWord ++ tailWord_376785).sum := by decide
  have hdescent : baseEnd_376785 < baseStart_376785 := by decide
  rcases family_descends (prefixWord ++ tailWord_376785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376789 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_376789 : Nat := 118140960795 + 376789 * 2 ^ 59
def prefixEnd_376789 : Nat := 4983230072969 + 3 ^ 40 * 376789 * 2
def baseEnd_376789 : Nat := 64491287442343848334895

theorem tailTrace_376789 : CollatzResearch.WordTrace tailWord_376789 prefixEnd_376789 64491287442343848334895 := by
  unfold tailWord_376789
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742623831965278283109421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9161749221310185522072947 13742623831965278283109421)
  ·
    refine ⟨5153483936986979356166033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13742623831965278283109421 5153483936986979356166033)
    ·
      refine ⟨3865112952740234517124525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5153483936986979356166033 3865112952740234517124525)
      ·
        refine ⟨1449417357277587943921697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3865112952740234517124525 1449417357277587943921697)
        ·
          refine ⟨1087063017958190957941273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449417357277587943921697 1087063017958190957941273)
          ·
            refine ⟨815297263468643218455955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087063017958190957941273 815297263468643218455955)
            ·
              refine ⟨1222945895202964827683933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815297263468643218455955 1222945895202964827683933)
              ·
                refine ⟨458604710701111810381475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1222945895202964827683933 458604710701111810381475)
                ·
                  refine ⟨687907066051667715572213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458604710701111810381475 687907066051667715572213)
                  ·
                    refine ⟨64491287442343848334895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 687907066051667715572213 64491287442343848334895)
                    ·
                      rfl

theorem cell23_376789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_376789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376789 prefixEnd_376789 := by exact prefixLift 376789
  have htrace : WordTrace (prefixWord ++ tailWord_376789) baseStart_376789 baseEnd_376789 := by
    simpa [prefixWord, tailWord_376789, baseEnd_376789] using wordTrace_append hprefix tailTrace_376789
  have hstable : (prefixWord ++ tailWord_376789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376789).length < 2 ^ (prefixWord ++ tailWord_376789).sum := by decide
  have hdescent : baseEnd_376789 < baseStart_376789 := by decide
  rcases family_descends (prefixWord ++ tailWord_376789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376812 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_376812 : Nat := 118140960795 + 376812 * 2 ^ 59
def prefixEnd_376812 : Nat := 4983230072969 + 3 ^ 40 * 376812 * 2
def baseEnd_376812 : Nat := 193485672382084955017079

theorem tailTrace_376812 : CollatzResearch.WordTrace tailWord_376812 prefixEnd_376812 193485672382084955017079 := by
  unfold tailWord_376812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871731355440976605598345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9162308473921302140797793 6871731355440976605598345)
  ·
    refine ⟨5153798516580732454198759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6871731355440976605598345 5153798516580732454198759)
    ·
      refine ⟨7730697774871098681298139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153798516580732454198759 7730697774871098681298139)
      ·
        refine ⟨11596046662306648021947209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730697774871098681298139 11596046662306648021947209)
        ·
          refine ⟨8697034996729986016460407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11596046662306648021947209 8697034996729986016460407)
          ·
            refine ⟨13045552495094979024690611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697034996729986016460407 13045552495094979024690611)
            ·
              refine ⟨19568328742642468537035917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13045552495094979024690611 19568328742642468537035917)
              ·
                refine ⟨7338123278490925701388469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19568328742642468537035917 7338123278490925701388469)
                ·
                  refine ⟨687949057358524284505169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7338123278490925701388469 687949057358524284505169)
                  ·
                    refine ⟨515961793018893213378877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 687949057358524284505169 515961793018893213378877)
                    ·
                      refine ⟨193485672382084955017079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515961793018893213378877 193485672382084955017079)
                      ·
                        rfl

theorem cell23_376812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_376812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376812 prefixEnd_376812 := by exact prefixLift 376812
  have htrace : WordTrace (prefixWord ++ tailWord_376812) baseStart_376812 baseEnd_376812 := by
    simpa [prefixWord, tailWord_376812, baseEnd_376812] using wordTrace_append hprefix tailTrace_376812
  have hstable : (prefixWord ++ tailWord_376812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376812).length < 2 ^ (prefixWord ++ tailWord_376812).sum := by decide
  have hdescent : baseEnd_376812 < baseStart_376812 := by decide
  rcases family_descends (prefixWord ++ tailWord_376812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376815 : List Nat := [1, 1, 2, 1, 4, 2, 2, 10]
def baseStart_376815 : Nat := 118140960795 + 376815 * 2 ^ 59
def prefixEnd_376815 : Nat := 4983230072969 + 3 ^ 40 * 376815 * 2
def baseEnd_376815 : Nat := 7166193067557349751095

theorem tailTrace_376815 : CollatzResearch.WordTrace tailWord_376815 prefixEnd_376815 7166193067557349751095 := by
  unfold tailWord_376815
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743572129871084723555899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162381419914056482370599 13743572129871084723555899)
  ·
    refine ⟨20615358194806627085333849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13743572129871084723555899 20615358194806627085333849)
    ·
      refine ⟨15461518646104970314000387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20615358194806627085333849 15461518646104970314000387)
      ·
        refine ⟨23192277969157455471000581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461518646104970314000387 23192277969157455471000581)
        ·
          refine ⟨4348552119217022900812609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23192277969157455471000581 4348552119217022900812609)
          ·
            refine ⟨3261414089412767175609457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348552119217022900812609 3261414089412767175609457)
            ·
              refine ⟨2446060567059575381707093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261414089412767175609457 2446060567059575381707093)
              ·
                refine ⟨7166193067557349751095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2446060567059575381707093 7166193067557349751095)
                ·
                  rfl

theorem cell23_376815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 10].length) (baseStart_376815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376815 prefixEnd_376815 := by exact prefixLift 376815
  have htrace : WordTrace (prefixWord ++ tailWord_376815) baseStart_376815 baseEnd_376815 := by
    simpa [prefixWord, tailWord_376815, baseEnd_376815] using wordTrace_append hprefix tailTrace_376815
  have hstable : (prefixWord ++ tailWord_376815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376815).length < 2 ^ (prefixWord ++ tailWord_376815).sum := by decide
  have hdescent : baseEnd_376815 < baseStart_376815 := by decide
  rcases family_descends (prefixWord ++ tailWord_376815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376829 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_376829 : Nat := 118140960795 + 376829 * 2 ^ 59
def prefixEnd_376829 : Nat := 4983230072969 + 3 ^ 40 * 376829 * 2
def baseEnd_376829 : Nat := 193494401553211388504501

theorem tailTrace_376829 : CollatzResearch.WordTrace tailWord_376829 prefixEnd_376829 193494401553211388504501 := by
  unfold tailWord_376829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744082751820365114565541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162721834546910076377027 13744082751820365114565541)
  ·
    refine ⟨2577015515966318458981039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13744082751820365114565541 2577015515966318458981039)
    ·
      refine ⟨3865523273949477688471559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577015515966318458981039 3865523273949477688471559)
      ·
        refine ⟨5798284910924216532707339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865523273949477688471559 5798284910924216532707339)
        ·
          refine ⟨8697427366386324799061009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798284910924216532707339 8697427366386324799061009)
          ·
            refine ⟨6523070524789743599295757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8697427366386324799061009 6523070524789743599295757)
            ·
              refine ⟨2446151446796153849735909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6523070524789743599295757 2446151446796153849735909)
              ·
                refine ⟨458653396274278846825483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2446151446796153849735909 458653396274278846825483)
                ·
                  refine ⟨687980094411418270238225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458653396274278846825483 687980094411418270238225)
                  ·
                    refine ⟨515985070808563702678669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 687980094411418270238225 515985070808563702678669)
                    ·
                      refine ⟨193494401553211388504501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 515985070808563702678669 193494401553211388504501)
                      ·
                        rfl

theorem cell23_376829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_376829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376829 prefixEnd_376829 := by exact prefixLift 376829
  have htrace : WordTrace (prefixWord ++ tailWord_376829) baseStart_376829 baseEnd_376829 := by
    simpa [prefixWord, tailWord_376829, baseEnd_376829] using wordTrace_append hprefix tailTrace_376829
  have hstable : (prefixWord ++ tailWord_376829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376829).length < 2 ^ (prefixWord ++ tailWord_376829).sum := by decide
  have hdescent : baseEnd_376829 < baseStart_376829 := by decide
  rcases family_descends (prefixWord ++ tailWord_376829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376835 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_376835 : Nat := 118140960795 + 376835 * 2 ^ 59
def prefixEnd_376835 : Nat := 4983230072969 + 3 ^ 40 * 376835 * 2
def baseEnd_376835 : Nat := 193497482437138365029473

theorem tailTrace_376835 : CollatzResearch.WordTrace tailWord_376835 prefixEnd_376835 193497482437138365029473 := by
  unfold tailWord_376835
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744301589798628139283959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162867726532418759522639 13744301589798628139283959)
  ·
    refine ⟨20616452384697942208925939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13744301589798628139283959 20616452384697942208925939)
    ·
      refine ⟨30924678577046913313388909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20616452384697942208925939 30924678577046913313388909)
      ·
        refine ⟨11596754466392592492520841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30924678577046913313388909 11596754466392592492520841)
        ·
          refine ⟨8697565849794444369390631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11596754466392592492520841 8697565849794444369390631)
          ·
            refine ⟨13046348774691666554085947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8697565849794444369390631 13046348774691666554085947)
            ·
              refine ⟨19569523162037499831128921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13046348774691666554085947 19569523162037499831128921)
              ·
                refine ⟨14677142371528124873346691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19569523162037499831128921 14677142371528124873346691)
                ·
                  refine ⟨22015713557292187310020037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14677142371528124873346691 22015713557292187310020037)
                  ·
                    refine ⟨4127946291992285120628757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22015713557292187310020037 4127946291992285120628757)
                    ·
                      refine ⟨193497482437138365029473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4127946291992285120628757 193497482437138365029473)
                      ·
                        rfl

theorem cell23_376835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_376835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376835 prefixEnd_376835 := by exact prefixLift 376835
  have htrace : WordTrace (prefixWord ++ tailWord_376835) baseStart_376835 baseEnd_376835 := by
    simpa [prefixWord, tailWord_376835, baseEnd_376835] using wordTrace_append hprefix tailTrace_376835
  have hstable : (prefixWord ++ tailWord_376835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376835).length < 2 ^ (prefixWord ++ tailWord_376835).sum := by decide
  have hdescent : baseEnd_376835 < baseStart_376835 := by decide
  rcases family_descends (prefixWord ++ tailWord_376835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376903 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_376903 : Nat := 118140960795 + 376903 * 2 ^ 59
def prefixEnd_376903 : Nat := 4983230072969 + 3 ^ 40 * 376903 * 2
def baseEnd_376903 : Nat := 193532399121644098979161

theorem tailTrace_376903 : CollatzResearch.WordTrace tailWord_376903 prefixEnd_376903 193532399121644098979161 := by
  unfold tailWord_376903
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746781753552275752759363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9164521169034850501839575 13746781753552275752759363)
  ·
    refine ⟨20620172630328413629139045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13746781753552275752759363 20620172630328413629139045)
    ·
      refine ⟨3866282368186577555463571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20620172630328413629139045 3866282368186577555463571)
      ·
        refine ⟨5799423552279866333195357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866282368186577555463571 5799423552279866333195357)
        ·
          refine ⟨2174783832104949874948259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5799423552279866333195357 2174783832104949874948259)
          ·
            refine ⟨3262175748157424812422389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174783832104949874948259 3262175748157424812422389)
            ·
              refine ⟨305828976389758576164599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3262175748157424812422389 305828976389758576164599)
              ·
                refine ⟨458743464584637864246899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305828976389758576164599 458743464584637864246899)
                ·
                  refine ⟨688115196876956796370349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458743464584637864246899 688115196876956796370349)
                  ·
                    refine ⟨258043198828858798638881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688115196876956796370349 258043198828858798638881)
                    ·
                      refine ⟨193532399121644098979161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258043198828858798638881 193532399121644098979161)
                      ·
                        rfl

theorem cell23_376903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_376903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376903 prefixEnd_376903 := by exact prefixLift 376903
  have htrace : WordTrace (prefixWord ++ tailWord_376903) baseStart_376903 baseEnd_376903 := by
    simpa [prefixWord, tailWord_376903, baseEnd_376903] using wordTrace_append hprefix tailTrace_376903
  have hstable : (prefixWord ++ tailWord_376903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376903).length < 2 ^ (prefixWord ++ tailWord_376903).sum := by decide
  have hdescent : baseEnd_376903 < baseStart_376903 := by decide
  rcases family_descends (prefixWord ++ tailWord_376903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376909 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_376909 : Nat := 118140960795 + 376909 * 2 ^ 59
def prefixEnd_376909 : Nat := 4983230072969 + 3 ^ 40 * 376909 * 2
def baseEnd_376909 : Nat := 64511826668523691834711

theorem tailTrace_376909 : CollatzResearch.WordTrace tailWord_376909 prefixEnd_376909 64511826668523691834711 := by
  unfold tailWord_376909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747000591530538777477781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9164667061020359184985187 13747000591530538777477781)
  ·
    refine ⟨644390652727994005194271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13747000591530538777477781 644390652727994005194271)
    ·
      refine ⟨966585979091991007791407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644390652727994005194271 966585979091991007791407)
      ·
        refine ⟨1449878968637986511687111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966585979091991007791407 1449878968637986511687111)
        ·
          refine ⟨2174818452956979767530667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449878968637986511687111 2174818452956979767530667)
          ·
            refine ⟨3262227679435469651296001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174818452956979767530667 3262227679435469651296001)
            ·
              refine ⟨2446670759576602238472001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262227679435469651296001 2446670759576602238472001)
              ·
                refine ⟨1835003069682451678854001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446670759576602238472001 1835003069682451678854001)
                ·
                  refine ⟨1376252302261838759140501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835003069682451678854001 1376252302261838759140501)
                  ·
                    refine ⟨64511826668523691834711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1376252302261838759140501 64511826668523691834711)
                    ·
                      rfl

theorem cell23_376909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_376909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376909 prefixEnd_376909 := by exact prefixLift 376909
  have htrace : WordTrace (prefixWord ++ tailWord_376909) baseStart_376909 baseEnd_376909 := by
    simpa [prefixWord, tailWord_376909, baseEnd_376909] using wordTrace_append hprefix tailTrace_376909
  have hstable : (prefixWord ++ tailWord_376909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376909).length < 2 ^ (prefixWord ++ tailWord_376909).sum := by decide
  have hdescent : baseEnd_376909 < baseStart_376909 := by decide
  rcases family_descends (prefixWord ++ tailWord_376909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376922 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_376922 : Nat := 118140960795 + 376922 * 2 ^ 59
def prefixEnd_376922 : Nat := 4983230072969 + 3 ^ 40 * 376922 * 2
def baseEnd_376922 : Nat := 21504683917119947182397

theorem tailTrace_376922 : CollatzResearch.WordTrace tailWord_376922 prefixEnd_376922 21504683917119947182397 := by
  unfold tailWord_376922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436868685120860499425255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9164983160322294665134013 3436868685120860499425255)
  ·
    refine ⟨5155303027681290749137883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3436868685120860499425255 5155303027681290749137883)
    ·
      refine ⟨7732954541521936123706825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155303027681290749137883 7732954541521936123706825)
      ·
        refine ⟨5799715906141452092780119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7732954541521936123706825 5799715906141452092780119)
        ·
          refine ⟨8699573859212178139170179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799715906141452092780119 8699573859212178139170179)
          ·
            refine ⟨13049360788818267208755269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699573859212178139170179 13049360788818267208755269)
            ·
              refine ⟨2446755147903425101641613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13049360788818267208755269 2446755147903425101641613)
              ·
                refine ⟨917533180463784413115605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2446755147903425101641613 917533180463784413115605)
                ·
                  refine ⟨21504683917119947182397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 917533180463784413115605 21504683917119947182397)
                  ·
                    rfl

theorem cell23_376922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_376922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376922 prefixEnd_376922 := by exact prefixLift 376922
  have htrace : WordTrace (prefixWord ++ tailWord_376922) baseStart_376922 baseEnd_376922 := by
    simpa [prefixWord, tailWord_376922, baseEnd_376922] using wordTrace_append hprefix tailTrace_376922
  have hstable : (prefixWord ++ tailWord_376922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376922).length < 2 ^ (prefixWord ++ tailWord_376922).sum := by decide
  have hdescent : baseEnd_376922 < baseStart_376922 := by decide
  rcases family_descends (prefixWord ++ tailWord_376922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376933 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_376933 : Nat := 118140960795 + 376933 * 2 ^ 59
def prefixEnd_376933 : Nat := 4983230072969 + 3 ^ 40 * 376933 * 2
def baseEnd_376933 : Nat := 193547803541278981604023

theorem tailTrace_376933 : CollatzResearch.WordTrace tailWord_376933 prefixEnd_376933 193547803541278981604023 := by
  unfold tailWord_376933
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747875943443590876351453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9165250628962393917567635 13747875943443590876351453)
  ·
    refine ⟨5155453478791346578631795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13747875943443590876351453 5155453478791346578631795)
    ·
      refine ⟨7733180218187019867947693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155453478791346578631795 7733180218187019867947693)
      ·
        refine ⟨2899942581820132450480385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7733180218187019867947693 2899942581820132450480385)
        ·
          refine ⟨2174956936365099337860289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899942581820132450480385 2174956936365099337860289)
          ·
            refine ⟨1631217702273824503395217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174956936365099337860289 1631217702273824503395217)
            ·
              refine ⟨1223413276705368377546413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631217702273824503395217 1223413276705368377546413)
              ·
                refine ⟨458779978764513141579905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223413276705368377546413 458779978764513141579905)
                ·
                  refine ⟨344084984073384856184929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 458779978764513141579905 344084984073384856184929)
                  ·
                    refine ⟨258063738055038642138697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344084984073384856184929 258063738055038642138697)
                    ·
                      refine ⟨193547803541278981604023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258063738055038642138697 193547803541278981604023)
                      ·
                        rfl

theorem cell23_376933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_376933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376933 prefixEnd_376933 := by exact prefixLift 376933
  have htrace : WordTrace (prefixWord ++ tailWord_376933) baseStart_376933 baseEnd_376933 := by
    simpa [prefixWord, tailWord_376933, baseEnd_376933] using wordTrace_append hprefix tailTrace_376933
  have hstable : (prefixWord ++ tailWord_376933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376933).length < 2 ^ (prefixWord ++ tailWord_376933).sum := by decide
  have hdescent : baseEnd_376933 < baseStart_376933 := by decide
  rcases family_descends (prefixWord ++ tailWord_376933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376956 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 5]
def baseStart_376956 : Nat := 118140960795 + 376956 * 2 ^ 59
def prefixEnd_376956 : Nat := 4983230072969 + 3 ^ 40 * 376956 * 2
def baseEnd_376956 : Nat := 21506623732925821290713

theorem tailTrace_376956 : CollatzResearch.WordTrace tailWord_376956 prefixEnd_376956 21506623732925821290713 := by
  unfold tailWord_376956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874357411180132902219361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9165809881573510536292481 6874357411180132902219361)
  ·
    refine ⟨5155768058385099676664521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6874357411180132902219361 5155768058385099676664521)
    ·
      refine ⟨3866826043788824757498391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5155768058385099676664521 3866826043788824757498391)
      ·
        refine ⟨5800239065683237136247587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866826043788824757498391 5800239065683237136247587)
        ·
          refine ⟨8700358598524855704371381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800239065683237136247587 8700358598524855704371381)
          ·
            refine ⟨815658618611705222284817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8700358598524855704371381 815658618611705222284817)
            ·
              refine ⟨611743963958778916713613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815658618611705222284817 611743963958778916713613)
              ·
                refine ⟨229403986484542093767605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611743963958778916713613 229403986484542093767605)
                ·
                  refine ⟨21506623732925821290713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229403986484542093767605 21506623732925821290713)
                  ·
                    rfl

theorem cell23_376956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_376956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376956 prefixEnd_376956 := by exact prefixLift 376956
  have htrace : WordTrace (prefixWord ++ tailWord_376956) baseStart_376956 baseEnd_376956 := by
    simpa [prefixWord, tailWord_376956, baseEnd_376956] using wordTrace_append hprefix tailTrace_376956
  have hstable : (prefixWord ++ tailWord_376956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376956).length < 2 ^ (prefixWord ++ tailWord_376956).sum := by decide
  have hdescent : baseEnd_376956 < baseStart_376956 := by decide
  rcases family_descends (prefixWord ++ tailWord_376956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376989 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_376989 : Nat := 118140960795 + 376989 * 2 ^ 59
def prefixEnd_376989 : Nat := 4983230072969 + 3 ^ 40 * 376989 * 2
def baseEnd_376989 : Nat := 193576558457930762503765

theorem tailTrace_376989 : CollatzResearch.WordTrace tailWord_376989 prefixEnd_376989 193576558457930762503765 := by
  unfold tailWord_376989
  simp only [CollatzResearch.WordTrace]
  refine ⟨13749918431240712440390021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9166612287493808293593347 13749918431240712440390021)
  ·
    refine ⟨2578109705857633582573129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13749918431240712440390021 2578109705857633582573129)
    ·
      refine ⟨1933582279393225186929847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2578109705857633582573129 1933582279393225186929847)
      ·
        refine ⟨2900373419089837780394771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933582279393225186929847 2900373419089837780394771)
        ·
          refine ⟨4350560128634756670592157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900373419089837780394771 4350560128634756670592157)
          ·
            refine ⟨1631460048238033751472059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4350560128634756670592157 1631460048238033751472059)
            ·
              refine ⟨2447190072357050627208089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631460048238033751472059 2447190072357050627208089)
              ·
                refine ⟨1835392554267787970406067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447190072357050627208089 1835392554267787970406067)
                ·
                  refine ⟨2753088831401681955609101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835392554267787970406067 2753088831401681955609101)
                  ·
                    refine ⟨1032408311775630733353413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753088831401681955609101 1032408311775630733353413)
                    ·
                      refine ⟨193576558457930762503765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1032408311775630733353413 193576558457930762503765)
                      ·
                        rfl

theorem cell23_376989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_376989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_376989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_376989 prefixEnd_376989 := by exact prefixLift 376989
  have htrace : WordTrace (prefixWord ++ tailWord_376989) baseStart_376989 baseEnd_376989 := by
    simpa [prefixWord, tailWord_376989, baseEnd_376989] using wordTrace_append hprefix tailTrace_376989
  have hstable : (prefixWord ++ tailWord_376989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376989).length < 2 ^ (prefixWord ++ tailWord_376989).sum := by decide
  have hdescent : baseEnd_376989 < baseStart_376989 := by decide
  rcases family_descends (prefixWord ++ tailWord_376989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377056 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3]
def baseStart_377056 : Nat := 118140960795 + 377056 * 2 ^ 59
def prefixEnd_377056 : Nat := 4983230072969 + 3 ^ 40 * 377056 * 2
def baseEnd_377056 : Nat := 193610961661782000365957

theorem tailTrace_377056 : CollatzResearch.WordTrace tailWord_377056 prefixEnd_377056 193610961661782000365957 := by
  unfold tailWord_377056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876181060998991441539511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9168241414665321922052681 6876181060998991441539511)
  ·
    refine ⟨10314271591498487162309267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6876181060998991441539511 10314271591498487162309267)
    ·
      refine ⟨15471407387247730743463901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10314271591498487162309267 15471407387247730743463901)
      ·
        refine ⟨5801777770217899028798963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15471407387247730743463901 5801777770217899028798963)
        ·
          refine ⟨8702666655326848543198445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5801777770217899028798963 8702666655326848543198445)
          ·
            refine ⟨3263499995747568203699417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8702666655326848543198445 3263499995747568203699417)
            ·
              refine ⟨2447624996810676152774563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263499995747568203699417 2447624996810676152774563)
              ·
                refine ⟨3671437495216014229161845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447624996810676152774563 3671437495216014229161845)
                ·
                  refine ⟨344197265176501333983923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3671437495216014229161845 344197265176501333983923)
                  ·
                    refine ⟨516295897764752000975885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 344197265176501333983923 516295897764752000975885)
                    ·
                      refine ⟨193610961661782000365957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 516295897764752000975885 193610961661782000365957)
                      ·
                        rfl

theorem cell23_377056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_377056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377056 prefixEnd_377056 := by exact prefixLift 377056
  have htrace : WordTrace (prefixWord ++ tailWord_377056) baseStart_377056 baseEnd_377056 := by
    simpa [prefixWord, tailWord_377056, baseEnd_377056] using wordTrace_append hprefix tailTrace_377056
  have hstable : (prefixWord ++ tailWord_377056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377056).length < 2 ^ (prefixWord ++ tailWord_377056).sum := by decide
  have hdescent : baseEnd_377056 < baseStart_377056 := by decide
  rcases family_descends (prefixWord ++ tailWord_377056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377079 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_377079 : Nat := 118140960795 + 377079 * 2 ^ 59
def prefixEnd_377079 : Nat := 4983230072969 + 3 ^ 40 * 377079 * 2
def baseEnd_377079 : Nat := 193622771716835410378351

theorem tailTrace_377079 : CollatzResearch.WordTrace tailWord_377079 prefixEnd_377079 193622771716835410378351 := by
  unfold tailWord_377079
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753201000914657811166291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9168800667276438540777527 13753201000914657811166291)
  ·
    refine ⟨20629801501371986716749437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753201000914657811166291 20629801501371986716749437)
    ·
      refine ⟨7736175563014495018781039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20629801501371986716749437 7736175563014495018781039)
      ·
        refine ⟨11604263344521742528171559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736175563014495018781039 11604263344521742528171559)
        ·
          refine ⟨17406395016782613792257339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11604263344521742528171559 17406395016782613792257339)
          ·
            refine ⟨26109592525173920688386009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17406395016782613792257339 26109592525173920688386009)
            ·
              refine ⟨19582194393880440516289507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26109592525173920688386009 19582194393880440516289507)
              ·
                refine ⟨29373291590820660774434261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19582194393880440516289507 29373291590820660774434261)
                ·
                  refine ⟨688436521659859236900803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29373291590820660774434261 688436521659859236900803)
                  ·
                    refine ⟨1032654782489788855351205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688436521659859236900803 1032654782489788855351205)
                    ·
                      refine ⟨193622771716835410378351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1032654782489788855351205 193622771716835410378351)
                      ·
                        rfl

theorem cell23_377079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_377079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377079 prefixEnd_377079 := by exact prefixLift 377079
  have htrace : WordTrace (prefixWord ++ tailWord_377079) baseStart_377079 baseEnd_377079 := by
    simpa [prefixWord, tailWord_377079, baseEnd_377079] using wordTrace_append hprefix tailTrace_377079
  have hstable : (prefixWord ++ tailWord_377079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377079).length < 2 ^ (prefixWord ++ tailWord_377079).sum := by decide
  have hdescent : baseEnd_377079 < baseStart_377079 := by decide
  rcases family_descends (prefixWord ++ tailWord_377079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377089 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_377089 : Nat := 118140960795 + 377089 * 2 ^ 59
def prefixEnd_377089 : Nat := 4983230072969 + 3 ^ 40 * 377089 * 2
def baseEnd_377089 : Nat := 64542635507793457084435

theorem tailTrace_377089 : CollatzResearch.WordTrace tailWord_377089 prefixEnd_377089 64542635507793457084435 := by
  unfold tailWord_377089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753565730878429519030321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169043820585619679353547 13753565730878429519030321)
  ·
    refine ⟨10315174298158822139272741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13753565730878429519030321 10315174298158822139272741)
    ·
      refine ⟨1934095180904779151113639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10315174298158822139272741 1934095180904779151113639)
      ·
        refine ⟨2901142771357168726670459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934095180904779151113639 2901142771357168726670459)
        ·
          refine ⟨4351714157035753090005689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901142771357168726670459 4351714157035753090005689)
          ·
            refine ⟨3263785617776814817504267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351714157035753090005689 3263785617776814817504267)
            ·
              refine ⟨4895678426665222226256401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263785617776814817504267 4895678426665222226256401)
              ·
                refine ⟨3671758819998916669692301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895678426665222226256401 3671758819998916669692301)
                ·
                  refine ⟨1376909557499593751134613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3671758819998916669692301 1376909557499593751134613)
                  ·
                    refine ⟨64542635507793457084435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1376909557499593751134613 64542635507793457084435)
                    ·
                      rfl

theorem cell23_377089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_377089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377089 prefixEnd_377089 := by exact prefixLift 377089
  have htrace : WordTrace (prefixWord ++ tailWord_377089) baseStart_377089 baseEnd_377089 := by
    simpa [prefixWord, tailWord_377089, baseEnd_377089] using wordTrace_append hprefix tailTrace_377089
  have hstable : (prefixWord ++ tailWord_377089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377089).length < 2 ^ (prefixWord ++ tailWord_377089).sum := by decide
  have hdescent : baseEnd_377089 < baseStart_377089 := by decide
  rcases family_descends (prefixWord ++ tailWord_377089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377096 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_377096 : Nat := 118140960795 + 377096 * 2 ^ 59
def prefixEnd_377096 : Nat := 4983230072969 + 3 ^ 40 * 377096 * 2
def baseEnd_377096 : Nat := 193631500887961843865773

theorem tailTrace_377096 : CollatzResearch.WordTrace tailWord_377096 prefixEnd_377096 193631500887961843865773 := by
  unfold tailWord_377096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876910520926534857267571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9169214027902046476356761 6876910520926534857267571)
  ·
    refine ⟨10315365781389802285901357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6876910520926534857267571 10315365781389802285901357)
    ·
      refine ⟨3868262168021175857213009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10315365781389802285901357 3868262168021175857213009)
      ·
        refine ⟨2901196626015881892909757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3868262168021175857213009 2901196626015881892909757)
        ·
          refine ⟨1087948734755955709841159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2901196626015881892909757 1087948734755955709841159)
          ·
            refine ⟨1631923102133933564761739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087948734755955709841159 1631923102133933564761739)
            ·
              refine ⟨2447884653200900347142609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631923102133933564761739 2447884653200900347142609)
              ·
                refine ⟨1835913489900675260356957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447884653200900347142609 1835913489900675260356957)
                ·
                  refine ⟨688467558712753222633859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1835913489900675260356957 688467558712753222633859)
                  ·
                    refine ⟨1032701338069129833950789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688467558712753222633859 1032701338069129833950789)
                    ·
                      refine ⟨193631500887961843865773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1032701338069129833950789 193631500887961843865773)
                      ·
                        rfl

theorem cell23_377096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_377096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377096 prefixEnd_377096 := by exact prefixLift 377096
  have htrace : WordTrace (prefixWord ++ tailWord_377096) baseStart_377096 baseEnd_377096 := by
    simpa [prefixWord, tailWord_377096, baseEnd_377096] using wordTrace_append hprefix tailTrace_377096
  have hstable : (prefixWord ++ tailWord_377096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377096).length < 2 ^ (prefixWord ++ tailWord_377096).sum := by decide
  have hdescent : baseEnd_377096 < baseStart_377096 := by decide
  rcases family_descends (prefixWord ++ tailWord_377096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377099 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_377099 : Nat := 118140960795 + 377099 * 2 ^ 59
def prefixEnd_377099 : Nat := 4983230072969 + 3 ^ 40 * 377099 * 2
def baseEnd_377099 : Nat := 193633041329925332128259

theorem tailTrace_377099 : CollatzResearch.WordTrace tailWord_377099 prefixEnd_377099 193633041329925332128259 := by
  unfold tailWord_377099
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753930460842201226894351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169286973894800817929567 13753930460842201226894351)
  ·
    refine ⟨20630895691263301840341527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13753930460842201226894351 20630895691263301840341527)
    ·
      refine ⟨30946343536894952760512291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630895691263301840341527 30946343536894952760512291)
      ·
        refine ⟨46419515305342429140768437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30946343536894952760512291 46419515305342429140768437)
        ·
          refine ⟨4351829559875852731947041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46419515305342429140768437 4351829559875852731947041)
          ·
            refine ⟨3263872169906889548960281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351829559875852731947041 3263872169906889548960281)
            ·
              refine ⟨2447904127430167161720211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263872169906889548960281 2447904127430167161720211)
              ·
                refine ⟨3671856191145250742580317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447904127430167161720211 3671856191145250742580317)
                ·
                  refine ⟨1376946071679469028467619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3671856191145250742580317 1376946071679469028467619)
                  ·
                    refine ⟨2065419107519203542701429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376946071679469028467619 2065419107519203542701429)
                    ·
                      refine ⟨193633041329925332128259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2065419107519203542701429 193633041329925332128259)
                      ·
                        rfl

theorem cell23_377099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_377099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377099 prefixEnd_377099 := by exact prefixLift 377099
  have htrace : WordTrace (prefixWord ++ tailWord_377099) baseStart_377099 baseEnd_377099 := by
    simpa [prefixWord, tailWord_377099, baseEnd_377099] using wordTrace_append hprefix tailTrace_377099
  have hstable : (prefixWord ++ tailWord_377099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377099).length < 2 ^ (prefixWord ++ tailWord_377099).sum := by decide
  have hdescent : baseEnd_377099 < baseStart_377099 := by decide
  rcases family_descends (prefixWord ++ tailWord_377099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377109 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_377109 : Nat := 118140960795 + 377109 * 2 ^ 59
def prefixEnd_377109 : Nat := 4983230072969 + 3 ^ 40 * 377109 * 2
def baseEnd_377109 : Nat := 193638176136470293003213

theorem tailTrace_377109 : CollatzResearch.WordTrace tailWord_377109 prefixEnd_377109 193638176136470293003213 := by
  unfold tailWord_377109
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754295190805972934758381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169530127203981956505587 13754295190805972934758381)
  ·
    refine ⟨5157860696552239850534393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13754295190805972934758381 5157860696552239850534393)
    ·
      refine ⟨3868395522414179887900795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5157860696552239850534393 3868395522414179887900795)
      ·
        refine ⟨5802593283621269831851193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868395522414179887900795 5802593283621269831851193)
        ·
          refine ⟨4351944962715952373888395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802593283621269831851193 4351944962715952373888395)
          ·
            refine ⟨6527917444073928560832593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351944962715952373888395 6527917444073928560832593)
            ·
              refine ⟨4895938083055446420624445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6527917444073928560832593 4895938083055446420624445)
              ·
                refine ⟨1835976781145792407734167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4895938083055446420624445 1835976781145792407734167)
                ·
                  refine ⟨2753965171718688611601251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835976781145792407734167 2753965171718688611601251)
                  ·
                    refine ⟨4130947757578032917401877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753965171718688611601251 4130947757578032917401877)
                    ·
                      refine ⟨193638176136470293003213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4130947757578032917401877 193638176136470293003213)
                      ·
                        rfl

theorem cell23_377109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_377109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377109 prefixEnd_377109 := by exact prefixLift 377109
  have htrace : WordTrace (prefixWord ++ tailWord_377109) baseStart_377109 baseEnd_377109 := by
    simpa [prefixWord, tailWord_377109, baseEnd_377109] using wordTrace_append hprefix tailTrace_377109
  have hstable : (prefixWord ++ tailWord_377109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377109).length < 2 ^ (prefixWord ++ tailWord_377109).sum := by decide
  have hdescent : baseEnd_377109 < baseStart_377109 := by decide
  rcases family_descends (prefixWord ++ tailWord_377109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377117 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_377117 : Nat := 118140960795 + 377117 * 2 ^ 59
def prefixEnd_377117 : Nat := 4983230072969 + 3 ^ 40 * 377117 * 2
def baseEnd_377117 : Nat := 193642283981706261703177

theorem tailTrace_377117 : CollatzResearch.WordTrace tailWord_377117 prefixEnd_377117 193642283981706261703177 := by
  unfold tailWord_377117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754586974776990301049605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169724649851326867366403 13754586974776990301049605)
  ·
    refine ⟨2578985057770685681446801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13754586974776990301049605 2578985057770685681446801)
    ·
      refine ⟨1934238793328014261085101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2578985057770685681446801 1934238793328014261085101)
      ·
        refine ⟨725339547498005347906913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1934238793328014261085101 725339547498005347906913)
        ·
          refine ⟨544004660623504010930185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725339547498005347906913 544004660623504010930185)
          ·
            refine ⟨408003495467628008197639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544004660623504010930185 408003495467628008197639)
            ·
              refine ⟨612005243201442012296459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408003495467628008197639 612005243201442012296459)
              ·
                refine ⟨918007864802163018444689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612005243201442012296459 918007864802163018444689)
                ·
                  refine ⟨688505898601622263833517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918007864802163018444689 688505898601622263833517)
                  ·
                    refine ⟨258189711975608348937569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688505898601622263833517 258189711975608348937569)
                    ·
                      refine ⟨193642283981706261703177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258189711975608348937569 193642283981706261703177)
                      ·
                        rfl

theorem cell23_377117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_377117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377117 prefixEnd_377117 := by exact prefixLift 377117
  have htrace : WordTrace (prefixWord ++ tailWord_377117) baseStart_377117 baseEnd_377117 := by
    simpa [prefixWord, tailWord_377117, baseEnd_377117] using wordTrace_append hprefix tailTrace_377117
  have hstable : (prefixWord ++ tailWord_377117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377117).length < 2 ^ (prefixWord ++ tailWord_377117).sum := by decide
  have hdescent : baseEnd_377117 < baseStart_377117 := by decide
  rcases family_descends (prefixWord ++ tailWord_377117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377127 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 1, 5]
def baseStart_377127 : Nat := 118140960795 + 377127 * 2 ^ 59
def prefixEnd_377127 : Nat := 4983230072969 + 3 ^ 40 * 377127 * 2
def baseEnd_377127 : Nat := 64549139596083740859377

theorem tailTrace_377127 : CollatzResearch.WordTrace tailWord_377127 prefixEnd_377127 64549139596083740859377 := by
  unfold tailWord_377127
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754951704740762008913635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169967803160508005942423 13754951704740762008913635)
  ·
    refine ⟨20632427557111143013370453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13754951704740762008913635 20632427557111143013370453)
    ·
      refine ⟨241786260434896207187935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 20632427557111143013370453 241786260434896207187935)
      ·
        refine ⟨362679390652344310781903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241786260434896207187935 362679390652344310781903)
        ·
          refine ⟨544019085978516466172855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362679390652344310781903 544019085978516466172855)
          ·
            refine ⟨816028628967774699259283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544019085978516466172855 816028628967774699259283)
            ·
              refine ⟨1224042943451662048888925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816028628967774699259283 1224042943451662048888925)
              ·
                refine ⟨459016103794373268333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224042943451662048888925 459016103794373268333347)
                ·
                  refine ⟨688524155691559902500021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459016103794373268333347 688524155691559902500021)
                  ·
                    refine ⟨64549139596083740859377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 688524155691559902500021 64549139596083740859377)
                    ·
                      rfl

theorem cell23_377127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_377127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377127 prefixEnd_377127 := by exact prefixLift 377127
  have htrace : WordTrace (prefixWord ++ tailWord_377127) baseStart_377127 baseEnd_377127 := by
    simpa [prefixWord, tailWord_377127, baseEnd_377127] using wordTrace_append hprefix tailTrace_377127
  have hstable : (prefixWord ++ tailWord_377127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377127).length < 2 ^ (prefixWord ++ tailWord_377127).sum := by decide
  have hdescent : baseEnd_377127 < baseStart_377127 := by decide
  rcases family_descends (prefixWord ++ tailWord_377127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377130 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_377130 : Nat := 118140960795 + 377130 * 2 ^ 59
def prefixEnd_377130 : Nat := 4983230072969 + 3 ^ 40 * 377130 * 2
def baseEnd_377130 : Nat := 193648959230214710840617

theorem tailTrace_377130 : CollatzResearch.WordTrace tailWord_377130 prefixEnd_377130 193648959230214710840617 := by
  unfold tailWord_377130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438765280932473380318211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9170040749153262347515229 3438765280932473380318211)
  ·
    refine ⟨5158147921398710070477317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3438765280932473380318211 5158147921398710070477317)
    ·
      refine ⟨967152735262258138214497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5158147921398710070477317 967152735262258138214497)
      ·
        refine ⟨725364551446693603660873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967152735262258138214497 725364551446693603660873)
        ·
          refine ⟨544023413585020202745655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725364551446693603660873 544023413585020202745655)
          ·
            refine ⟨816035120377530304118483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544023413585020202745655 816035120377530304118483)
            ·
              refine ⟨1224052680566295456177725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816035120377530304118483 1224052680566295456177725)
              ·
                refine ⟨459019755212360796066647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224052680566295456177725 459019755212360796066647)
                ·
                  refine ⟨688529632818541194099971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459019755212360796066647 688529632818541194099971)
                  ·
                    refine ⟨1032794449227811791149957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688529632818541194099971 1032794449227811791149957)
                    ·
                      refine ⟨193648959230214710840617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1032794449227811791149957 193648959230214710840617)
                      ·
                        rfl

theorem cell23_377130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_377130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377130 prefixEnd_377130 := by exact prefixLift 377130
  have htrace : WordTrace (prefixWord ++ tailWord_377130) baseStart_377130 baseEnd_377130 := by
    simpa [prefixWord, tailWord_377130, baseEnd_377130] using wordTrace_append hprefix tailTrace_377130
  have hstable : (prefixWord ++ tailWord_377130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377130).length < 2 ^ (prefixWord ++ tailWord_377130).sum := by decide
  have hdescent : baseEnd_377130 < baseStart_377130 := by decide
  rcases family_descends (prefixWord ++ tailWord_377130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377140 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_377140 : Nat := 118140960795 + 377140 * 2 ^ 59
def prefixEnd_377140 : Nat := 4983230072969 + 3 ^ 40 * 377140 * 2
def baseEnd_377140 : Nat := 64551364678919890571857

theorem tailTrace_377140 : CollatzResearch.WordTrace tailWord_377140 prefixEnd_377140 64551364678919890571857 := by
  unfold tailWord_377140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877712926846832614568437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9170283902462443486091249 6877712926846832614568437)
  ·
    refine ⟨644785586891890557615791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6877712926846832614568437 644785586891890557615791)
    ·
      refine ⟨967178380337835836423687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644785586891890557615791 967178380337835836423687)
      ·
        refine ⟨1450767570506753754635531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967178380337835836423687 1450767570506753754635531)
        ·
          refine ⟨2176151355760130631953297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450767570506753754635531 2176151355760130631953297)
          ·
            refine ⟨1632113516820097973964973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176151355760130631953297 1632113516820097973964973)
            ·
              refine ⟨612042568807536740236865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1632113516820097973964973 612042568807536740236865)
              ·
                refine ⟨459031926605652555177649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612042568807536740236865 459031926605652555177649)
                ·
                  refine ⟨344273944954239416383237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459031926605652555177649 344273944954239416383237)
                  ·
                    refine ⟨64551364678919890571857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 344273944954239416383237 64551364678919890571857)
                    ·
                      rfl

theorem cell23_377140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_377140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377140 prefixEnd_377140 := by exact prefixLift 377140
  have htrace : WordTrace (prefixWord ++ tailWord_377140) baseStart_377140 baseEnd_377140 := by
    simpa [prefixWord, tailWord_377140, baseEnd_377140] using wordTrace_append hprefix tailTrace_377140
  have hstable : (prefixWord ++ tailWord_377140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377140).length < 2 ^ (prefixWord ++ tailWord_377140).sum := by decide
  have hdescent : baseEnd_377140 < baseStart_377140 := by decide
  rcases family_descends (prefixWord ++ tailWord_377140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377199 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_377199 : Nat := 118140960795 + 377199 * 2 ^ 59
def prefixEnd_377199 : Nat := 4983230072969 + 3 ^ 40 * 377199 * 2
def baseEnd_377199 : Nat := 193684389395374940877799

theorem tailTrace_377199 : CollatzResearch.WordTrace tailWord_377199 prefixEnd_377199 193684389395374940877799 := by
  unfold tailWord_377199
  simp only [CollatzResearch.WordTrace]
  refine ⟨13757577760479918305534651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9171718506986612203689767 13757577760479918305534651)
  ·
    refine ⟨20636366640719877458301977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13757577760479918305534651 20636366640719877458301977)
    ·
      refine ⟨15477274980539908093726483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20636366640719877458301977 15477274980539908093726483)
      ·
        refine ⟨23215912470809862140589725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15477274980539908093726483 23215912470809862140589725)
        ·
          refine ⟨8705967176553698302721147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23215912470809862140589725 8705967176553698302721147)
          ·
            refine ⟨13058950764830547454081721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705967176553698302721147 13058950764830547454081721)
            ·
              refine ⟨9794213073622910590561291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13058950764830547454081721 9794213073622910590561291)
              ·
                refine ⟨14691319610434365885841937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9794213073622910590561291 14691319610434365885841937)
                ·
                  refine ⟨11018489707825774414381453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14691319610434365885841937 11018489707825774414381453)
                  ·
                    refine ⟨4131933640434665405393045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11018489707825774414381453 4131933640434665405393045)
                    ·
                      refine ⟨193684389395374940877799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4131933640434665405393045 193684389395374940877799)
                      ·
                        rfl

theorem cell23_377199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_377199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377199 prefixEnd_377199 := by exact prefixLift 377199
  have htrace : WordTrace (prefixWord ++ tailWord_377199) baseStart_377199 baseEnd_377199 := by
    simpa [prefixWord, tailWord_377199, baseEnd_377199] using wordTrace_append hprefix tailTrace_377199
  have hstable : (prefixWord ++ tailWord_377199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377199).length < 2 ^ (prefixWord ++ tailWord_377199).sum := by decide
  have hdescent : baseEnd_377199 < baseStart_377199 := by decide
  rcases family_descends (prefixWord ++ tailWord_377199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377266 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_377266 : Nat := 118140960795 + 377266 * 2 ^ 59
def prefixEnd_377266 : Nat := 4983230072969 + 3 ^ 40 * 377266 * 2
def baseEnd_377266 : Nat := 193718792599226178739991

theorem tailTrace_377266 : CollatzResearch.WordTrace tailWord_377266 prefixEnd_377266 193718792599226178739991 := by
  unfold tailWord_377266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440005362809297187055913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9173347634158125832149101 3440005362809297187055913)
  ·
    refine ⟨2580004022106972890291935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440005362809297187055913 2580004022106972890291935)
    ·
      refine ⟨3870006033160459335437903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580004022106972890291935 3870006033160459335437903)
      ·
        refine ⟨5805009049740689003156855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870006033160459335437903 5805009049740689003156855)
        ·
          refine ⟨8707513574611033504735283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805009049740689003156855 8707513574611033504735283)
          ·
            refine ⟨13061270361916550257102925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707513574611033504735283 13061270361916550257102925)
            ·
              refine ⟨4897976385718706346413597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13061270361916550257102925 4897976385718706346413597)
              ·
                refine ⟨1836741144644514879905099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4897976385718706346413597 1836741144644514879905099)
                ·
                  refine ⟨2755111716966772319857649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836741144644514879905099 2755111716966772319857649)
                  ·
                    refine ⟨2066333787725079239893237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2755111716966772319857649 2066333787725079239893237)
                    ·
                      refine ⟨193718792599226178739991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2066333787725079239893237 193718792599226178739991)
                      ·
                        rfl

theorem cell23_377266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_377266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377266 prefixEnd_377266 := by exact prefixLift 377266
  have htrace : WordTrace (prefixWord ++ tailWord_377266) baseStart_377266 baseEnd_377266 := by
    simpa [prefixWord, tailWord_377266, baseEnd_377266] using wordTrace_append hprefix tailTrace_377266
  have hstable : (prefixWord ++ tailWord_377266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377266).length < 2 ^ (prefixWord ++ tailWord_377266).sum := by decide
  have hdescent : baseEnd_377266 < baseStart_377266 := by decide
  rcases family_descends (prefixWord ++ tailWord_377266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377306 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_377306 : Nat := 118140960795 + 377306 * 2 ^ 59
def prefixEnd_377306 : Nat := 4983230072969 + 3 ^ 40 * 377306 * 2
def baseEnd_377306 : Nat := 193739331825406022239807

theorem tailTrace_377306 : CollatzResearch.WordTrace tailWord_377306 prefixEnd_377306 193739331825406022239807 := by
  unfold tailWord_377306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440370092773068894919943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9174320247394850386453181 3440370092773068894919943)
  ·
    refine ⟨5160555139159603342379915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3440370092773068894919943 5160555139159603342379915)
    ·
      refine ⟨7740832708739405013569873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5160555139159603342379915 7740832708739405013569873)
      ·
        refine ⟨5805624531554553760177405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7740832708739405013569873 5805624531554553760177405)
        ·
          refine ⟨2177109199332957660066527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5805624531554553760177405 2177109199332957660066527)
          ·
            refine ⟨3265663798999436490099791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177109199332957660066527 3265663798999436490099791)
            ·
              refine ⟨4898495698499154735149687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265663798999436490099791 4898495698499154735149687)
              ·
                refine ⟨7347743547748732102724531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898495698499154735149687 7347743547748732102724531)
                ·
                  refine ⟨11021615321623098154086797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347743547748732102724531 11021615321623098154086797)
                  ·
                    refine ⟨4133105745608661807782549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11021615321623098154086797 4133105745608661807782549)
                    ·
                      refine ⟨193739331825406022239807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4133105745608661807782549 193739331825406022239807)
                      ·
                        rfl

theorem cell23_377306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_377306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377306 prefixEnd_377306 := by exact prefixLift 377306
  have htrace : WordTrace (prefixWord ++ tailWord_377306) baseStart_377306 baseEnd_377306 := by
    simpa [prefixWord, tailWord_377306, baseEnd_377306] using wordTrace_append hprefix tailTrace_377306
  have hstable : (prefixWord ++ tailWord_377306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377306).length < 2 ^ (prefixWord ++ tailWord_377306).sum := by decide
  have hdescent : baseEnd_377306 < baseStart_377306 := by decide
  rcases family_descends (prefixWord ++ tailWord_377306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377313 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_377313 : Nat := 118140960795 + 377313 * 2 ^ 59
def prefixEnd_377313 : Nat := 4983230072969 + 3 ^ 40 * 377313 * 2
def baseEnd_377313 : Nat := 193742926189987494852275

theorem tailTrace_377313 : CollatzResearch.WordTrace tailWord_377313 prefixEnd_377313 193742926189987494852275 := by
  unfold tailWord_377313
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761735682066915775184593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9174490454711277183456395 13761735682066915775184593)
  ·
    refine ⟨10321301761550186831388445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13761735682066915775184593 10321301761550186831388445)
    ·
      refine ⟨3870488160581320061770667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10321301761550186831388445 3870488160581320061770667)
      ·
        refine ⟨5805732240871980092656001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870488160581320061770667 5805732240871980092656001)
        ·
          refine ⟨4354299180653985069492001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805732240871980092656001 4354299180653985069492001)
          ·
            refine ⟨3265724385490488802119001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4354299180653985069492001 3265724385490488802119001)
            ·
              refine ⟨2449293289117866601589251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265724385490488802119001 2449293289117866601589251)
              ·
                refine ⟨3673939933676799902383877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449293289117866601589251 3673939933676799902383877)
                ·
                  refine ⟨688863737564399981696977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3673939933676799902383877 688863737564399981696977)
                  ·
                    refine ⟨516647803173299986272733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 688863737564399981696977 516647803173299986272733)
                    ·
                      refine ⟨193742926189987494852275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 516647803173299986272733 193742926189987494852275)
                      ·
                        rfl

theorem cell23_377313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_377313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377313 prefixEnd_377313 := by exact prefixLift 377313
  have htrace : WordTrace (prefixWord ++ tailWord_377313) baseStart_377313 baseEnd_377313 := by
    simpa [prefixWord, tailWord_377313, baseEnd_377313] using wordTrace_append hprefix tailTrace_377313
  have hstable : (prefixWord ++ tailWord_377313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377313).length < 2 ^ (prefixWord ++ tailWord_377313).sum := by decide
  have hdescent : baseEnd_377313 < baseStart_377313 := by decide
  rcases family_descends (prefixWord ++ tailWord_377313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377320 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_377320 : Nat := 118140960795 + 377320 * 2 ^ 59
def prefixEnd_377320 : Nat := 4983230072969 + 3 ^ 40 * 377320 * 2
def baseEnd_377320 : Nat := 64582173518189655821581

theorem tailTrace_377320 : CollatzResearch.WordTrace tailWord_377320 prefixEnd_377320 64582173518189655821581 := by
  unfold tailWord_377320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880995496520777985344707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9174660662027703980459609 6880995496520777985344707)
  ·
    refine ⟨10321493244781166978017061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6880995496520777985344707 10321493244781166978017061)
    ·
      refine ⟨1935279983396468808378199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10321493244781166978017061 1935279983396468808378199)
      ·
        refine ⟨2902919975094703212567299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935279983396468808378199 2902919975094703212567299)
        ·
          refine ⟨4354379962642054818850949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902919975094703212567299 4354379962642054818850949)
          ·
            refine ⟨816446242995385278534553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4354379962642054818850949 816446242995385278534553)
            ·
              refine ⟨612334682246538958900915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816446242995385278534553 612334682246538958900915)
              ·
                refine ⟨918502023369808438351373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612334682246538958900915 918502023369808438351373)
                ·
                  refine ⟨344438258763678164381765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918502023369808438351373 344438258763678164381765)
                  ·
                    refine ⟨64582173518189655821581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 344438258763678164381765 64582173518189655821581)
                    ·
                      rfl

theorem cell23_377320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_377320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377320 prefixEnd_377320 := by exact prefixLift 377320
  have htrace : WordTrace (prefixWord ++ tailWord_377320) baseStart_377320 baseEnd_377320 := by
    simpa [prefixWord, tailWord_377320, baseEnd_377320] using wordTrace_append hprefix tailTrace_377320
  have hstable : (prefixWord ++ tailWord_377320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377320).length < 2 ^ (prefixWord ++ tailWord_377320).sum := by decide
  have hdescent : baseEnd_377320 < baseStart_377320 := by decide
  rcases family_descends (prefixWord ++ tailWord_377320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377336 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_377336 : Nat := 118140960795 + 377336 * 2 ^ 59
def prefixEnd_377336 : Nat := 4983230072969 + 3 ^ 40 * 377336 * 2
def baseEnd_377336 : Nat := 193754736245040904864669

theorem tailTrace_377336 : CollatzResearch.WordTrace tailWord_377336 prefixEnd_377336 193754736245040904864669 := by
  unfold tailWord_377336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881287280491795351635931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9175049707322393802181241 6881287280491795351635931)
  ·
    refine ⟨10321930920737693027453897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6881287280491795351635931 10321930920737693027453897)
    ·
      refine ⟨7741448190553269770590423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10321930920737693027453897 7741448190553269770590423)
      ·
        refine ⟨11612172285829904655885635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741448190553269770590423 11612172285829904655885635)
        ·
          refine ⟨17418258428744856983828453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11612172285829904655885635 17418258428744856983828453)
          ·
            refine ⟨3265923455389660684467835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17418258428744856983828453 3265923455389660684467835)
            ·
              refine ⟨4898885183084491026701753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265923455389660684467835 4898885183084491026701753)
              ·
                refine ⟨3674163887313368270026315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4898885183084491026701753 3674163887313368270026315)
                ·
                  refine ⟨5511245830970052405039473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674163887313368270026315 5511245830970052405039473)
                  ·
                    refine ⟨4133434373227539303779605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5511245830970052405039473 4133434373227539303779605)
                    ·
                      refine ⟨193754736245040904864669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4133434373227539303779605 193754736245040904864669)
                      ·
                        rfl

theorem cell23_377336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_377336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377336 prefixEnd_377336 := by exact prefixLift 377336
  have htrace : WordTrace (prefixWord ++ tailWord_377336) baseStart_377336 baseEnd_377336 := by
    simpa [prefixWord, tailWord_377336, baseEnd_377336] using wordTrace_append hprefix tailTrace_377336
  have hstable : (prefixWord ++ tailWord_377336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377336).length < 2 ^ (prefixWord ++ tailWord_377336).sum := by decide
  have hdescent : baseEnd_377336 < baseStart_377336 := by decide
  rcases family_descends (prefixWord ++ tailWord_377336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377363 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 1, 5]
def baseStart_377363 : Nat := 118140960795 + 377363 * 2 ^ 59
def prefixEnd_377363 : Nat := 4983230072969 + 3 ^ 40 * 377363 * 2
def baseEnd_377363 : Nat := 64589533407570766409015

theorem tailTrace_377363 : CollatzResearch.WordTrace tailWord_377363 prefixEnd_377363 64589533407570766409015 := by
  unfold tailWord_377363
  simp only [CollatzResearch.WordTrace]
  refine ⟨13763559331885774314504743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9175706221257182876336495 13763559331885774314504743)
  ·
    refine ⟨20645338997828661471757115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13763559331885774314504743 20645338997828661471757115)
    ·
      refine ⟨30968008496742992207635673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20645338997828661471757115 30968008496742992207635673)
      ·
        refine ⟨23226006372557244155726755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30968008496742992207635673 23226006372557244155726755)
        ·
          refine ⟨34839009558835866233590133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23226006372557244155726755 34839009558835866233590133)
          ·
            refine ⟨3266157146140862459399075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34839009558835866233590133 3266157146140862459399075)
            ·
              refine ⟨4899235719211293689098613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266157146140862459399075 4899235719211293689098613)
              ·
                refine ⟨459303348676058783352995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4899235719211293689098613 459303348676058783352995)
                ·
                  refine ⟨688955023014088175029493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459303348676058783352995 688955023014088175029493)
                  ·
                    refine ⟨64589533407570766409015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 688955023014088175029493 64589533407570766409015)
                    ·
                      rfl

theorem cell23_377363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 5].length) (baseStart_377363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377363 prefixEnd_377363 := by exact prefixLift 377363
  have htrace : WordTrace (prefixWord ++ tailWord_377363) baseStart_377363 baseEnd_377363 := by
    simpa [prefixWord, tailWord_377363, baseEnd_377363] using wordTrace_append hprefix tailTrace_377363
  have hstable : (prefixWord ++ tailWord_377363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377363).length < 2 ^ (prefixWord ++ tailWord_377363).sum := by decide
  have hdescent : baseEnd_377363 < baseStart_377363 := by decide
  rcases family_descends (prefixWord ++ tailWord_377363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377370 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_377370 : Nat := 118140960795 + 377370 * 2 ^ 59
def prefixEnd_377370 : Nat := 4983230072969 + 3 ^ 40 * 377370 * 2
def baseEnd_377370 : Nat := 193772194587293771839513

theorem tailTrace_377370 : CollatzResearch.WordTrace tailWord_377370 prefixEnd_377370 193772194587293771839513 := by
  unfold tailWord_377370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440953660715103627502391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9175876428573609673339709 3440953660715103627502391)
  ·
    refine ⟨5161430491072655441253587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3440953660715103627502391 5161430491072655441253587)
    ·
      refine ⟨7742145736608983161880381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5161430491072655441253587 7742145736608983161880381)
      ·
        refine ⟨2903304651228368685705143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7742145736608983161880381 2903304651228368685705143)
        ·
          refine ⟨4354956976842553028557715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2903304651228368685705143 4354956976842553028557715)
          ·
            refine ⟨6532435465263829542836573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354956976842553028557715 6532435465263829542836573)
            ·
              refine ⟨2449663299473936078563715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6532435465263829542836573 2449663299473936078563715)
              ·
                refine ⟨3674494949210904117845573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449663299473936078563715 3674494949210904117845573)
                ·
                  refine ⟨688967802977044522096045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3674494949210904117845573 688967802977044522096045)
                  ·
                    refine ⟨258362926116391695786017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688967802977044522096045 258362926116391695786017)
                    ·
                      refine ⟨193772194587293771839513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258362926116391695786017 193772194587293771839513)
                      ·
                        rfl

theorem cell23_377370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_377370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377370 prefixEnd_377370 := by exact prefixLift 377370
  have htrace : WordTrace (prefixWord ++ tailWord_377370) baseStart_377370 baseEnd_377370 := by
    simpa [prefixWord, tailWord_377370, baseEnd_377370] using wordTrace_append hprefix tailTrace_377370
  have hstable : (prefixWord ++ tailWord_377370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377370).length < 2 ^ (prefixWord ++ tailWord_377370).sum := by decide
  have hdescent : baseEnd_377370 < baseStart_377370 := by decide
  rcases family_descends (prefixWord ++ tailWord_377370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377413 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_377413 : Nat := 118140960795 + 377413 * 2 ^ 59
def prefixEnd_377413 : Nat := 4983230072969 + 3 ^ 40 * 377413 * 2
def baseEnd_377413 : Nat := 193794274255437103601815

theorem tailTrace_377413 : CollatzResearch.WordTrace tailWord_377413 prefixEnd_377413 193794274255437103601815 := by
  unfold tailWord_377413
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765382981704632853824893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9176921987803088569216595 13765382981704632853824893)
  ·
    refine ⟨5162018618139237320184335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13765382981704632853824893 5162018618139237320184335)
    ·
      refine ⟨7743027927208855980276503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5162018618139237320184335 7743027927208855980276503)
      ·
        refine ⟨11614541890813283970414755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743027927208855980276503 11614541890813283970414755)
        ·
          refine ⟨17421812836219925955622133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614541890813283970414755 17421812836219925955622133)
          ·
            refine ⟨1633294953395618058339575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17421812836219925955622133 1633294953395618058339575)
            ·
              refine ⟨2449942430093427087509363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633294953395618058339575 2449942430093427087509363)
              ·
                refine ⟨3674913645140140631264045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449942430093427087509363 3674913645140140631264045)
                ·
                  refine ⟨1378092616927552736724017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3674913645140140631264045 1378092616927552736724017)
                  ·
                    refine ⟨1033569462695664552543013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1378092616927552736724017 1033569462695664552543013)
                    ·
                      refine ⟨193794274255437103601815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1033569462695664552543013 193794274255437103601815)
                      ·
                        rfl

theorem cell23_377413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_377413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377413 prefixEnd_377413 := by exact prefixLift 377413
  have htrace : WordTrace (prefixWord ++ tailWord_377413) baseStart_377413 baseEnd_377413 := by
    simpa [prefixWord, tailWord_377413, baseEnd_377413] using wordTrace_append hprefix tailTrace_377413
  have hstable : (prefixWord ++ tailWord_377413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377413).length < 2 ^ (prefixWord ++ tailWord_377413).sum := by decide
  have hdescent : baseEnd_377413 < baseStart_377413 := by decide
  rcases family_descends (prefixWord ++ tailWord_377413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377474 : List Nat := [3, 4, 3, 1, 1, 1, 10]
def baseStart_377474 : Nat := 118140960795 + 377474 * 2 ^ 59
def prefixEnd_377474 : Nat := 4983230072969 + 3 ^ 40 * 377474 * 2
def baseEnd_377474 : Nat := 2392908599695819320235

theorem tailTrace_377474 : CollatzResearch.WordTrace tailWord_377474 prefixEnd_377474 2392908599695819320235 := by
  unfold tailWord_377474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441901958620910067948869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9178405222989093514530317 3441901958620910067948869)
  ·
    refine ⟨645356617241420637740413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3441901958620910067948869 645356617241420637740413)
    ·
      refine ⟨242008731465532739152655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 645356617241420637740413 242008731465532739152655)
      ·
        refine ⟨363013097198299108728983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242008731465532739152655 363013097198299108728983)
        ·
          refine ⟨544519645797448663093475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363013097198299108728983 544519645797448663093475)
          ·
            refine ⟨816779468696172994640213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544519645797448663093475 816779468696172994640213)
            ·
              refine ⟨2392908599695819320235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 816779468696172994640213 2392908599695819320235)
              ·
                rfl

theorem cell23_377474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 10].length) (baseStart_377474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377474 prefixEnd_377474 := by exact prefixLift 377474
  have htrace : WordTrace (prefixWord ++ tailWord_377474) baseStart_377474 baseEnd_377474 := by
    simpa [prefixWord, tailWord_377474, baseEnd_377474] using wordTrace_append hprefix tailTrace_377474
  have hstable : (prefixWord ++ tailWord_377474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377474).length < 2 ^ (prefixWord ++ tailWord_377474).sum := by decide
  have hdescent : baseEnd_377474 < baseStart_377474 := by decide
  rcases family_descends (prefixWord ++ tailWord_377474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377493 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_377493 : Nat := 118140960795 + 377493 * 2 ^ 59
def prefixEnd_377493 : Nat := 4983230072969 + 3 ^ 40 * 377493 * 2
def baseEnd_377493 : Nat := 193835352707796790601447

theorem tailTrace_377493 : CollatzResearch.WordTrace tailWord_377493 prefixEnd_377493 193835352707796790601447 := by
  unfold tailWord_377493
  simp only [CollatzResearch.WordTrace]
  refine ⟨13768300821414806516737133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9178867214276537677824755 13768300821414806516737133)
  ·
    refine ⟨5163112808030552443776425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13768300821414806516737133 5163112808030552443776425)
    ·
      refine ⟨3872334606022914332832319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5163112808030552443776425 3872334606022914332832319)
      ·
        refine ⟨5808501909034371499248479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872334606022914332832319 5808501909034371499248479)
        ·
          refine ⟨8712752863551557248872719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808501909034371499248479 8712752863551557248872719)
          ·
            refine ⟨13069129295327335873309079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712752863551557248872719 13069129295327335873309079)
            ·
              refine ⟨19603693942991003809963619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069129295327335873309079 19603693942991003809963619)
              ·
                refine ⟨29405540914486505714945429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19603693942991003809963619 29405540914486505714945429)
                ·
                  refine ⟨1378384730366554955388067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29405540914486505714945429 1378384730366554955388067)
                  ·
                    refine ⟨2067577095549832433082101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1378384730366554955388067 2067577095549832433082101)
                    ·
                      refine ⟨193835352707796790601447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2067577095549832433082101 193835352707796790601447)
                      ·
                        rfl

theorem cell23_377493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_377493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377493 prefixEnd_377493 := by exact prefixLift 377493
  have htrace : WordTrace (prefixWord ++ tailWord_377493) baseStart_377493 baseEnd_377493 := by
    simpa [prefixWord, tailWord_377493, baseEnd_377493] using wordTrace_append hprefix tailTrace_377493
  have hstable : (prefixWord ++ tailWord_377493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377493).length < 2 ^ (prefixWord ++ tailWord_377493).sum := by decide
  have hdescent : baseEnd_377493 < baseStart_377493 := by decide
  rcases family_descends (prefixWord ++ tailWord_377493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377500 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_377500 : Nat := 118140960795 + 377500 * 2 ^ 59
def prefixEnd_377500 : Nat := 4983230072969 + 3 ^ 40 * 377500 * 2
def baseEnd_377500 : Nat := 64612982357459421071305

theorem tailTrace_377500 : CollatzResearch.WordTrace tailWord_377500 prefixEnd_377500 64612982357459421071305 := by
  unfold tailWord_377500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6884278066194723356120977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9179037421592964474827969 6884278066194723356120977)
  ·
    refine ⟨5163208549646042517090733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6884278066194723356120977 5163208549646042517090733)
    ·
      refine ⟨1936203206117265943909025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5163208549646042517090733 1936203206117265943909025)
      ·
        refine ⟨1452152404587949457931769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936203206117265943909025 1452152404587949457931769)
        ·
          refine ⟨1089114303440962093448827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452152404587949457931769 1089114303440962093448827)
          ·
            refine ⟨1633671455161443140173241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089114303440962093448827 1633671455161443140173241)
            ·
              refine ⟨1225253591371082355129931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633671455161443140173241 1225253591371082355129931)
              ·
                refine ⟨1837880387056623532694897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225253591371082355129931 1837880387056623532694897)
                ·
                  refine ⟨1378410290292467649521173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837880387056623532694897 1378410290292467649521173)
                  ·
                    refine ⟨64612982357459421071305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1378410290292467649521173 64612982357459421071305)
                    ·
                      rfl

theorem cell23_377500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_377500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377500 prefixEnd_377500 := by exact prefixLift 377500
  have htrace : WordTrace (prefixWord ++ tailWord_377500) baseStart_377500 baseEnd_377500 := by
    simpa [prefixWord, tailWord_377500, baseEnd_377500] using wordTrace_append hprefix tailTrace_377500
  have hstable : (prefixWord ++ tailWord_377500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377500).length < 2 ^ (prefixWord ++ tailWord_377500).sum := by decide
  have hdescent : baseEnd_377500 < baseStart_377500 := by decide
  rcases family_descends (prefixWord ++ tailWord_377500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377543 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 7]
def baseStart_377543 : Nat := 118140960795 + 377543 * 2 ^ 59
def prefixEnd_377543 : Nat := 4983230072969 + 3 ^ 40 * 377543 * 2
def baseEnd_377543 : Nat := 64620342246840531658739

theorem tailTrace_377543 : CollatzResearch.WordTrace tailWord_377543 prefixEnd_377543 64620342246840531658739 := by
  unfold tailWord_377543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13770124471233665056057283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9180082980822443370704855 13770124471233665056057283)
  ·
    refine ⟨20655186706850497584085925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13770124471233665056057283 20655186706850497584085925)
    ·
      refine ⟨3872847507534468297016111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20655186706850497584085925 3872847507534468297016111)
      ·
        refine ⟨5809271261301702445524167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872847507534468297016111 5809271261301702445524167)
        ·
          refine ⟨8713906891952553668286251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809271261301702445524167 8713906891952553668286251)
          ·
            refine ⟨13070860337928830502429377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713906891952553668286251 13070860337928830502429377)
            ·
              refine ⟨9803145253446622876822033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13070860337928830502429377 9803145253446622876822033)
              ·
                refine ⟨7352358940084967157616525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9803145253446622876822033 7352358940084967157616525)
                ·
                  refine ⟨2757134602531862684106197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7352358940084967157616525 2757134602531862684106197)
                  ·
                    refine ⟨64620342246840531658739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2757134602531862684106197 64620342246840531658739)
                    ·
                      rfl

theorem cell23_377543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_377543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377543 prefixEnd_377543 := by exact prefixLift 377543
  have htrace : WordTrace (prefixWord ++ tailWord_377543) baseStart_377543 baseEnd_377543 := by
    simpa [prefixWord, tailWord_377543, baseEnd_377543] using wordTrace_append hprefix tailTrace_377543
  have hstable : (prefixWord ++ tailWord_377543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377543).length < 2 ^ (prefixWord ++ tailWord_377543).sum := by decide
  have hdescent : baseEnd_377543 < baseStart_377543 := by decide
  rcases family_descends (prefixWord ++ tailWord_377543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377597 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_377597 : Nat := 118140960795 + 377597 * 2 ^ 59
def prefixEnd_377597 : Nat := 4983230072969 + 3 ^ 40 * 377597 * 2
def baseEnd_377597 : Nat := 193888754695864383700969

theorem tailTrace_377597 : CollatzResearch.WordTrace tailWord_377597 prefixEnd_377597 193888754695864383700969 := by
  unfold tailWord_377597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13772094013038032278523045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9181396008692021519015363 13772094013038032278523045)
  ·
    refine ⟨2582267627444631052223071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13772094013038032278523045 2582267627444631052223071)
    ·
      refine ⟨3873401441166946578334607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582267627444631052223071 3873401441166946578334607)
      ·
        refine ⟨5810102161750419867501911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873401441166946578334607 5810102161750419867501911)
        ·
          refine ⟨8715153242625629801252867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5810102161750419867501911 8715153242625629801252867)
          ·
            refine ⟨13072729863938444701879301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715153242625629801252867 13072729863938444701879301)
            ·
              refine ⟨2451136849488458381602369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13072729863938444701879301 2451136849488458381602369)
              ·
                refine ⟨1838352637116343786201777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451136849488458381602369 1838352637116343786201777)
                ·
                  refine ⟨1378764477837257839651333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838352637116343786201777 1378764477837257839651333)
                  ·
                    refine ⟨258518339594485844934625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378764477837257839651333 258518339594485844934625)
                    ·
                      refine ⟨193888754695864383700969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258518339594485844934625 193888754695864383700969)
                      ·
                        rfl

theorem cell23_377597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_377597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377597 prefixEnd_377597 := by exact prefixLift 377597
  have htrace : WordTrace (prefixWord ++ tailWord_377597) baseStart_377597 baseEnd_377597 := by
    simpa [prefixWord, tailWord_377597, baseEnd_377597] using wordTrace_append hprefix tailTrace_377597
  have hstable : (prefixWord ++ tailWord_377597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377597).length < 2 ^ (prefixWord ++ tailWord_377597).sum := by decide
  have hdescent : baseEnd_377597 < baseStart_377597 := by decide
  rcases family_descends (prefixWord ++ tailWord_377597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377634 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_377634 : Nat := 118140960795 + 377634 * 2 ^ 59
def prefixEnd_377634 : Nat := 4983230072969 + 3 ^ 40 * 377634 * 2
def baseEnd_377634 : Nat := 193907753480080738938299

theorem tailTrace_377634 : CollatzResearch.WordTrace tailWord_377634 prefixEnd_377634 193907753480080738938299 := by
  unfold tailWord_377634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443360878475996899404989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9182295675935991731746637 3443360878475996899404989)
  ·
    refine ⟨1291260329428498837276871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3443360878475996899404989 1291260329428498837276871)
    ·
      refine ⟨1936890494142748255915307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291260329428498837276871 1936890494142748255915307)
      ·
        refine ⟨2905335741214122383872961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936890494142748255915307 2905335741214122383872961)
        ·
          refine ⟨2179001805910591787904721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2905335741214122383872961 2179001805910591787904721)
          ·
            refine ⟨1634251354432943840928541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179001805910591787904721 1634251354432943840928541)
            ·
              refine ⟨612844257912353940348203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634251354432943840928541 612844257912353940348203)
              ·
                refine ⟨919266386868530910522305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612844257912353940348203 919266386868530910522305)
                ·
                  refine ⟨689449790151398182891729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919266386868530910522305 689449790151398182891729)
                  ·
                    refine ⟨517087342613548637168797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689449790151398182891729 517087342613548637168797)
                    ·
                      refine ⟨193907753480080738938299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517087342613548637168797 193907753480080738938299)
                      ·
                        rfl

theorem cell23_377634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_377634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377634 prefixEnd_377634 := by exact prefixLift 377634
  have htrace : WordTrace (prefixWord ++ tailWord_377634) baseStart_377634 baseEnd_377634 := by
    simpa [prefixWord, tailWord_377634, baseEnd_377634] using wordTrace_append hprefix tailTrace_377634
  have hstable : (prefixWord ++ tailWord_377634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377634).length < 2 ^ (prefixWord ++ tailWord_377634).sum := by decide
  have hdescent : baseEnd_377634 < baseStart_377634 := by decide
  rcases family_descends (prefixWord ++ tailWord_377634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377654 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_377654 : Nat := 118140960795 + 377654 * 2 ^ 59
def prefixEnd_377654 : Nat := 4983230072969 + 3 ^ 40 * 377654 * 2
def baseEnd_377654 : Nat := 21546447010352295632023

theorem tailTrace_377654 : CollatzResearch.WordTrace tailWord_377654 prefixEnd_377654 21546447010352295632023 := by
  unfold tailWord_377654
  simp only [CollatzResearch.WordTrace]
  refine ⟨860885810864470688334251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9182781982554354008898677 860885810864470688334251)
  ·
    refine ⟨1291328716296706032501377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860885810864470688334251 1291328716296706032501377)
    ·
      refine ⟨968496537222529524376033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1291328716296706032501377 968496537222529524376033)
      ·
        refine ⟨726372402916897143282025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 968496537222529524376033 726372402916897143282025)
        ·
          refine ⟨544779302187672857461519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726372402916897143282025 544779302187672857461519)
          ·
            refine ⟨817168953281509286192279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544779302187672857461519 817168953281509286192279)
            ·
              refine ⟨1225753429922263929288419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817168953281509286192279 1225753429922263929288419)
              ·
                refine ⟨1838630144883395893932629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225753429922263929288419 1838630144883395893932629)
                ·
                  refine ⟨21546447010352295632023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1838630144883395893932629 21546447010352295632023)
                  ·
                    rfl

theorem cell23_377654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_377654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377654 prefixEnd_377654 := by exact prefixLift 377654
  have htrace : WordTrace (prefixWord ++ tailWord_377654) baseStart_377654 baseEnd_377654 := by
    simpa [prefixWord, tailWord_377654, baseEnd_377654] using wordTrace_append hprefix tailTrace_377654
  have hstable : (prefixWord ++ tailWord_377654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377654).length < 2 ^ (prefixWord ++ tailWord_377654).sum := by decide
  have hdescent : baseEnd_377654 < baseStart_377654 := by decide
  rcases family_descends (prefixWord ++ tailWord_377654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377704 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_377704 : Nat := 118140960795 + 377704 * 2 ^ 59
def prefixEnd_377704 : Nat := 4983230072969 + 3 ^ 40 * 377704 * 2
def baseEnd_377704 : Nat := 193943697125895465062977

theorem tailTrace_377704 : CollatzResearch.WordTrace tailWord_377704 prefixEnd_377704 193943697125895465062977 := by
  unfold tailWord_377704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887998311825194776334083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9183997749100259701778777 6887998311825194776334083)
  ·
    refine ⟨10331997467737792164501125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887998311825194776334083 10331997467737792164501125)
    ·
      refine ⟨1937249525200836030843961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10331997467737792164501125 1937249525200836030843961)
      ·
        refine ⟨1452937143900627023132971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937249525200836030843961 1452937143900627023132971)
        ·
          refine ⟨2179405715850940534699457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452937143900627023132971 2179405715850940534699457)
          ·
            refine ⟨1634554286888205401024593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179405715850940534699457 1634554286888205401024593)
            ·
              refine ⟨1225915715166154050768445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634554286888205401024593 1225915715166154050768445)
              ·
                refine ⟨459718393187307769038167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1225915715166154050768445 459718393187307769038167)
                ·
                  refine ⟨689577589780961653557251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459718393187307769038167 689577589780961653557251)
                  ·
                    refine ⟨1034366384671442480335877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 689577589780961653557251 1034366384671442480335877)
                    ·
                      refine ⟨193943697125895465062977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1034366384671442480335877 193943697125895465062977)
                      ·
                        rfl

theorem cell23_377704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_377704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377704 prefixEnd_377704 := by exact prefixLift 377704
  have htrace : WordTrace (prefixWord ++ tailWord_377704) baseStart_377704 baseEnd_377704 := by
    simpa [prefixWord, tailWord_377704, baseEnd_377704] using wordTrace_append hprefix tailTrace_377704
  have hstable : (prefixWord ++ tailWord_377704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377704).length < 2 ^ (prefixWord ++ tailWord_377704).sum := by decide
  have hdescent : baseEnd_377704 < baseStart_377704 := by decide
  rcases family_descends (prefixWord ++ tailWord_377704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377717 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_377717 : Nat := 118140960795 + 377717 * 2 ^ 59
def prefixEnd_377717 : Nat := 4983230072969 + 3 ^ 40 * 377717 * 2
def baseEnd_377717 : Nat := 193950372374403914200417

theorem tailTrace_377717 : CollatzResearch.WordTrace tailWord_377717 prefixEnd_377717 193950372374403914200417 := by
  unfold tailWord_377717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13776470772603292772891405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9184313848402195181927603 13776470772603292772891405)
  ·
    refine ⟨5166176539726234789834277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13776470772603292772891405 5166176539726234789834277)
    ·
      refine ⟨968658101198669023093927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5166176539726234789834277 968658101198669023093927)
      ·
        refine ⟨1452987151798003534640891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968658101198669023093927 1452987151798003534640891)
        ·
          refine ⟨2179480727697005301961337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452987151798003534640891 2179480727697005301961337)
          ·
            refine ⟨1634610545772753976471003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179480727697005301961337 1634610545772753976471003)
            ·
              refine ⟨2451915818659130964706505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634610545772753976471003 2451915818659130964706505)
              ·
                refine ⟨1838936863994348223529879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451915818659130964706505 1838936863994348223529879)
                ·
                  refine ⟨2758405295991522335294819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838936863994348223529879 2758405295991522335294819)
                  ·
                    refine ⟨4137607943987283502942229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758405295991522335294819 4137607943987283502942229)
                    ·
                      refine ⟨193950372374403914200417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4137607943987283502942229 193950372374403914200417)
                      ·
                        rfl

theorem cell23_377717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_377717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377717 prefixEnd_377717 := by exact prefixLift 377717
  have htrace : WordTrace (prefixWord ++ tailWord_377717) baseStart_377717 baseEnd_377717 := by
    simpa [prefixWord, tailWord_377717, baseEnd_377717] using wordTrace_append hprefix tailTrace_377717
  have hstable : (prefixWord ++ tailWord_377717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377717).length < 2 ^ (prefixWord ++ tailWord_377717).sum := by decide
  have hdescent : baseEnd_377717 < baseStart_377717 := by decide
  rcases family_descends (prefixWord ++ tailWord_377717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377721 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 3, 2, 2]
def baseStart_377721 : Nat := 118140960795 + 377721 * 2 ^ 59
def prefixEnd_377721 : Nat := 4983230072969 + 3 ^ 40 * 377721 * 2
def baseEnd_377721 : Nat := 193952426297021898550399

theorem tailTrace_377721 : CollatzResearch.WordTrace tailWord_377721 prefixEnd_377721 193952426297021898550399 := by
  unfold tailWord_377721
  simp only [CollatzResearch.WordTrace]
  refine ⟨13776616664588801456037017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9184411109725867637358011 13776616664588801456037017)
  ·
    refine ⟨10332462498441601092027763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13776616664588801456037017 10332462498441601092027763)
    ·
      refine ⟨15498693747662401638041645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10332462498441601092027763 15498693747662401638041645)
      ·
        refine ⟨5812010155373400614265617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15498693747662401638041645 5812010155373400614265617)
        ·
          refine ⟨4359007616530050460699213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5812010155373400614265617 4359007616530050460699213)
          ·
            refine ⟨1634627856198768922762205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4359007616530050460699213 1634627856198768922762205)
            ·
              refine ⟨612985446074538346035827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634627856198768922762205 612985446074538346035827)
              ·
                refine ⟨919478169111807519053741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612985446074538346035827 919478169111807519053741)
                ·
                  refine ⟨344804313416927819645153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919478169111807519053741 344804313416927819645153)
                  ·
                    refine ⟨258603235062695864733865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344804313416927819645153 258603235062695864733865)
                    ·
                      refine ⟨193952426297021898550399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258603235062695864733865 193952426297021898550399)
                      ·
                        rfl

theorem cell23_377721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_377721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377721 prefixEnd_377721 := by exact prefixLift 377721
  have htrace : WordTrace (prefixWord ++ tailWord_377721) baseStart_377721 baseEnd_377721 := by
    simpa [prefixWord, tailWord_377721, baseEnd_377721] using wordTrace_append hprefix tailTrace_377721
  have hstable : (prefixWord ++ tailWord_377721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377721).length < 2 ^ (prefixWord ++ tailWord_377721).sum := by decide
  have hdescent : baseEnd_377721 < baseStart_377721 := by decide
  rcases family_descends (prefixWord ++ tailWord_377721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377834 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_377834 : Nat := 118140960795 + 377834 * 2 ^ 59
def prefixEnd_377834 : Nat := 4983230072969 + 3 ^ 40 * 377834 * 2
def baseEnd_377834 : Nat := 21556716623442217381931

theorem tailTrace_377834 : CollatzResearch.WordTrace tailWord_377834 prefixEnd_377834 21556716623442217381931 := by
  unfold tailWord_377834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445184528294855438725139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9187158742119614503267037 3445184528294855438725139)
  ·
    refine ⟨5167776792442283158087709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3445184528294855438725139 5167776792442283158087709)
    ·
      refine ⟨1937916297165856184282891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5167776792442283158087709 1937916297165856184282891)
      ·
        refine ⟨2906874445748784276424337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937916297165856184282891 2906874445748784276424337)
        ·
          refine ⟨2180155834311588207318253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2906874445748784276424337 2180155834311588207318253)
          ·
            refine ⟨817558437866845577744345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2180155834311588207318253 817558437866845577744345)
            ·
              refine ⟨613168828400134183308259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817558437866845577744345 613168828400134183308259)
              ·
                refine ⟨919753242600201274962389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613168828400134183308259 919753242600201274962389)
                ·
                  refine ⟨21556716623442217381931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 919753242600201274962389 21556716623442217381931)
                  ·
                    rfl

theorem cell23_377834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_377834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377834 prefixEnd_377834 := by exact prefixLift 377834
  have htrace : WordTrace (prefixWord ++ tailWord_377834) baseStart_377834 baseEnd_377834 := by
    simpa [prefixWord, tailWord_377834, baseEnd_377834] using wordTrace_append hprefix tailTrace_377834
  have hstable : (prefixWord ++ tailWord_377834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377834).length < 2 ^ (prefixWord ++ tailWord_377834).sum := by decide
  have hdescent : baseEnd_377834 < baseStart_377834 := by decide
  rcases family_descends (prefixWord ++ tailWord_377834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377904 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_377904 : Nat := 118140960795 + 377904 * 2 ^ 59
def prefixEnd_377904 : Nat := 4983230072969 + 3 ^ 40 * 377904 * 2
def baseEnd_377904 : Nat := 194046393256794682562057

theorem tailTrace_377904 : CollatzResearch.WordTrace tailWord_377904 prefixEnd_377904 194046393256794682562057 := by
  unfold tailWord_377904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891645611462911854974383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9188860815283882473299177 6891645611462911854974383)
  ·
    refine ⟨10337468417194367782461575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891645611462911854974383 10337468417194367782461575)
    ·
      refine ⟨15506202625791551673692363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10337468417194367782461575 15506202625791551673692363)
      ·
        refine ⟨23259303938687327510538545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15506202625791551673692363 23259303938687327510538545)
        ·
          refine ⟨17444477954015495632903909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23259303938687327510538545 17444477954015495632903909)
          ·
            refine ⟨3270839616377905431169483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17444477954015495632903909 3270839616377905431169483)
            ·
              refine ⟨4906259424566858146754225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270839616377905431169483 4906259424566858146754225)
              ·
                refine ⟨3679694568425143610065669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906259424566858146754225 3679694568425143610065669)
                ·
                  refine ⟨689942731579714426887313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3679694568425143610065669 689942731579714426887313)
                  ·
                    refine ⟨517457048684785820165485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689942731579714426887313 517457048684785820165485)
                    ·
                      refine ⟨194046393256794682562057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517457048684785820165485 194046393256794682562057)
                      ·
                        rfl

theorem cell23_377904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_377904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377904 prefixEnd_377904 := by exact prefixLift 377904
  have htrace : WordTrace (prefixWord ++ tailWord_377904) baseStart_377904 baseEnd_377904 := by
    simpa [prefixWord, tailWord_377904, baseEnd_377904] using wordTrace_append hprefix tailTrace_377904
  have hstable : (prefixWord ++ tailWord_377904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377904).length < 2 ^ (prefixWord ++ tailWord_377904).sum := by decide
  have hdescent : baseEnd_377904 < baseStart_377904 := by decide
  rcases family_descends (prefixWord ++ tailWord_377904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377918 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_377918 : Nat := 118140960795 + 377918 * 2 ^ 59
def prefixEnd_377918 : Nat := 4983230072969 + 3 ^ 40 * 377918 * 2
def baseEnd_377918 : Nat := 194053581985957627786993

theorem tailTrace_377918 : CollatzResearch.WordTrace tailWord_377918 prefixEnd_377918 194053581985957627786993 := by
  unfold tailWord_377918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722975230609388012619801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9189201229916736067305605 1722975230609388012619801)
  ·
    refine ⟨1292231422957041009464851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1722975230609388012619801 1292231422957041009464851)
    ·
      refine ⟨1938347134435561514197277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292231422957041009464851 1938347134435561514197277)
      ·
        refine ⟨726880175413335567823979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1938347134435561514197277 726880175413335567823979)
        ·
          refine ⟨1090320263120003351735969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726880175413335567823979 1090320263120003351735969)
          ·
            refine ⟨817740197340002513801977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1090320263120003351735969 817740197340002513801977)
            ·
              refine ⟨613305148005001885351483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817740197340002513801977 613305148005001885351483)
              ·
                refine ⟨919957722007502828027225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613305148005001885351483 919957722007502828027225)
                ·
                  refine ⟨689968291505627121020419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919957722007502828027225 689968291505627121020419)
                  ·
                    refine ⟨1034952437258440681530629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 689968291505627121020419 1034952437258440681530629)
                    ·
                      refine ⟨194053581985957627786993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1034952437258440681530629 194053581985957627786993)
                      ·
                        rfl

theorem cell23_377918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_377918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377918 prefixEnd_377918 := by exact prefixLift 377918
  have htrace : WordTrace (prefixWord ++ tailWord_377918) baseStart_377918 baseEnd_377918 := by
    simpa [prefixWord, tailWord_377918, baseEnd_377918] using wordTrace_append hprefix tailTrace_377918
  have hstable : (prefixWord ++ tailWord_377918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377918).length < 2 ^ (prefixWord ++ tailWord_377918).sum := by decide
  have hdescent : baseEnd_377918 < baseStart_377918 := by decide
  rcases family_descends (prefixWord ++ tailWord_377918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377951 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 3]
def baseStart_377951 : Nat := 118140960795 + 377951 * 2 ^ 59
def prefixEnd_377951 : Nat := 4983230072969 + 3 ^ 40 * 377951 * 2
def baseEnd_377951 : Nat := 194070526847555998674341

theorem tailTrace_377951 : CollatzResearch.WordTrace tailWord_377951 prefixEnd_377951 194070526847555998674341 := by
  unfold tailWord_377951
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785005453755550736909707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9190003635837033824606471 13785005453755550736909707)
  ·
    refine ⟨20677508180633326105364561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785005453755550736909707 20677508180633326105364561)
    ·
      refine ⟨15508131135474994579023421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20677508180633326105364561 15508131135474994579023421)
      ·
        refine ⟨5815549175803122967133783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15508131135474994579023421 5815549175803122967133783)
        ·
          refine ⟨8723323763704684450700675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815549175803122967133783 8723323763704684450700675)
          ·
            refine ⟨13084985645557026676051013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723323763704684450700675 13084985645557026676051013)
            ·
              refine ⟨2453434808541942501759565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13084985645557026676051013 2453434808541942501759565)
              ·
                refine ⟨920038053203228438159837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453434808541942501759565 920038053203228438159837)
                ·
                  refine ⟨345014269951210664309939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920038053203228438159837 345014269951210664309939)
                  ·
                    refine ⟨517521404926815996464909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345014269951210664309939 517521404926815996464909)
                    ·
                      refine ⟨194070526847555998674341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517521404926815996464909 194070526847555998674341)
                      ·
                        rfl

theorem cell23_377951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_377951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377951 prefixEnd_377951 := by exact prefixLift 377951
  have htrace : WordTrace (prefixWord ++ tailWord_377951) baseStart_377951 baseEnd_377951 := by
    simpa [prefixWord, tailWord_377951, baseEnd_377951] using wordTrace_append hprefix tailTrace_377951
  have hstable : (prefixWord ++ tailWord_377951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377951).length < 2 ^ (prefixWord ++ tailWord_377951).sum := by decide
  have hdescent : baseEnd_377951 < baseStart_377951 := by decide
  rcases family_descends (prefixWord ++ tailWord_377951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377984 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_377984 : Nat := 118140960795 + 377984 * 2 ^ 59
def prefixEnd_377984 : Nat := 4983230072969 + 3 ^ 40 * 377984 * 2
def baseEnd_377984 : Nat := 64695823903051456520563

theorem tailTrace_377984 : CollatzResearch.WordTrace tailWord_377984 prefixEnd_377984 64695823903051456520563 := by
  unfold tailWord_377984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893104531317998686430503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9190806041757331581907337 6893104531317998686430503)
  ·
    refine ⟨10339656796976998029645755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6893104531317998686430503 10339656796976998029645755)
    ·
      refine ⟨15509485195465497044468633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339656796976998029645755 15509485195465497044468633)
      ·
        refine ⟨11632113896599122783351475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15509485195465497044468633 11632113896599122783351475)
        ·
          refine ⟨17448170844898684175027213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632113896599122783351475 17448170844898684175027213)
          ·
            refine ⟨6543064066837006565635205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17448170844898684175027213 6543064066837006565635205)
            ·
              refine ⟨1226824512531938731056601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6543064066837006565635205 1226824512531938731056601)
              ·
                refine ⟨920118384398954048292451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226824512531938731056601 920118384398954048292451)
                ·
                  refine ⟨1380177576598431072438677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920118384398954048292451 1380177576598431072438677)
                  ·
                    refine ⟨64695823903051456520563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1380177576598431072438677 64695823903051456520563)
                    ·
                      rfl

theorem cell23_377984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_377984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377984 prefixEnd_377984 := by exact prefixLift 377984
  have htrace : WordTrace (prefixWord ++ tailWord_377984) baseStart_377984 baseEnd_377984 := by
    simpa [prefixWord, tailWord_377984, baseEnd_377984] using wordTrace_append hprefix tailTrace_377984
  have hstable : (prefixWord ++ tailWord_377984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377984).length < 2 ^ (prefixWord ++ tailWord_377984).sum := by decide
  have hdescent : baseEnd_377984 < baseStart_377984 := by decide
  rcases family_descends (prefixWord ++ tailWord_377984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377985 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_377985 : Nat := 118140960795 + 377985 * 2 ^ 59
def prefixEnd_377985 : Nat := 4983230072969 + 3 ^ 40 * 377985 * 2
def baseEnd_377985 : Nat := 194087985189808865649185

theorem tailTrace_377985 : CollatzResearch.WordTrace tailWord_377985 prefixEnd_377985 194087985189808865649185 := by
  unfold tailWord_377985
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786245535632374543647409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9190830357088249695764939 13786245535632374543647409)
  ·
    refine ⟨10339684151724280907735557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13786245535632374543647409 10339684151724280907735557)
    ·
      refine ⟨1938690778448302670200417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10339684151724280907735557 1938690778448302670200417)
      ·
        refine ⟨1454018083836227002650313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1938690778448302670200417 1454018083836227002650313)
        ·
          refine ⟨1090513562877170251987735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454018083836227002650313 1090513562877170251987735)
          ·
            refine ⟨1635770344315755377981603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090513562877170251987735 1635770344315755377981603)
            ·
              refine ⟨2453655516473633066972405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635770344315755377981603 2453655516473633066972405)
              ·
                refine ⟨230030204669403100028663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2453655516473633066972405 230030204669403100028663)
                ·
                  refine ⟨345045307004104650042995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230030204669403100028663 345045307004104650042995)
                  ·
                    refine ⟨517567960506156975064493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345045307004104650042995 517567960506156975064493)
                    ·
                      refine ⟨194087985189808865649185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517567960506156975064493 194087985189808865649185)
                      ·
                        rfl

theorem cell23_377985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_377985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377985 prefixEnd_377985 := by exact prefixLift 377985
  have htrace : WordTrace (prefixWord ++ tailWord_377985) baseStart_377985 baseEnd_377985 := by
    simpa [prefixWord, tailWord_377985, baseEnd_377985] using wordTrace_append hprefix tailTrace_377985
  have hstable : (prefixWord ++ tailWord_377985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377985).length < 2 ^ (prefixWord ++ tailWord_377985).sum := by decide
  have hdescent : baseEnd_377985 < baseStart_377985 := by decide
  rcases family_descends (prefixWord ++ tailWord_377985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377988 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_377988 : Nat := 118140960795 + 377988 * 2 ^ 59
def prefixEnd_377988 : Nat := 4983230072969 + 3 ^ 40 * 377988 * 2
def baseEnd_377988 : Nat := 64696508543924117970557

theorem tailTrace_377988 : CollatzResearch.WordTrace tailWord_377988 prefixEnd_377988 64696508543924117970557 := by
  unfold tailWord_377988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893177477310753028003309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9190903303081004037337745 6893177477310753028003309)
  ·
    refine ⟨2584941553991532385501241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6893177477310753028003309 2584941553991532385501241)
    ·
      refine ⟨1938706165493649289125931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2584941553991532385501241 1938706165493649289125931)
      ·
        refine ⟨2908059248240473933688897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938706165493649289125931 2908059248240473933688897)
        ·
          refine ⟨2181044436180355450266673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2908059248240473933688897 2181044436180355450266673)
          ·
            refine ⟨1635783327135266587700005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181044436180355450266673 1635783327135266587700005)
            ·
              refine ⟨306709373837862485193751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1635783327135266587700005 306709373837862485193751)
              ·
                refine ⟨460064060756793727790627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306709373837862485193751 460064060756793727790627)
                ·
                  refine ⟨690096091135190591685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460064060756793727790627 690096091135190591685941)
                  ·
                    refine ⟨64696508543924117970557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 690096091135190591685941 64696508543924117970557)
                    ·
                      rfl

theorem cell23_377988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_377988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_377988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_377988 prefixEnd_377988 := by exact prefixLift 377988
  have htrace : WordTrace (prefixWord ++ tailWord_377988) baseStart_377988 baseEnd_377988 := by
    simpa [prefixWord, tailWord_377988, baseEnd_377988] using wordTrace_append hprefix tailTrace_377988
  have hstable : (prefixWord ++ tailWord_377988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377988).length < 2 ^ (prefixWord ++ tailWord_377988).sum := by decide
  have hdescent : baseEnd_377988 < baseStart_377988 := by decide
  rcases family_descends (prefixWord ++ tailWord_377988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378021 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_378021 : Nat := 118140960795 + 378021 * 2 ^ 59
def prefixEnd_378021 : Nat := 4983230072969 + 3 ^ 40 * 378021 * 2
def baseEnd_378021 : Nat := 194106470493370724799019

theorem tailTrace_378021 : CollatzResearch.WordTrace tailWord_378021 prefixEnd_378021 194106470493370724799019 := by
  unfold tailWord_378021
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787558563501952691957917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9191705709001301794638611 13787558563501952691957917)
  ·
    refine ⟨5170334461313232259484219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13787558563501952691957917 5170334461313232259484219)
    ·
      refine ⟨7755501691969848389226329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170334461313232259484219 7755501691969848389226329)
      ·
        refine ⟨5816626268977386291919747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7755501691969848389226329 5816626268977386291919747)
        ·
          refine ⟨8724939403466079437879621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816626268977386291919747 8724939403466079437879621)
          ·
            refine ⟨1635926138149889894602429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8724939403466079437879621 1635926138149889894602429)
            ·
              refine ⟨613472301806208710475911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635926138149889894602429 613472301806208710475911)
              ·
                refine ⟨920208452709313065713867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613472301806208710475911 920208452709313065713867)
                ·
                  refine ⟨1380312679063969598570801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920208452709313065713867 1380312679063969598570801)
                  ·
                    refine ⟨1035234509297977198928101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380312679063969598570801 1035234509297977198928101)
                    ·
                      refine ⟨194106470493370724799019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1035234509297977198928101 194106470493370724799019)
                      ·
                        rfl

theorem cell23_378021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_378021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378021 prefixEnd_378021 := by exact prefixLift 378021
  have htrace : WordTrace (prefixWord ++ tailWord_378021) baseStart_378021 baseEnd_378021 := by
    simpa [prefixWord, tailWord_378021, baseEnd_378021] using wordTrace_append hprefix tailTrace_378021
  have hstable : (prefixWord ++ tailWord_378021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378021).length < 2 ^ (prefixWord ++ tailWord_378021).sum := by decide
  have hdescent : baseEnd_378021 < baseStart_378021 := by decide
  rcases family_descends (prefixWord ++ tailWord_378021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378058 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_378058 : Nat := 118140960795 + 378058 * 2 ^ 59
def prefixEnd_378058 : Nat := 4983230072969 + 3 ^ 40 * 378058 * 2
def baseEnd_378058 : Nat := 194125469277587080036349

theorem tailTrace_378058 : CollatzResearch.WordTrace tailWord_378058 prefixEnd_378058 194125469277587080036349 := by
  unfold tailWord_378058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447227016091977002763707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9192605376245272007369885 3447227016091977002763707)
  ·
    refine ⟨5170840524137965504145561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447227016091977002763707 5170840524137965504145561)
    ·
      refine ⟨3878130393103474128109171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170840524137965504145561 3878130393103474128109171)
      ·
        refine ⟨5817195589655211192163757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878130393103474128109171 5817195589655211192163757)
        ·
          refine ⟨2181448346120704197061409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5817195589655211192163757 2181448346120704197061409)
          ·
            refine ⟨1636086259590528147796057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181448346120704197061409 1636086259590528147796057)
            ·
              refine ⟨1227064694692896110847043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636086259590528147796057 1227064694692896110847043)
              ·
                refine ⟨1840597042039344166270565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227064694692896110847043 1840597042039344166270565)
                ·
                  refine ⟨345111945382377031175731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840597042039344166270565 345111945382377031175731)
                  ·
                    refine ⟨517667918073565546763597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345111945382377031175731 517667918073565546763597)
                    ·
                      refine ⟨194125469277587080036349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517667918073565546763597 194125469277587080036349)
                      ·
                        rfl

theorem cell23_378058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_378058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378058 prefixEnd_378058 := by exact prefixLift 378058
  have htrace : WordTrace (prefixWord ++ tailWord_378058) baseStart_378058 baseEnd_378058 := by
    simpa [prefixWord, tailWord_378058, baseEnd_378058] using wordTrace_append hprefix tailTrace_378058
  have hstable : (prefixWord ++ tailWord_378058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378058).length < 2 ^ (prefixWord ++ tailWord_378058).sum := by decide
  have hdescent : baseEnd_378058 < baseStart_378058 := by decide
  rcases family_descends (prefixWord ++ tailWord_378058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378074 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_378074 : Nat := 118140960795 + 378074 * 2 ^ 59
def prefixEnd_378074 : Nat := 4983230072969 + 3 ^ 40 * 378074 * 2
def baseEnd_378074 : Nat := 64711228322686339145425

theorem tailTrace_378074 : CollatzResearch.WordTrace tailWord_378074 prefixEnd_378074 64711228322686339145425 := by
  unfold tailWord_378074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447372908077485685909319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9192994421539961829091517 3447372908077485685909319)
  ·
    refine ⟨5171059362116228528863979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447372908077485685909319 5171059362116228528863979)
    ·
      refine ⟨7756589043174342793295969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171059362116228528863979 7756589043174342793295969)
      ·
        refine ⟨5817441782380757094971977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756589043174342793295969 5817441782380757094971977)
        ·
          refine ⟨4363081336785567821228983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817441782380757094971977 4363081336785567821228983)
          ·
            refine ⟨6544622005178351731843475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363081336785567821228983 6544622005178351731843475)
            ·
              refine ⟨9816933007767527597765213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544622005178351731843475 9816933007767527597765213)
              ·
                refine ⟨3681349877912822849161955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9816933007767527597765213 3681349877912822849161955)
                ·
                  refine ⟨5522024816869234273742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681349877912822849161955 5522024816869234273742933)
                  ·
                    refine ⟨64711228322686339145425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5522024816869234273742933 64711228322686339145425)
                    ·
                      rfl

theorem cell23_378074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_378074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378074 prefixEnd_378074 := by exact prefixLift 378074
  have htrace : WordTrace (prefixWord ++ tailWord_378074) baseStart_378074 baseEnd_378074 := by
    simpa [prefixWord, tailWord_378074, baseEnd_378074] using wordTrace_append hprefix tailTrace_378074
  have hstable : (prefixWord ++ tailWord_378074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378074).length < 2 ^ (prefixWord ++ tailWord_378074).sum := by decide
  have hdescent : baseEnd_378074 < baseStart_378074 := by decide
  rcases family_descends (prefixWord ++ tailWord_378074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378085 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_378085 : Nat := 118140960795 + 378085 * 2 ^ 59
def prefixEnd_378085 : Nat := 4983230072969 + 3 ^ 40 * 378085 * 2
def baseEnd_378085 : Nat := 194139333255258474398725

theorem tailTrace_378085 : CollatzResearch.WordTrace tailWord_378085 prefixEnd_378085 194139333255258474398725 := by
  unfold tailWord_378085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789892835270091622287709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9193261890180061081525139 13789892835270091622287709)
  ·
    refine ⟨5171209813226284358357891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13789892835270091622287709 5171209813226284358357891)
    ·
      refine ⟨7756814719839426537536837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171209813226284358357891 7756814719839426537536837)
      ·
        refine ⟨1454402759969892475788157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7756814719839426537536837 1454402759969892475788157)
        ·
          refine ⟨545401034988709678420559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1454402759969892475788157 545401034988709678420559)
          ·
            refine ⟨818101552483064517630839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545401034988709678420559 818101552483064517630839)
            ·
              refine ⟨1227152328724596776446259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818101552483064517630839 1227152328724596776446259)
              ·
                refine ⟨1840728493086895164669389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227152328724596776446259 1840728493086895164669389)
                ·
                  refine ⟨690273184907585686751021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1840728493086895164669389 690273184907585686751021)
                  ·
                    refine ⟨258852444340344632531633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690273184907585686751021 258852444340344632531633)
                    ·
                      refine ⟨194139333255258474398725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258852444340344632531633 194139333255258474398725)
                      ·
                        rfl

theorem cell23_378085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_378085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378085 prefixEnd_378085 := by exact prefixLift 378085
  have htrace : WordTrace (prefixWord ++ tailWord_378085) baseStart_378085 baseEnd_378085 := by
    simpa [prefixWord, tailWord_378085, baseEnd_378085] using wordTrace_append hprefix tailTrace_378085
  have hstable : (prefixWord ++ tailWord_378085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378085).length < 2 ^ (prefixWord ++ tailWord_378085).sum := by decide
  have hdescent : baseEnd_378085 < baseStart_378085 := by decide
  rcases family_descends (prefixWord ++ tailWord_378085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378115 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 2, 2, 2]
def baseStart_378115 : Nat := 118140960795 + 378115 * 2 ^ 59
def prefixEnd_378115 : Nat := 4983230072969 + 3 ^ 40 * 378115 * 2
def baseEnd_378115 : Nat := 194154737674893357023587

theorem tailTrace_378115 : CollatzResearch.WordTrace tailWord_378115 prefixEnd_378115 194154737674893357023587 := by
  unfold tailWord_378115
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790987025161406745879799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9193991350107604497253199 13790987025161406745879799)
  ·
    refine ⟨20686480537742110118819699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13790987025161406745879799 20686480537742110118819699)
    ·
      refine ⟨31029720806613165178229549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20686480537742110118819699 31029720806613165178229549)
      ·
        refine ⟨11636145302479936941836081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31029720806613165178229549 11636145302479936941836081)
        ·
          refine ⟨8727108976859952706377061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11636145302479936941836081 8727108976859952706377061)
          ·
            refine ⟨1636332933161241132445699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8727108976859952706377061 1636332933161241132445699)
            ·
              refine ⟨2454499399741861698668549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636332933161241132445699 2454499399741861698668549)
              ·
                refine ⟨460218637451599068500353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2454499399741861698668549 460218637451599068500353)
                ·
                  refine ⟨345163978088699301375265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460218637451599068500353 345163978088699301375265)
                  ·
                    refine ⟨258872983566524476031449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345163978088699301375265 258872983566524476031449)
                    ·
                      refine ⟨194154737674893357023587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258872983566524476031449 194154737674893357023587)
                      ·
                        rfl

theorem cell23_378115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_378115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378115 prefixEnd_378115 := by exact prefixLift 378115
  have htrace : WordTrace (prefixWord ++ tailWord_378115) baseStart_378115 baseEnd_378115 := by
    simpa [prefixWord, tailWord_378115, baseEnd_378115] using wordTrace_append hprefix tailTrace_378115
  have hstable : (prefixWord ++ tailWord_378115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378115).length < 2 ^ (prefixWord ++ tailWord_378115).sum := by decide
  have hdescent : baseEnd_378115 < baseStart_378115 := by decide
  rcases family_descends (prefixWord ++ tailWord_378115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378208 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_378208 : Nat := 118140960795 + 378208 * 2 ^ 59
def prefixEnd_378208 : Nat := 4983230072969 + 3 ^ 40 * 378208 * 2
def baseEnd_378208 : Nat := 194202491375761493160659

theorem tailTrace_378208 : CollatzResearch.WordTrace tailWord_378208 prefixEnd_378208 194202491375761493160659 := by
  unfold tailWord_378208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897189506912241814507639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9196252675882989086010185 6897189506912241814507639)
  ·
    refine ⟨10345784260368362721761459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6897189506912241814507639 10345784260368362721761459)
    ·
      refine ⟨15518676390552544082642189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345784260368362721761459 15518676390552544082642189)
      ·
        refine ⟨5819503646457204030990821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15518676390552544082642189 5819503646457204030990821)
        ·
          refine ⟨1091156933710725755810779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5819503646457204030990821 1091156933710725755810779)
          ·
            refine ⟨1636735400566088633716169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091156933710725755810779 1636735400566088633716169)
            ·
              refine ⟨1227551550424566475287127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636735400566088633716169 1227551550424566475287127)
              ·
                refine ⟨1841327325636849712930691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227551550424566475287127 1841327325636849712930691)
                ·
                  refine ⟨2761990988455274569396037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841327325636849712930691 2761990988455274569396037)
                  ·
                    refine ⟨517873310335363981761757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761990988455274569396037 517873310335363981761757)
                    ·
                      refine ⟨194202491375761493160659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517873310335363981761757 194202491375761493160659)
                      ·
                        rfl

theorem cell23_378208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_378208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378208 prefixEnd_378208 := by exact prefixLift 378208
  have htrace : WordTrace (prefixWord ++ tailWord_378208) baseStart_378208 baseEnd_378208 := by
    simpa [prefixWord, tailWord_378208, baseEnd_378208] using wordTrace_append hprefix tailTrace_378208
  have hstable : (prefixWord ++ tailWord_378208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378208).length < 2 ^ (prefixWord ++ tailWord_378208).sum := by decide
  have hdescent : baseEnd_378208 < baseStart_378208 := by decide
  rcases family_descends (prefixWord ++ tailWord_378208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378211 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 8]
def baseStart_378211 : Nat := 118140960795 + 378211 * 2 ^ 59
def prefixEnd_378211 : Nat := 4983230072969 + 3 ^ 40 * 378211 * 2
def baseEnd_378211 : Nat := 21578225757524997935905

theorem tailTrace_378211 : CollatzResearch.WordTrace tailWord_378211 prefixEnd_378211 21578225757524997935905 := by
  unfold tailWord_378211
  simp only [CollatzResearch.WordTrace]
  refine ⟨13794488432813615141374487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9196325621875743427582991 13794488432813615141374487)
  ·
    refine ⟨20691732649220422712061731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13794488432813615141374487 20691732649220422712061731)
    ·
      refine ⟨31037598973830634068092597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20691732649220422712061731 31037598973830634068092597)
      ·
        refine ⟨2909774903796621943883681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31037598973830634068092597 2909774903796621943883681)
        ·
          refine ⟨2182331177847466457912761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2909774903796621943883681 2182331177847466457912761)
          ·
            refine ⟨1636748383385599843434571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182331177847466457912761 1636748383385599843434571)
            ·
              refine ⟨2455122575078399765151857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636748383385599843434571 2455122575078399765151857)
              ·
                refine ⟨1841341931308799823863893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455122575078399765151857 1841341931308799823863893)
                ·
                  refine ⟨21578225757524997935905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1841341931308799823863893 21578225757524997935905)
                  ·
                    rfl

theorem cell23_378211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 8].length) (baseStart_378211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378211 prefixEnd_378211 := by exact prefixLift 378211
  have htrace : WordTrace (prefixWord ++ tailWord_378211) baseStart_378211 baseEnd_378211 := by
    simpa [prefixWord, tailWord_378211, baseEnd_378211] using wordTrace_append hprefix tailTrace_378211
  have hstable : (prefixWord ++ tailWord_378211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378211).length < 2 ^ (prefixWord ++ tailWord_378211).sum := by decide
  have hdescent : baseEnd_378211 < baseStart_378211 := by decide
  rcases family_descends (prefixWord ++ tailWord_378211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378222 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_378222 : Nat := 118140960795 + 378222 * 2 ^ 59
def prefixEnd_378222 : Nat := 4983230072969 + 3 ^ 40 * 378222 * 2
def baseEnd_378222 : Nat := 194209680104924438385595

theorem tailTrace_378222 : CollatzResearch.WordTrace tailWord_378222 prefixEnd_378222 194209680104924438385595 := by
  unfold tailWord_378222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724361204471720502503115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9196593090515842680016613 1724361204471720502503115)
  ·
    refine ⟨2586541806707580753754673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1724361204471720502503115 2586541806707580753754673)
    ·
      refine ⟨1939906355030685565316005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2586541806707580753754673 1939906355030685565316005)
      ·
        refine ⟨363732441568253543496751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1939906355030685565316005 363732441568253543496751)
        ·
          refine ⟨545598662352380315245127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363732441568253543496751 545598662352380315245127)
          ·
            refine ⟨818397993528570472867691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545598662352380315245127 818397993528570472867691)
            ·
              refine ⟨1227596990292855709301537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818397993528570472867691 1227596990292855709301537)
              ·
                refine ⟨920697742719641781976153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227596990292855709301537 920697742719641781976153)
                ·
                  refine ⟨690523307039731336482115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920697742719641781976153 690523307039731336482115)
                  ·
                    refine ⟨1035784960559597004723173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690523307039731336482115 1035784960559597004723173)
                    ·
                      refine ⟨194209680104924438385595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1035784960559597004723173 194209680104924438385595)
                      ·
                        rfl

theorem cell23_378222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_378222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378222 prefixEnd_378222 := by exact prefixLift 378222
  have htrace : WordTrace (prefixWord ++ tailWord_378222) baseStart_378222 baseEnd_378222 := by
    simpa [prefixWord, tailWord_378222, baseEnd_378222] using wordTrace_append hprefix tailTrace_378222
  have hstable : (prefixWord ++ tailWord_378222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378222).length < 2 ^ (prefixWord ++ tailWord_378222).sum := by decide
  have hdescent : baseEnd_378222 < baseStart_378222 := by decide
  rcases family_descends (prefixWord ++ tailWord_378222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378265 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 2, 3, 2]
def baseStart_378265 : Nat := 118140960795 + 378265 * 2 ^ 59
def prefixEnd_378265 : Nat := 4983230072969 + 3 ^ 40 * 378265 * 2
def baseEnd_378265 : Nat := 194231759773067770147897

theorem tailTrace_378265 : CollatzResearch.WordTrace tailWord_378265 prefixEnd_378265 194231759773067770147897 := by
  unfold tailWord_378265
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796457974617982363840249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9197638649745321575893499 13796457974617982363840249)
  ·
    refine ⟨10347343480963486772880187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13796457974617982363840249 10347343480963486772880187)
    ·
      refine ⟨15521015221445230159320281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347343480963486772880187 15521015221445230159320281)
      ·
        refine ⟨11640761416083922619490211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15521015221445230159320281 11640761416083922619490211)
        ·
          refine ⟨17461142124125883929235317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11640761416083922619490211 17461142124125883929235317)
          ·
            refine ⟨1636982074136801618365811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17461142124125883929235317 1636982074136801618365811)
            ·
              refine ⟨2455473111205202427548717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636982074136801618365811 2455473111205202427548717)
              ·
                refine ⟨920802416701950910330769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2455473111205202427548717 920802416701950910330769)
                ·
                  refine ⟨690601812526463182748077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920802416701950910330769 690601812526463182748077)
                  ·
                    refine ⟨258975679697423693530529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690601812526463182748077 258975679697423693530529)
                    ·
                      refine ⟨194231759773067770147897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 258975679697423693530529 194231759773067770147897)
                      ·
                        rfl

theorem cell23_378265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_378265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378265 prefixEnd_378265 := by exact prefixLift 378265
  have htrace : WordTrace (prefixWord ++ tailWord_378265) baseStart_378265 baseEnd_378265 := by
    simpa [prefixWord, tailWord_378265, baseEnd_378265] using wordTrace_append hprefix tailTrace_378265
  have hstable : (prefixWord ++ tailWord_378265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378265).length < 2 ^ (prefixWord ++ tailWord_378265).sum := by decide
  have hdescent : baseEnd_378265 < baseStart_378265 := by decide
  rcases family_descends (prefixWord ++ tailWord_378265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378272 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 1, 1, 3]
def baseStart_378272 : Nat := 118140960795 + 378272 * 2 ^ 59
def prefixEnd_378272 : Nat := 4983230072969 + 3 ^ 40 * 378272 * 2
def baseEnd_378272 : Nat := 194235354137649242760365

theorem tailTrace_378272 : CollatzResearch.WordTrace tailWord_378272 prefixEnd_378272 194235354137649242760365 := by
  unfold tailWord_378272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898356642796311279672535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9197808857061748372896713 6898356642796311279672535)
  ·
    refine ⟨10347534964194466919508803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6898356642796311279672535 10347534964194466919508803)
    ·
      refine ⟨15521302446291700379263205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347534964194466919508803 15521302446291700379263205)
      ·
        refine ⟨2910244208679693821111851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15521302446291700379263205 2910244208679693821111851)
        ·
          refine ⟨4365366313019540731667777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910244208679693821111851 4365366313019540731667777)
          ·
            refine ⟨3274024734764655548750833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4365366313019540731667777 3274024734764655548750833)
            ·
              refine ⟨2455518551073491661563125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274024734764655548750833 2455518551073491661563125)
              ·
                refine ⟨230204864163139843271543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2455518551073491661563125 230204864163139843271543)
                ·
                  refine ⟨345307296244709764907315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230204864163139843271543 345307296244709764907315)
                  ·
                    refine ⟨517960944367064647360973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345307296244709764907315 517960944367064647360973)
                    ·
                      refine ⟨194235354137649242760365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 517960944367064647360973 194235354137649242760365)
                      ·
                        rfl

theorem cell23_378272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_378272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378272 prefixEnd_378272 := by exact prefixLift 378272
  have htrace : WordTrace (prefixWord ++ tailWord_378272) baseStart_378272 baseEnd_378272 := by
    simpa [prefixWord, tailWord_378272, baseEnd_378272] using wordTrace_append hprefix tailTrace_378272
  have hstable : (prefixWord ++ tailWord_378272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378272).length < 2 ^ (prefixWord ++ tailWord_378272).sum := by decide
  have hdescent : baseEnd_378272 < baseStart_378272 := by decide
  rcases family_descends (prefixWord ++ tailWord_378272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378275 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 1, 5]
def baseStart_378275 : Nat := 118140960795 + 378275 * 2 ^ 59
def prefixEnd_378275 : Nat := 4983230072969 + 3 ^ 40 * 378275 * 2
def baseEnd_378275 : Nat := 64745631526537577007617

theorem tailTrace_378275 : CollatzResearch.WordTrace tailWord_378275 prefixEnd_378275 64745631526537577007617 := by
  unfold tailWord_378275
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796822704581754071704279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9197881803054502714469519 13796822704581754071704279)
  ·
    refine ⟨20695234056872631107556419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13796822704581754071704279 20695234056872631107556419)
    ·
      refine ⟨31042851085308946661334629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20695234056872631107556419 31042851085308946661334629)
      ·
        refine ⟨5820534578495427499000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31042851085308946661334629 5820534578495427499000243)
        ·
          refine ⟨8730801867743141248500365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820534578495427499000243 8730801867743141248500365)
          ·
            refine ⟨3274050700403677968187637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8730801867743141248500365 3274050700403677968187637)
            ·
              refine ⟨306942253162844809517591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3274050700403677968187637 306942253162844809517591)
              ·
                refine ⟨460413379744267214276387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306942253162844809517591 460413379744267214276387)
                ·
                  refine ⟨690620069616400821414581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460413379744267214276387 690620069616400821414581)
                  ·
                    refine ⟨64745631526537577007617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 690620069616400821414581 64745631526537577007617)
                    ·
                      rfl

theorem cell23_378275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 5].length) (baseStart_378275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378275 prefixEnd_378275 := by exact prefixLift 378275
  have htrace : WordTrace (prefixWord ++ tailWord_378275) baseStart_378275 baseEnd_378275 := by
    simpa [prefixWord, tailWord_378275, baseEnd_378275] using wordTrace_append hprefix tailTrace_378275
  have hstable : (prefixWord ++ tailWord_378275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378275).length < 2 ^ (prefixWord ++ tailWord_378275).sum := by decide
  have hdescent : baseEnd_378275 < baseStart_378275 := by decide
  rcases family_descends (prefixWord ++ tailWord_378275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378291 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_378291 : Nat := 118140960795 + 378291 * 2 ^ 59
def prefixEnd_378291 : Nat := 4983230072969 + 3 ^ 40 * 378291 * 2
def baseEnd_378291 : Nat := 194245110270084668422777

theorem tailTrace_378291 : CollatzResearch.WordTrace tailWord_378291 prefixEnd_378291 194245110270084668422777 := by
  unfold tailWord_378291
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797406272523788804286727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9198270848349192536191151 13797406272523788804286727)
  ·
    refine ⟨20696109408785683206430091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13797406272523788804286727 20696109408785683206430091)
    ·
      refine ⟨31044164113178524809645137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20696109408785683206430091 31044164113178524809645137)
      ·
        refine ⟨23283123084883893607233853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31044164113178524809645137 23283123084883893607233853)
        ·
          refine ⟨8731171156831460102712695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23283123084883893607233853 8731171156831460102712695)
          ·
            refine ⟨13096756735247190154069043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731171156831460102712695 13096756735247190154069043)
            ·
              refine ⟨19645135102870785231103565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096756735247190154069043 19645135102870785231103565)
              ·
                refine ⟨7366925663576544461663837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19645135102870785231103565 7366925663576544461663837)
                ·
                  refine ⟨2762597123841204173123939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7366925663576544461663837 2762597123841204173123939)
                  ·
                    refine ⟨4143895685761806259685909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2762597123841204173123939 4143895685761806259685909)
                    ·
                      refine ⟨194245110270084668422777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4143895685761806259685909 194245110270084668422777)
                      ·
                        rfl

theorem cell23_378291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_378291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378291 prefixEnd_378291 := by exact prefixLift 378291
  have htrace : WordTrace (prefixWord ++ tailWord_378291) baseStart_378291 baseEnd_378291 := by
    simpa [prefixWord, tailWord_378291, baseEnd_378291] using wordTrace_append hprefix tailTrace_378291
  have hstable : (prefixWord ++ tailWord_378291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378291).length < 2 ^ (prefixWord ++ tailWord_378291).sum := by decide
  have hdescent : baseEnd_378291 < baseStart_378291 := by decide
  rcases family_descends (prefixWord ++ tailWord_378291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378312 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_378312 : Nat := 118140960795 + 378312 * 2 ^ 59
def prefixEnd_378312 : Nat := 4983230072969 + 3 ^ 40 * 378312 * 2
def baseEnd_378312 : Nat := 194255893363829086260181

theorem tailTrace_378312 : CollatzResearch.WordTrace tailWord_378312 prefixEnd_378312 194255893363829086260181 := by
  unfold tailWord_378312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899086102723854695400595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9198781470298472927200793 6899086102723854695400595)
  ·
    refine ⟨10348629154085782043100893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899086102723854695400595 10348629154085782043100893)
    ·
      refine ⟨3880735932782168266162835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10348629154085782043100893 3880735932782168266162835)
      ·
        refine ⟨5821103899173252399244253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880735932782168266162835 5821103899173252399244253)
        ·
          refine ⟨2182913962189969649716595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5821103899173252399244253 2182913962189969649716595)
          ·
            refine ⟨3274370943284954474574893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182913962189969649716595 3274370943284954474574893)
            ·
              refine ⟨1227889103731857927965585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3274370943284954474574893 1227889103731857927965585)
              ·
                refine ⟨920916827798893445974189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227889103731857927965585 920916827798893445974189)
                ·
                  refine ⟨345343810424585042240321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920916827798893445974189 345343810424585042240321)
                  ·
                    refine ⟨259007857818438781680241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345343810424585042240321 259007857818438781680241)
                    ·
                      refine ⟨194255893363829086260181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259007857818438781680241 194255893363829086260181)
                      ·
                        rfl

theorem cell23_378312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_378312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378312 prefixEnd_378312 := by exact prefixLift 378312
  have htrace : WordTrace (prefixWord ++ tailWord_378312) baseStart_378312 baseEnd_378312 := by
    simpa [prefixWord, tailWord_378312, baseEnd_378312] using wordTrace_append hprefix tailTrace_378312
  have hstable : (prefixWord ++ tailWord_378312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378312).length < 2 ^ (prefixWord ++ tailWord_378312).sum := by decide
  have hdescent : baseEnd_378312 < baseStart_378312 := by decide
  rcases family_descends (prefixWord ++ tailWord_378312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378329 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 1, 2, 2]
def baseStart_378329 : Nat := 118140960795 + 378329 * 2 ^ 59
def prefixEnd_378329 : Nat := 4983230072969 + 3 ^ 40 * 378329 * 2
def baseEnd_378329 : Nat := 194264622534955519747603

theorem tailTrace_378329 : CollatzResearch.WordTrace tailWord_378329 prefixEnd_378329 194264622534955519747603 := by
  unfold tailWord_378329
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798792246386121294170041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9199194830924080862780027 13798792246386121294170041)
  ·
    refine ⟨10349094184789590970627531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13798792246386121294170041 10349094184789590970627531)
    ·
      refine ⟨15523641277184386455941297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10349094184789590970627531 15523641277184386455941297)
      ·
        refine ⟨11642730957888289841955973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15523641277184386455941297 11642730957888289841955973)
        ·
          refine ⟨2183012054604054345366745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11642730957888289841955973 2183012054604054345366745)
          ·
            refine ⟨1637259040953040759025059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183012054604054345366745 1637259040953040759025059)
            ·
              refine ⟨2455888561429561138537589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637259040953040759025059 2455888561429561138537589)
              ·
                refine ⟨230239552634021356737899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2455888561429561138537589 230239552634021356737899)
                ·
                  refine ⟨345359328951032035106849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230239552634021356737899 345359328951032035106849)
                  ·
                    refine ⟨259019496713274026330137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345359328951032035106849 259019496713274026330137)
                    ·
                      refine ⟨194264622534955519747603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259019496713274026330137 194264622534955519747603)
                      ·
                        rfl

theorem cell23_378329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_378329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378329 prefixEnd_378329 := by exact prefixLift 378329
  have htrace : WordTrace (prefixWord ++ tailWord_378329) baseStart_378329 baseEnd_378329 := by
    simpa [prefixWord, tailWord_378329, baseEnd_378329] using wordTrace_append hprefix tailTrace_378329
  have hstable : (prefixWord ++ tailWord_378329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378329).length < 2 ^ (prefixWord ++ tailWord_378329).sum := by decide
  have hdescent : baseEnd_378329 < baseStart_378329 := by decide
  rcases family_descends (prefixWord ++ tailWord_378329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378355 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 3, 3, 2]
def baseStart_378355 : Nat := 118140960795 + 378355 * 2 ^ 59
def prefixEnd_378355 : Nat := 4983230072969 + 3 ^ 40 * 378355 * 2
def baseEnd_378355 : Nat := 194277973031972418022483

theorem tailTrace_378355 : CollatzResearch.WordTrace tailWord_378355 prefixEnd_378355 194277973031972418022483 := by
  unfold tailWord_378355
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799740544291927734616519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9199827029527951823077679 13799740544291927734616519)
  ·
    refine ⟨20699610816437891601924779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13799740544291927734616519 20699610816437891601924779)
    ·
      refine ⟨31049416224656837402887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20699610816437891601924779 31049416224656837402887169)
      ·
        refine ⟨23287062168492628052165377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31049416224656837402887169 23287062168492628052165377)
        ·
          refine ⟨17465296626369471039124033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23287062168492628052165377 17465296626369471039124033)
          ·
            refine ⟨13098972469777103279343025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17465296626369471039124033 13098972469777103279343025)
            ·
              refine ⟨9824229352332827459507269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13098972469777103279343025 9824229352332827459507269)
              ·
                refine ⟨1842043003562405148657613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9824229352332827459507269 1842043003562405148657613)
                ·
                  refine ⟨690766126335901930746605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1842043003562405148657613 690766126335901930746605)
                  ·
                    refine ⟨259037297375963224029977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690766126335901930746605 259037297375963224029977)
                    ·
                      refine ⟨194277973031972418022483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259037297375963224029977 194277973031972418022483)
                      ·
                        rfl

theorem cell23_378355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3, 2].length) (baseStart_378355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378355 prefixEnd_378355 := by exact prefixLift 378355
  have htrace : WordTrace (prefixWord ++ tailWord_378355) baseStart_378355 baseEnd_378355 := by
    simpa [prefixWord, tailWord_378355, baseEnd_378355] using wordTrace_append hprefix tailTrace_378355
  have hstable : (prefixWord ++ tailWord_378355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378355).length < 2 ^ (prefixWord ++ tailWord_378355).sum := by decide
  have hdescent : baseEnd_378355 < baseStart_378355 := by decide
  rcases family_descends (prefixWord ++ tailWord_378355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378366 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_378366 : Nat := 118140960795 + 378366 * 2 ^ 59
def prefixEnd_378366 : Nat := 4983230072969 + 3 ^ 40 * 378366 * 2
def baseEnd_378366 : Nat := 194283621319171874984933

theorem tailTrace_378366 : CollatzResearch.WordTrace tailWord_378366 prefixEnd_378366 194283621319171874984933 := by
  unfold tailWord_378366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725017718406509576658369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9200094498168051075511301 1725017718406509576658369)
  ·
    refine ⟨1293763288804882182493777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1725017718406509576658369 1293763288804882182493777)
    ·
      refine ⟨970322466603661636870333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1293763288804882182493777 970322466603661636870333)
      ·
        refine ⟨363870924976373113826375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 970322466603661636870333 363870924976373113826375)
        ·
          refine ⟨545806387464559670739563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363870924976373113826375 545806387464559670739563)
          ·
            refine ⟨818709581196839506109345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545806387464559670739563 818709581196839506109345)
            ·
              refine ⟨614032185897629629582009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818709581196839506109345 614032185897629629582009)
              ·
                refine ⟨460524139423222222186507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614032185897629629582009 460524139423222222186507)
                ·
                  refine ⟨690786209134833333279761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460524139423222222186507 690786209134833333279761)
                  ·
                    refine ⟨518089656851124999959821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690786209134833333279761 518089656851124999959821)
                    ·
                      refine ⟨194283621319171874984933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 518089656851124999959821 194283621319171874984933)
                      ·
                        rfl

theorem cell23_378366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_378366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378366 prefixEnd_378366 := by exact prefixLift 378366
  have htrace : WordTrace (prefixWord ++ tailWord_378366) baseStart_378366 baseEnd_378366 := by
    simpa [prefixWord, tailWord_378366, baseEnd_378366] using wordTrace_append hprefix tailTrace_378366
  have hstable : (prefixWord ++ tailWord_378366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378366).length < 2 ^ (prefixWord ++ tailWord_378366).sum := by decide
  have hdescent : baseEnd_378366 < baseStart_378366 := by decide
  rcases family_descends (prefixWord ++ tailWord_378366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378385 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_378385 : Nat := 118140960795 + 378385 * 2 ^ 59
def prefixEnd_378385 : Nat := 4983230072969 + 3 ^ 40 * 378385 * 2
def baseEnd_378385 : Nat := 194293377451607300647345

theorem tailTrace_378385 : CollatzResearch.WordTrace tailWord_378385 prefixEnd_378385 194293377451607300647345 := by
  unfold tailWord_378385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800834734183242858208609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9200556489455495238805739 13800834734183242858208609)
  ·
    refine ⟨10350626050637432143656457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13800834734183242858208609 10350626050637432143656457)
    ·
      refine ⟨7762969537978074107742343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10350626050637432143656457 7762969537978074107742343)
      ·
        refine ⟨11644454306967111161613515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762969537978074107742343 11644454306967111161613515)
        ·
          refine ⟨17466681460450666742420273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644454306967111161613515 17466681460450666742420273)
          ·
            refine ⟨13100011095338000056815205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17466681460450666742420273 13100011095338000056815205)
            ·
              refine ⟨2456252080375875010652851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13100011095338000056815205 2456252080375875010652851)
              ·
                refine ⟨3684378120563812515979277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456252080375875010652851 3684378120563812515979277)
                ·
                  refine ⟨1381641795211429693492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3684378120563812515979277 1381641795211429693492229)
                  ·
                    refine ⟨259057836602143067529793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381641795211429693492229 259057836602143067529793)
                    ·
                      refine ⟨194293377451607300647345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259057836602143067529793 194293377451607300647345)
                      ·
                        rfl

theorem cell23_378385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_378385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378385 prefixEnd_378385 := by exact prefixLift 378385
  have htrace : WordTrace (prefixWord ++ tailWord_378385) baseStart_378385 baseEnd_378385 := by
    simpa [prefixWord, tailWord_378385, baseEnd_378385] using wordTrace_append hprefix tailTrace_378385
  have hstable : (prefixWord ++ tailWord_378385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378385).length < 2 ^ (prefixWord ++ tailWord_378385).sum := by decide
  have hdescent : baseEnd_378385 < baseStart_378385 := by decide
  rcases family_descends (prefixWord ++ tailWord_378385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378419 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 2, 2, 2]
def baseStart_378419 : Nat := 118140960795 + 378419 * 2 ^ 59
def prefixEnd_378419 : Nat := 4983230072969 + 3 ^ 40 * 378419 * 2
def baseEnd_378419 : Nat := 194310835793860167622189

theorem tailTrace_378419 : CollatzResearch.WordTrace tailWord_378419 prefixEnd_378419 194310835793860167622189 := by
  unfold tailWord_378419
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802074816060066664946311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9201383210706711109964207 13802074816060066664946311)
  ·
    refine ⟨20703112224090099997419467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13802074816060066664946311 20703112224090099997419467)
    ·
      refine ⟨31054668336135149996129201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20703112224090099997419467 31054668336135149996129201)
      ·
        refine ⟨23291001252101362497096901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31054668336135149996129201 23291001252101362497096901)
        ·
          refine ⟨4367062734769005468205669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23291001252101362497096901 4367062734769005468205669)
          ·
            refine ⟨818824262769188525288563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4367062734769005468205669 818824262769188525288563)
            ·
              refine ⟨1228236394153782787932845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818824262769188525288563 1228236394153782787932845)
              ·
                refine ⟨460588647807668545474817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228236394153782787932845 460588647807668545474817)
                ·
                  refine ⟨345441485855751409106113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460588647807668545474817 345441485855751409106113)
                  ·
                    refine ⟨259081114391813556829585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345441485855751409106113 259081114391813556829585)
                    ·
                      refine ⟨194310835793860167622189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259081114391813556829585 194310835793860167622189)
                      ·
                        rfl

theorem cell23_378419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2, 2].length) (baseStart_378419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378419 prefixEnd_378419 := by exact prefixLift 378419
  have htrace : WordTrace (prefixWord ++ tailWord_378419) baseStart_378419 baseEnd_378419 := by
    simpa [prefixWord, tailWord_378419, baseEnd_378419] using wordTrace_append hprefix tailTrace_378419
  have hstable : (prefixWord ++ tailWord_378419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378419).length < 2 ^ (prefixWord ++ tailWord_378419).sum := by decide
  have hdescent : baseEnd_378419 < baseStart_378419 := by decide
  rcases family_descends (prefixWord ++ tailWord_378419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378448 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_378448 : Nat := 118140960795 + 378448 * 2 ^ 59
def prefixEnd_378448 : Nat := 4983230072969 + 3 ^ 40 * 378448 * 2
def baseEnd_378448 : Nat := 194325726732840554159555

theorem tailTrace_378448 : CollatzResearch.WordTrace tailWord_378448 prefixEnd_378448 194325726732840554159555 := by
  unfold tailWord_378448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901566266477502308875999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9202088355303336411834665 6901566266477502308875999)
  ·
    refine ⟨10352349399716253463313999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6901566266477502308875999 10352349399716253463313999)
    ·
      refine ⟨15528524099574380194970999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352349399716253463313999 15528524099574380194970999)
      ·
        refine ⟨23292786149361570292456499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15528524099574380194970999 23292786149361570292456499)
        ·
          refine ⟨34939179224042355438684749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23292786149361570292456499 34939179224042355438684749)
          ·
            refine ⟨13102192209015883289506781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34939179224042355438684749 13102192209015883289506781)
            ·
              refine ⟨4913322078380956233565043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13102192209015883289506781 4913322078380956233565043)
              ·
                refine ⟨7369983117571434350347565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913322078380956233565043 7369983117571434350347565)
                ·
                  refine ⟨2763743669089287881380337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7369983117571434350347565 2763743669089287881380337)
                  ·
                    refine ⟨2072807751816965911035253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763743669089287881380337 2072807751816965911035253)
                    ·
                      refine ⟨194325726732840554159555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2072807751816965911035253 194325726732840554159555)
                      ·
                        rfl

theorem cell23_378448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_378448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378448 prefixEnd_378448 := by exact prefixLift 378448
  have htrace : WordTrace (prefixWord ++ tailWord_378448) baseStart_378448 baseEnd_378448 := by
    simpa [prefixWord, tailWord_378448, baseEnd_378448] using wordTrace_append hprefix tailTrace_378448
  have hstable : (prefixWord ++ tailWord_378448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378448).length < 2 ^ (prefixWord ++ tailWord_378448).sum := by decide
  have hdescent : baseEnd_378448 < baseStart_378448 := by decide
  rcases family_descends (prefixWord ++ tailWord_378448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
