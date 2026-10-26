import V185TrunkScan23Chunk0628

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3719624 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_3719624 : Nat := 118140960795 + 3719624 * 2 ^ 59
def prefixEnd_3719624 : Nat := 4983230072969 + 3 ^ 40 * 3719624 * 2
def baseEnd_3719624 : Nat := 1909954965999460187693767

theorem tailTrace_3719624 : CollatzResearch.WordTrace tailWord_3719624 prefixEnd_3719624 1909954965999460187693767 := by
  unfold tailWord_3719624
  simp only [CollatzResearch.WordTrace]
  refine ⟨67832916338222492024290963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90443888450963322699054617 67832916338222492024290963)
  ·
    refine ⟨101749374507333738036436445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67832916338222492024290963 101749374507333738036436445)
    ·
      refine ⟨38156015440250151763663667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101749374507333738036436445 38156015440250151763663667)
      ·
        refine ⟨57234023160375227645495501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38156015440250151763663667 57234023160375227645495501)
        ·
          refine ⟨21462758685140710367060813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57234023160375227645495501 21462758685140710367060813)
          ·
            refine ⟨8048534506927766387647805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21462758685140710367060813 8048534506927766387647805)
            ·
              refine ⟨3018200440097912395367927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8048534506927766387647805 3018200440097912395367927)
              ·
                refine ⟨4527300660146868593051891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018200440097912395367927 4527300660146868593051891)
                ·
                  refine ⟨6790950990220302889577837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527300660146868593051891 6790950990220302889577837)
                  ·
                    refine ⟨2546606621332613583591689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6790950990220302889577837 2546606621332613583591689)
                    ·
                      refine ⟨1909954965999460187693767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546606621332613583591689 1909954965999460187693767)
                      ·
                        rfl

theorem cell23_3719624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_3719624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719624 prefixEnd_3719624 := by exact prefixLift 3719624
  have htrace : WordTrace (prefixWord ++ tailWord_3719624) baseStart_3719624 baseEnd_3719624 := by
    simpa [prefixWord, tailWord_3719624, baseEnd_3719624] using wordTrace_append hprefix tailTrace_3719624
  have hstable : (prefixWord ++ tailWord_3719624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719624).length < 2 ^ (prefixWord ++ tailWord_3719624).sum := by decide
  have hdescent : baseEnd_3719624 < baseStart_3719624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719670 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3719670 : Nat := 118140960795 + 3719670 * 2 ^ 59
def prefixEnd_3719670 : Nat := 4983230072969 + 3 ^ 40 * 3719670 * 2
def baseEnd_3719670 : Nat := 1909978586109567007718555

theorem tailTrace_3719670 : CollatzResearch.WordTrace tailWord_3719670 prefixEnd_3719670 1909978586109567007718555 := by
  unfold tailWord_3719670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479219402142395869047279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90445006956185555936504309 8479219402142395869047279)
  ·
    refine ⟨12718829103213593803570919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479219402142395869047279 12718829103213593803570919)
    ·
      refine ⟨19078243654820390705356379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718829103213593803570919 19078243654820390705356379)
      ·
        refine ⟨28617365482230586058034569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19078243654820390705356379 28617365482230586058034569)
        ·
          refine ⟨21463024111672939543525927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28617365482230586058034569 21463024111672939543525927)
          ·
            refine ⟨32194536167509409315288891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21463024111672939543525927 32194536167509409315288891)
            ·
              refine ⟨48291804251264113972933337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32194536167509409315288891 48291804251264113972933337)
              ·
                refine ⟨36218853188448085479700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48291804251264113972933337 36218853188448085479700003)
                ·
                  refine ⟨54328279782672128219550005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36218853188448085479700003 54328279782672128219550005)
                  ·
                    refine ⟨5093276229625512020582813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54328279782672128219550005 5093276229625512020582813)
                    ·
                      refine ⟨1909978586109567007718555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093276229625512020582813 1909978586109567007718555)
                      ·
                        rfl

theorem cell23_3719670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3719670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719670 prefixEnd_3719670 := by exact prefixLift 3719670
  have htrace : WordTrace (prefixWord ++ tailWord_3719670) baseStart_3719670 baseEnd_3719670 := by
    simpa [prefixWord, tailWord_3719670, baseEnd_3719670] using wordTrace_append hprefix tailTrace_3719670
  have hstable : (prefixWord ++ tailWord_3719670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719670).length < 2 ^ (prefixWord ++ tailWord_3719670).sum := by decide
  have hdescent : baseEnd_3719670 < baseStart_3719670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719730 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_3719730 : Nat := 118140960795 + 3719730 * 2 ^ 59
def prefixEnd_3719730 : Nat := 4983230072969 + 3 ^ 40 * 3719730 * 2
def baseEnd_3719730 : Nat := 1910009394948836772968279

theorem tailTrace_3719730 : CollatzResearch.WordTrace tailWord_3719730 prefixEnd_3719730 1910009394948836772968279 := by
  unfold tailWord_3719730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33917424703515241037985161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90446465876040642767960429 33917424703515241037985161)
  ·
    refine ⟨25438068527636430778488871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33917424703515241037985161 25438068527636430778488871)
    ·
      refine ⟨38157102791454646167733307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25438068527636430778488871 38157102791454646167733307)
      ·
        refine ⟨57235654187181969251599961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38157102791454646167733307 57235654187181969251599961)
        ·
          refine ⟨42926740640386476938699971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57235654187181969251599961 42926740640386476938699971)
          ·
            refine ⟨64390110960579715408049957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42926740640386476938699971 64390110960579715408049957)
            ·
              refine ⟨12073145805108696639009367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64390110960579715408049957 12073145805108696639009367)
              ·
                refine ⟨18109718707663044958514051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073145805108696639009367 18109718707663044958514051)
                ·
                  refine ⟨27164578061494567437771077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18109718707663044958514051 27164578061494567437771077)
                  ·
                    refine ⟨5093358386530231394582077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27164578061494567437771077 5093358386530231394582077)
                    ·
                      refine ⟨1910009394948836772968279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093358386530231394582077 1910009394948836772968279)
                      ·
                        rfl

theorem cell23_3719730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_3719730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719730 prefixEnd_3719730 := by exact prefixLift 3719730
  have htrace : WordTrace (prefixWord ++ tailWord_3719730) baseStart_3719730 baseEnd_3719730 := by
    simpa [prefixWord, tailWord_3719730, baseEnd_3719730] using wordTrace_append hprefix tailTrace_3719730
  have hstable : (prefixWord ++ tailWord_3719730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719730).length < 2 ^ (prefixWord ++ tailWord_3719730).sum := by decide
  have hdescent : baseEnd_3719730 < baseStart_3719730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719733 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 10]
def baseStart_3719733 : Nat := 118140960795 + 3719733 * 2 ^ 59
def prefixEnd_3719733 : Nat := 4983230072969 + 3 ^ 40 * 3719733 * 2
def baseEnd_3719733 : Nat := 212223437265644473470085

theorem tailTrace_3719733 : CollatzResearch.WordTrace tailWord_3719733 prefixEnd_3719733 212223437265644473470085 := by
  unfold tailWord_3719733
  simp only [CollatzResearch.WordTrace]
  refine ⟨135669808233050095664299853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90446538822033397109533235 135669808233050095664299853)
  ·
    refine ⟨50876178087393785874112445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135669808233050095664299853 50876178087393785874112445)
    ·
      refine ⟨19078566782772669702792167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50876178087393785874112445 19078566782772669702792167)
      ·
        refine ⟨28617850174159004554188251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19078566782772669702792167 28617850174159004554188251)
        ·
          refine ⟨42926775261238506831282377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28617850174159004554188251 42926775261238506831282377)
          ·
            refine ⟨32195081445928880123461783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42926775261238506831282377 32195081445928880123461783)
            ·
              refine ⟨48292622168893320185192675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32195081445928880123461783 48292622168893320185192675)
              ·
                refine ⟨72438933253339980277789013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48292622168893320185192675 72438933253339980277789013)
                ·
                  refine ⟨212223437265644473470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72438933253339980277789013 212223437265644473470085)
                  ·
                    rfl

theorem cell23_3719733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_3719733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719733 prefixEnd_3719733 := by exact prefixLift 3719733
  have htrace : WordTrace (prefixWord ++ tailWord_3719733) baseStart_3719733 baseEnd_3719733 := by
    simpa [prefixWord, tailWord_3719733, baseEnd_3719733] using wordTrace_append hprefix tailTrace_3719733
  have hstable : (prefixWord ++ tailWord_3719733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719733).length < 2 ^ (prefixWord ++ tailWord_3719733).sum := by decide
  have hdescent : baseEnd_3719733 < baseStart_3719733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719780 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_3719780 : Nat := 118140960795 + 3719780 * 2 ^ 59
def prefixEnd_3719780 : Nat := 4983230072969 + 3 ^ 40 * 3719780 * 2
def baseEnd_3719780 : Nat := 636678356327187192447683

theorem tailTrace_3719780 : CollatzResearch.WordTrace tailWord_3719780 prefixEnd_3719780 636678356327187192447683 := by
  unfold tailWord_3719780
  simp only [CollatzResearch.WordTrace]
  refine ⟨67835761231939911345630397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90447681642586548460840529 67835761231939911345630397)
  ·
    refine ⟨25438410461977466754611399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67835761231939911345630397 25438410461977466754611399)
    ·
      refine ⟨38157615692966200131917099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25438410461977466754611399 38157615692966200131917099)
      ·
        refine ⟨57236423539449300197875649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38157615692966200131917099 57236423539449300197875649)
        ·
          refine ⟨42927317654586975148406737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57236423539449300197875649 42927317654586975148406737)
          ·
            refine ⟨32195488240940231361305053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42927317654586975148406737 32195488240940231361305053)
            ·
              refine ⟨12073308090352586760489395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32195488240940231361305053 12073308090352586760489395)
              ·
                refine ⟨18109962135528880140734093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073308090352586760489395 18109962135528880140734093)
                ·
                  refine ⟨6791235800823330052775285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18109962135528880140734093 6791235800823330052775285)
                  ·
                    refine ⟨636678356327187192447683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6791235800823330052775285 636678356327187192447683)
                    ·
                      rfl

theorem cell23_3719780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_3719780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719780 prefixEnd_3719780 := by exact prefixLift 3719780
  have htrace : WordTrace (prefixWord ++ tailWord_3719780) baseStart_3719780 baseEnd_3719780 := by
    simpa [prefixWord, tailWord_3719780, baseEnd_3719780] using wordTrace_append hprefix tailTrace_3719780
  have hstable : (prefixWord ++ tailWord_3719780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719780).length < 2 ^ (prefixWord ++ tailWord_3719780).sum := by decide
  have hdescent : baseEnd_3719780 < baseStart_3719780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719811 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 1, 1, 3]
def baseStart_3719811 : Nat := 118140960795 + 3719811 * 2 ^ 59
def prefixEnd_3719811 : Nat := 4983230072969 + 3 ^ 40 * 3719811 * 2
def baseEnd_3719811 : Nat := 1910050986881850956055407

theorem tailTrace_3719811 : CollatzResearch.WordTrace tailWord_3719811 prefixEnd_3719811 1910050986881850956055407 := by
  unfold tailWord_3719811
  simp only [CollatzResearch.WordTrace]
  refine ⟨135672653126767514985639287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90448435417845009990426191 135672653126767514985639287)
  ·
    refine ⟨203508979690151272478458931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135672653126767514985639287 203508979690151272478458931)
    ·
      refine ⟨305263469535226908717688397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203508979690151272478458931 305263469535226908717688397)
      ·
        refine ⟨114473801075710090769133149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305263469535226908717688397 114473801075710090769133149)
        ·
          refine ⟨42927675403391284038424931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114473801075710090769133149 42927675403391284038424931)
          ·
            refine ⟨64391513105086926057637397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42927675403391284038424931 64391513105086926057637397)
            ·
              refine ⟨3018352176800949658951753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64391513105086926057637397 3018352176800949658951753)
              ·
                refine ⟨2263764132600712244213815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018352176800949658951753 2263764132600712244213815)
                ·
                  refine ⟨3395646198901068366320723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263764132600712244213815 3395646198901068366320723)
                  ·
                    refine ⟨5093469298351602549481085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3395646198901068366320723 5093469298351602549481085)
                    ·
                      refine ⟨1910050986881850956055407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093469298351602549481085 1910050986881850956055407)
                      ·
                        rfl

theorem cell23_3719811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_3719811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719811 prefixEnd_3719811 := by exact prefixLift 3719811
  have htrace : WordTrace (prefixWord ++ tailWord_3719811) baseStart_3719811 baseEnd_3719811 := by
    simpa [prefixWord, tailWord_3719811, baseEnd_3719811] using wordTrace_append hprefix tailTrace_3719811
  have hstable : (prefixWord ++ tailWord_3719811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719811).length < 2 ^ (prefixWord ++ tailWord_3719811).sum := by decide
  have hdescent : baseEnd_3719811 < baseStart_3719811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719837 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3719837 : Nat := 118140960795 + 3719837 * 2 ^ 59
def prefixEnd_3719837 : Nat := 4983230072969 + 3 ^ 40 * 3719837 * 2
def baseEnd_3719837 : Nat := 1910064337378867854330287

theorem tailTrace_3719837 : CollatzResearch.WordTrace tailWord_3719837 prefixEnd_3719837 1910064337378867854330287 := by
  unfold tailWord_3719837
  simp only [CollatzResearch.WordTrace]
  refine ⟨135673601424673321426085765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90449067616448880950723843 135673601424673321426085765)
  ·
    refine ⟨25438800267126247767391081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135673601424673321426085765 25438800267126247767391081)
    ·
      refine ⟨19079100200344685825543311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25438800267126247767391081 19079100200344685825543311)
      ·
        refine ⟨28618650300517028738314967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079100200344685825543311 28618650300517028738314967)
        ·
          refine ⟨42927975450775543107472451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28618650300517028738314967 42927975450775543107472451)
          ·
            refine ⟨64391963176163314661208677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42927975450775543107472451 64391963176163314661208677)
            ·
              refine ⟨12073493095530621498976627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64391963176163314661208677 12073493095530621498976627)
              ·
                refine ⟨18110239643295932248464941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073493095530621498976627 18110239643295932248464941)
                ·
                  refine ⟨6791339866235974593174353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18110239643295932248464941 6791339866235974593174353)
                  ·
                    refine ⟨5093504899676980944880765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6791339866235974593174353 5093504899676980944880765)
                    ·
                      refine ⟨1910064337378867854330287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093504899676980944880765 1910064337378867854330287)
                      ·
                        rfl

theorem cell23_3719837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3719837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719837 prefixEnd_3719837 := by exact prefixLift 3719837
  have htrace : WordTrace (prefixWord ++ tailWord_3719837) baseStart_3719837 baseEnd_3719837 := by
    simpa [prefixWord, tailWord_3719837, baseEnd_3719837] using wordTrace_append hprefix tailTrace_3719837
  have hstable : (prefixWord ++ tailWord_3719837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719837).length < 2 ^ (prefixWord ++ tailWord_3719837).sum := by decide
  have hdescent : baseEnd_3719837 < baseStart_3719837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719857 : List Nat := [1, 2, 2, 6, 1, 1, 10]
def baseStart_3719857 : Nat := 118140960795 + 3719857 * 2 ^ 59
def prefixEnd_3719857 : Nat := 4983230072969 + 3 ^ 40 * 3719857 * 2
def baseEnd_3719857 : Nat := 23581167987555034272595

theorem tailTrace_3719857 : CollatzResearch.WordTrace tailWord_3719857 prefixEnd_3719857 23581167987555034272595 := by
  unfold tailWord_3719857
  simp only [CollatzResearch.WordTrace]
  refine ⟨135674330884600864841813825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90449553923067243227875883 135674330884600864841813825)
  ·
    refine ⟨101755748163450648631360369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135674330884600864841813825 101755748163450648631360369)
    ·
      refine ⟨76316811122587986473520277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101755748163450648631360369 76316811122587986473520277)
      ·
        refine ⟨3577350521371311865946263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76316811122587986473520277 3577350521371311865946263)
        ·
          refine ⟨5366025782056967798919395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577350521371311865946263 5366025782056967798919395)
          ·
            refine ⟨8049038673085451698379093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366025782056967798919395 8049038673085451698379093)
            ·
              refine ⟨23581167987555034272595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8049038673085451698379093 23581167987555034272595)
              ·
                rfl

theorem cell23_3719857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 10].length) (baseStart_3719857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719857 prefixEnd_3719857 := by exact prefixLift 3719857
  have htrace : WordTrace (prefixWord ++ tailWord_3719857) baseStart_3719857 baseEnd_3719857 := by
    simpa [prefixWord, tailWord_3719857, baseEnd_3719857] using wordTrace_append hprefix tailTrace_3719857
  have hstable : (prefixWord ++ tailWord_3719857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719857).length < 2 ^ (prefixWord ++ tailWord_3719857).sum := by decide
  have hdescent : baseEnd_3719857 < baseStart_3719857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719861 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3719861 : Nat := 118140960795 + 3719861 * 2 ^ 59
def prefixEnd_3719861 : Nat := 4983230072969 + 3 ^ 40 * 3719861 * 2
def baseEnd_3719861 : Nat := 636692220304858586810059

theorem tailTrace_3719861 : CollatzResearch.WordTrace tailWord_3719861 prefixEnd_3719861 636692220304858586810059 := by
  unfold tailWord_3719861
  simp only [CollatzResearch.WordTrace]
  refine ⟨135674476776586373524959437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90449651184390915683306291 135674476776586373524959437)
  ·
    refine ⟨50877928791219890071859789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135674476776586373524959437 50877928791219890071859789)
    ·
      refine ⟨19079223296707458776947421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50877928791219890071859789 19079223296707458776947421)
      ·
        refine ⟨7154708736265297041355283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19079223296707458776947421 7154708736265297041355283)
        ·
          refine ⟨10732063104397945562032925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154708736265297041355283 10732063104397945562032925)
          ·
            refine ⟨4024523664149229585762347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10732063104397945562032925 4024523664149229585762347)
            ·
              refine ⟨6036785496223844378643521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024523664149229585762347 6036785496223844378643521)
              ·
                refine ⟨4527589122167883283982641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036785496223844378643521 4527589122167883283982641)
                ·
                  refine ⟨3395691841625912462986981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527589122167883283982641 3395691841625912462986981)
                  ·
                    refine ⟨636692220304858586810059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395691841625912462986981 636692220304858586810059)
                    ·
                      rfl

theorem cell23_3719861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3719861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719861 prefixEnd_3719861 := by exact prefixLift 3719861
  have htrace : WordTrace (prefixWord ++ tailWord_3719861) baseStart_3719861 baseEnd_3719861 := by
    simpa [prefixWord, tailWord_3719861, baseEnd_3719861] using wordTrace_append hprefix tailTrace_3719861
  have hstable : (prefixWord ++ tailWord_3719861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719861).length < 2 ^ (prefixWord ++ tailWord_3719861).sum := by decide
  have hdescent : baseEnd_3719861 < baseStart_3719861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719878 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3719878 : Nat := 118140960795 + 3719878 * 2 ^ 59
def prefixEnd_3719878 : Nat := 4983230072969 + 3 ^ 40 * 3719878 * 2
def baseEnd_3719878 : Nat := 636695130028567397972533

theorem tailTrace_3719878 : CollatzResearch.WordTrace tailWord_3719878 prefixEnd_3719878 636695130028567397972533 := by
  unfold tailWord_3719878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239846775547649544635259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90450064545016523618885525 4239846775547649544635259)
  ·
    refine ⟨6359770163321474316952889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239846775547649544635259 6359770163321474316952889)
    ·
      refine ⟨4769827622491105737714667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6359770163321474316952889 4769827622491105737714667)
      ·
        refine ⟨7154741433736658606572001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769827622491105737714667 7154741433736658606572001)
        ·
          refine ⟨5366056075302493954929001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7154741433736658606572001 5366056075302493954929001)
          ·
            refine ⟨4024542056476870466196751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5366056075302493954929001 4024542056476870466196751)
            ·
              refine ⟨6036813084715305699295127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024542056476870466196751 6036813084715305699295127)
              ·
                refine ⟨9055219627072958548942691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036813084715305699295127 9055219627072958548942691)
                ·
                  refine ⟨13582829440609437823414037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9055219627072958548942691 13582829440609437823414037)
                  ·
                    refine ⟨636695130028567397972533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13582829440609437823414037 636695130028567397972533)
                    ·
                      rfl

theorem cell23_3719878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3719878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719878 prefixEnd_3719878 := by exact prefixLift 3719878
  have htrace : WordTrace (prefixWord ++ tailWord_3719878) baseStart_3719878 baseEnd_3719878 := by
    simpa [prefixWord, tailWord_3719878, baseEnd_3719878] using wordTrace_append hprefix tailTrace_3719878
  have hstable : (prefixWord ++ tailWord_3719878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719878).length < 2 ^ (prefixWord ++ tailWord_3719878).sum := by decide
  have hdescent : baseEnd_3719878 < baseStart_3719878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719884 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3719884 : Nat := 118140960795 + 3719884 * 2 ^ 59
def prefixEnd_3719884 : Nat := 4983230072969 + 3 ^ 40 * 3719884 * 2
def baseEnd_3719884 : Nat := 1910088470969629170442571

theorem tailTrace_3719884 : CollatzResearch.WordTrace tailWord_3719884 prefixEnd_3719884 1910088470969629170442571 := by
  unfold tailWord_3719884
  simp only [CollatzResearch.WordTrace]
  refine ⟨67837657827751524226523353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90450210437002032302031137 67837657827751524226523353)
  ·
    refine ⟨50878243370813643169892515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67837657827751524226523353 50878243370813643169892515)
    ·
      refine ⟨76317365056220464754838773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50878243370813643169892515 76317365056220464754838773)
      ·
        refine ⟨7154752974020668570766135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76317365056220464754838773 7154752974020668570766135)
        ·
          refine ⟨10732129461031002856149203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154752974020668570766135 10732129461031002856149203)
          ·
            refine ⟨16098194191546504284223805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732129461031002856149203 16098194191546504284223805)
            ·
              refine ⟨6036822821829939106583927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16098194191546504284223805 6036822821829939106583927)
              ·
                refine ⟨9055234232744908659875891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036822821829939106583927 9055234232744908659875891)
                ·
                  refine ⟨13582851349117362989813837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9055234232744908659875891 13582851349117362989813837)
                  ·
                    refine ⟨5093569255919011121180189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13582851349117362989813837 5093569255919011121180189)
                    ·
                      refine ⟨1910088470969629170442571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093569255919011121180189 1910088470969629170442571)
                      ·
                        rfl

theorem cell23_3719884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3719884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719884 prefixEnd_3719884 := by exact prefixLift 3719884
  have htrace : WordTrace (prefixWord ++ tailWord_3719884) baseStart_3719884 baseEnd_3719884 := by
    simpa [prefixWord, tailWord_3719884, baseEnd_3719884] using wordTrace_append hprefix tailTrace_3719884
  have hstable : (prefixWord ++ tailWord_3719884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719884).length < 2 ^ (prefixWord ++ tailWord_3719884).sum := by decide
  have hdescent : baseEnd_3719884 < baseStart_3719884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719987 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_3719987 : Nat := 118140960795 + 3719987 * 2 ^ 59
def prefixEnd_3719987 : Nat := 4983230072969 + 3 ^ 40 * 3719987 * 2
def baseEnd_3719987 : Nat := 1910141359477042267454597

theorem tailTrace_3719987 : CollatzResearch.WordTrace tailWord_3719987 prefixEnd_3719987 1910141359477042267454597 := by
  unfold tailWord_3719987
  simp only [CollatzResearch.WordTrace]
  refine ⟨135679072374129897044046215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90452714916086598029364143 135679072374129897044046215)
  ·
    refine ⟨203518608561194845566069323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135679072374129897044046215 203518608561194845566069323)
    ·
      refine ⟨305277912841792268349103985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203518608561194845566069323 305277912841792268349103985)
      ·
        refine ⟨228958434631344201261827989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305277912841792268349103985 228958434631344201261827989)
        ·
          refine ⟨10732426623344259434148187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228958434631344201261827989 10732426623344259434148187)
          ·
            refine ⟨16098639935016389151222281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732426623344259434148187 16098639935016389151222281)
            ·
              refine ⟨12073979951262291863416711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16098639935016389151222281 12073979951262291863416711)
              ·
                refine ⟨18110969926893437795125067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073979951262291863416711 18110969926893437795125067)
                ·
                  refine ⟨27166454890340156692687601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18110969926893437795125067 27166454890340156692687601)
                  ·
                    refine ⟨20374841167755117519515701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27166454890340156692687601 20374841167755117519515701)
                    ·
                      refine ⟨1910141359477042267454597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20374841167755117519515701 1910141359477042267454597)
                      ·
                        rfl

theorem cell23_3719987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_3719987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719987 prefixEnd_3719987 := by exact prefixLift 3719987
  have htrace : WordTrace (prefixWord ++ tailWord_3719987) baseStart_3719987 baseEnd_3719987 := by
    simpa [prefixWord, tailWord_3719987, baseEnd_3719987] using wordTrace_append hprefix tailTrace_3719987
  have hstable : (prefixWord ++ tailWord_3719987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719987).length < 2 ^ (prefixWord ++ tailWord_3719987).sum := by decide
  have hdescent : baseEnd_3719987 < baseStart_3719987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720064 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3]
def baseStart_3720064 : Nat := 118140960795 + 3720064 * 2 ^ 59
def prefixEnd_3720064 : Nat := 4983230072969 + 3 ^ 40 * 3720064 * 2
def baseEnd_3720064 : Nat := 1910180897487438466191743

theorem tailTrace_3720064 : CollatzResearch.WordTrace tailWord_3720064 prefixEnd_3720064 1910180897487438466191743 := by
  unfold tailWord_3720064
  simp only [CollatzResearch.WordTrace]
  refine ⟨67840940397425469597299623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90454587196567292796399497 67840940397425469597299623)
  ·
    refine ⟨101761410596138204395949435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67840940397425469597299623 101761410596138204395949435)
    ·
      refine ⟨152642115894207306593924153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101761410596138204395949435 152642115894207306593924153)
      ·
        refine ⟨114481586920655479945443115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152642115894207306593924153 114481586920655479945443115)
        ·
          refine ⟨171722380380983219918164673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114481586920655479945443115 171722380380983219918164673)
          ·
            refine ⟨128791785285737414938623505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171722380380983219918164673 128791785285737414938623505)
            ·
              refine ⟨96593838964303061203967629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128791785285737414938623505 96593838964303061203967629)
              ·
                refine ⟨36222689611613647951487861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96593838964303061203967629 36222689611613647951487861)
                ·
                  refine ⟨3395877151088779495451987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36222689611613647951487861 3395877151088779495451987)
                  ·
                    refine ⟨5093815726633169243177981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3395877151088779495451987 5093815726633169243177981)
                    ·
                      refine ⟨1910180897487438466191743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093815726633169243177981 1910180897487438466191743)
                      ·
                        rfl

theorem cell23_3720064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_3720064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720064 prefixEnd_3720064 := by exact prefixLift 3720064
  have htrace : WordTrace (prefixWord ++ tailWord_3720064) baseStart_3720064 baseEnd_3720064 := by
    simpa [prefixWord, tailWord_3720064, baseEnd_3720064] using wordTrace_append hprefix tailTrace_3720064
  have hstable : (prefixWord ++ tailWord_3720064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720064).length < 2 ^ (prefixWord ++ tailWord_3720064).sum := by decide
  have hdescent : baseEnd_3720064 < baseStart_3720064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720098 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3720098 : Nat := 118140960795 + 3720098 * 2 ^ 59
def prefixEnd_3720098 : Nat := 4983230072969 + 3 ^ 40 * 3720098 * 2
def baseEnd_3720098 : Nat := 1910198355829691333166587

theorem tailTrace_3720098 : CollatzResearch.WordTrace tailWord_3720098 prefixEnd_3720098 1910198355829691333166587 := by
  unfold tailWord_3720098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920780219181940750334237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90455413917818508667557965 33920780219181940750334237)
  ·
    refine ⟨12720292582193227781375339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33920780219181940750334237 12720292582193227781375339)
    ·
      refine ⟨19080438873289841672063009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12720292582193227781375339 19080438873289841672063009)
      ·
        refine ⟨14310329154967381254047257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080438873289841672063009 14310329154967381254047257)
        ·
          refine ⟨10732746866225535940535443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14310329154967381254047257 10732746866225535940535443)
          ·
            refine ⟨16099120299338303910803165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732746866225535940535443 16099120299338303910803165)
            ·
              refine ⟨6037170112251863966551187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16099120299338303910803165 6037170112251863966551187)
              ·
                refine ⟨9055755168377795949826781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037170112251863966551187 9055755168377795949826781)
                ·
                  refine ⟨3395908188141673481185043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9055755168377795949826781 3395908188141673481185043)
                  ·
                    refine ⟨5093862282212510221777565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3395908188141673481185043 5093862282212510221777565)
                    ·
                      refine ⟨1910198355829691333166587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093862282212510221777565 1910198355829691333166587)
                      ·
                        rfl

theorem cell23_3720098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3720098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720098 prefixEnd_3720098 := by exact prefixLift 3720098
  have htrace : WordTrace (prefixWord ++ tailWord_3720098) baseStart_3720098 baseEnd_3720098 := by
    simpa [prefixWord, tailWord_3720098, baseEnd_3720098] using wordTrace_append hprefix tailTrace_3720098
  have hstable : (prefixWord ++ tailWord_3720098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720098).length < 2 ^ (prefixWord ++ tailWord_3720098).sum := by decide
  have hdescent : baseEnd_3720098 < baseStart_3720098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720121 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3720121 : Nat := 118140960795 + 3720121 * 2 ^ 59
def prefixEnd_3720121 : Nat := 4983230072969 + 3 ^ 40 * 3720121 * 2
def baseEnd_3720121 : Nat := 1910210165884744743178981

theorem tailTrace_3720121 : CollatzResearch.WordTrace tailWord_3720121 prefixEnd_3720121 1910210165884744743178981 := by
  unfold tailWord_3720121
  simp only [CollatzResearch.WordTrace]
  refine ⟨135683959755644437929424217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90455973170429625286282811 135683959755644437929424217)
  ·
    refine ⟨101762969816733328447068163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135683959755644437929424217 101762969816733328447068163)
    ·
      refine ⟨152644454725099992670602245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101762969816733328447068163 152644454725099992670602245)
      ·
        refine ⟨28620835260956248625737921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152644454725099992670602245 28620835260956248625737921)
        ·
          refine ⟨21465626445717186469303441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28620835260956248625737921 21465626445717186469303441)
          ·
            refine ⟨16099219834287889851977581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21465626445717186469303441 16099219834287889851977581)
            ·
              refine ⟨6037207437857958694491593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16099219834287889851977581 6037207437857958694491593)
              ·
                refine ⟨4527905578393469020868695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6037207437857958694491593 4527905578393469020868695)
                ·
                  refine ⟨6791858367590203531303043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527905578393469020868695 6791858367590203531303043)
                  ·
                    refine ⟨10187787551385305296954565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6791858367590203531303043 10187787551385305296954565)
                    ·
                      refine ⟨1910210165884744743178981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10187787551385305296954565 1910210165884744743178981)
                      ·
                        rfl

theorem cell23_3720121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3720121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720121 prefixEnd_3720121 := by exact prefixLift 3720121
  have htrace : WordTrace (prefixWord ++ tailWord_3720121) baseStart_3720121 baseEnd_3720121 := by
    simpa [prefixWord, tailWord_3720121, baseEnd_3720121] using wordTrace_append hprefix tailTrace_3720121
  have hstable : (prefixWord ++ tailWord_3720121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720121).length < 2 ^ (prefixWord ++ tailWord_3720121).sum := by decide
  have hdescent : baseEnd_3720121 < baseStart_3720121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720148 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_3720148 : Nat := 118140960795 + 3720148 * 2 ^ 59
def prefixEnd_3720148 : Nat := 4983230072969 + 3 ^ 40 * 3720148 * 2
def baseEnd_3720148 : Nat := 636741343287472045847119

theorem tailTrace_3720148 : CollatzResearch.WordTrace tailWord_3720148 prefixEnd_3720148 636741343287472045847119 := by
  unfold tailWord_3720148
  simp only [CollatzResearch.WordTrace]
  refine ⟨67842472263273310770328549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90456629684364414360438065 67842472263273310770328549)
  ·
    refine ⟨12720463549363745769436603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67842472263273310770328549 12720463549363745769436603)
    ·
      refine ⟨19080695324045618654154905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12720463549363745769436603 19080695324045618654154905)
      ·
        refine ⟨14310521493034213990616179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080695324045618654154905 14310521493034213990616179)
        ·
          refine ⟨21465782239551320985924269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310521493034213990616179 21465782239551320985924269)
          ·
            refine ⟨8049668339831745369721601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21465782239551320985924269 8049668339831745369721601)
            ·
              refine ⟨6037251254873809027291201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049668339831745369721601 6037251254873809027291201)
              ·
                refine ⟨4527938441155356770468401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6037251254873809027291201 4527938441155356770468401)
                ·
                  refine ⟨3395953830866517577851301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527938441155356770468401 3395953830866517577851301)
                  ·
                    refine ⟨636741343287472045847119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395953830866517577851301 636741343287472045847119)
                    ·
                      rfl

theorem cell23_3720148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_3720148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720148 prefixEnd_3720148 := by exact prefixLift 3720148
  have htrace : WordTrace (prefixWord ++ tailWord_3720148) baseStart_3720148 baseEnd_3720148 := by
    simpa [prefixWord, tailWord_3720148, baseEnd_3720148] using wordTrace_append hprefix tailTrace_3720148
  have hstable : (prefixWord ++ tailWord_3720148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720148).length < 2 ^ (prefixWord ++ tailWord_3720148).sum := by decide
  have hdescent : baseEnd_3720148 < baseStart_3720148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720149 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3720149 : Nat := 118140960795 + 3720149 * 2 ^ 59
def prefixEnd_3720149 : Nat := 4983230072969 + 3 ^ 40 * 3720149 * 2
def baseEnd_3720149 : Nat := 1910224543343070633628853

theorem tailTrace_3720149 : CollatzResearch.WordTrace tailWord_3720149 prefixEnd_3720149 1910224543343070633628853 := by
  unfold tailWord_3720149
  simp only [CollatzResearch.WordTrace]
  refine ⟨135684980999542998711443501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90456653999695332474295667 135684980999542998711443501)
  ·
    refine ⟨50881867874828624516791313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135684980999542998711443501 50881867874828624516791313)
    ·
      refine ⟨38161400906121468387593485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50881867874828624516791313 38161400906121468387593485)
      ·
        refine ⟨14310525339795550645347557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38161400906121468387593485 14310525339795550645347557)
        ·
          refine ⟨2683223501211665746002667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14310525339795550645347557 2683223501211665746002667)
          ·
            refine ⟨4024835251817498619004001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683223501211665746002667 4024835251817498619004001)
            ·
              refine ⟨3018626438863123964253001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4024835251817498619004001 3018626438863123964253001)
              ·
                refine ⟨2263969829147342973189751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018626438863123964253001 2263969829147342973189751)
                ·
                  refine ⟨3395954743721014459784627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263969829147342973189751 3395954743721014459784627)
                  ·
                    refine ⟨5093932115581521689676941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3395954743721014459784627 5093932115581521689676941)
                    ·
                      refine ⟨1910224543343070633628853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5093932115581521689676941 1910224543343070633628853)
                      ·
                        rfl

theorem cell23_3720149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3720149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720149 prefixEnd_3720149 := by exact prefixLift 3720149
  have htrace : WordTrace (prefixWord ++ tailWord_3720149) baseStart_3720149 baseEnd_3720149 := by
    simpa [prefixWord, tailWord_3720149, baseEnd_3720149] using wordTrace_append hprefix tailTrace_3720149
  have hstable : (prefixWord ++ tailWord_3720149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720149).length < 2 ^ (prefixWord ++ tailWord_3720149).sum := by decide
  have hdescent : baseEnd_3720149 < baseStart_3720149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720178 : List Nat := [3, 2, 1, 5, 1, 1, 3, 7]
def baseStart_3720178 : Nat := 118140960795 + 3720178 * 2 ^ 59
def prefixEnd_3720178 : Nat := 4983230072969 + 3 ^ 40 * 3720178 * 2
def baseEnd_3720178 : Nat := 70749608677113000746897

theorem tailTrace_3720178 : CollatzResearch.WordTrace tailWord_3720178 prefixEnd_3720178 70749608677113000746897 := by
  unfold tailWord_3720178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921509679109484166062297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90457359144291957776166125 33921509679109484166062297)
  ·
    refine ⟨25441132259332113124546723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33921509679109484166062297 25441132259332113124546723)
    ·
      refine ⟨38161698388998169686820085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25441132259332113124546723 38161698388998169686820085)
      ·
        refine ⟨3577659223968578408139383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38161698388998169686820085 3577659223968578408139383)
        ·
          refine ⟨5366488835952867612209075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577659223968578408139383 5366488835952867612209075)
          ·
            refine ⟨8049733253929301418313613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366488835952867612209075 8049733253929301418313613)
            ·
              refine ⟨3018649970223488031867605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8049733253929301418313613 3018649970223488031867605)
              ·
                refine ⟨70749608677113000746897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3018649970223488031867605 70749608677113000746897)
                ·
                  rfl

theorem cell23_3720178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_3720178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720178 prefixEnd_3720178 := by exact prefixLift 3720178
  have htrace : WordTrace (prefixWord ++ tailWord_3720178) baseStart_3720178 baseEnd_3720178 := by
    simpa [prefixWord, tailWord_3720178, baseEnd_3720178] using wordTrace_append hprefix tailTrace_3720178
  have hstable : (prefixWord ++ tailWord_3720178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720178).length < 2 ^ (prefixWord ++ tailWord_3720178).sum := by decide
  have hdescent : baseEnd_3720178 < baseStart_3720178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720187 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 8]
def baseStart_3720187 : Nat := 118140960795 + 3720187 * 2 ^ 59
def prefixEnd_3720187 : Nat := 4983230072969 + 3 ^ 40 * 3720187 * 2
def baseEnd_3720187 : Nat := 636748018535980494984559

theorem tailTrace_3720187 : CollatzResearch.WordTrace tailWord_3720187 prefixEnd_3720187 636748018535980494984559 := by
  unfold tailWord_3720187
  simp only [CollatzResearch.WordTrace]
  refine ⟨135686366973405331201326815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90457577982270220800884543 135686366973405331201326815)
  ·
    refine ⟨203529550460107996801990223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135686366973405331201326815 203529550460107996801990223)
    ·
      refine ⟨305294325690161995202985335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203529550460107996801990223 305294325690161995202985335)
      ·
        refine ⟨457941488535242992804478003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305294325690161995202985335 457941488535242992804478003)
        ·
          refine ⟨686912232802864489206717005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457941488535242992804478003 686912232802864489206717005)
          ·
            refine ⟨257592087301074183452518877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686912232802864489206717005 257592087301074183452518877)
            ·
              refine ⟨96597032737902818794694579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257592087301074183452518877 96597032737902818794694579)
              ·
                refine ⟨144895549106854228192041869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96597032737902818794694579 144895549106854228192041869)
                ·
                  refine ⟨54335830915070335572015701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144895549106854228192041869 54335830915070335572015701)
                  ·
                    refine ⟨636748018535980494984559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54335830915070335572015701 636748018535980494984559)
                    ·
                      rfl

theorem cell23_3720187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_3720187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720187 prefixEnd_3720187 := by exact prefixLift 3720187
  have htrace : WordTrace (prefixWord ++ tailWord_3720187) baseStart_3720187 baseEnd_3720187 := by
    simpa [prefixWord, tailWord_3720187, baseEnd_3720187] using wordTrace_append hprefix tailTrace_3720187
  have hstable : (prefixWord ++ tailWord_3720187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720187).length < 2 ^ (prefixWord ++ tailWord_3720187).sum := by decide
  have hdescent : baseEnd_3720187 < baseStart_3720187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720204 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_3720204 : Nat := 118140960795 + 3720204 * 2 ^ 59
def prefixEnd_3720204 : Nat := 4983230072969 + 3 ^ 40 * 3720204 * 2
def baseEnd_3720204 : Nat := 636750928259689306147033

theorem tailTrace_3720204 : CollatzResearch.WordTrace tailWord_3720204 prefixEnd_3720204 636750928259689306147033 := by
  unfold tailWord_3720204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67843493507171871552347833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90457991342895828736463777 67843493507171871552347833)
  ·
    refine ⟨50882620130378903664260875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67843493507171871552347833 50882620130378903664260875)
    ·
      refine ⟨76323930195568355496391313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50882620130378903664260875 76323930195568355496391313)
      ·
        refine ⟨57242947646676266622293485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76323930195568355496391313 57242947646676266622293485)
        ·
          refine ⟨21466105367503599983360057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57242947646676266622293485 21466105367503599983360057)
          ·
            refine ⟨16099579025627699987520043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21466105367503599983360057 16099579025627699987520043)
            ·
              refine ⟨24149368538441549981280065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16099579025627699987520043 24149368538441549981280065)
              ·
                refine ⟨18112026403831162485960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24149368538441549981280065 18112026403831162485960049)
                ·
                  refine ⟨13584019802873371864470037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18112026403831162485960049 13584019802873371864470037)
                  ·
                    refine ⟨636750928259689306147033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13584019802873371864470037 636750928259689306147033)
                    ·
                      rfl

theorem cell23_3720204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_3720204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720204 prefixEnd_3720204 := by exact prefixLift 3720204
  have htrace : WordTrace (prefixWord ++ tailWord_3720204) baseStart_3720204 baseEnd_3720204 := by
    simpa [prefixWord, tailWord_3720204, baseEnd_3720204] using wordTrace_append hprefix tailTrace_3720204
  have hstable : (prefixWord ++ tailWord_3720204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720204).length < 2 ^ (prefixWord ++ tailWord_3720204).sum := by decide
  have hdescent : baseEnd_3720204 < baseStart_3720204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720262 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3720262 : Nat := 118140960795 + 3720262 * 2 ^ 59
def prefixEnd_3720262 : Nat := 4983230072969 + 3 ^ 40 * 3720262 * 2
def baseEnd_3720262 : Nat := 1910282566657028691515833

theorem tailTrace_3720262 : CollatzResearch.WordTrace tailWord_3720262 prefixEnd_3720262 1910282566657028691515833 := by
  unfold tailWord_3720262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240284451504175594072095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90459401632089079340204693 4240284451504175594072095)
  ·
    refine ⟨6360426677256263391108143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240284451504175594072095 6360426677256263391108143)
    ·
      refine ⟨9540640015884395086662215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360426677256263391108143 9540640015884395086662215)
      ·
        refine ⟨14310960023826592629993323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540640015884395086662215 14310960023826592629993323)
        ·
          refine ⟨21466440035739888944989985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310960023826592629993323 21466440035739888944989985)
          ·
            refine ⟨16099830026804916708742489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21466440035739888944989985 16099830026804916708742489)
            ·
              refine ⟨12074872520103687531556867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16099830026804916708742489 12074872520103687531556867)
              ·
                refine ⟨18112308780155531297335301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12074872520103687531556867 18112308780155531297335301)
                ·
                  refine ⟨3396057896279162118250369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18112308780155531297335301 3396057896279162118250369)
                  ·
                    refine ⟨2547043422209371588687777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396057896279162118250369 2547043422209371588687777)
                    ·
                      refine ⟨1910282566657028691515833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547043422209371588687777 1910282566657028691515833)
                      ·
                        rfl

theorem cell23_3720262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3720262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720262 prefixEnd_3720262 := by exact prefixLift 3720262
  have htrace : WordTrace (prefixWord ++ tailWord_3720262) baseStart_3720262 baseEnd_3720262 := by
    simpa [prefixWord, tailWord_3720262, baseEnd_3720262] using wordTrace_append hprefix tailTrace_3720262
  have hstable : (prefixWord ++ tailWord_3720262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720262).length < 2 ^ (prefixWord ++ tailWord_3720262).sum := by decide
  have hdescent : baseEnd_3720262 < baseStart_3720262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720298 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3720298 : Nat := 118140960795 + 3720298 * 2 ^ 59
def prefixEnd_3720298 : Nat := 4983230072969 + 3 ^ 40 * 3720298 * 2
def baseEnd_3720298 : Nat := 636767017320196850221889

theorem tailTrace_3720298 : CollatzResearch.WordTrace tailWord_3720298 prefixEnd_3720298 636767017320196850221889 := by
  unfold tailWord_3720298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33922603869000799289654387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90460276984002131439078365 33922603869000799289654387)
  ·
    refine ⟨50883905803501198934481581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33922603869000799289654387 50883905803501198934481581)
    ·
      refine ⟨19081464676312949600430593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50883905803501198934481581 19081464676312949600430593)
      ·
        refine ⟨14311098507234712200322945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19081464676312949600430593 14311098507234712200322945)
        ·
          refine ⟨10733323880426034150242209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14311098507234712200322945 10733323880426034150242209)
          ·
            refine ⟨8049992910319525612681657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733323880426034150242209 8049992910319525612681657)
            ·
              refine ⟨6037494682739644209511243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049992910319525612681657 6037494682739644209511243)
              ·
                refine ⟨9056242024109466314266865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037494682739644209511243 9056242024109466314266865)
                ·
                  refine ⟨6792181518082099735700149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9056242024109466314266865 6792181518082099735700149)
                  ·
                    refine ⟨636767017320196850221889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6792181518082099735700149 636767017320196850221889)
                    ·
                      rfl

theorem cell23_3720298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3720298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720298 prefixEnd_3720298 := by exact prefixLift 3720298
  have htrace : WordTrace (prefixWord ++ tailWord_3720298) baseStart_3720298 baseEnd_3720298 := by
    simpa [prefixWord, tailWord_3720298, baseEnd_3720298] using wordTrace_append hprefix tailTrace_3720298
  have hstable : (prefixWord ++ tailWord_3720298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720298).length < 2 ^ (prefixWord ++ tailWord_3720298).sum := by decide
  have hdescent : baseEnd_3720298 < baseStart_3720298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720362 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3720362 : Nat := 118140960795 + 3720362 * 2 ^ 59
def prefixEnd_3720362 : Nat := 4983230072969 + 3 ^ 40 * 3720362 * 2
def baseEnd_3720362 : Nat := 636777971574159433421791

theorem tailTrace_3720362 : CollatzResearch.WordTrace tailWord_3720362 prefixEnd_3720362 636777971574159433421791 := by
  unfold tailWord_3720362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33923187436942834022236835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90461833165180890725964893 33923187436942834022236835)
  ·
    refine ⟨50884781155414251033355253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33923187436942834022236835 50884781155414251033355253)
    ·
      refine ⟨4770448233320086034377055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50884781155414251033355253 4770448233320086034377055)
      ·
        refine ⟨7155672349980129051565583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770448233320086034377055 7155672349980129051565583)
        ·
          refine ⟨10733508524970193577348375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155672349980129051565583 10733508524970193577348375)
          ·
            refine ⟨16100262787455290366022563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733508524970193577348375 16100262787455290366022563)
            ·
              refine ⟨24150394181182935549033845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16100262787455290366022563 24150394181182935549033845)
              ·
                refine ⟨2264099454485900207721923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24150394181182935549033845 2264099454485900207721923)
                ·
                  refine ⟨3396149181728850311582885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264099454485900207721923 3396149181728850311582885)
                  ·
                    refine ⟨636777971574159433421791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396149181728850311582885 636777971574159433421791)
                    ·
                      rfl

theorem cell23_3720362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3720362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720362 prefixEnd_3720362 := by exact prefixLift 3720362
  have htrace : WordTrace (prefixWord ++ tailWord_3720362) baseStart_3720362 baseEnd_3720362 := by
    simpa [prefixWord, tailWord_3720362, baseEnd_3720362] using wordTrace_append hprefix tailTrace_3720362
  have hstable : (prefixWord ++ tailWord_3720362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720362).length < 2 ^ (prefixWord ++ tailWord_3720362).sum := by decide
  have hdescent : baseEnd_3720362 < baseStart_3720362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720378 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_3720378 : Nat := 118140960795 + 3720378 * 2 ^ 59
def prefixEnd_3720378 : Nat := 4983230072969 + 3 ^ 40 * 3720378 * 2
def baseEnd_3720378 : Nat := 1910342130412950237665299

theorem tailTrace_3720378 : CollatzResearch.WordTrace tailWord_3720378 prefixEnd_3720378 1910342130412950237665299 := by
  unfold tailWord_3720378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33923333328928342705382447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90462222210475580547686525 33923333328928342705382447)
  ·
    refine ⟨50884999993392514058073671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33923333328928342705382447 50884999993392514058073671)
    ·
      refine ⟨76327499990088771087110507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50884999993392514058073671 76327499990088771087110507)
      ·
        refine ⟨114491249985133156630665761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76327499990088771087110507 114491249985133156630665761)
        ·
          refine ⟨85868437488849867472999321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114491249985133156630665761 85868437488849867472999321)
          ·
            refine ⟨64401328116637400604749491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85868437488849867472999321 64401328116637400604749491)
            ·
              refine ⟨96601992174956100907124237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64401328116637400604749491 96601992174956100907124237)
              ·
                refine ⟨36225747065608537840171589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96601992174956100907124237 36225747065608537840171589)
                ·
                  refine ⟨6792327574801600845032173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36225747065608537840171589 6792327574801600845032173)
                  ·
                    refine ⟨2547122840550600316887065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6792327574801600845032173 2547122840550600316887065)
                    ·
                      refine ⟨1910342130412950237665299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547122840550600316887065 1910342130412950237665299)
                      ·
                        rfl

theorem cell23_3720378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_3720378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720378 prefixEnd_3720378 := by exact prefixLift 3720378
  have htrace : WordTrace (prefixWord ++ tailWord_3720378) baseStart_3720378 baseEnd_3720378 := by
    simpa [prefixWord, tailWord_3720378, baseEnd_3720378] using wordTrace_append hprefix tailTrace_3720378
  have hstable : (prefixWord ++ tailWord_3720378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720378).length < 2 ^ (prefixWord ++ tailWord_3720378).sum := by decide
  have hdescent : baseEnd_3720378 < baseStart_3720378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720391 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3720391 : Nat := 118140960795 + 3720391 * 2 ^ 59
def prefixEnd_3720391 : Nat := 4983230072969 + 3 ^ 40 * 3720391 * 2
def baseEnd_3720391 : Nat := 1910348805661458686802739

theorem tailTrace_3720391 : CollatzResearch.WordTrace tailWord_3720391 prefixEnd_3720391 1910348805661458686802739 := by
  unfold tailWord_3720391
  simp only [CollatzResearch.WordTrace]
  refine ⟨135693807464666274041753027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90462538309777516027835351 135693807464666274041753027)
  ·
    refine ⟨203540711196999411062629541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135693807464666274041753027 203540711196999411062629541)
    ·
      refine ⟨38163883349437389574243039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203540711196999411062629541 38163883349437389574243039)
      ·
        refine ⟨57245825024156084361364559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38163883349437389574243039 57245825024156084361364559)
        ·
          refine ⟨85868737536234126542046839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57245825024156084361364559 85868737536234126542046839)
          ·
            refine ⟨128803106304351189813070259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85868737536234126542046839 128803106304351189813070259)
            ·
              refine ⟨193204659456526784719605389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128803106304351189813070259 193204659456526784719605389)
              ·
                refine ⟨72451747296197544269852021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193204659456526784719605389 72451747296197544269852021)
                ·
                  refine ⟨6792351309018519775298627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72451747296197544269852021 6792351309018519775298627)
                  ·
                    refine ⟨10188526963527779662947941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6792351309018519775298627 10188526963527779662947941)
                    ·
                      refine ⟨1910348805661458686802739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10188526963527779662947941 1910348805661458686802739)
                      ·
                        rfl

theorem cell23_3720391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3720391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720391 prefixEnd_3720391 := by exact prefixLift 3720391
  have htrace : WordTrace (prefixWord ++ tailWord_3720391) baseStart_3720391 baseEnd_3720391 := by
    simpa [prefixWord, tailWord_3720391, baseEnd_3720391] using wordTrace_append hprefix tailTrace_3720391
  have hstable : (prefixWord ++ tailWord_3720391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720391).length < 2 ^ (prefixWord ++ tailWord_3720391).sum := by decide
  have hdescent : baseEnd_3720391 < baseStart_3720391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720405 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3720405 : Nat := 118140960795 + 3720405 * 2 ^ 59
def prefixEnd_3720405 : Nat := 4983230072969 + 3 ^ 40 * 3720405 * 2
def baseEnd_3720405 : Nat := 636785331463540544009225

theorem tailTrace_3720405 : CollatzResearch.WordTrace tailWord_3720405 prefixEnd_3720405 636785331463540544009225 := by
  unfold tailWord_3720405
  simp only [CollatzResearch.WordTrace]
  refine ⟨135694318086615554432762669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90462878724410369621841779 135694318086615554432762669)
  ·
    refine ⟨50885369282480832912286001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135694318086615554432762669 50885369282480832912286001)
    ·
      refine ⟨38164026961860624684214501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50885369282480832912286001 38164026961860624684214501)
      ·
        refine ⟨7155755055348867128290219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38164026961860624684214501 7155755055348867128290219)
        ·
          refine ⟨10733632583023300692435329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155755055348867128290219 10733632583023300692435329)
          ·
            refine ⟨8050224437267475519326497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733632583023300692435329 8050224437267475519326497)
            ·
              refine ⟨6037668327950606639494873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8050224437267475519326497 6037668327950606639494873)
              ·
                refine ⟨4528251245962954979621155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6037668327950606639494873 4528251245962954979621155)
                ·
                  refine ⟨6792376868944432469431733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528251245962954979621155 6792376868944432469431733)
                  ·
                    refine ⟨636785331463540544009225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6792376868944432469431733 636785331463540544009225)
                    ·
                      rfl

theorem cell23_3720405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3720405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720405 prefixEnd_3720405 := by exact prefixLift 3720405
  have htrace : WordTrace (prefixWord ++ tailWord_3720405) baseStart_3720405 baseEnd_3720405 := by
    simpa [prefixWord, tailWord_3720405, baseEnd_3720405] using wordTrace_append hprefix tailTrace_3720405
  have hstable : (prefixWord ++ tailWord_3720405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720405).length < 2 ^ (prefixWord ++ tailWord_3720405).sum := by decide
  have hdescent : baseEnd_3720405 < baseStart_3720405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720428 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_3720428 : Nat := 118140960795 + 3720428 * 2 ^ 59
def prefixEnd_3720428 : Nat := 4983230072969 + 3 ^ 40 * 3720428 * 2
def baseEnd_3720428 : Nat := 1910367804445675042040069

theorem tailTrace_3720428 : CollatzResearch.WordTrace tailWord_3720428 prefixEnd_3720428 1910367804445675042040069 := by
  unfold tailWord_3720428
  simp only [CollatzResearch.WordTrace]
  refine ⟨67847578482766114680424969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90463437977021486240566625 67847578482766114680424969)
  ·
    refine ⟨50885683862074586010318727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67847578482766114680424969 50885683862074586010318727)
    ·
      refine ⟨76328525793111879015478091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50885683862074586010318727 76328525793111879015478091)
      ·
        refine ⟨114492788689667818523217137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76328525793111879015478091 114492788689667818523217137)
        ·
          refine ⟨85869591517250863892412853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114492788689667818523217137 85869591517250863892412853)
          ·
            refine ⟨8050274204742268489913705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85869591517250863892412853 8050274204742268489913705)
            ·
              refine ⟨6037705653556701367435279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8050274204742268489913705 6037705653556701367435279)
              ·
                refine ⟨9056558480335052051152919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037705653556701367435279 9056558480335052051152919)
                ·
                  refine ⟨13584837720502578076729379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056558480335052051152919 13584837720502578076729379)
                  ·
                    refine ⟨20377256580753867115094069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13584837720502578076729379 20377256580753867115094069)
                    ·
                      refine ⟨1910367804445675042040069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20377256580753867115094069 1910367804445675042040069)
                      ·
                        rfl

theorem cell23_3720428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_3720428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720428 prefixEnd_3720428 := by exact prefixLift 3720428
  have htrace : WordTrace (prefixWord ++ tailWord_3720428) baseStart_3720428 baseEnd_3720428 := by
    simpa [prefixWord, tailWord_3720428, baseEnd_3720428] using wordTrace_append hprefix tailTrace_3720428
  have hstable : (prefixWord ++ tailWord_3720428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720428).length < 2 ^ (prefixWord ++ tailWord_3720428).sum := by decide
  have hdescent : baseEnd_3720428 < baseStart_3720428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720452 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_3720452 : Nat := 118140960795 + 3720452 * 2 ^ 59
def prefixEnd_3720452 : Nat := 4983230072969 + 3 ^ 40 * 3720452 * 2
def baseEnd_3720452 : Nat := 636793375993794316046653

theorem tailTrace_3720452 : CollatzResearch.WordTrace tailWord_3720452 prefixEnd_3720452 636793375993794316046653 := by
  unfold tailWord_3720452
  simp only [CollatzResearch.WordTrace]
  refine ⟨67848016158722640729861805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90464021544963520973149073 67848016158722640729861805)
  ·
    refine ⟨25443006059520990273698177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67848016158722640729861805 25443006059520990273698177)
    ·
      refine ⟨19082254544640742705273633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25443006059520990273698177 19082254544640742705273633)
      ·
        refine ⟨14311690908480557028955225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19082254544640742705273633 14311690908480557028955225)
        ·
          refine ⟨10733768181360417771716419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14311690908480557028955225 10733768181360417771716419)
          ·
            refine ⟨16100652272040626657574629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733768181360417771716419 16100652272040626657574629)
            ·
              refine ⟨3018872301007617498295243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16100652272040626657574629 3018872301007617498295243)
              ·
                refine ⟨4528308451511426247442865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018872301007617498295243 4528308451511426247442865)
                ·
                  refine ⟨3396231338633569685582149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528308451511426247442865 3396231338633569685582149)
                  ·
                    refine ⟨636793375993794316046653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396231338633569685582149 636793375993794316046653)
                    ·
                      rfl

theorem cell23_3720452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_3720452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720452 prefixEnd_3720452 := by exact prefixLift 3720452
  have htrace : WordTrace (prefixWord ++ tailWord_3720452) baseStart_3720452 baseEnd_3720452 := by
    simpa [prefixWord, tailWord_3720452, baseEnd_3720452] using wordTrace_append hprefix tailTrace_3720452
  have hstable : (prefixWord ++ tailWord_3720452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720452).length < 2 ^ (prefixWord ++ tailWord_3720452).sum := by decide
  have hdescent : baseEnd_3720452 < baseStart_3720452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720458 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3720458 : Nat := 118140960795 + 3720458 * 2 ^ 59
def prefixEnd_3720458 : Nat := 4983230072969 + 3 ^ 40 * 3720458 * 2
def baseEnd_3720458 : Nat := 1910383208865309924664931

theorem tailTrace_3720458 : CollatzResearch.WordTrace tailWord_3720458 prefixEnd_3720458 1910383208865309924664931 := by
  unfold tailWord_3720458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924062788855886121110507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90464167436949029656294685 33924062788855886121110507)
  ·
    refine ⟨50886094183283829181665761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33924062788855886121110507 50886094183283829181665761)
    ·
      refine ⟨38164570637462871886249321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50886094183283829181665761 38164570637462871886249321)
      ·
        refine ⟨28623427978097153914686991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38164570637462871886249321 28623427978097153914686991)
        ·
          refine ⟨42935141967145730872030487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28623427978097153914686991 42935141967145730872030487)
          ·
            refine ⟨64402712950718596308045731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42935141967145730872030487 64402712950718596308045731)
            ·
              refine ⟨96604069426077894462068597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64402712950718596308045731 96604069426077894462068597)
              ·
                refine ⟨9056631508694802605818931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96604069426077894462068597 9056631508694802605818931)
                ·
                  refine ⟨13584947263042203908728397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056631508694802605818931 13584947263042203908728397)
                  ·
                    refine ⟨5094355223640826465773149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13584947263042203908728397 5094355223640826465773149)
                    ·
                      refine ⟨1910383208865309924664931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094355223640826465773149 1910383208865309924664931)
                      ·
                        rfl

theorem cell23_3720458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3720458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720458 prefixEnd_3720458 := by exact prefixLift 3720458
  have htrace : WordTrace (prefixWord ++ tailWord_3720458) baseStart_3720458 baseEnd_3720458 := by
    simpa [prefixWord, tailWord_3720458, baseEnd_3720458] using wordTrace_append hprefix tailTrace_3720458
  have hstable : (prefixWord ++ tailWord_3720458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720458).length < 2 ^ (prefixWord ++ tailWord_3720458).sum := by decide
  have hdescent : baseEnd_3720458 < baseStart_3720458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720462 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3720462 : Nat := 118140960795 + 3720462 * 2 ^ 59
def prefixEnd_3720462 : Nat := 4983230072969 + 3 ^ 40 * 3720462 * 2
def baseEnd_3720462 : Nat := 1910385262787927909014913

theorem tailTrace_3720462 : CollatzResearch.WordTrace tailWord_3720462 prefixEnd_3720462 1910385262787927909014913 := by
  unfold tailWord_3720462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962049630926131645948455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90464264698272702111725093 16962049630926131645948455)
  ·
    refine ⟨25443074446389197468922683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962049630926131645948455 25443074446389197468922683)
    ·
      refine ⟨38164611669583796203384025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25443074446389197468922683 38164611669583796203384025)
      ·
        refine ⟨28623458752187847152538019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38164611669583796203384025 28623458752187847152538019)
        ·
          refine ⟨42935188128281770728807029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28623458752187847152538019 42935188128281770728807029)
          ·
            refine ⟨4025173887026416005825659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42935188128281770728807029 4025173887026416005825659)
            ·
              refine ⟨6037760830539624008738489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025173887026416005825659 6037760830539624008738489)
              ·
                refine ⟨4528320622904718006553867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6037760830539624008738489 4528320622904718006553867)
                ·
                  refine ⟨6792480934357077009830801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528320622904718006553867 6792480934357077009830801)
                  ·
                    refine ⟨5094360700767807757373101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6792480934357077009830801 5094360700767807757373101)
                    ·
                      refine ⟨1910385262787927909014913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094360700767807757373101 1910385262787927909014913)
                      ·
                        rfl

theorem cell23_3720462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3720462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720462 prefixEnd_3720462 := by exact prefixLift 3720462
  have htrace : WordTrace (prefixWord ++ tailWord_3720462) baseStart_3720462 baseEnd_3720462 := by
    simpa [prefixWord, tailWord_3720462, baseEnd_3720462] using wordTrace_append hprefix tailTrace_3720462
  have hstable : (prefixWord ++ tailWord_3720462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720462).length < 2 ^ (prefixWord ++ tailWord_3720462).sum := by decide
  have hdescent : baseEnd_3720462 < baseStart_3720462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720493 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3720493 : Nat := 118140960795 + 3720493 * 2 ^ 59
def prefixEnd_3720493 : Nat := 4983230072969 + 3 ^ 40 * 3720493 * 2
def baseEnd_3720493 : Nat := 1910401180688217287727271

theorem tailTrace_3720493 : CollatzResearch.WordTrace tailWord_3720493 prefixEnd_3720493 1910401180688217287727271 := by
  unfold tailWord_3720493
  simp only [CollatzResearch.WordTrace]
  refine ⟨135697527710296745461966133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90465018473531163641310755 135697527710296745461966133)
  ·
    refine ⟨12721643222840319887059325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135697527710296745461966133 12721643222840319887059325)
    ·
      refine ⟨4770616208565119957647247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12721643222840319887059325 4770616208565119957647247)
      ·
        refine ⟨7155924312847679936470871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770616208565119957647247 7155924312847679936470871)
        ·
          refine ⟨10733886469271519904706307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155924312847679936470871 10733886469271519904706307)
          ·
            refine ⟨16100829703907279857059461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733886469271519904706307 16100829703907279857059461)
            ·
              refine ⟨3018905569482614973198649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16100829703907279857059461 3018905569482614973198649)
              ·
                refine ⟨2264179177111961229898987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018905569482614973198649 2264179177111961229898987)
                ·
                  refine ⟨3396268765667941844848481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264179177111961229898987 3396268765667941844848481)
                  ·
                    refine ⟨2547201574250956383636361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396268765667941844848481 2547201574250956383636361)
                    ·
                      refine ⟨1910401180688217287727271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547201574250956383636361 1910401180688217287727271)
                      ·
                        rfl

theorem cell23_3720493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3720493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720493 prefixEnd_3720493 := by exact prefixLift 3720493
  have htrace : WordTrace (prefixWord ++ tailWord_3720493) baseStart_3720493 baseEnd_3720493 := by
    simpa [prefixWord, tailWord_3720493, baseEnd_3720493] using wordTrace_append hprefix tailTrace_3720493
  have hstable : (prefixWord ++ tailWord_3720493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720493).length < 2 ^ (prefixWord ++ tailWord_3720493).sum := by decide
  have hdescent : baseEnd_3720493 < baseStart_3720493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720498 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3720498 : Nat := 118140960795 + 3720498 * 2 ^ 59
def prefixEnd_3720498 : Nat := 4983230072969 + 3 ^ 40 * 3720498 * 2
def baseEnd_3720498 : Nat := 1910403748091489768164747

theorem tailTrace_3720498 : CollatzResearch.WordTrace tailWord_3720498 prefixEnd_3720498 1910403748091489768164747 := by
  unfold tailWord_3720498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924427518819657828974537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90465140050185754210598765 33924427518819657828974537)
  ·
    refine ⟨25443320639114743371730903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33924427518819657828974537 25443320639114743371730903)
    ·
      refine ⟨38164980958672115057596355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25443320639114743371730903 38164980958672115057596355)
      ·
        refine ⟨57247471438008172586394533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38164980958672115057596355 57247471438008172586394533)
        ·
          refine ⟨10733900894626532359948975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57247471438008172586394533 10733900894626532359948975)
          ·
            refine ⟨16100851341939798539923463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10733900894626532359948975 16100851341939798539923463)
            ·
              refine ⟨24151277012909697809885195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16100851341939798539923463 24151277012909697809885195)
              ·
                refine ⟨36226915519364546714827793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24151277012909697809885195 36226915519364546714827793)
                ·
                  refine ⟨27170186639523410036120845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36226915519364546714827793 27170186639523410036120845)
                  ·
                    refine ⟨10188819989821278763545317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27170186639523410036120845 10188819989821278763545317)
                    ·
                      refine ⟨1910403748091489768164747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10188819989821278763545317 1910403748091489768164747)
                      ·
                        rfl

theorem cell23_3720498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3720498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720498 prefixEnd_3720498 := by exact prefixLift 3720498
  have htrace : WordTrace (prefixWord ++ tailWord_3720498) baseStart_3720498 baseEnd_3720498 := by
    simpa [prefixWord, tailWord_3720498, baseEnd_3720498] using wordTrace_append hprefix tailTrace_3720498
  have hstable : (prefixWord ++ tailWord_3720498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720498).length < 2 ^ (prefixWord ++ tailWord_3720498).sum := by decide
  have hdescent : baseEnd_3720498 < baseStart_3720498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720508 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_3720508 : Nat := 118140960795 + 3720508 * 2 ^ 59
def prefixEnd_3720508 : Nat := 4983230072969 + 3 ^ 40 * 3720508 * 2
def baseEnd_3720508 : Nat := 636802960966011576346567

theorem tailTrace_3720508 : CollatzResearch.WordTrace tailWord_3720508 prefixEnd_3720508 636802960966011576346567 := by
  unfold tailWord_3720508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849037402621201511881089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90465383203494935349174785 67849037402621201511881089)
  ·
    refine ⟨50886778051965901133910817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67849037402621201511881089 50886778051965901133910817)
    ·
      refine ⟨38165083538974425850433113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50886778051965901133910817 38165083538974425850433113)
      ·
        refine ⟨28623812654230819387824835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38165083538974425850433113 28623812654230819387824835)
        ·
          refine ⟨42935718981346229081737253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28623812654230819387824835 42935718981346229081737253)
          ·
            refine ⟨8050447309002417952825735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42935718981346229081737253 8050447309002417952825735)
            ·
              refine ⟨12075670963503626929238603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050447309002417952825735 12075670963503626929238603)
              ·
                refine ⟨18113506445255440393857905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12075670963503626929238603 18113506445255440393857905)
                ·
                  refine ⟨13585129833941580295393429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18113506445255440393857905 13585129833941580295393429)
                  ·
                    refine ⟨636802960966011576346567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13585129833941580295393429 636802960966011576346567)
                    ·
                      rfl

theorem cell23_3720508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_3720508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720508 prefixEnd_3720508 := by exact prefixLift 3720508
  have htrace : WordTrace (prefixWord ++ tailWord_3720508) baseStart_3720508 baseEnd_3720508 := by
    simpa [prefixWord, tailWord_3720508, baseEnd_3720508] using wordTrace_append hprefix tailTrace_3720508
  have hstable : (prefixWord ++ tailWord_3720508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720508).length < 2 ^ (prefixWord ++ tailWord_3720508).sum := by decide
  have hdescent : baseEnd_3720508 < baseStart_3720508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720515 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 6, 2, 2]
def baseStart_3720515 : Nat := 118140960795 + 3720515 * 2 ^ 59
def prefixEnd_3720515 : Nat := 4983230072969 + 3 ^ 40 * 3720515 * 2
def baseEnd_3720515 : Nat := 1910412477262616201652169

theorem tailTrace_3720515 : CollatzResearch.WordTrace tailWord_3720515 prefixEnd_3720515 1910412477262616201652169 := by
  unfold tailWord_3720515
  simp only [CollatzResearch.WordTrace]
  refine ⟨135698330116217043219266999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90465553410811362146177999 135698330116217043219266999)
  ·
    refine ⟨203547495174325564828900499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135698330116217043219266999 203547495174325564828900499)
    ·
      refine ⟨305321242761488347243350749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203547495174325564828900499 305321242761488347243350749)
      ·
        refine ⟨114495466035558130216256531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305321242761488347243350749 114495466035558130216256531)
        ·
          refine ⟨171743199053337195324384797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114495466035558130216256531 171743199053337195324384797)
          ·
            refine ⟨64403699645001448246644299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171743199053337195324384797 64403699645001448246644299)
            ·
              refine ⟨96605549467502172369966449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64403699645001448246644299 96605549467502172369966449)
              ·
                refine ⟨72454162100626629277474837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96605549467502172369966449 72454162100626629277474837)
                ·
                  refine ⟨3396288848466873247381633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72454162100626629277474837 3396288848466873247381633)
                  ·
                    refine ⟨2547216636350154935536225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396288848466873247381633 2547216636350154935536225)
                    ·
                      refine ⟨1910412477262616201652169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547216636350154935536225 1910412477262616201652169)
                      ·
                        rfl

theorem cell23_3720515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_3720515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720515 prefixEnd_3720515 := by exact prefixLift 3720515
  have htrace : WordTrace (prefixWord ++ tailWord_3720515) baseStart_3720515 baseEnd_3720515 := by
    simpa [prefixWord, tailWord_3720515, baseEnd_3720515] using wordTrace_append hprefix tailTrace_3720515
  have hstable : (prefixWord ++ tailWord_3720515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720515).length < 2 ^ (prefixWord ++ tailWord_3720515).sum := by decide
  have hdescent : baseEnd_3720515 < baseStart_3720515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720521 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 9]
def baseStart_3720521 : Nat := 118140960795 + 3720521 * 2 ^ 59
def prefixEnd_3720521 : Nat := 4983230072969 + 3 ^ 40 * 3720521 * 2
def baseEnd_3720521 : Nat := 212268395349615908686349

theorem tailTrace_3720521 : CollatzResearch.WordTrace tailWord_3720521 prefixEnd_3720521 212268395349615908686349 := by
  unfold tailWord_3720521
  simp only [CollatzResearch.WordTrace]
  refine ⟨135698548954195306243985417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90465699302796870829323611 135698548954195306243985417)
  ·
    refine ⟨101773911715646479682989063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135698548954195306243985417 101773911715646479682989063)
    ·
      refine ⟨152660867573469719524483595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101773911715646479682989063 152660867573469719524483595)
      ·
        refine ⟨228991301360204579286725393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152660867573469719524483595 228991301360204579286725393)
        ·
          refine ⟨171743476020153434465044045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228991301360204579286725393 171743476020153434465044045)
          ·
            refine ⟨64403803507557537924391517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171743476020153434465044045 64403803507557537924391517)
            ·
              refine ⟨24151426315334076721646819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64403803507557537924391517 24151426315334076721646819)
              ·
                refine ⟨36227139473001115082470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24151426315334076721646819 36227139473001115082470229)
                ·
                  refine ⟨212268395349615908686349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36227139473001115082470229 212268395349615908686349)
                  ·
                    rfl

theorem cell23_3720521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_3720521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720521 prefixEnd_3720521 := by exact prefixLift 3720521
  have htrace : WordTrace (prefixWord ++ tailWord_3720521) baseStart_3720521 baseEnd_3720521 := by
    simpa [prefixWord, tailWord_3720521, baseEnd_3720521] using wordTrace_append hprefix tailTrace_3720521
  have hstable : (prefixWord ++ tailWord_3720521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720521).length < 2 ^ (prefixWord ++ tailWord_3720521).sum := by decide
  have hdescent : baseEnd_3720521 < baseStart_3720521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720532 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_3720532 : Nat := 118140960795 + 3720532 * 2 ^ 59
def prefixEnd_3720532 : Nat := 4983230072969 + 3 ^ 40 * 3720532 * 2
def baseEnd_3720532 : Nat := 1910421206433742635139591

theorem tailTrace_3720532 : CollatzResearch.WordTrace tailWord_3720532 prefixEnd_3720532 1910421206433742635139591 := by
  unfold tailWord_3720532
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849475078577727561317925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90465966771436970081757233 67849475078577727561317925)
  ·
    refine ⟨12721776577233323917747111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67849475078577727561317925 12721776577233323917747111)
    ·
      refine ⟨19082664865849985876620667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12721776577233323917747111 19082664865849985876620667)
      ·
        refine ⟨28623997298774978814931001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19082664865849985876620667 28623997298774978814931001)
        ·
          refine ⟨21467997974081234111198251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28623997298774978814931001 21467997974081234111198251)
          ·
            refine ⟨32201996961121851166797377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21467997974081234111198251 32201996961121851166797377)
            ·
              refine ⟨24151497720841388375098033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32201996961121851166797377 24151497720841388375098033)
              ·
                refine ⟨18113623290631041281323525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24151497720841388375098033 18113623290631041281323525)
                ·
                  refine ⟨3396304366993320240248161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18113623290631041281323525 3396304366993320240248161)
                  ·
                    refine ⟨2547228275244990180186121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396304366993320240248161 2547228275244990180186121)
                    ·
                      refine ⟨1910421206433742635139591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547228275244990180186121 1910421206433742635139591)
                      ·
                        rfl

theorem cell23_3720532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_3720532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720532 prefixEnd_3720532 := by exact prefixLift 3720532
  have htrace : WordTrace (prefixWord ++ tailWord_3720532) baseStart_3720532 baseEnd_3720532 := by
    simpa [prefixWord, tailWord_3720532, baseEnd_3720532] using wordTrace_append hprefix tailTrace_3720532
  have hstable : (prefixWord ++ tailWord_3720532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720532).length < 2 ^ (prefixWord ++ tailWord_3720532).sum := by decide
  have hdescent : baseEnd_3720532 < baseStart_3720532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720588 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_3720588 : Nat := 118140960795 + 3720588 * 2 ^ 59
def prefixEnd_3720588 : Nat := 4983230072969 + 3 ^ 40 * 3720588 * 2
def baseEnd_3720588 : Nat := 1910449961350394416039333

theorem tailTrace_3720588 : CollatzResearch.WordTrace tailWord_3720588 prefixEnd_3720588 1910449961350394416039333 := by
  unfold tailWord_3720588
  simp only [CollatzResearch.WordTrace]
  refine ⟨67850496322476288343337209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90467328429968384457782945 67850496322476288343337209)
  ·
    refine ⟨50887872241857216257502907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67850496322476288343337209 50887872241857216257502907)
    ·
      refine ⟨76331808362785824386254361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50887872241857216257502907 76331808362785824386254361)
      ·
        refine ⟨57248856272089368289690771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76331808362785824386254361 57248856272089368289690771)
        ·
          refine ⟨85873284408134052434536157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57248856272089368289690771 85873284408134052434536157)
          ·
            refine ⟨32202481653050269662951059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85873284408134052434536157 32202481653050269662951059)
            ·
              refine ⟨48303722479575404494426589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32202481653050269662951059 48303722479575404494426589)
              ·
                refine ⟨18113895929840776685409971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48303722479575404494426589 18113895929840776685409971)
                ·
                  refine ⟨27170843894761165028114957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18113895929840776685409971 27170843894761165028114957)
                  ·
                    refine ⟨10189066460535436885543109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27170843894761165028114957 10189066460535436885543109)
                    ·
                      refine ⟨1910449961350394416039333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10189066460535436885543109 1910449961350394416039333)
                      ·
                        rfl

theorem cell23_3720588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_3720588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720588 prefixEnd_3720588 := by exact prefixLift 3720588
  have htrace : WordTrace (prefixWord ++ tailWord_3720588) baseStart_3720588 baseEnd_3720588 := by
    simpa [prefixWord, tailWord_3720588, baseEnd_3720588] using wordTrace_append hprefix tailTrace_3720588
  have hstable : (prefixWord ++ tailWord_3720588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720588).length < 2 ^ (prefixWord ++ tailWord_3720588).sum := by decide
  have hdescent : baseEnd_3720588 < baseStart_3720588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720605 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3720605 : Nat := 118140960795 + 3720605 * 2 ^ 59
def prefixEnd_3720605 : Nat := 4983230072969 + 3 ^ 40 * 3720605 * 2
def baseEnd_3720605 : Nat := 1910458690521520849526755

theorem tailTrace_3720605 : CollatzResearch.WordTrace tailWord_3720605 prefixEnd_3720605 1910458690521520849526755 := by
  unfold tailWord_3720605
  simp only [CollatzResearch.WordTrace]
  refine ⟨135701612685890988590043269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90467741790593992393362179 135701612685890988590043269)
  ·
    refine ⟨25444052378604560360633113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135701612685890988590043269 25444052378604560360633113)
    ·
      refine ⟨19083039283953420270474835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25444052378604560360633113 19083039283953420270474835)
      ·
        refine ⟨28624558925930130405712253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19083039283953420270474835 28624558925930130405712253)
        ·
          refine ⟨10734209597223798902142095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28624558925930130405712253 10734209597223798902142095)
          ·
            refine ⟨16101314395835698353213143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734209597223798902142095 16101314395835698353213143)
            ·
              refine ⟨24151971593753547529819715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16101314395835698353213143 24151971593753547529819715)
              ·
                refine ⟨36227957390630321294729573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24151971593753547529819715 36227957390630321294729573)
                ·
                  refine ⟨6792742010743185242761795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36227957390630321294729573 6792742010743185242761795)
                  ·
                    refine ⟨10189113016114777864142693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6792742010743185242761795 10189113016114777864142693)
                    ·
                      refine ⟨1910458690521520849526755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10189113016114777864142693 1910458690521520849526755)
                      ·
                        rfl

theorem cell23_3720605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3720605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720605 prefixEnd_3720605 := by exact prefixLift 3720605
  have htrace : WordTrace (prefixWord ++ tailWord_3720605) baseStart_3720605 baseEnd_3720605 := by
    simpa [prefixWord, tailWord_3720605, baseEnd_3720605] using wordTrace_append hprefix tailTrace_3720605
  have hstable : (prefixWord ++ tailWord_3720605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720605).length < 2 ^ (prefixWord ++ tailWord_3720605).sum := by decide
  have hdescent : baseEnd_3720605 < baseStart_3720605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720606 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3720606 : Nat := 118140960795 + 3720606 * 2 ^ 59
def prefixEnd_3720606 : Nat := 4983230072969 + 3 ^ 40 * 3720606 * 2
def baseEnd_3720606 : Nat := 212273244889130593957139

theorem tailTrace_3720606 : CollatzResearch.WordTrace tailWord_3720606 prefixEnd_3720606 212273244889130593957139 := by
  unfold tailWord_3720606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962706144860920720103709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90467766105924910507219781 16962706144860920720103709)
  ·
    refine ⟨6361014804322845270038891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16962706144860920720103709 6361014804322845270038891)
    ·
      refine ⟨9541522206484267905058337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361014804322845270038891 9541522206484267905058337)
      ·
        refine ⟨7156141654863200928793753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9541522206484267905058337 7156141654863200928793753)
        ·
          refine ⟨5367106241147400696595315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7156141654863200928793753 5367106241147400696595315)
          ·
            refine ⟨8050659361721101044892973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367106241147400696595315 8050659361721101044892973)
            ·
              refine ⟨3018997260645412891834865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8050659361721101044892973 3018997260645412891834865)
              ·
                refine ⟨2264247945484059668876149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018997260645412891834865 2264247945484059668876149)
                ·
                  refine ⟨212273244889130593957139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2264247945484059668876149 212273244889130593957139)
                  ·
                    rfl

theorem cell23_3720606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3720606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720606 prefixEnd_3720606 := by exact prefixLift 3720606
  have htrace : WordTrace (prefixWord ++ tailWord_3720606) baseStart_3720606 baseEnd_3720606 := by
    simpa [prefixWord, tailWord_3720606, baseEnd_3720606] using wordTrace_append hprefix tailTrace_3720606
  have hstable : (prefixWord ++ tailWord_3720606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720606).length < 2 ^ (prefixWord ++ tailWord_3720606).sum := by decide
  have hdescent : baseEnd_3720606 < baseStart_3720606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720625 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3720625 : Nat := 118140960795 + 3720625 * 2 ^ 59
def prefixEnd_3720625 : Nat := 4983230072969 + 3 ^ 40 * 3720625 * 2
def baseEnd_3720625 : Nat := 1910468960134610771276663

theorem tailTrace_3720625 : CollatzResearch.WordTrace tailWord_3720625 prefixEnd_3720625 1910468960134610771276663 := by
  unfold tailWord_3720625
  simp only [CollatzResearch.WordTrace]
  refine ⟨135702342145818532005771329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90468228097212354670514219 135702342145818532005771329)
  ·
    refine ⟨101776756609363899004328497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135702342145818532005771329 101776756609363899004328497)
    ·
      refine ⟨76332567457022924253246373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101776756609363899004328497 76332567457022924253246373)
      ·
        refine ⟨14312356398191798297483695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76332567457022924253246373 14312356398191798297483695)
        ·
          refine ⟨21468534597287697446225543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14312356398191798297483695 21468534597287697446225543)
          ·
            refine ⟨32202801895931546169338315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21468534597287697446225543 32202801895931546169338315)
            ·
              refine ⟨48304202843897319254007473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32202801895931546169338315 48304202843897319254007473)
              ·
                refine ⟨36228152132922989440505605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48304202843897319254007473 36228152132922989440505605)
                ·
                  refine ⟨6792778524923060520094801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36228152132922989440505605 6792778524923060520094801)
                  ·
                    refine ⟨5094583893692295390071101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6792778524923060520094801 5094583893692295390071101)
                    ·
                      refine ⟨1910468960134610771276663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094583893692295390071101 1910468960134610771276663)
                      ·
                        rfl

theorem cell23_3720625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3720625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720625 prefixEnd_3720625 := by exact prefixLift 3720625
  have htrace : WordTrace (prefixWord ++ tailWord_3720625) baseStart_3720625 baseEnd_3720625 := by
    simpa [prefixWord, tailWord_3720625, baseEnd_3720625] using wordTrace_append hprefix tailTrace_3720625
  have hstable : (prefixWord ++ tailWord_3720625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720625).length < 2 ^ (prefixWord ++ tailWord_3720625).sum := by decide
  have hdescent : baseEnd_3720625 < baseStart_3720625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720662 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3720662 : Nat := 118140960795 + 3720662 * 2 ^ 59
def prefixEnd_3720662 : Nat := 4983230072969 + 3 ^ 40 * 3720662 * 2
def baseEnd_3720662 : Nat := 212276439879869680723777

theorem tailTrace_3720662 : CollatzResearch.WordTrace tailWord_3720662 prefixEnd_3720662 212276439879869680723777 := by
  unfold tailWord_3720662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481480727917780457804265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90469127764456324883245493 8481480727917780457804265)
  ·
    refine ⟨6361110545938335343353199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8481480727917780457804265 6361110545938335343353199)
    ·
      refine ⟨9541665818907503015029799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361110545938335343353199 9541665818907503015029799)
      ·
        refine ⟨14312498728361254522544699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9541665818907503015029799 14312498728361254522544699)
        ·
          refine ⟨21468748092541881783817049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14312498728361254522544699 21468748092541881783817049)
          ·
            refine ⟨16101561069406411337862787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21468748092541881783817049 16101561069406411337862787)
            ·
              refine ⟨24152341604109617006794181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16101561069406411337862787 24152341604109617006794181)
              ·
                refine ⟨4528564050770553188773909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24152341604109617006794181 4528564050770553188773909)
                ·
                  refine ⟨212276439879869680723777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4528564050770553188773909 212276439879869680723777)
                  ·
                    rfl

theorem cell23_3720662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3720662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720662 prefixEnd_3720662 := by exact prefixLift 3720662
  have htrace : WordTrace (prefixWord ++ tailWord_3720662) baseStart_3720662 baseEnd_3720662 := by
    simpa [prefixWord, tailWord_3720662, baseEnd_3720662] using wordTrace_append hprefix tailTrace_3720662
  have hstable : (prefixWord ++ tailWord_3720662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720662).length < 2 ^ (prefixWord ++ tailWord_3720662).sum := by decide
  have hdescent : baseEnd_3720662 < baseStart_3720662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720666 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_3720666 : Nat := 118140960795 + 3720666 * 2 ^ 59
def prefixEnd_3720666 : Nat := 4983230072969 + 3 ^ 40 * 3720666 * 2
def baseEnd_3720666 : Nat := 636830004280481703621325

theorem tailTrace_3720666 : CollatzResearch.WordTrace tailWord_3720666 prefixEnd_3720666 636830004280481703621325 := by
  unfold tailWord_3720666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925959384667499002003463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90469225025779997338675901 33925959384667499002003463)
  ·
    refine ⟨50888939077001248503005195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33925959384667499002003463 50888939077001248503005195)
    ·
      refine ⟨76333408615501872754507793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50888939077001248503005195 76333408615501872754507793)
      ·
        refine ⟨57250056461626404565880845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76333408615501872754507793 57250056461626404565880845)
        ·
          refine ⟨21468771173109901712205317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57250056461626404565880845 21468771173109901712205317)
          ·
            refine ⟨4025394594958106571038497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21468771173109901712205317 4025394594958106571038497)
            ·
              refine ⟨3019045946218579928278873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4025394594958106571038497 3019045946218579928278873)
              ·
                refine ⟨2264284459663934946209155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019045946218579928278873 2264284459663934946209155)
                ·
                  refine ⟨3396426689495902419313733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264284459663934946209155 3396426689495902419313733)
                  ·
                    refine ⟨636830004280481703621325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396426689495902419313733 636830004280481703621325)
                    ·
                      rfl

theorem cell23_3720666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_3720666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720666 prefixEnd_3720666 := by exact prefixLift 3720666
  have htrace : WordTrace (prefixWord ++ tailWord_3720666) baseStart_3720666 baseEnd_3720666 := by
    simpa [prefixWord, tailWord_3720666, baseEnd_3720666] using wordTrace_append hprefix tailTrace_3720666
  have hstable : (prefixWord ++ tailWord_3720666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720666).length < 2 ^ (prefixWord ++ tailWord_3720666).sum := by decide
  have hdescent : baseEnd_3720666 < baseStart_3720666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720675 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 3, 5]
def baseStart_3720675 : Nat := 118140960795 + 3720675 * 2 ^ 59
def prefixEnd_3720675 : Nat := 4983230072969 + 3 ^ 40 * 3720675 * 2
def baseEnd_3720675 : Nat := 636831544722445191883811

theorem tailTrace_3720675 : CollatzResearch.WordTrace tailWord_3720675 prefixEnd_3720675 636831544722445191883811 := by
  unfold tailWord_3720675
  simp only [CollatzResearch.WordTrace]
  refine ⟨135704165795637390545091479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90469443863758260363394319 135704165795637390545091479)
  ·
    refine ⟨203556248693456085817637219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135704165795637390545091479 203556248693456085817637219)
    ·
      refine ⟨305334373040184128726455829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203556248693456085817637219 305334373040184128726455829)
      ·
        refine ⟨14312548736258631034052617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 305334373040184128726455829 14312548736258631034052617)
        ·
          refine ⟨10734411552193973275539463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14312548736258631034052617 10734411552193973275539463)
          ·
            refine ⟨16101617328290959913309195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734411552193973275539463 16101617328290959913309195)
            ·
              refine ⟨24152425992436439869963793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16101617328290959913309195 24152425992436439869963793)
              ·
                refine ⟨18114319494327329902472845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24152425992436439869963793 18114319494327329902472845)
                ·
                  refine ⟨6792869810372748713427317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18114319494327329902472845 6792869810372748713427317)
                  ·
                    refine ⟨636831544722445191883811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6792869810372748713427317 636831544722445191883811)
                    ·
                      rfl

theorem cell23_3720675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 5].length) (baseStart_3720675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720675 prefixEnd_3720675 := by exact prefixLift 3720675
  have htrace : WordTrace (prefixWord ++ tailWord_3720675) baseStart_3720675 baseEnd_3720675 := by
    simpa [prefixWord, tailWord_3720675, baseEnd_3720675] using wordTrace_append hprefix tailTrace_3720675
  have hstable : (prefixWord ++ tailWord_3720675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720675).length < 2 ^ (prefixWord ++ tailWord_3720675).sum := by decide
  have hdescent : baseEnd_3720675 < baseStart_3720675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720695 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_3720695 : Nat := 118140960795 + 3720695 * 2 ^ 59
def prefixEnd_3720695 : Nat := 4983230072969 + 3 ^ 40 * 3720695 * 2
def baseEnd_3720695 : Nat := 1910504903780425497401341

theorem tailTrace_3720695 : CollatzResearch.WordTrace tailWord_3720695 prefixEnd_3720695 1910504903780425497401341 := by
  unfold tailWord_3720695
  simp only [CollatzResearch.WordTrace]
  refine ⟨135704895255564933960819539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90469930170376622640546359 135704895255564933960819539)
  ·
    refine ⟨203557342883347400941229309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135704895255564933960819539 203557342883347400941229309)
    ·
      refine ⟨76334003581255275352960991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203557342883347400941229309 76334003581255275352960991)
      ·
        refine ⟨114501005371882913029441487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76334003581255275352960991 114501005371882913029441487)
        ·
          refine ⟨171751508057824369544162231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114501005371882913029441487 171751508057824369544162231)
          ·
            refine ⟨257627262086736554316243347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171751508057824369544162231 257627262086736554316243347)
            ·
              refine ⟨386440893130104831474365021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257627262086736554316243347 386440893130104831474365021)
              ·
                refine ⟨144915334923789311802886883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386440893130104831474365021 144915334923789311802886883)
                ·
                  refine ⟨217373002385683967704330325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144915334923789311802886883 217373002385683967704330325)
                  ·
                    refine ⟨2547339871707233996535121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 217373002385683967704330325 2547339871707233996535121)
                    ·
                      refine ⟨1910504903780425497401341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547339871707233996535121 1910504903780425497401341)
                      ·
                        rfl

theorem cell23_3720695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_3720695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720695 prefixEnd_3720695 := by exact prefixLift 3720695
  have htrace : WordTrace (prefixWord ++ tailWord_3720695) baseStart_3720695 baseEnd_3720695 := by
    simpa [prefixWord, tailWord_3720695, baseEnd_3720695] using wordTrace_append hprefix tailTrace_3720695
  have hstable : (prefixWord ++ tailWord_3720695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720695).length < 2 ^ (prefixWord ++ tailWord_3720695).sum := by decide
  have hdescent : baseEnd_3720695 < baseStart_3720695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720739 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 1, 6]
def baseStart_3720739 : Nat := 118140960795 + 3720739 * 2 ^ 59
def prefixEnd_3720739 : Nat := 4983230072969 + 3 ^ 40 * 3720739 * 2
def baseEnd_3720739 : Nat := 636842498976407775083713

theorem tailTrace_3720739 : CollatzResearch.WordTrace tailWord_3720739 prefixEnd_3720739 636842498976407775083713 := by
  unfold tailWord_3720739
  simp only [CollatzResearch.WordTrace]
  refine ⟨135706500067405529475421271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90471000044937019650280847 135706500067405529475421271)
  ·
    refine ⟨203559750101108294213131907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135706500067405529475421271 203559750101108294213131907)
    ·
      refine ⟨305339625151662441319697861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203559750101108294213131907 305339625151662441319697861)
      ·
        refine ⟨57251179715936707747443349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305339625151662441319697861 57251179715936707747443349)
        ·
          refine ⟨2683649049184533175661407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57251179715936707747443349 2683649049184533175661407)
          ·
            refine ⟨4025473573776799763492111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683649049184533175661407 4025473573776799763492111)
            ·
              refine ⟨6038210360665199645238167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025473573776799763492111 6038210360665199645238167)
              ·
                refine ⟨9057315540997799467857251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038210360665199645238167 9057315540997799467857251)
                ·
                  refine ⟨13585973311496699201785877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9057315540997799467857251 13585973311496699201785877)
                  ·
                    refine ⟨636842498976407775083713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13585973311496699201785877 636842498976407775083713)
                    ·
                      rfl

theorem cell23_3720739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 6].length) (baseStart_3720739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720739 prefixEnd_3720739 := by exact prefixLift 3720739
  have htrace : WordTrace (prefixWord ++ tailWord_3720739) baseStart_3720739 baseEnd_3720739 := by
    simpa [prefixWord, tailWord_3720739, baseEnd_3720739] using wordTrace_append hprefix tailTrace_3720739
  have hstable : (prefixWord ++ tailWord_3720739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720739).length < 2 ^ (prefixWord ++ tailWord_3720739).sum := by decide
  have hdescent : baseEnd_3720739 < baseStart_3720739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720762 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_3720762 : Nat := 118140960795 + 3720762 * 2 ^ 59
def prefixEnd_3720762 : Nat := 4983230072969 + 3 ^ 40 * 3720762 * 2
def baseEnd_3720762 : Nat := 1910539306984276735263533

theorem tailTrace_3720762 : CollatzResearch.WordTrace tailWord_3720762 prefixEnd_3720762 1910539306984276735263533 := by
  unfold tailWord_3720762
  simp only [CollatzResearch.WordTrace]
  refine ⟨33926834736580551100877135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90471559297548136269005693 33926834736580551100877135)
  ·
    refine ⟨50890252104870826651315703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33926834736580551100877135 50890252104870826651315703)
    ·
      refine ⟨76335378157306239976973555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50890252104870826651315703 76335378157306239976973555)
      ·
        refine ⟨114503067235959359965460333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76335378157306239976973555 114503067235959359965460333)
        ·
          refine ⟨42938650213484759987047625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114503067235959359965460333 42938650213484759987047625)
          ·
            refine ⟨32203987660113569990285719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42938650213484759987047625 32203987660113569990285719)
            ·
              refine ⟨48305981490170354985428579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32203987660113569990285719 48305981490170354985428579)
              ·
                refine ⟨72458972235255532478142869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48305981490170354985428579 72458972235255532478142869)
                ·
                  refine ⟨3396514323527603084912947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72458972235255532478142869 3396514323527603084912947)
                  ·
                    refine ⟨5094771485291404627369421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396514323527603084912947 5094771485291404627369421)
                    ·
                      refine ⟨1910539306984276735263533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094771485291404627369421 1910539306984276735263533)
                      ·
                        rfl

theorem cell23_3720762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_3720762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720762 prefixEnd_3720762 := by exact prefixLift 3720762
  have htrace : WordTrace (prefixWord ++ tailWord_3720762) baseStart_3720762 baseEnd_3720762 := by
    simpa [prefixWord, tailWord_3720762, baseEnd_3720762] using wordTrace_append hprefix tailTrace_3720762
  have hstable : (prefixWord ++ tailWord_3720762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720762).length < 2 ^ (prefixWord ++ tailWord_3720762).sum := by decide
  have hdescent : baseEnd_3720762 < baseStart_3720762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720785 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3720785 : Nat := 118140960795 + 3720785 * 2 ^ 59
def prefixEnd_3720785 : Nat := 4983230072969 + 3 ^ 40 * 3720785 * 2
def baseEnd_3720785 : Nat := 1910551117039330145275927

theorem tailTrace_3720785 : CollatzResearch.WordTrace tailWord_3720785 prefixEnd_3720785 1910551117039330145275927 := by
  unfold tailWord_3720785
  simp only [CollatzResearch.WordTrace]
  refine ⟨135708177825238879331595809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90472118550159252887730539 135708177825238879331595809)
  ·
    refine ⟨101781133368929159498696857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135708177825238879331595809 101781133368929159498696857)
    ·
      refine ⟨76335850026696869624022643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101781133368929159498696857 76335850026696869624022643)
      ·
        refine ⟨114503775040045304436033965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76335850026696869624022643 114503775040045304436033965)
        ·
          refine ⟨42938915640016989163512737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114503775040045304436033965 42938915640016989163512737)
          ·
            refine ⟨32204186730012741872634553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42938915640016989163512737 32204186730012741872634553)
            ·
              refine ⟨24153140047509556404475915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32204186730012741872634553 24153140047509556404475915)
              ·
                refine ⟨36229710071264334606713873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24153140047509556404475915 36229710071264334606713873)
                ·
                  refine ⟨27172282553448250955035405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36229710071264334606713873 27172282553448250955035405)
                  ·
                    refine ⟨10189605957543094108138277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27172282553448250955035405 10189605957543094108138277)
                    ·
                      refine ⟨1910551117039330145275927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10189605957543094108138277 1910551117039330145275927)
                      ·
                        rfl

theorem cell23_3720785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3720785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720785 prefixEnd_3720785 := by exact prefixLift 3720785
  have htrace : WordTrace (prefixWord ++ tailWord_3720785) baseStart_3720785 baseEnd_3720785 := by
    simpa [prefixWord, tailWord_3720785, baseEnd_3720785] using wordTrace_append hprefix tailTrace_3720785
  have hstable : (prefixWord ++ tailWord_3720785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720785).length < 2 ^ (prefixWord ++ tailWord_3720785).sum := by decide
  have hdescent : baseEnd_3720785 < baseStart_3720785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720796 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3720796 : Nat := 118140960795 + 3720796 * 2 ^ 59
def prefixEnd_3720796 : Nat := 4983230072969 + 3 ^ 40 * 3720796 * 2
def baseEnd_3720796 : Nat := 1910556765326529602238377

theorem tailTrace_3720796 : CollatzResearch.WordTrace tailWord_3720796 prefixEnd_3720796 1910556765326529602238377 := by
  unfold tailWord_3720796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67854289514099514105123121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90472386018799352140164161 67854289514099514105123121)
  ·
    refine ⟨50890717135574635578842341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67854289514099514105123121 50890717135574635578842341)
    ·
      refine ⟨9542009462920244171032939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50890717135574635578842341 9542009462920244171032939)
      ·
        refine ⟨14313014194380366256549409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542009462920244171032939 14313014194380366256549409)
        ·
          refine ⟨10734760645785274692412057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14313014194380366256549409 10734760645785274692412057)
          ·
            refine ⟨8051070484338956019309043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734760645785274692412057 8051070484338956019309043)
            ·
              refine ⟨12076605726508434028963565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051070484338956019309043 12076605726508434028963565)
              ·
                refine ⟨4528727147440662760861337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12076605726508434028963565 4528727147440662760861337)
                ·
                  refine ⟨3396545360580497070646003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528727147440662760861337 3396545360580497070646003)
                  ·
                    refine ⟨5094818040870745605969005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396545360580497070646003 5094818040870745605969005)
                    ·
                      refine ⟨1910556765326529602238377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094818040870745605969005 1910556765326529602238377)
                      ·
                        rfl

theorem cell23_3720796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3720796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720796 prefixEnd_3720796 := by exact prefixLift 3720796
  have htrace : WordTrace (prefixWord ++ tailWord_3720796) baseStart_3720796 baseEnd_3720796 := by
    simpa [prefixWord, tailWord_3720796, baseEnd_3720796] using wordTrace_append hprefix tailTrace_3720796
  have hstable : (prefixWord ++ tailWord_3720796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720796).length < 2 ^ (prefixWord ++ tailWord_3720796).sum := by decide
  have hdescent : baseEnd_3720796 < baseStart_3720796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720815 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_3720815 : Nat := 118140960795 + 3720815 * 2 ^ 59
def prefixEnd_3720815 : Nat := 4983230072969 + 3 ^ 40 * 3720815 * 2
def baseEnd_3720815 : Nat := 1910566521458965027900789

theorem tailTrace_3720815 : CollatzResearch.WordTrace tailWord_3720815 prefixEnd_3720815 1910566521458965027900789 := by
  unfold tailWord_3720815
  simp only [CollatzResearch.WordTrace]
  refine ⟨135709272015130194455187899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90472848010086796303458599 135709272015130194455187899)
  ·
    refine ⟨203563908022695291682781849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135709272015130194455187899 203563908022695291682781849)
    ·
      refine ⟨152672931017021468762086387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203563908022695291682781849 152672931017021468762086387)
      ·
        refine ⟨229009396525532203143129581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152672931017021468762086387 229009396525532203143129581)
        ·
          refine ⟨85878523697074576178673593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229009396525532203143129581 85878523697074576178673593)
          ·
            refine ⟨64408892772805932134005195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85878523697074576178673593 64408892772805932134005195)
            ·
              refine ⟨96613339159208898201007793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64408892772805932134005195 96613339159208898201007793)
              ·
                refine ⟨72460004369406673650755845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96613339159208898201007793 72460004369406673650755845)
                ·
                  refine ⟨13586250819263751309516721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72460004369406673650755845 13586250819263751309516721)
                  ·
                    refine ⟨10189688114447813482137541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13586250819263751309516721 10189688114447813482137541)
                    ·
                      refine ⟨1910566521458965027900789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10189688114447813482137541 1910566521458965027900789)
                      ·
                        rfl

theorem cell23_3720815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_3720815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720815 prefixEnd_3720815 := by exact prefixLift 3720815
  have htrace : WordTrace (prefixWord ++ tailWord_3720815) baseStart_3720815 baseEnd_3720815 := by
    simpa [prefixWord, tailWord_3720815, baseEnd_3720815] using wordTrace_append hprefix tailTrace_3720815
  have hstable : (prefixWord ++ tailWord_3720815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720815).length < 2 ^ (prefixWord ++ tailWord_3720815).sum := by decide
  have hdescent : baseEnd_3720815 < baseStart_3720815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720886 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3720886 : Nat := 118140960795 + 3720886 * 2 ^ 59
def prefixEnd_3720886 : Nat := 4983230072969 + 3 ^ 40 * 3720886 * 2
def baseEnd_3720886 : Nat := 1910602978585434250112963

theorem tailTrace_3720886 : CollatzResearch.WordTrace tailWord_3720886 prefixEnd_3720886 1910602978585434250112963 := by
  unfold tailWord_3720886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481991349867060848813907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90474574398581982387348341 8481991349867060848813907)
  ·
    refine ⟨12722987024800591273220861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8481991349867060848813907 12722987024800591273220861)
    ·
      refine ⟨4771120134300221727457823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12722987024800591273220861 4771120134300221727457823)
      ·
        refine ⟨7156680201450332591186735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771120134300221727457823 7156680201450332591186735)
        ·
          refine ⟨10735020302175498886780103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156680201450332591186735 10735020302175498886780103)
          ·
            refine ⟨16102530453263248330170155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735020302175498886780103 16102530453263248330170155)
            ·
              refine ⟨24153795679894872495255233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16102530453263248330170155 24153795679894872495255233)
              ·
                refine ⟨18115346759921154371441425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24153795679894872495255233 18115346759921154371441425)
                ·
                  refine ⟨13586510069940865778581069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18115346759921154371441425 13586510069940865778581069)
                  ·
                    refine ⟨5094941276227824666967901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13586510069940865778581069 5094941276227824666967901)
                    ·
                      refine ⟨1910602978585434250112963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094941276227824666967901 1910602978585434250112963)
                      ·
                        rfl

theorem cell23_3720886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3720886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720886 prefixEnd_3720886 := by exact prefixLift 3720886
  have htrace : WordTrace (prefixWord ++ tailWord_3720886) baseStart_3720886 baseEnd_3720886 := by
    simpa [prefixWord, tailWord_3720886, baseEnd_3720886] using wordTrace_append hprefix tailTrace_3720886
  have hstable : (prefixWord ++ tailWord_3720886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720886).length < 2 ^ (prefixWord ++ tailWord_3720886).sum := by decide
  have hdescent : baseEnd_3720886 < baseStart_3720886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720912 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_3720912 : Nat := 118140960795 + 3720912 * 2 ^ 59
def prefixEnd_3720912 : Nat := 4983230072969 + 3 ^ 40 * 3720912 * 2
def baseEnd_3720912 : Nat := 1910616329082451148387843

theorem tailTrace_3720912 : CollatzResearch.WordTrace tailWord_3720912 prefixEnd_3720912 1910616329082451148387843 := by
  unfold tailWord_3720912
  simp only [CollatzResearch.WordTrace]
  refine ⟨67856404947889390010734495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90475206597185853347645993 67856404947889390010734495)
  ·
    refine ⟨101784607421834085016101743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67856404947889390010734495 101784607421834085016101743)
    ·
      refine ⟨152676911132751127524152615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101784607421834085016101743 152676911132751127524152615)
      ·
        refine ⟨229015366699126691286228923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152676911132751127524152615 229015366699126691286228923)
        ·
          refine ⟨343523050048690036929343385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229015366699126691286228923 343523050048690036929343385)
          ·
            refine ⟨257642287536517527697007539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343523050048690036929343385 257642287536517527697007539)
            ·
              refine ⟨386463431304776291545511309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257642287536517527697007539 386463431304776291545511309)
              ·
                refine ⟨144923786739291109329566741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386463431304776291545511309 144923786739291109329566741)
                ·
                  refine ⟨6793302503404270749823441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144923786739291109329566741 6793302503404270749823441)
                  ·
                    refine ⟨5094976877553203062367581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6793302503404270749823441 5094976877553203062367581)
                    ·
                      refine ⟨1910616329082451148387843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5094976877553203062367581 1910616329082451148387843)
                      ·
                        rfl

theorem cell23_3720912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_3720912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720912 prefixEnd_3720912 := by exact prefixLift 3720912
  have htrace : WordTrace (prefixWord ++ tailWord_3720912) baseStart_3720912 baseEnd_3720912 := by
    simpa [prefixWord, tailWord_3720912, baseEnd_3720912] using wordTrace_append hprefix tailTrace_3720912
  have hstable : (prefixWord ++ tailWord_3720912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720912).length < 2 ^ (prefixWord ++ tailWord_3720912).sum := by decide
  have hdescent : baseEnd_3720912 < baseStart_3720912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720969 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 6, 3, 2]
def baseStart_3720969 : Nat := 118140960795 + 3720969 * 2 ^ 59
def prefixEnd_3720969 : Nat := 4983230072969 + 3 ^ 40 * 3720969 * 2
def baseEnd_3720969 : Nat := 1910645597479757425375081

theorem tailTrace_3720969 : CollatzResearch.WordTrace tailWord_3720969 prefixEnd_3720969 1910645597479757425375081 := by
  unfold tailWord_3720969
  simp only [CollatzResearch.WordTrace]
  refine ⟨135714888856572278756293961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90476592571048185837529307 135714888856572278756293961)
  ·
    refine ⟨101786166642429209067220471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135714888856572278756293961 101786166642429209067220471)
    ·
      refine ⟨152679249963643813600830707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101786166642429209067220471 152679249963643813600830707)
      ·
        refine ⟨229018874945465720401246061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152679249963643813600830707 229018874945465720401246061)
        ·
          refine ⟨85882078104549645150467273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229018874945465720401246061 85882078104549645150467273)
          ·
            refine ⟨64411558578412233862850455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85882078104549645150467273 64411558578412233862850455)
            ·
              refine ⟨96617337867618350794275683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64411558578412233862850455 96617337867618350794275683)
              ·
                refine ⟨144926006801427526191413525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96617337867618350794275683 144926006801427526191413525)
                ·
                  refine ⟨6793406568816915290222509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144926006801427526191413525 6793406568816915290222509)
                  ·
                    refine ⟨2547527463306343233833441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6793406568816915290222509 2547527463306343233833441)
                    ·
                      refine ⟨1910645597479757425375081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547527463306343233833441 1910645597479757425375081)
                      ·
                        rfl

theorem cell23_3720969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 3, 2].length) (baseStart_3720969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720969 prefixEnd_3720969 := by exact prefixLift 3720969
  have htrace : WordTrace (prefixWord ++ tailWord_3720969) baseStart_3720969 baseEnd_3720969 := by
    simpa [prefixWord, tailWord_3720969, baseEnd_3720969] using wordTrace_append hprefix tailTrace_3720969
  have hstable : (prefixWord ++ tailWord_3720969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720969).length < 2 ^ (prefixWord ++ tailWord_3720969).sum := by decide
  have hdescent : baseEnd_3720969 < baseStart_3720969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720986 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_3720986 : Nat := 118140960795 + 3720986 * 2 ^ 59
def prefixEnd_3720986 : Nat := 4983230072969 + 3 ^ 40 * 3720986 * 2
def baseEnd_3720986 : Nat := 1910654326650883858862503

theorem tailTrace_3720986 : CollatzResearch.WordTrace tailWord_3720986 prefixEnd_3720986 1910654326650883858862503 := by
  unfold tailWord_3720986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33928877224377672664915703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90477005931673793773108541 33928877224377672664915703)
  ·
    refine ⟨50893315836566508997373555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33928877224377672664915703 50893315836566508997373555)
    ·
      refine ⟨76339973754849763496060333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50893315836566508997373555 76339973754849763496060333)
      ·
        refine ⟨28627490158068661311022625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76339973754849763496060333 28627490158068661311022625)
        ·
          refine ⟨21470617618551495983266969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28627490158068661311022625 21470617618551495983266969)
          ·
            refine ⟨16102963213913621987450227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21470617618551495983266969 16102963213913621987450227)
            ·
              refine ⟨24154444820870432981175341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16102963213913621987450227 24154444820870432981175341)
              ·
                refine ⟨9057916807826412367940753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24154444820870432981175341 9057916807826412367940753)
                ·
                  refine ⟨6793437605869809275955565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9057916807826412367940753 6793437605869809275955565)
                  ·
                    refine ⟨2547539102201178478483337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6793437605869809275955565 2547539102201178478483337)
                    ·
                      refine ⟨1910654326650883858862503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547539102201178478483337 1910654326650883858862503)
                      ·
                        rfl

theorem cell23_3720986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_3720986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3720986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3720986 prefixEnd_3720986 := by exact prefixLift 3720986
  have htrace : WordTrace (prefixWord ++ tailWord_3720986) baseStart_3720986 baseEnd_3720986 := by
    simpa [prefixWord, tailWord_3720986, baseEnd_3720986] using wordTrace_append hprefix tailTrace_3720986
  have hstable : (prefixWord ++ tailWord_3720986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720986).length < 2 ^ (prefixWord ++ tailWord_3720986).sum := by decide
  have hdescent : baseEnd_3720986 < baseStart_3720986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721010 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_3721010 : Nat := 118140960795 + 3721010 * 2 ^ 59
def prefixEnd_3721010 : Nat := 4983230072969 + 3 ^ 40 * 3721010 * 2
def baseEnd_3721010 : Nat := 1910666650186591764962393

theorem tailTrace_3721010 : CollatzResearch.WordTrace tailWord_3721010 prefixEnd_3721010 1910666650186591764962393 := by
  unfold tailWord_3721010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33929096062355935689634121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90477589499615828505690989 33929096062355935689634121)
  ·
    refine ⟨25446822046766951767225591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33929096062355935689634121 25446822046766951767225591)
    ·
      refine ⟨38170233070150427650838387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25446822046766951767225591 38170233070150427650838387)
      ·
        refine ⟨57255349605225641476257581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38170233070150427650838387 57255349605225641476257581)
        ·
          refine ⟨21470756101959615553596593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57255349605225641476257581 21470756101959615553596593)
          ·
            refine ⟨16103067076469711665197445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21470756101959615553596593 16103067076469711665197445)
            ·
              refine ⟨3019325076838070937224521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16103067076469711665197445 3019325076838070937224521)
              ·
                refine ⟨2264493807628553202918391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019325076838070937224521 2264493807628553202918391)
                ·
                  refine ⟨3396740711442829804377587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264493807628553202918391 3396740711442829804377587)
                  ·
                    refine ⟨5095111067164244706566381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396740711442829804377587 5095111067164244706566381)
                    ·
                      refine ⟨1910666650186591764962393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095111067164244706566381 1910666650186591764962393)
                      ·
                        rfl

theorem cell23_3721010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_3721010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721010 prefixEnd_3721010 := by exact prefixLift 3721010
  have htrace : WordTrace (prefixWord ++ tailWord_3721010) baseStart_3721010 baseEnd_3721010 := by
    simpa [prefixWord, tailWord_3721010, baseEnd_3721010] using wordTrace_append hprefix tailTrace_3721010
  have hstable : (prefixWord ++ tailWord_3721010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721010).length < 2 ^ (prefixWord ++ tailWord_3721010).sum := by decide
  have hdescent : baseEnd_3721010 < baseStart_3721010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721029 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_3721029 : Nat := 118140960795 + 3721029 * 2 ^ 59
def prefixEnd_3721029 : Nat := 4983230072969 + 3 ^ 40 * 3721029 * 2
def baseEnd_3721029 : Nat := 1910676406319027190624805

theorem tailTrace_3721029 : CollatzResearch.WordTrace tailWord_3721029 prefixEnd_3721029 1910676406319027190624805 := by
  unfold tailWord_3721029
  simp only [CollatzResearch.WordTrace]
  refine ⟨135717077236354909003478141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90478051490903272668985427 135717077236354909003478141)
  ·
    refine ⟨50893903963633090876304303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135717077236354909003478141 50893903963633090876304303)
    ·
      refine ⟨76340855945449636314456455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50893903963633090876304303 76340855945449636314456455)
      ·
        refine ⟨114511283918174454471684683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76340855945449636314456455 114511283918174454471684683)
        ·
          refine ⟨171766925877261681707527025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114511283918174454471684683 171766925877261681707527025)
          ·
            refine ⟨128825194407946261280645269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171766925877261681707527025 128825194407946261280645269)
            ·
              refine ⟨6038680987872480997530247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128825194407946261280645269 6038680987872480997530247)
              ·
                refine ⟨9058021481808721496295371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038680987872480997530247 9058021481808721496295371)
                ·
                  refine ⟨13587032222713082244443057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9058021481808721496295371 13587032222713082244443057)
                  ·
                    refine ⟨10190274167034811683332293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13587032222713082244443057 10190274167034811683332293)
                    ·
                      refine ⟨1910676406319027190624805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10190274167034811683332293 1910676406319027190624805)
                      ·
                        rfl

theorem cell23_3721029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_3721029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721029 prefixEnd_3721029 := by exact prefixLift 3721029
  have htrace : WordTrace (prefixWord ++ tailWord_3721029) baseStart_3721029 baseEnd_3721029 := by
    simpa [prefixWord, tailWord_3721029, baseEnd_3721029] using wordTrace_append hprefix tailTrace_3721029
  have hstable : (prefixWord ++ tailWord_3721029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721029).length < 2 ^ (prefixWord ++ tailWord_3721029).sum := by decide
  have hdescent : baseEnd_3721029 < baseStart_3721029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721049 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_3721049 : Nat := 118140960795 + 3721049 * 2 ^ 59
def prefixEnd_3721049 : Nat := 4983230072969 + 3 ^ 40 * 3721049 * 2
def baseEnd_3721049 : Nat := 1910686675932117112374713

theorem tailTrace_3721049 : CollatzResearch.WordTrace tailWord_3721049 prefixEnd_3721049 1910686675932117112374713 := by
  unfold tailWord_3721049
  simp only [CollatzResearch.WordTrace]
  refine ⟨135717806696282452419206201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90478537797521634946137467 135717806696282452419206201)
  ·
    refine ⟨101788355022211839314404651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135717806696282452419206201 101788355022211839314404651)
    ·
      refine ⟨152682532533317758971606977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101788355022211839314404651 152682532533317758971606977)
      ·
        refine ⟨114511899399988319228705233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152682532533317758971606977 114511899399988319228705233)
        ·
          refine ⟨85883924549991239421528925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114511899399988319228705233 85883924549991239421528925)
          ·
            refine ⟨32206471706246714783073347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85883924549991239421528925 32206471706246714783073347)
            ·
              refine ⟨48309707559370072174610021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32206471706246714783073347 48309707559370072174610021)
              ·
                refine ⟨9058070167381888532739379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48309707559370072174610021 9058070167381888532739379)
                ·
                  refine ⟨13587105251072832799109069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9058070167381888532739379 13587105251072832799109069)
                  ·
                    refine ⟨5095164469152312299665901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13587105251072832799109069 5095164469152312299665901)
                    ·
                      refine ⟨1910686675932117112374713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095164469152312299665901 1910686675932117112374713)
                      ·
                        rfl

theorem cell23_3721049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_3721049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721049 prefixEnd_3721049 := by exact prefixLift 3721049
  have htrace : WordTrace (prefixWord ++ tailWord_3721049) baseStart_3721049 baseEnd_3721049 := by
    simpa [prefixWord, tailWord_3721049, baseEnd_3721049] using wordTrace_append hprefix tailTrace_3721049
  have hstable : (prefixWord ++ tailWord_3721049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721049).length < 2 ^ (prefixWord ++ tailWord_3721049).sum := by decide
  have hdescent : baseEnd_3721049 < baseStart_3721049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721050 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2]
def baseStart_3721050 : Nat := 118140960795 + 3721050 * 2 ^ 59
def prefixEnd_3721050 : Nat := 4983230072969 + 3 ^ 40 * 3721050 * 2
def baseEnd_3721050 : Nat := 1910687189412771608462209

theorem tailTrace_3721050 : CollatzResearch.WordTrace tailWord_3721050 prefixEnd_3721050 1910687189412771608462209 := by
  unfold tailWord_3721050
  simp only [CollatzResearch.WordTrace]
  refine ⟨33929460792319707397498151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90478562112852553059995069 33929460792319707397498151)
  ·
    refine ⟨50894191188479561096247227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33929460792319707397498151 50894191188479561096247227)
    ·
      refine ⟨76341286782719341644370841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50894191188479561096247227 76341286782719341644370841)
      ·
        refine ⟨57255965087039506233278131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76341286782719341644370841 57255965087039506233278131)
        ·
          refine ⟨85883947630559259349917197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57255965087039506233278131 85883947630559259349917197)
          ·
            refine ⟨32206480361459722256218949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85883947630559259349917197 32206480361459722256218949)
            ·
              refine ⟨6038715067773697923041053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32206480361459722256218949 6038715067773697923041053)
              ·
                refine ⟨2264518150415136721140395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6038715067773697923041053 2264518150415136721140395)
                ·
                  refine ⟨3396777225622705081710593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264518150415136721140395 3396777225622705081710593)
                  ·
                    refine ⟨2547582919217028811282945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396777225622705081710593 2547582919217028811282945)
                    ·
                      refine ⟨1910687189412771608462209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547582919217028811282945 1910687189412771608462209)
                      ·
                        rfl

theorem cell23_3721050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_3721050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721050 prefixEnd_3721050 := by exact prefixLift 3721050
  have htrace : WordTrace (prefixWord ++ tailWord_3721050) baseStart_3721050 baseEnd_3721050 := by
    simpa [prefixWord, tailWord_3721050, baseEnd_3721050] using wordTrace_append hprefix tailTrace_3721050
  have hstable : (prefixWord ++ tailWord_3721050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721050).length < 2 ^ (prefixWord ++ tailWord_3721050).sum := by decide
  have hdescent : baseEnd_3721050 < baseStart_3721050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721060 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_3721060 : Nat := 118140960795 + 3721060 * 2 ^ 59
def prefixEnd_3721060 : Nat := 4983230072969 + 3 ^ 40 * 3721060 * 2
def baseEnd_3721060 : Nat := 636897441406438856445721

theorem tailTrace_3721060 : CollatzResearch.WordTrace tailWord_3721060 prefixEnd_3721060 636897441406438856445721 := by
  unfold tailWord_3721060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67859103949621300648928317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90478805266161734198571089 67859103949621300648928317)
  ·
    refine ⟨25447163981107987743348119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67859103949621300648928317 25447163981107987743348119)
    ·
      refine ⟨38170745971661981615022179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25447163981107987743348119 38170745971661981615022179)
      ·
        refine ⟨57256118957492972422533269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38170745971661981615022179 57256118957492972422533269)
        ·
          refine ⟨2683880576132483082306247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57256118957492972422533269 2683880576132483082306247)
          ·
            refine ⟨4025820864198724623459371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683880576132483082306247 4025820864198724623459371)
            ·
              refine ⟨6038731296298086935189057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025820864198724623459371 6038731296298086935189057)
              ·
                refine ⟨4529048472223565201391793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038731296298086935189057 4529048472223565201391793)
                ·
                  refine ⟨3396786354167673901043845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4529048472223565201391793 3396786354167673901043845)
                  ·
                    refine ⟨636897441406438856445721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3396786354167673901043845 636897441406438856445721)
                    ·
                      rfl

theorem cell23_3721060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_3721060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721060 prefixEnd_3721060 := by exact prefixLift 3721060
  have htrace : WordTrace (prefixWord ++ tailWord_3721060) baseStart_3721060 baseEnd_3721060 := by
    simpa [prefixWord, tailWord_3721060, baseEnd_3721060] using wordTrace_append hprefix tailTrace_3721060
  have hstable : (prefixWord ++ tailWord_3721060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721060).length < 2 ^ (prefixWord ++ tailWord_3721060).sum := by decide
  have hdescent : baseEnd_3721060 < baseStart_3721060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721093 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_3721093 : Nat := 118140960795 + 3721093 * 2 ^ 59
def prefixEnd_3721093 : Nat := 4983230072969 + 3 ^ 40 * 3721093 * 2
def baseEnd_3721093 : Nat := 1910709269080914940224511

theorem tailTrace_3721093 : CollatzResearch.WordTrace tailWord_3721093 prefixEnd_3721093 1910709269080914940224511 := by
  unfold tailWord_3721093
  simp only [CollatzResearch.WordTrace]
  refine ⟨135719411508123047933807933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90479607672082031955871955 135719411508123047933807933)
  ·
    refine ⟨50894779315546142975177975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135719411508123047933807933 50894779315546142975177975)
    ·
      refine ⟨76342168973319214462766963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50894779315546142975177975 76342168973319214462766963)
      ·
        refine ⟨114513253459978821694150445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76342168973319214462766963 114513253459978821694150445)
        ·
          refine ⟨42942470047492058135306417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114513253459978821694150445 42942470047492058135306417)
          ·
            refine ⟨32206852535619043601479813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42942470047492058135306417 32206852535619043601479813)
            ·
              refine ⟨6038784850428570675277465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32206852535619043601479813 6038784850428570675277465)
              ·
                refine ⟨4529088637821428006458099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038784850428570675277465 4529088637821428006458099)
                ·
                  refine ⟨6793632956732142009687149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529088637821428006458099 6793632956732142009687149)
                  ·
                    refine ⟨2547612358774553253632681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6793632956732142009687149 2547612358774553253632681)
                    ·
                      refine ⟨1910709269080914940224511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547612358774553253632681 1910709269080914940224511)
                      ·
                        rfl

theorem cell23_3721093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_3721093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721093 prefixEnd_3721093 := by exact prefixLift 3721093
  have htrace : WordTrace (prefixWord ++ tailWord_3721093) baseStart_3721093 baseEnd_3721093 := by
    simpa [prefixWord, tailWord_3721093, baseEnd_3721093] using wordTrace_append hprefix tailTrace_3721093
  have hstable : (prefixWord ++ tailWord_3721093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721093).length < 2 ^ (prefixWord ++ tailWord_3721093).sum := by decide
  have hdescent : baseEnd_3721093 < baseStart_3721093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721109 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3721109 : Nat := 118140960795 + 3721109 * 2 ^ 59
def prefixEnd_3721109 : Nat := 4983230072969 + 3 ^ 40 * 3721109 * 2
def baseEnd_3721109 : Nat := 1910717484771386877624437

theorem tailTrace_3721109 : CollatzResearch.WordTrace tailWord_3721109 prefixEnd_3721109 1910717484771386877624437 := by
  unfold tailWord_3721109
  simp only [CollatzResearch.WordTrace]
  refine ⟨135719995076065082666390381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90479996717376721777593587 135719995076065082666390381)
  ·
    refine ⟨50894998153524405999896393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135719995076065082666390381 50894998153524405999896393)
    ·
      refine ⟨38171248615143304499922295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50894998153524405999896393 38171248615143304499922295)
      ·
        refine ⟨57256872922714956749883443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38171248615143304499922295 57256872922714956749883443)
        ·
          refine ⟨85885309384072435124825165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57256872922714956749883443 85885309384072435124825165)
          ·
            refine ⟨32206991019027163171809437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85885309384072435124825165 32206991019027163171809437)
            ·
              refine ⟨12077621632135186189428539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32206991019027163171809437 12077621632135186189428539)
              ·
                refine ⟨18116432448202779284142809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077621632135186189428539 18116432448202779284142809)
                ·
                  refine ⟨13587324336152084463107107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18116432448202779284142809 13587324336152084463107107)
                  ·
                    refine ⟨20380986504228126694660661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13587324336152084463107107 20380986504228126694660661)
                    ·
                      refine ⟨1910717484771386877624437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20380986504228126694660661 1910717484771386877624437)
                      ·
                        rfl

theorem cell23_3721109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3721109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721109 prefixEnd_3721109 := by exact prefixLift 3721109
  have htrace : WordTrace (prefixWord ++ tailWord_3721109) baseStart_3721109 baseEnd_3721109 := by
    simpa [prefixWord, tailWord_3721109, baseEnd_3721109] using wordTrace_append hprefix tailTrace_3721109
  have hstable : (prefixWord ++ tailWord_3721109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721109).length < 2 ^ (prefixWord ++ tailWord_3721109).sum := by decide
  have hdescent : baseEnd_3721109 < baseStart_3721109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721123 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 2, 2, 2]
def baseStart_3721123 : Nat := 118140960795 + 3721123 * 2 ^ 59
def prefixEnd_3721123 : Nat := 4983230072969 + 3 ^ 40 * 3721123 * 2
def baseEnd_3721123 : Nat := 1910724673500549822849373

theorem tailTrace_3721123 : CollatzResearch.WordTrace tailWord_3721123 prefixEnd_3721123 1910724673500549822849373 := by
  unfold tailWord_3721123
  simp only [CollatzResearch.WordTrace]
  refine ⟨135720505698014363057400023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90480337132009575371600015 135720505698014363057400023)
  ·
    refine ⟨203580758547021544586100035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135720505698014363057400023 203580758547021544586100035)
    ·
      refine ⟨305371137820532316879150053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203580758547021544586100035 305371137820532316879150053)
      ·
        refine ⟨57257088341349809414840635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305371137820532316879150053 57257088341349809414840635)
        ·
          refine ⟨85885632512024714122260953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57257088341349809414840635 85885632512024714122260953)
          ·
            refine ⟨64414224384018535591695715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85885632512024714122260953 64414224384018535591695715)
            ·
              refine ⟨96621336576027803387543573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64414224384018535591695715 96621336576027803387543573)
              ·
                refine ⟨4529125152001303283791105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96621336576027803387543573 4529125152001303283791105)
                ·
                  refine ⟨3396843864000977462843329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4529125152001303283791105 3396843864000977462843329)
                  ·
                    refine ⟨2547632898000733097132497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396843864000977462843329 2547632898000733097132497)
                    ·
                      refine ⟨1910724673500549822849373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547632898000733097132497 1910724673500549822849373)
                      ·
                        rfl

theorem cell23_3721123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_3721123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721123 prefixEnd_3721123 := by exact prefixLift 3721123
  have htrace : WordTrace (prefixWord ++ tailWord_3721123) baseStart_3721123 baseEnd_3721123 := by
    simpa [prefixWord, tailWord_3721123, baseEnd_3721123] using wordTrace_append hprefix tailTrace_3721123
  have hstable : (prefixWord ++ tailWord_3721123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721123).length < 2 ^ (prefixWord ++ tailWord_3721123).sum := by decide
  have hdescent : baseEnd_3721123 < baseStart_3721123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721134 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3721134 : Nat := 118140960795 + 3721134 * 2 ^ 59
def prefixEnd_3721134 : Nat := 4983230072969 + 3 ^ 40 * 3721134 * 2
def baseEnd_3721134 : Nat := 1910730321787749279811823

theorem tailTrace_3721134 : CollatzResearch.WordTrace tailWord_3721134 prefixEnd_3721134 1910730321787749279811823 := by
  unfold tailWord_3721134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16965113362621813992006307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90480604600649674624033637 16965113362621813992006307)
  ·
    refine ⟨25447670043932720988009461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16965113362621813992006307 25447670043932720988009461)
    ·
      refine ⟨2385719066618692592625887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25447670043932720988009461 2385719066618692592625887)
      ·
        refine ⟨3578578599928038888938831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385719066618692592625887 3578578599928038888938831)
        ·
          refine ⟨5367867899892058333408247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578578599928038888938831 5367867899892058333408247)
          ·
            refine ⟨8051801849838087500112371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367867899892058333408247 8051801849838087500112371)
            ·
              refine ⟨12077702774757131250168557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051801849838087500112371 12077702774757131250168557)
              ·
                refine ⟨4529138540533924218813209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12077702774757131250168557 4529138540533924218813209)
                ·
                  refine ⟨3396853905400443164109907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4529138540533924218813209 3396853905400443164109907)
                  ·
                    refine ⟨5095280858100664746164861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3396853905400443164109907 5095280858100664746164861)
                    ·
                      refine ⟨1910730321787749279811823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095280858100664746164861 1910730321787749279811823)
                      ·
                        rfl

theorem cell23_3721134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3721134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721134 prefixEnd_3721134 := by exact prefixLift 3721134
  have htrace : WordTrace (prefixWord ++ tailWord_3721134) baseStart_3721134 baseEnd_3721134 := by
    simpa [prefixWord, tailWord_3721134, baseEnd_3721134] using wordTrace_append hprefix tailTrace_3721134
  have hstable : (prefixWord ++ tailWord_3721134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721134).length < 2 ^ (prefixWord ++ tailWord_3721134).sum := by decide
  have hdescent : baseEnd_3721134 < baseStart_3721134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721139 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3]
def baseStart_3721139 : Nat := 118140960795 + 3721139 * 2 ^ 59
def prefixEnd_3721139 : Nat := 4983230072969 + 3 ^ 40 * 3721139 * 2
def baseEnd_3721139 : Nat := 1910732889191021760249299

theorem tailTrace_3721139 : CollatzResearch.WordTrace tailWord_3721139 prefixEnd_3721139 1910732889191021760249299 := by
  unfold tailWord_3721139
  simp only [CollatzResearch.WordTrace]
  refine ⟨135721089265956397789982471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90480726177304265193321647 135721089265956397789982471)
  ·
    refine ⟨203581633898934596684973707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135721089265956397789982471 203581633898934596684973707)
    ·
      refine ⟨305372450848401895027460561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203581633898934596684973707 305372450848401895027460561)
      ·
        refine ⟨229029338136301421270595421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305372450848401895027460561 229029338136301421270595421)
        ·
          refine ⟨85886001801113032976473283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229029338136301421270595421 85886001801113032976473283)
          ·
            refine ⟨128829002701669549464709925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85886001801113032976473283 128829002701669549464709925)
            ·
              refine ⟨24155438006563040524633111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128829002701669549464709925 24155438006563040524633111)
              ·
                refine ⟨36233157009844560786949667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24155438006563040524633111 36233157009844560786949667)
                ·
                  refine ⟨54349735514766841180424501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36233157009844560786949667 54349735514766841180424501)
                  ·
                    refine ⟨5095287704509391360664797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54349735514766841180424501 5095287704509391360664797)
                    ·
                      refine ⟨1910732889191021760249299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095287704509391360664797 1910732889191021760249299)
                      ·
                        rfl

theorem cell23_3721139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_3721139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721139 prefixEnd_3721139 := by exact prefixLift 3721139
  have htrace : WordTrace (prefixWord ++ tailWord_3721139) baseStart_3721139 baseEnd_3721139 := by
    simpa [prefixWord, tailWord_3721139, baseEnd_3721139] using wordTrace_append hprefix tailTrace_3721139
  have hstable : (prefixWord ++ tailWord_3721139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721139).length < 2 ^ (prefixWord ++ tailWord_3721139).sum := by decide
  have hdescent : baseEnd_3721139 < baseStart_3721139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721174 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3721174 : Nat := 118140960795 + 3721174 * 2 ^ 59
def prefixEnd_3721174 : Nat := 4983230072969 + 3 ^ 40 * 3721174 * 2
def baseEnd_3721174 : Nat := 1910750861013929123311639

theorem tailTrace_3721174 : CollatzResearch.WordTrace tailWord_3721174 prefixEnd_3721174 1910750861013929123311639 := by
  unfold tailWord_3721174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482647863801849922969161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90481577213886399178337717 8482647863801849922969161)
  ·
    refine ⟨6361985897851387442226871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8482647863801849922969161 6361985897851387442226871)
    ·
      refine ⟨9542978846777081163340307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361985897851387442226871 9542978846777081163340307)
      ·
        refine ⟨14314468270165621745010461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542978846777081163340307 14314468270165621745010461)
        ·
          refine ⟨5367925601312108154378923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14314468270165621745010461 5367925601312108154378923)
          ·
            refine ⟨8051888401968162231568385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367925601312108154378923 8051888401968162231568385)
            ·
              refine ⟨6038916301476121673676289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051888401968162231568385 6038916301476121673676289)
              ·
                refine ⟨4529187226107091255257217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038916301476121673676289 4529187226107091255257217)
                ·
                  refine ⟨3396890419580318441442913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4529187226107091255257217 3396890419580318441442913)
                  ·
                    refine ⟨2547667814685238831082185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3396890419580318441442913 2547667814685238831082185)
                    ·
                      refine ⟨1910750861013929123311639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547667814685238831082185 1910750861013929123311639)
                      ·
                        rfl

theorem cell23_3721174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3721174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721174 prefixEnd_3721174 := by exact prefixLift 3721174
  have htrace : WordTrace (prefixWord ++ tailWord_3721174) baseStart_3721174 baseEnd_3721174 := by
    simpa [prefixWord, tailWord_3721174, baseEnd_3721174] using wordTrace_append hprefix tailTrace_3721174
  have hstable : (prefixWord ++ tailWord_3721174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721174).length < 2 ^ (prefixWord ++ tailWord_3721174).sum := by decide
  have hdescent : baseEnd_3721174 < baseStart_3721174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721216 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_3721216 : Nat := 118140960795 + 3721216 * 2 ^ 59
def prefixEnd_3721216 : Nat := 4983230072969 + 3 ^ 40 * 3721216 * 2
def baseEnd_3721216 : Nat := 1910772427201417958986445

theorem tailTrace_3721216 : CollatzResearch.WordTrace tailWord_3721216 prefixEnd_3721216 1910772427201417958986445 := by
  unfold tailWord_3721216
  simp only [CollatzResearch.WordTrace]
  refine ⟨67861948843338719970267751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90482598457784959960357001 67861948843338719970267751)
  ·
    refine ⟨101792923265008079955401627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67861948843338719970267751 101792923265008079955401627)
    ·
      refine ⟨152689384897512119933102441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101792923265008079955401627 152689384897512119933102441)
      ·
        refine ⟨114517038673134089949826831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152689384897512119933102441 114517038673134089949826831)
        ·
          refine ⟨171775558009701134924740247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114517038673134089949826831 171775558009701134924740247)
          ·
            refine ⟨257663337014551702387110371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171775558009701134924740247 257663337014551702387110371)
            ·
              refine ⟨386495005521827553580665557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257663337014551702387110371 386495005521827553580665557)
              ·
                refine ⟨9058476691917833287046849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386495005521827553580665557 9058476691917833287046849)
                ·
                  refine ⟨6793857518938374965285137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9058476691917833287046849 6793857518938374965285137)
                  ·
                    refine ⟨5095393139203781223963853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6793857518938374965285137 5095393139203781223963853)
                    ·
                      refine ⟨1910772427201417958986445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095393139203781223963853 1910772427201417958986445)
                      ·
                        rfl

theorem cell23_3721216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_3721216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721216 prefixEnd_3721216 := by exact prefixLift 3721216
  have htrace : WordTrace (prefixWord ++ tailWord_3721216) baseStart_3721216 baseEnd_3721216 := by
    simpa [prefixWord, tailWord_3721216, baseEnd_3721216] using wordTrace_append hprefix tailTrace_3721216
  have hstable : (prefixWord ++ tailWord_3721216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721216).length < 2 ^ (prefixWord ++ tailWord_3721216).sum := by decide
  have hdescent : baseEnd_3721216 < baseStart_3721216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721253 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 6]
def baseStart_3721253 : Nat := 118140960795 + 3721253 * 2 ^ 59
def prefixEnd_3721253 : Nat := 4983230072969 + 3 ^ 40 * 3721253 * 2
def baseEnd_3721253 : Nat := 212310158442848257135975

theorem tailTrace_3721253 : CollatzResearch.WordTrace tailWord_3721253 prefixEnd_3721253 212310158442848257135975 := by
  unfold tailWord_3721253
  simp only [CollatzResearch.WordTrace]
  refine ⟨135725247187543395259632413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90483498125028930173088275 135725247187543395259632413)
  ·
    refine ⟨50896967695328773222362155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135725247187543395259632413 50896967695328773222362155)
    ·
      refine ⟨76345451542993159833543233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50896967695328773222362155 76345451542993159833543233)
      ·
        refine ⟨57259088657244869875157425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76345451542993159833543233 57259088657244869875157425)
        ·
          refine ⟨42944316492933652406368069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57259088657244869875157425 42944316492933652406368069)
          ·
            refine ⟨8052059342425059826194013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42944316492933652406368069 8052059342425059826194013)
            ·
              refine ⟨3019522253409397434822755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8052059342425059826194013 3019522253409397434822755)
              ·
                refine ⟨4529283380114096152234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019522253409397434822755 4529283380114096152234133)
                ·
                  refine ⟨212310158442848257135975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4529283380114096152234133 212310158442848257135975)
                  ·
                    rfl

theorem cell23_3721253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_3721253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721253 prefixEnd_3721253 := by exact prefixLift 3721253
  have htrace : WordTrace (prefixWord ++ tailWord_3721253) baseStart_3721253 baseEnd_3721253 := by
    simpa [prefixWord, tailWord_3721253, baseEnd_3721253] using wordTrace_append hprefix tailTrace_3721253
  have hstable : (prefixWord ++ tailWord_3721253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721253).length < 2 ^ (prefixWord ++ tailWord_3721253).sum := by decide
  have hdescent : baseEnd_3721253 < baseStart_3721253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721306 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_3721306 : Nat := 118140960795 + 3721306 * 2 ^ 59
def prefixEnd_3721306 : Nat := 4983230072969 + 3 ^ 40 * 3721306 * 2
def baseEnd_3721306 : Nat := 1910818640460322606861031

theorem tailTrace_3721306 : CollatzResearch.WordTrace tailWord_3721306 prefixEnd_3721306 1910818640460322606861031 := by
  unfold tailWord_3721306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33931795064087846327827943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90484786837567590207541181 33931795064087846327827943)
  ·
    refine ⟨50897692596131769491741915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33931795064087846327827943 50897692596131769491741915)
    ·
      refine ⟨76346538894197654237612873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50897692596131769491741915 76346538894197654237612873)
      ·
        refine ⟨57259904170648240678209655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76346538894197654237612873 57259904170648240678209655)
        ·
          refine ⟨85889856255972361017314483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57259904170648240678209655 85889856255972361017314483)
          ·
            refine ⟨128834784383958541525971725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85889856255972361017314483 128834784383958541525971725)
            ·
              refine ⟨48313044143984453072239397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128834784383958541525971725 48313044143984453072239397)
              ·
                refine ⟨9058695776997084951044887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48313044143984453072239397 9058695776997084951044887)
                ·
                  refine ⟨13588043665495627426567331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9058695776997084951044887 13588043665495627426567331)
                  ·
                    refine ⟨20382065498243441139850997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13588043665495627426567331 20382065498243441139850997)
                    ·
                      refine ⟨1910818640460322606861031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20382065498243441139850997 1910818640460322606861031)
                      ·
                        rfl

theorem cell23_3721306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_3721306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721306 prefixEnd_3721306 := by exact prefixLift 3721306
  have htrace : WordTrace (prefixWord ++ tailWord_3721306) baseStart_3721306 baseEnd_3721306 := by
    simpa [prefixWord, tailWord_3721306, baseEnd_3721306] using wordTrace_append hprefix tailTrace_3721306
  have hstable : (prefixWord ++ tailWord_3721306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721306).length < 2 ^ (prefixWord ++ tailWord_3721306).sum := by decide
  have hdescent : baseEnd_3721306 < baseStart_3721306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721316 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3721316 : Nat := 118140960795 + 3721316 * 2 ^ 59
def prefixEnd_3721316 : Nat := 4983230072969 + 3 ^ 40 * 3721316 * 2
def baseEnd_3721316 : Nat := 1910823775266867567735985

theorem tailTrace_3721316 : CollatzResearch.WordTrace tailWord_3721316 prefixEnd_3721316 1910823775266867567735985 := by
  unfold tailWord_3721316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67863772493157578509587901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90485029990876771346117201 67863772493157578509587901)
  ·
    refine ⟨25448914684934091941095463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67863772493157578509587901 25448914684934091941095463)
    ·
      refine ⟨38173372027401137911643195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25448914684934091941095463 38173372027401137911643195)
      ·
        refine ⟨57260058041101706867464793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38173372027401137911643195 57260058041101706867464793)
        ·
          refine ⟨42945043530826280150598595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57260058041101706867464793 42945043530826280150598595)
          ·
            refine ⟨64417565296239420225897893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42945043530826280150598595 64417565296239420225897893)
            ·
              refine ⟨12078293493044891292355855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64417565296239420225897893 12078293493044891292355855)
              ·
                refine ⟨18117440239567336938533783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12078293493044891292355855 18117440239567336938533783)
                ·
                  refine ⟨27176160359351005407800675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18117440239567336938533783 27176160359351005407800675)
                  ·
                    refine ⟨40764240539026508111701013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27176160359351005407800675 40764240539026508111701013)
                    ·
                      refine ⟨1910823775266867567735985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40764240539026508111701013 1910823775266867567735985)
                      ·
                        rfl

theorem cell23_3721316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3721316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721316 prefixEnd_3721316 := by exact prefixLift 3721316
  have htrace : WordTrace (prefixWord ++ tailWord_3721316) baseStart_3721316 baseEnd_3721316 := by
    simpa [prefixWord, tailWord_3721316, baseEnd_3721316] using wordTrace_append hprefix tailTrace_3721316
  have hstable : (prefixWord ++ tailWord_3721316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721316).length < 2 ^ (prefixWord ++ tailWord_3721316).sum := by decide
  have hdescent : baseEnd_3721316 < baseStart_3721316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721326 : List Nat := [4, 1, 2, 2, 1, 1, 1, 11]
def baseStart_3721326 : Nat := 118140960795 + 3721326 * 2 ^ 59
def prefixEnd_3721326 : Nat := 4983230072969 + 3 ^ 40 * 3721326 * 2
def baseEnd_3721326 : Nat := 70771441113830093652257

theorem tailTrace_3721326 : CollatzResearch.WordTrace tailWord_3721326 prefixEnd_3721326 70771441113830093652257 := by
  unfold tailWord_3721326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16965988714534866090879979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90485273144185952484693221 16965988714534866090879979)
  ·
    refine ⟨25448983071802299136319969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16965988714534866090879979 25448983071802299136319969)
    ·
      refine ⟨19086737303851724352239977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25448983071802299136319969 19086737303851724352239977)
      ·
        refine ⟨14315052977888793264179983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19086737303851724352239977 14315052977888793264179983)
        ·
          refine ⟨21472579466833189896269975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315052977888793264179983 21472579466833189896269975)
          ·
            refine ⟨32208869200249784844404963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21472579466833189896269975 32208869200249784844404963)
            ·
              refine ⟨48313303800374677266607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32208869200249784844404963 48313303800374677266607445)
              ·
                refine ⟨70771441113830093652257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48313303800374677266607445 70771441113830093652257)
                ·
                  rfl

theorem cell23_3721326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_3721326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721326 prefixEnd_3721326 := by exact prefixLift 3721326
  have htrace : WordTrace (prefixWord ++ tailWord_3721326) baseStart_3721326 baseEnd_3721326 := by
    simpa [prefixWord, tailWord_3721326, baseEnd_3721326] using wordTrace_append hprefix tailTrace_3721326
  have hstable : (prefixWord ++ tailWord_3721326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721326).length < 2 ^ (prefixWord ++ tailWord_3721326).sum := by decide
  have hdescent : baseEnd_3721326 < baseStart_3721326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721354 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_3721354 : Nat := 118140960795 + 3721354 * 2 ^ 59
def prefixEnd_3721354 : Nat := 4983230072969 + 3 ^ 40 * 3721354 * 2
def baseEnd_3721354 : Nat := 1910843287531738419060811

theorem tailTrace_3721354 : CollatzResearch.WordTrace tailWord_3721354 prefixEnd_3721354 1910843287531738419060811 := by
  unfold tailWord_3721354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33932232740044372377264779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90485953973451659672706077 33932232740044372377264779)
  ·
    refine ⟨50898349110066558565897169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33932232740044372377264779 50898349110066558565897169)
    ·
      refine ⟨38173761832549918924422877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50898349110066558565897169 38173761832549918924422877)
      ·
        refine ⟨14315160687206219596658579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38173761832549918924422877 14315160687206219596658579)
        ·
          refine ⟨21472741030809329394987869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315160687206219596658579 21472741030809329394987869)
          ·
            refine ⟨8052277886553498523120451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21472741030809329394987869 8052277886553498523120451)
            ·
              refine ⟨12078416829830247784680677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052277886553498523120451 12078416829830247784680677)
              ·
                refine ⟨2264703155593171459627627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12078416829830247784680677 2264703155593171459627627)
                ·
                  refine ⟨3397054733389757189441441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264703155593171459627627 3397054733389757189441441)
                  ·
                    refine ⟨2547791050042317892081081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397054733389757189441441 2547791050042317892081081)
                    ·
                      refine ⟨1910843287531738419060811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547791050042317892081081 1910843287531738419060811)
                      ·
                        rfl

theorem cell23_3721354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_3721354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721354 prefixEnd_3721354 := by exact prefixLift 3721354
  have htrace : WordTrace (prefixWord ++ tailWord_3721354) baseStart_3721354 baseEnd_3721354 := by
    simpa [prefixWord, tailWord_3721354, baseEnd_3721354] using wordTrace_append hprefix tailTrace_3721354
  have hstable : (prefixWord ++ tailWord_3721354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721354).length < 2 ^ (prefixWord ++ tailWord_3721354).sum := by decide
  have hdescent : baseEnd_3721354 < baseStart_3721354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721404 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3721404 : Nat := 118140960795 + 3721404 * 2 ^ 59
def prefixEnd_3721404 : Nat := 4983230072969 + 3 ^ 40 * 3721404 * 2
def baseEnd_3721404 : Nat := 1910868961564463223435581

theorem tailTrace_3721404 : CollatzResearch.WordTrace tailWord_3721404 prefixEnd_3721404 1910868961564463223435581 := by
  unfold tailWord_3721404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67865377304998174024189633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90487169739997565365586177 67865377304998174024189633)
  ·
    refine ⟨50899032978748630518142225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67865377304998174024189633 50899032978748630518142225)
    ·
      refine ⟨38174274734061472888606669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50899032978748630518142225 38174274734061472888606669)
      ·
        refine ⟨14315353025273052333227501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38174274734061472888606669 14315353025273052333227501)
        ·
          refine ⟨5368257384477394624960313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14315353025273052333227501 5368257384477394624960313)
          ·
            refine ⟨4026193038358045968720235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368257384477394624960313 4026193038358045968720235)
            ·
              refine ⟨6039289557537068953080353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026193038358045968720235 6039289557537068953080353)
              ·
                refine ⟨4529467168152801714810265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6039289557537068953080353 4529467168152801714810265)
                ·
                  refine ⟨3397100376114601286107699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4529467168152801714810265 3397100376114601286107699)
                  ·
                    refine ⟨5095650564171901929161549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397100376114601286107699 5095650564171901929161549)
                    ·
                      refine ⟨1910868961564463223435581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095650564171901929161549 1910868961564463223435581)
                      ·
                        rfl

theorem cell23_3721404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3721404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721404 prefixEnd_3721404 := by exact prefixLift 3721404
  have htrace : WordTrace (prefixWord ++ tailWord_3721404) baseStart_3721404 baseEnd_3721404 := by
    simpa [prefixWord, tailWord_3721404, baseEnd_3721404] using wordTrace_append hprefix tailTrace_3721404
  have hstable : (prefixWord ++ tailWord_3721404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721404).length < 2 ^ (prefixWord ++ tailWord_3721404).sum := by decide
  have hdescent : baseEnd_3721404 < baseStart_3721404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721456 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_3721456 : Nat := 118140960795 + 3721456 * 2 ^ 59
def prefixEnd_3721456 : Nat := 4983230072969 + 3 ^ 40 * 3721456 * 2
def baseEnd_3721456 : Nat := 1910895662558497019985341

theorem tailTrace_3721456 : CollatzResearch.WordTrace tailWord_3721456 prefixEnd_3721456 1910895662558497019985341 := by
  unfold tailWord_3721456
  simp only [CollatzResearch.WordTrace]
  refine ⟨67866325602903980464636111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90488434137205307286181481 67866325602903980464636111)
  ·
    refine ⟨101799488404355970696954167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67866325602903980464636111 101799488404355970696954167)
    ·
      refine ⟨152699232606533956045431251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101799488404355970696954167 152699232606533956045431251)
      ·
        refine ⟨229048848909800934068146877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152699232606533956045431251 229048848909800934068146877)
        ·
          refine ⟨85893318341175350275555079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229048848909800934068146877 85893318341175350275555079)
          ·
            refine ⟨128839977511763025413332619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85893318341175350275555079 128839977511763025413332619)
            ·
              refine ⟨193259966267644538119998929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128839977511763025413332619 193259966267644538119998929)
              ·
                refine ⟨144944974700733403589999197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193259966267644538119998929 144944974700733403589999197)
                ·
                  refine ⟨54354365512775026346249699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144944974700733403589999197 54354365512775026346249699)
                  ·
                    refine ⟨81531548269162539519374549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54354365512775026346249699 81531548269162539519374549)
                    ·
                      refine ⟨1910895662558497019985341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81531548269162539519374549 1910895662558497019985341)
                      ·
                        rfl

theorem cell23_3721456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_3721456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721456 prefixEnd_3721456 := by exact prefixLift 3721456
  have htrace : WordTrace (prefixWord ++ tailWord_3721456) baseStart_3721456 baseEnd_3721456 := by
    simpa [prefixWord, tailWord_3721456, baseEnd_3721456] using wordTrace_append hprefix tailTrace_3721456
  have hstable : (prefixWord ++ tailWord_3721456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721456).length < 2 ^ (prefixWord ++ tailWord_3721456).sum := by decide
  have hdescent : baseEnd_3721456 < baseStart_3721456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721473 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3721473 : Nat := 118140960795 + 3721473 * 2 ^ 59
def prefixEnd_3721473 : Nat := 4983230072969 + 3 ^ 40 * 3721473 * 2
def baseEnd_3721473 : Nat := 1910904391729623453472763

theorem tailTrace_3721473 : CollatzResearch.WordTrace tailWord_3721473 prefixEnd_3721473 1910904391729623453472763 := by
  unfold tailWord_3721473
  simp only [CollatzResearch.WordTrace]
  refine ⟨135733271246746372832641073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90488847497830915221760715 135733271246746372832641073)
  ·
    refine ⟨101799953435059779624480805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135733271246746372832641073 101799953435059779624480805)
    ·
      refine ⟨19087491269073708679590151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101799953435059779624480805 19087491269073708679590151)
      ·
        refine ⟨28631236903610563019385227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19087491269073708679590151 28631236903610563019385227)
        ·
          refine ⟨42946855355415844529077841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28631236903610563019385227 42946855355415844529077841)
          ·
            refine ⟨32210141516561883396808381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42946855355415844529077841 32210141516561883396808381)
            ·
              refine ⟨12078803068710706273803143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32210141516561883396808381 12078803068710706273803143)
              ·
                refine ⟨18118204603066059410704715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12078803068710706273803143 18118204603066059410704715)
                ·
                  refine ⟨27177306904599089116057073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18118204603066059410704715 27177306904599089116057073)
                  ·
                    refine ⟨20382980178449316837042805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27177306904599089116057073 20382980178449316837042805)
                    ·
                      refine ⟨1910904391729623453472763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20382980178449316837042805 1910904391729623453472763)
                      ·
                        rfl

theorem cell23_3721473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3721473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721473 prefixEnd_3721473 := by exact prefixLift 3721473
  have htrace : WordTrace (prefixWord ++ tailWord_3721473) baseStart_3721473 baseEnd_3721473 := by
    simpa [prefixWord, tailWord_3721473, baseEnd_3721473] using wordTrace_append hprefix tailTrace_3721473
  have hstable : (prefixWord ++ tailWord_3721473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721473).length < 2 ^ (prefixWord ++ tailWord_3721473).sum := by decide
  have hdescent : baseEnd_3721473 < baseStart_3721473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721483 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4]
def baseStart_3721483 : Nat := 118140960795 + 3721483 * 2 ^ 59
def prefixEnd_3721483 : Nat := 4983230072969 + 3 ^ 40 * 3721483 * 2
def baseEnd_3721483 : Nat := 1910909526536168414347717

theorem tailTrace_3721483 : CollatzResearch.WordTrace tailWord_3721483 prefixEnd_3721483 1910909526536168414347717 := by
  unfold tailWord_3721483
  simp only [CollatzResearch.WordTrace]
  refine ⟨135733635976710144540505103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90489090651140096360336735 135733635976710144540505103)
  ·
    refine ⟨203600453965065216810757655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135733635976710144540505103 203600453965065216810757655)
    ·
      refine ⟨305400680947597825216136483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203600453965065216810757655 305400680947597825216136483)
      ·
        refine ⟨458101021421396737824204725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305400680947597825216136483 458101021421396737824204725)
        ·
          refine ⟨42946970758255944171019193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 458101021421396737824204725 42946970758255944171019193)
          ·
            refine ⟨32210228068691958128264395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42946970758255944171019193 32210228068691958128264395)
            ·
              refine ⟨48315342103037937192396593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32210228068691958128264395 48315342103037937192396593)
              ·
                refine ⟨36236506577278452894297445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48315342103037937192396593 36236506577278452894297445)
                ·
                  refine ⟨6794344983239709917680771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36236506577278452894297445 6794344983239709917680771)
                  ·
                    refine ⟨10191517474859564876521157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794344983239709917680771 10191517474859564876521157)
                    ·
                      refine ⟨1910909526536168414347717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10191517474859564876521157 1910909526536168414347717)
                      ·
                        rfl

theorem cell23_3721483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 4].length) (baseStart_3721483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721483 prefixEnd_3721483 := by exact prefixLift 3721483
  have htrace : WordTrace (prefixWord ++ tailWord_3721483) baseStart_3721483 baseEnd_3721483 := by
    simpa [prefixWord, tailWord_3721483, baseEnd_3721483] using wordTrace_append hprefix tailTrace_3721483
  have hstable : (prefixWord ++ tailWord_3721483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721483).length < 2 ^ (prefixWord ++ tailWord_3721483).sum := by decide
  have hdescent : baseEnd_3721483 < baseStart_3721483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3721500 : Nat := 118140960795 + 3721500 * 2 ^ 59
def prefixEnd_3721500 : Nat := 4983230072969 + 3 ^ 40 * 3721500 * 2
def baseEnd_3721500 : Nat := 1910918255707294847835139

theorem tailTrace_3721500 : CollatzResearch.WordTrace tailWord_3721500 prefixEnd_3721500 1910918255707294847835139 := by
  unfold tailWord_3721500
  simp only [CollatzResearch.WordTrace]
  refine ⟨67867128008824278221936977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90489504011765704295915969 67867128008824278221936977)
  ·
    refine ⟨50900346006618208666452733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67867128008824278221936977 50900346006618208666452733)
    ·
      refine ⟨19087629752481828249919775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50900346006618208666452733 19087629752481828249919775)
      ·
        refine ⟨28631444628722742374879663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19087629752481828249919775 28631444628722742374879663)
        ·
          refine ⟨42947166943084113562319495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28631444628722742374879663 42947166943084113562319495)
          ·
            refine ⟨64420750414626170343479243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42947166943084113562319495 64420750414626170343479243)
            ·
              refine ⟨96631125621939255515218865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64420750414626170343479243 96631125621939255515218865)
              ·
                refine ⟨72473344216454441636414149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96631125621939255515218865 72473344216454441636414149)
                ·
                  refine ⟨13588752040585207806827653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72473344216454441636414149 13588752040585207806827653)
                  ·
                    refine ⟨2547891007609726463780185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13588752040585207806827653 2547891007609726463780185)
                    ·
                      refine ⟨1910918255707294847835139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2547891007609726463780185 1910918255707294847835139)
                      ·
                        rfl

theorem cell23_3721500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3721500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721500 prefixEnd_3721500 := by exact prefixLift 3721500
  have htrace : WordTrace (prefixWord ++ tailWord_3721500) baseStart_3721500 baseEnd_3721500 := by
    simpa [prefixWord, tailWord_3721500, baseEnd_3721500] using wordTrace_append hprefix tailTrace_3721500
  have hstable : (prefixWord ++ tailWord_3721500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721500).length < 2 ^ (prefixWord ++ tailWord_3721500).sum := by decide
  have hdescent : baseEnd_3721500 < baseStart_3721500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721518 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_3721518 : Nat := 118140960795 + 3721518 * 2 ^ 59
def prefixEnd_3721518 : Nat := 4983230072969 + 3 ^ 40 * 3721518 * 2
def baseEnd_3721518 : Nat := 212325277595452864156673

theorem tailTrace_3721518 : CollatzResearch.WordTrace tailWord_3721518 prefixEnd_3721518 212325277595452864156673 := by
  unfold tailWord_3721518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966864066447918189753651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90489941687722230345352805 16966864066447918189753651)
  ·
    refine ⟨25450296099671877284630477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16966864066447918189753651 25450296099671877284630477)
    ·
      refine ⟨9543861037376953981736429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25450296099671877284630477 9543861037376953981736429)
      ·
        refine ⟨3578947889016357743151161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9543861037376953981736429 3578947889016357743151161)
        ·
          refine ⟨2684210916762268307363371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3578947889016357743151161 2684210916762268307363371)
          ·
            refine ⟨4026316375143402461045057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684210916762268307363371 4026316375143402461045057)
            ·
              refine ⟨3019737281357551845783793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026316375143402461045057 3019737281357551845783793)
              ·
                refine ⟨2264802961018163884337845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019737281357551845783793 2264802961018163884337845)
                ·
                  refine ⟨212325277595452864156673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2264802961018163884337845 212325277595452864156673)
                  ·
                    rfl

theorem cell23_3721518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_3721518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721518 prefixEnd_3721518 := by exact prefixLift 3721518
  have htrace : WordTrace (prefixWord ++ tailWord_3721518) baseStart_3721518 baseEnd_3721518 := by
    simpa [prefixWord, tailWord_3721518, baseEnd_3721518] using wordTrace_append hprefix tailTrace_3721518
  have hstable : (prefixWord ++ tailWord_3721518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721518).length < 2 ^ (prefixWord ++ tailWord_3721518).sum := by decide
  have hdescent : baseEnd_3721518 < baseStart_3721518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721584 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 1, 1, 3]
def baseStart_3721584 : Nat := 118140960795 + 3721584 * 2 ^ 59
def prefixEnd_3721584 : Nat := 4983230072969 + 3 ^ 40 * 3721584 * 2
def baseEnd_3721584 : Nat := 1910961388082272519184753

theorem tailTrace_3721584 : CollatzResearch.WordTrace tailWord_3721584 prefixEnd_3721584 1910961388082272519184753 := by
  unfold tailWord_3721584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67868659874672119394965903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90491546499562825859954537 67868659874672119394965903)
  ·
    refine ⟨101802989812008179092448855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67868659874672119394965903 101802989812008179092448855)
    ·
      refine ⟨152704484718012268638673283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101802989812008179092448855 152704484718012268638673283)
      ·
        refine ⟨229056727077018402958009925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152704484718012268638673283 229056727077018402958009925)
        ·
          refine ⟨42948136326940950554626861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229056727077018402958009925 42948136326940950554626861)
          ·
            refine ⟨16105551122602856457985073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42948136326940950554626861 16105551122602856457985073)
            ·
              refine ⟨12079163341952142343488805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16105551122602856457985073 12079163341952142343488805)
              ·
                refine ⟨2264843126616026689404151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12079163341952142343488805 2264843126616026689404151)
                ·
                  refine ⟨3397264689924040034106227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264843126616026689404151 3397264689924040034106227)
                  ·
                    refine ⟨5095897034886060051159341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397264689924040034106227 5095897034886060051159341)
                    ·
                      refine ⟨1910961388082272519184753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5095897034886060051159341 1910961388082272519184753)
                      ·
                        rfl

theorem cell23_3721584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 1, 3].length) (baseStart_3721584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721584 prefixEnd_3721584 := by exact prefixLift 3721584
  have htrace : WordTrace (prefixWord ++ tailWord_3721584) baseStart_3721584 baseEnd_3721584 := by
    simpa [prefixWord, tailWord_3721584, baseEnd_3721584] using wordTrace_append hprefix tailTrace_3721584
  have hstable : (prefixWord ++ tailWord_3721584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721584).length < 2 ^ (prefixWord ++ tailWord_3721584).sum := by decide
  have hdescent : baseEnd_3721584 < baseStart_3721584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721607 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_3721607 : Nat := 118140960795 + 3721607 * 2 ^ 59
def prefixEnd_3721607 : Nat := 4983230072969 + 3 ^ 40 * 3721607 * 2
def baseEnd_3721607 : Nat := 1910973198137325929197147

theorem tailTrace_3721607 : CollatzResearch.WordTrace tailWord_3721607 prefixEnd_3721607 1910973198137325929197147 := by
  unfold tailWord_3721607
  simp only [CollatzResearch.WordTrace]
  refine ⟨135738158628260913718019075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90492105752173942478679383 135738158628260913718019075)
  ·
    refine ⟨203607237942391370577028613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135738158628260913718019075 203607237942391370577028613)
    ·
      refine ⟨38176357114198381983192865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203607237942391370577028613 38176357114198381983192865)
      ·
        refine ⟨28632267835648786487394649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38176357114198381983192865 28632267835648786487394649)
        ·
          refine ⟨21474200876736589865545987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28632267835648786487394649 21474200876736589865545987)
          ·
            refine ⟨32211301315104884798318981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474200876736589865545987 32211301315104884798318981)
            ·
              refine ⟨6039618996582165899684809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32211301315104884798318981 6039618996582165899684809)
              ·
                refine ⟨4529714247436624424763607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6039618996582165899684809 4529714247436624424763607)
                ·
                  refine ⟨6794571371154936637145411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529714247436624424763607 6794571371154936637145411)
                  ·
                    refine ⟨10191857056732404955718117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6794571371154936637145411 10191857056732404955718117)
                    ·
                      refine ⟨1910973198137325929197147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10191857056732404955718117 1910973198137325929197147)
                      ·
                        rfl

theorem cell23_3721607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_3721607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721607 prefixEnd_3721607 := by exact prefixLift 3721607
  have htrace : WordTrace (prefixWord ++ tailWord_3721607) baseStart_3721607 baseEnd_3721607 := by
    simpa [prefixWord, tailWord_3721607, baseEnd_3721607] using wordTrace_append hprefix tailTrace_3721607
  have hstable : (prefixWord ++ tailWord_3721607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721607).length < 2 ^ (prefixWord ++ tailWord_3721607).sum := by decide
  have hdescent : baseEnd_3721607 < baseStart_3721607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721663 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_3721663 : Nat := 118140960795 + 3721663 * 2 ^ 59
def prefixEnd_3721663 : Nat := 4983230072969 + 3 ^ 40 * 3721663 * 2
def baseEnd_3721663 : Nat := 1911001953053977710096889

theorem tailTrace_3721663 : CollatzResearch.WordTrace tailWord_3721663 prefixEnd_3721663 1911001953053977710096889 := by
  unfold tailWord_3721663
  simp only [CollatzResearch.WordTrace]
  refine ⟨135740201116058035282057643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90493467410705356854705095 135740201116058035282057643)
  ·
    refine ⟨203610301674087052923086465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135740201116058035282057643 203610301674087052923086465)
    ·
      refine ⟨152707726255565289692314849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203610301674087052923086465 152707726255565289692314849)
      ·
        refine ⟨114530794691673967269236137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152707726255565289692314849 114530794691673967269236137)
        ·
          refine ⟨85898096018755475451927103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114530794691673967269236137 85898096018755475451927103)
          ·
            refine ⟨128847144028133213177890655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85898096018755475451927103 128847144028133213177890655)
            ·
              refine ⟨193270716042199819766835983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128847144028133213177890655 193270716042199819766835983)
              ·
                refine ⟨289906074063299729650253975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193270716042199819766835983 289906074063299729650253975)
                ·
                  refine ⟨434859111094949594475380963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289906074063299729650253975 434859111094949594475380963)
                  ·
                    refine ⟨652288666642424391713071445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434859111094949594475380963 652288666642424391713071445)
                    ·
                      refine ⟨1911001953053977710096889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 652288666642424391713071445 1911001953053977710096889)
                      ·
                        rfl

theorem cell23_3721663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_3721663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721663 prefixEnd_3721663 := by exact prefixLift 3721663
  have htrace : WordTrace (prefixWord ++ tailWord_3721663) baseStart_3721663 baseEnd_3721663 := by
    simpa [prefixWord, tailWord_3721663, baseEnd_3721663] using wordTrace_append hprefix tailTrace_3721663
  have hstable : (prefixWord ++ tailWord_3721663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721663).length < 2 ^ (prefixWord ++ tailWord_3721663).sum := by decide
  have hdescent : baseEnd_3721663 < baseStart_3721663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721690 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_3721690 : Nat := 118140960795 + 3721690 * 2 ^ 59
def prefixEnd_3721690 : Nat := 4983230072969 + 3 ^ 40 * 3721690 * 2
def baseEnd_3721690 : Nat := 637005272343883034819755

theorem tailTrace_3721690 : CollatzResearch.WordTrace tailWord_3721690 prefixEnd_3721690 637005272343883034819755 := by
  unfold tailWord_3721690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33935296471740054723322631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90494123924640145928860349 33935296471740054723322631)
  ·
    refine ⟨50902944707610082084983947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33935296471740054723322631 50902944707610082084983947)
    ·
      refine ⟨76354417061415123127475921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50902944707610082084983947 76354417061415123127475921)
      ·
        refine ⟨57265812796061342345606941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76354417061415123127475921 57265812796061342345606941)
        ·
          refine ⟨21474679798523003379602603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57265812796061342345606941 21474679798523003379602603)
          ·
            refine ⟨32212019697784505069403905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21474679798523003379602603 32212019697784505069403905)
            ·
              refine ⟨24159014773338378802052929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32212019697784505069403905 24159014773338378802052929)
              ·
                refine ⟨18119261080003784101539697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24159014773338378802052929 18119261080003784101539697)
                ·
                  refine ⟨13589445810002838076154773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18119261080003784101539697 13589445810002838076154773)
                  ·
                    refine ⟨637005272343883034819755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13589445810002838076154773 637005272343883034819755)
                    ·
                      rfl

theorem cell23_3721690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_3721690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721690 prefixEnd_3721690 := by exact prefixLift 3721690
  have htrace : WordTrace (prefixWord ++ tailWord_3721690) baseStart_3721690 baseEnd_3721690 := by
    simpa [prefixWord, tailWord_3721690, baseEnd_3721690] using wordTrace_append hprefix tailTrace_3721690
  have hstable : (prefixWord ++ tailWord_3721690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721690).length < 2 ^ (prefixWord ++ tailWord_3721690).sum := by decide
  have hdescent : baseEnd_3721690 < baseStart_3721690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721697 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_3721697 : Nat := 118140960795 + 3721697 * 2 ^ 59
def prefixEnd_3721697 : Nat := 4983230072969 + 3 ^ 40 * 3721697 * 2
def baseEnd_3721697 : Nat := 1911019411396230577071733

theorem tailTrace_3721697 : CollatzResearch.WordTrace tailWord_3721697 prefixEnd_3721697 1911019411396230577071733 := by
  unfold tailWord_3721697
  simp only [CollatzResearch.WordTrace]
  refine ⟨135741441197934859088795345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90494294131956572725863563 135741441197934859088795345)
  ·
    refine ⟨101806080898451144316596509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135741441197934859088795345 101806080898451144316596509)
    ·
      refine ⟨38177280336919179118723691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101806080898451144316596509 38177280336919179118723691)
      ·
        refine ⟨57265920505378768678085537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38177280336919179118723691 57265920505378768678085537)
        ·
          refine ⟨42949440379034076508564153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57265920505378768678085537 42949440379034076508564153)
          ·
            refine ⟨32212080284275557381423115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42949440379034076508564153 32212080284275557381423115)
            ·
              refine ⟨48318120426413336072134673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32212080284275557381423115 48318120426413336072134673)
              ·
                refine ⟨36238590319810002054101005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48318120426413336072134673 36238590319810002054101005)
                ·
                  refine ⟨13589471369928750770287877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36238590319810002054101005 13589471369928750770287877)
                  ·
                    refine ⟨2548025881861640769428977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13589471369928750770287877 2548025881861640769428977)
                    ·
                      refine ⟨1911019411396230577071733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548025881861640769428977 1911019411396230577071733)
                      ·
                        rfl

theorem cell23_3721697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_3721697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721697 prefixEnd_3721697 := by exact prefixLift 3721697
  have htrace : WordTrace (prefixWord ++ tailWord_3721697) baseStart_3721697 baseEnd_3721697 := by
    simpa [prefixWord, tailWord_3721697, baseEnd_3721697] using wordTrace_append hprefix tailTrace_3721697
  have hstable : (prefixWord ++ tailWord_3721697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721697).length < 2 ^ (prefixWord ++ tailWord_3721697).sum := by decide
  have hdescent : baseEnd_3721697 < baseStart_3721697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721720 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 7]
def baseStart_3721720 : Nat := 118140960795 + 3721720 * 2 ^ 59
def prefixEnd_3721720 : Nat := 4983230072969 + 3 ^ 40 * 3721720 * 2
def baseEnd_3721720 : Nat := 212336802383475998564903

theorem tailTrace_3721720 : CollatzResearch.WordTrace tailWord_3721720 prefixEnd_3721720 212336802383475998564903 := by
  unfold tailWord_3721720
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871140038425767008441307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90494853384567689344588409 67871140038425767008441307)
  ·
    refine ⟨101806710057638650512661961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67871140038425767008441307 101806710057638650512661961)
    ·
      refine ⟨76355032543228987884496471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101806710057638650512661961 76355032543228987884496471)
      ·
        refine ⟨114532548814843481826744707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76355032543228987884496471 114532548814843481826744707)
        ·
          refine ⟨171798823222265222740117061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114532548814843481826744707 171798823222265222740117061)
          ·
            refine ⟨32212279354174729263771949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171798823222265222740117061 32212279354174729263771949)
            ·
              refine ⟨12079604757815523473914481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32212279354174729263771949 12079604757815523473914481)
              ·
                refine ⟨9059703568361642605435861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12079604757815523473914481 9059703568361642605435861)
                ·
                  refine ⟨212336802383475998564903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9059703568361642605435861 212336802383475998564903)
                  ·
                    rfl

theorem cell23_3721720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_3721720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721720 prefixEnd_3721720 := by exact prefixLift 3721720
  have htrace : WordTrace (prefixWord ++ tailWord_3721720) baseStart_3721720 baseEnd_3721720 := by
    simpa [prefixWord, tailWord_3721720, baseEnd_3721720] using wordTrace_append hprefix tailTrace_3721720
  have hstable : (prefixWord ++ tailWord_3721720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721720).length < 2 ^ (prefixWord ++ tailWord_3721720).sum := by decide
  have hdescent : baseEnd_3721720 < baseStart_3721720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721735 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3721735 : Nat := 118140960795 + 3721735 * 2 ^ 59
def prefixEnd_3721735 : Nat := 4983230072969 + 3 ^ 40 * 3721735 * 2
def baseEnd_3721735 : Nat := 1911038923661101428396559

theorem tailTrace_3721735 : CollatzResearch.WordTrace tailWord_3721735 prefixEnd_3721735 1911038923661101428396559 := by
  unfold tailWord_3721735
  simp only [CollatzResearch.WordTrace]
  refine ⟨135742827171797191578678659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90495218114531461052452439 135742827171797191578678659)
  ·
    refine ⟨203614240757695787368017989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135742827171797191578678659 203614240757695787368017989)
    ·
      refine ⟨38177670142067960131503373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203614240757695787368017989 38177670142067960131503373)
      ·
        refine ⟨14316626303275485049313765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38177670142067960131503373 14316626303275485049313765)
        ·
          refine ⟨2684367431864153446746331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14316626303275485049313765 2684367431864153446746331)
          ·
            refine ⟨4026551147796230170119497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684367431864153446746331 4026551147796230170119497)
            ·
              refine ⟨3019913360847172627589623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026551147796230170119497 3019913360847172627589623)
              ·
                refine ⟨4529870041270758941384435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019913360847172627589623 4529870041270758941384435)
                ·
                  refine ⟨6794805061906138412076653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529870041270758941384435 6794805061906138412076653)
                  ·
                    refine ⟨2548051898214801904528745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6794805061906138412076653 2548051898214801904528745)
                    ·
                      refine ⟨1911038923661101428396559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548051898214801904528745 1911038923661101428396559)
                      ·
                        rfl

theorem cell23_3721735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3721735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721735 prefixEnd_3721735 := by exact prefixLift 3721735
  have htrace : WordTrace (prefixWord ++ tailWord_3721735) baseStart_3721735 baseEnd_3721735 := by
    simpa [prefixWord, tailWord_3721735, baseEnd_3721735] using wordTrace_append hprefix tailTrace_3721735
  have hstable : (prefixWord ++ tailWord_3721735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721735).length < 2 ^ (prefixWord ++ tailWord_3721735).sum := by decide
  have hdescent : baseEnd_3721735 < baseStart_3721735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721748 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3721748 : Nat := 118140960795 + 3721748 * 2 ^ 59
def prefixEnd_3721748 : Nat := 4983230072969 + 3 ^ 40 * 3721748 * 2
def baseEnd_3721748 : Nat := 1911045598909609877533999

theorem tailTrace_3721748 : CollatzResearch.WordTrace tailWord_3721748 prefixEnd_3721748 1911045598909609877533999 := by
  unfold tailWord_3721748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871650660375047399450949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90495534213833396532601265 67871650660375047399450949)
  ·
    refine ⟨12725934498820321387397053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67871650660375047399450949 12725934498820321387397053)
    ·
      refine ⟨4772225437057620520273895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12725934498820321387397053 4772225437057620520273895)
      ·
        refine ⟨7158338155586430780410843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4772225437057620520273895 7158338155586430780410843)
        ·
          refine ⟨10737507233379646170616265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158338155586430780410843 10737507233379646170616265)
          ·
            refine ⟨8053130425034734627962199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10737507233379646170616265 8053130425034734627962199)
            ·
              refine ⟨12079695637552101941943299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053130425034734627962199 12079695637552101941943299)
              ·
                refine ⟨18119543456328152912914949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12079695637552101941943299 18119543456328152912914949)
                ·
                  refine ⟨3397414398061528671171553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18119543456328152912914949 3397414398061528671171553)
                  ·
                    refine ⟨2548060798546146503378665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397414398061528671171553 2548060798546146503378665)
                    ·
                      refine ⟨1911045598909609877533999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548060798546146503378665 1911045598909609877533999)
                      ·
                        rfl

theorem cell23_3721748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3721748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721748 prefixEnd_3721748 := by exact prefixLift 3721748
  have htrace : WordTrace (prefixWord ++ tailWord_3721748) baseStart_3721748 baseEnd_3721748 := by
    simpa [prefixWord, tailWord_3721748, baseEnd_3721748] using wordTrace_append hprefix tailTrace_3721748
  have hstable : (prefixWord ++ tailWord_3721748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721748).length < 2 ^ (prefixWord ++ tailWord_3721748).sum := by decide
  have hdescent : baseEnd_3721748 < baseStart_3721748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721800 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3721800 : Nat := 118140960795 + 3721800 * 2 ^ 59
def prefixEnd_3721800 : Nat := 4983230072969 + 3 ^ 40 * 3721800 * 2
def baseEnd_3721800 : Nat := 1911072299903643674083759

theorem tailTrace_3721800 : CollatzResearch.WordTrace tailWord_3721800 prefixEnd_3721800 1911072299903643674083759 := by
  unfold tailWord_3721800
  simp only [CollatzResearch.WordTrace]
  refine ⟨67872598958280853839897427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90496798611041138453196569 67872598958280853839897427)
  ·
    refine ⟨101808898437421280759846141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67872598958280853839897427 101808898437421280759846141)
    ·
      refine ⟨38178336914032980284942303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101808898437421280759846141 38178336914032980284942303)
      ·
        refine ⟨57267505371049470427413455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38178336914032980284942303 57267505371049470427413455)
        ·
          refine ⟨85901258056574205641120183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57267505371049470427413455 85901258056574205641120183)
          ·
            refine ⟨128851887084861308461680275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85901258056574205641120183 128851887084861308461680275)
            ·
              refine ⟨193277830627291962692520413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128851887084861308461680275 193277830627291962692520413)
              ·
                refine ⟨72479186485234486009695155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193277830627291962692520413 72479186485234486009695155)
                ·
                  refine ⟨108718779727851729014542733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72479186485234486009695155 108718779727851729014542733)
                  ·
                    refine ⟨40769542397944398380453525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108718779727851729014542733 40769542397944398380453525)
                    ·
                      refine ⟨1911072299903643674083759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40769542397944398380453525 1911072299903643674083759)
                      ·
                        rfl

theorem cell23_3721800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3721800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721800 prefixEnd_3721800 := by exact prefixLift 3721800
  have htrace : WordTrace (prefixWord ++ tailWord_3721800) baseStart_3721800 baseEnd_3721800 := by
    simpa [prefixWord, tailWord_3721800, baseEnd_3721800] using wordTrace_append hprefix tailTrace_3721800
  have hstable : (prefixWord ++ tailWord_3721800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721800).length < 2 ^ (prefixWord ++ tailWord_3721800).sum := by decide
  have hdescent : baseEnd_3721800 < baseStart_3721800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721807 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_3721807 : Nat := 118140960795 + 3721807 * 2 ^ 59
def prefixEnd_3721807 : Nat := 4983230072969 + 3 ^ 40 * 3721807 * 2
def baseEnd_3721807 : Nat := 1911075894268225146696227

theorem tailTrace_3721807 : CollatzResearch.WordTrace tailWord_3721807 prefixEnd_3721807 1911075894268225146696227 := by
  unfold tailWord_3721807
  simp only [CollatzResearch.WordTrace]
  refine ⟨135745453227536347875299675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90496968818357565250199783 135745453227536347875299675)
  ·
    refine ⟨203618179841304521812949513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135745453227536347875299675 203618179841304521812949513)
    ·
      refine ⟨152713634880978391359712135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203618179841304521812949513 152713634880978391359712135)
      ·
        refine ⟨229070452321467587039568203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152713634880978391359712135 229070452321467587039568203)
        ·
          refine ⟨343605678482201380559352305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229070452321467587039568203 343605678482201380559352305)
          ·
            refine ⟨257704258861651035419514229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343605678482201380559352305 257704258861651035419514229)
            ·
              refine ⟨24159774268279784570579459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257704258861651035419514229 24159774268279784570579459)
              ·
                refine ⟨36239661402419676855869189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24159774268279784570579459 36239661402419676855869189)
                ·
                  refine ⟨6794936512953689410475473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36239661402419676855869189 6794936512953689410475473)
                  ·
                    refine ⟨5096202384715267057856605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6794936512953689410475473 5096202384715267057856605)
                    ·
                      refine ⟨1911075894268225146696227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096202384715267057856605 1911075894268225146696227)
                      ·
                        rfl

theorem cell23_3721807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_3721807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721807 prefixEnd_3721807 := by exact prefixLift 3721807
  have htrace : WordTrace (prefixWord ++ tailWord_3721807) baseStart_3721807 baseEnd_3721807 := by
    simpa [prefixWord, tailWord_3721807, baseEnd_3721807] using wordTrace_append hprefix tailTrace_3721807
  have hstable : (prefixWord ++ tailWord_3721807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721807).length < 2 ^ (prefixWord ++ tailWord_3721807).sum := by decide
  have hdescent : baseEnd_3721807 < baseStart_3721807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721827 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 6]
def baseStart_3721827 : Nat := 118140960795 + 3721827 * 2 ^ 59
def prefixEnd_3721827 : Nat := 4983230072969 + 3 ^ 40 * 3721827 * 2
def baseEnd_3721827 : Nat := 212342907097923896494015

theorem tailTrace_3721827 : CollatzResearch.WordTrace tailWord_3721827 prefixEnd_3721827 212342907097923896494015 := by
  unfold tailWord_3721827
  simp only [CollatzResearch.WordTrace]
  refine ⟨135746182687463891291027735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90497455124975927527351823 135746182687463891291027735)
  ·
    refine ⟨203619274031195836936541603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135746182687463891291027735 203619274031195836936541603)
    ·
      refine ⟨305428911046793755404812405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203619274031195836936541603 305428911046793755404812405)
      ·
        refine ⟨28633960410636914569201163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305428911046793755404812405 28633960410636914569201163)
        ·
          refine ⟨42950940615955371853801745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28633960410636914569201163 42950940615955371853801745)
          ·
            refine ⟨32213205461966528890351309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42950940615955371853801745 32213205461966528890351309)
            ·
              refine ⟨12079952048237448333881741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32213205461966528890351309 12079952048237448333881741)
              ·
                refine ⟨4529982018089043125205653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12079952048237448333881741 4529982018089043125205653)
                ·
                  refine ⟨212342907097923896494015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4529982018089043125205653 212342907097923896494015)
                  ·
                    rfl

theorem cell23_3721827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 6].length) (baseStart_3721827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721827 prefixEnd_3721827 := by exact prefixLift 3721827
  have htrace : WordTrace (prefixWord ++ tailWord_3721827) baseStart_3721827 baseEnd_3721827 := by
    simpa [prefixWord, tailWord_3721827, baseEnd_3721827] using wordTrace_append hprefix tailTrace_3721827
  have hstable : (prefixWord ++ tailWord_3721827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721827).length < 2 ^ (prefixWord ++ tailWord_3721827).sum := by decide
  have hdescent : baseEnd_3721827 < baseStart_3721827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 1, 1, 3]
def baseStart_3721871 : Nat := 118140960795 + 3721871 * 2 ^ 59
def prefixEnd_3721871 : Nat := 4983230072969 + 3 ^ 40 * 3721871 * 2
def baseEnd_3721871 : Nat := 1911108757030112896295933

theorem tailTrace_3721871 : CollatzResearch.WordTrace tailWord_3721871 prefixEnd_3721871 1911108757030112896295933 := by
  unfold tailWord_3721871
  simp only [CollatzResearch.WordTrace]
  refine ⟨135747787499304486805629467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90498524999536324537086311 135747787499304486805629467)
  ·
    refine ⟨203621681248956730208444201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135747787499304486805629467 203621681248956730208444201)
    ·
      refine ⟨152716260936717547656333151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203621681248956730208444201 152716260936717547656333151)
      ·
        refine ⟨229074391405076321484499727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152716260936717547656333151 229074391405076321484499727)
        ·
          refine ⟨343611587107614482226749591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229074391405076321484499727 343611587107614482226749591)
          ·
            refine ⟨515417380661421723340124387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343611587107614482226749591 515417380661421723340124387)
            ·
              refine ⟨773126070992132585010186581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515417380661421723340124387 773126070992132585010186581)
              ·
                refine ⟨2265017786109763432647031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 773126070992132585010186581 2265017786109763432647031)
                ·
                  refine ⟨3397526679164645148970547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265017786109763432647031 3397526679164645148970547)
                  ·
                    refine ⟨5096290018746967723455821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397526679164645148970547 5096290018746967723455821)
                    ·
                      refine ⟨1911108757030112896295933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096290018746967723455821 1911108757030112896295933)
                      ·
                        rfl

theorem cell23_3721871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 1, 3].length) (baseStart_3721871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721871 prefixEnd_3721871 := by exact prefixLift 3721871
  have htrace : WordTrace (prefixWord ++ tailWord_3721871) baseStart_3721871 baseEnd_3721871 := by
    simpa [prefixWord, tailWord_3721871, baseEnd_3721871] using wordTrace_append hprefix tailTrace_3721871
  have hstable : (prefixWord ++ tailWord_3721871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721871).length < 2 ^ (prefixWord ++ tailWord_3721871).sum := by decide
  have hdescent : baseEnd_3721871 < baseStart_3721871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721874 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3721874 : Nat := 118140960795 + 3721874 * 2 ^ 59
def prefixEnd_3721874 : Nat := 4983230072969 + 3 ^ 40 * 3721874 * 2
def baseEnd_3721874 : Nat := 637036765824025461519473

theorem tailTrace_3721874 : CollatzResearch.WordTrace tailWord_3721874 prefixEnd_3721874 637036765824025461519473 := by
  unfold tailWord_3721874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33936974229573404579497169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90498597945529078878659117 33936974229573404579497169)
  ·
    refine ⟨25452730672180053434622877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33936974229573404579497169 25452730672180053434622877)
    ·
      refine ⟨9544774002067520037983579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25452730672180053434622877 9544774002067520037983579)
      ·
        refine ⟨14317161003101280056975369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544774002067520037983579 14317161003101280056975369)
        ·
          refine ⟨10737870752325960042731527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14317161003101280056975369 10737870752325960042731527)
          ·
            refine ⟨16106806128488940064097291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737870752325960042731527 16106806128488940064097291)
            ·
              refine ⟨24160209192733410096145937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106806128488940064097291 24160209192733410096145937)
              ·
                refine ⟨18120156894550057572109453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24160209192733410096145937 18120156894550057572109453)
                ·
                  refine ⟨6795058835456271589541045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18120156894550057572109453 6795058835456271589541045)
                  ·
                    refine ⟨637036765824025461519473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6795058835456271589541045 637036765824025461519473)
                    ·
                      rfl

theorem cell23_3721874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3721874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721874 prefixEnd_3721874 := by exact prefixLift 3721874
  have htrace : WordTrace (prefixWord ++ tailWord_3721874) baseStart_3721874 baseEnd_3721874 := by
    simpa [prefixWord, tailWord_3721874, baseEnd_3721874] using wordTrace_append hprefix tailTrace_3721874
  have hstable : (prefixWord ++ tailWord_3721874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721874).length < 2 ^ (prefixWord ++ tailWord_3721874).sum := by decide
  have hdescent : baseEnd_3721874 < baseStart_3721874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721911 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_3721911 : Nat := 118140960795 + 3721911 * 2 ^ 59
def prefixEnd_3721911 : Nat := 4983230072969 + 3 ^ 40 * 3721911 * 2
def baseEnd_3721911 : Nat := 1911129296256292739795749

theorem tailTrace_3721911 : CollatzResearch.WordTrace tailWord_3721911 prefixEnd_3721911 1911129296256292739795749 := by
  unfold tailWord_3721911
  simp only [CollatzResearch.WordTrace]
  refine ⟨135749246419159573637085587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90499497612773049091390391 135749246419159573637085587)
  ·
    refine ⟨203623869628739360455628381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135749246419159573637085587 203623869628739360455628381)
    ·
      refine ⟨76358951110777260170860643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203623869628739360455628381 76358951110777260170860643)
      ·
        refine ⟨114538426666165890256290965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76358951110777260170860643 114538426666165890256290965)
        ·
          refine ⟨5368988749976526105763639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114538426666165890256290965 5368988749976526105763639)
          ·
            refine ⟨8053483124964789158645459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368988749976526105763639 8053483124964789158645459)
            ·
              refine ⟨12080224687447183737968189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053483124964789158645459 12080224687447183737968189)
              ·
                refine ⟨4530084257792693901738071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12080224687447183737968189 4530084257792693901738071)
                ·
                  refine ⟨6795126386689040852607107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530084257792693901738071 6795126386689040852607107)
                  ·
                    refine ⟨10192689580033561278910661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6795126386689040852607107 10192689580033561278910661)
                    ·
                      refine ⟨1911129296256292739795749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10192689580033561278910661 1911129296256292739795749)
                      ·
                        rfl

theorem cell23_3721911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_3721911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721911 prefixEnd_3721911 := by exact prefixLift 3721911
  have htrace : WordTrace (prefixWord ++ tailWord_3721911) baseStart_3721911 baseEnd_3721911 := by
    simpa [prefixWord, tailWord_3721911, baseEnd_3721911] using wordTrace_append hprefix tailTrace_3721911
  have hstable : (prefixWord ++ tailWord_3721911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721911).length < 2 ^ (prefixWord ++ tailWord_3721911).sum := by decide
  have hdescent : baseEnd_3721911 < baseStart_3721911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721917 : List Nat := [1, 4, 1, 2, 1, 4, 10]
def baseStart_3721917 : Nat := 118140960795 + 3721917 * 2 ^ 59
def prefixEnd_3721917 : Nat := 4983230072969 + 3 ^ 40 * 3721917 * 2
def baseEnd_3721917 : Nat := 23594226878274317485441

theorem tailTrace_3721917 : CollatzResearch.WordTrace tailWord_3721917 prefixEnd_3721917 23594226878274317485441 := by
  unfold tailWord_3721917
  simp only [CollatzResearch.WordTrace]
  refine ⟨135749465257137836661804005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90499643504758557774536003 135749465257137836661804005)
  ·
    refine ⟨25453024735713344374088251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135749465257137836661804005 25453024735713344374088251)
    ·
      refine ⟨38179537103570016561132377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25453024735713344374088251 38179537103570016561132377)
      ·
        refine ⟨28634652827677512420849283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38179537103570016561132377 28634652827677512420849283)
        ·
          refine ⟨42951979241516268631273925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28634652827677512420849283 42951979241516268631273925)
          ·
            refine ⟨8053496107784300368363861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42951979241516268631273925 8053496107784300368363861)
            ·
              refine ⟨23594226878274317485441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8053496107784300368363861 23594226878274317485441)
              ·
                rfl

theorem cell23_3721917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 10].length) (baseStart_3721917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721917 prefixEnd_3721917 := by exact prefixLift 3721917
  have htrace : WordTrace (prefixWord ++ tailWord_3721917) baseStart_3721917 baseEnd_3721917 := by
    simpa [prefixWord, tailWord_3721917, baseEnd_3721917] using wordTrace_append hprefix tailTrace_3721917
  have hstable : (prefixWord ++ tailWord_3721917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721917).length < 2 ^ (prefixWord ++ tailWord_3721917).sum := by decide
  have hdescent : baseEnd_3721917 < baseStart_3721917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721928 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_3721928 : Nat := 118140960795 + 3721928 * 2 ^ 59
def prefixEnd_3721928 : Nat := 4983230072969 + 3 ^ 40 * 3721928 * 2
def baseEnd_3721928 : Nat := 1911138025427419173283171

theorem tailTrace_3721928 : CollatzResearch.WordTrace tailWord_3721928 prefixEnd_3721928 1911138025427419173283171 := by
  unfold tailWord_3721928
  simp only [CollatzResearch.WordTrace]
  refine ⟨67874933230048992770227219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90499910973398657026969625 67874933230048992770227219)
  ·
    refine ⟨101812399845073489155340829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67874933230048992770227219 101812399845073489155340829)
    ·
      refine ⟨38179649941902558433252811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101812399845073489155340829 38179649941902558433252811)
      ·
        refine ⟨57269474912853837649879217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38179649941902558433252811 57269474912853837649879217)
        ·
          refine ⟨42952106184640378237409413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57269474912853837649879217 42952106184640378237409413)
          ·
            refine ⟨8053519909620070919514265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42952106184640378237409413 8053519909620070919514265)
            ·
              refine ⟨6040139932215053189635699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053519909620070919514265 6040139932215053189635699)
              ·
                refine ⟨9060209898322579784453549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040139932215053189635699 9060209898322579784453549)
                ·
                  refine ⟨3397578711870967419170081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9060209898322579784453549 3397578711870967419170081)
                  ·
                    refine ⟨2548184033903225564377561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397578711870967419170081 2548184033903225564377561)
                    ·
                      refine ⟨1911138025427419173283171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548184033903225564377561 1911138025427419173283171)
                      ·
                        rfl

theorem cell23_3721928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_3721928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721928 prefixEnd_3721928 := by exact prefixLift 3721928
  have htrace : WordTrace (prefixWord ++ tailWord_3721928) baseStart_3721928 baseEnd_3721928 := by
    simpa [prefixWord, tailWord_3721928, baseEnd_3721928] using wordTrace_append hprefix tailTrace_3721928
  have hstable : (prefixWord ++ tailWord_3721928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721928).length < 2 ^ (prefixWord ++ tailWord_3721928).sum := by decide
  have hdescent : baseEnd_3721928 < baseStart_3721928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721938 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3721938 : Nat := 118140960795 + 3721938 * 2 ^ 59
def prefixEnd_3721938 : Nat := 4983230072969 + 3 ^ 40 * 3721938 * 2
def baseEnd_3721938 : Nat := 637047720077988044719375

theorem tailTrace_3721938 : CollatzResearch.WordTrace tailWord_3721938 prefixEnd_3721938 637047720077988044719375 := by
  unfold tailWord_3721938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33937557797515439312079617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90500154126707838165545645 33937557797515439312079617)
  ·
    refine ⟨25453168348136579484059713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33937557797515439312079617 25453168348136579484059713)
    ·
      refine ⟨19089876261102434613044785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25453168348136579484059713 19089876261102434613044785)
      ·
        refine ⟨14317407195826825959783589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19089876261102434613044785 14317407195826825959783589)
        ·
          refine ⟨2684513849217529867459423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14317407195826825959783589 2684513849217529867459423)
          ·
            refine ⟨4026770773826294801189135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684513849217529867459423 4026770773826294801189135)
            ·
              refine ⟨6040156160739442201783703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026770773826294801189135 6040156160739442201783703)
              ·
                refine ⟨9060234241109163302675555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040156160739442201783703 9060234241109163302675555)
                ·
                  refine ⟨13590351361663744954013333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060234241109163302675555 13590351361663744954013333)
                  ·
                    refine ⟨637047720077988044719375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13590351361663744954013333 637047720077988044719375)
                    ·
                      rfl

theorem cell23_3721938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3721938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721938 prefixEnd_3721938 := by exact prefixLift 3721938
  have htrace : WordTrace (prefixWord ++ tailWord_3721938) baseStart_3721938 baseEnd_3721938 := by
    simpa [prefixWord, tailWord_3721938, baseEnd_3721938] using wordTrace_append hprefix tailTrace_3721938
  have hstable : (prefixWord ++ tailWord_3721938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721938).length < 2 ^ (prefixWord ++ tailWord_3721938).sum := by decide
  have hdescent : baseEnd_3721938 < baseStart_3721938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721941 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3721941 : Nat := 118140960795 + 3721941 * 2 ^ 59
def prefixEnd_3721941 : Nat := 4983230072969 + 3 ^ 40 * 3721941 * 2
def baseEnd_3721941 : Nat := 1911144700675927622420611

theorem tailTrace_3721941 : CollatzResearch.WordTrace tailWord_3721941 prefixEnd_3721941 1911144700675927622420611 := by
  unfold tailWord_3721941
  simp only [CollatzResearch.WordTrace]
  refine ⟨135750340609050888760677677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90500227072700592507118451 135750340609050888760677677)
  ·
    refine ⟨50906377728394083285254129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135750340609050888760677677 50906377728394083285254129)
    ·
      refine ⟨38179783296295562463940597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50906377728394083285254129 38179783296295562463940597)
      ·
        refine ⟨3579354684027708980994431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38179783296295562463940597 3579354684027708980994431)
        ·
          refine ⟨5369032026041563471491647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579354684027708980994431 5369032026041563471491647)
          ·
            refine ⟨8053548039062345207237471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369032026041563471491647 8053548039062345207237471)
            ·
              refine ⟨12080322058593517810856207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053548039062345207237471 12080322058593517810856207)
              ·
                refine ⟨18120483087890276716284311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080322058593517810856207 18120483087890276716284311)
                ·
                  refine ⟨27180724631835415074426467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18120483087890276716284311 27180724631835415074426467)
                  ·
                    refine ⟨40771086947753122611639701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27180724631835415074426467 40771086947753122611639701)
                    ·
                      refine ⟨1911144700675927622420611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40771086947753122611639701 1911144700675927622420611)
                      ·
                        rfl

theorem cell23_3721941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3721941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721941 prefixEnd_3721941 := by exact prefixLift 3721941
  have htrace : WordTrace (prefixWord ++ tailWord_3721941) baseStart_3721941 baseEnd_3721941 := by
    simpa [prefixWord, tailWord_3721941, baseEnd_3721941] using wordTrace_append hprefix tailTrace_3721941
  have hstable : (prefixWord ++ tailWord_3721941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721941).length < 2 ^ (prefixWord ++ tailWord_3721941).sum := by decide
  have hdescent : baseEnd_3721941 < baseStart_3721941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721948 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3721948 : Nat := 118140960795 + 3721948 * 2 ^ 59
def prefixEnd_3721948 : Nat := 4983230072969 + 3 ^ 40 * 3721948 * 2
def baseEnd_3721948 : Nat := 1911148295040509095033079

theorem tailTrace_3721948 : CollatzResearch.WordTrace tailWord_3721948 prefixEnd_3721948 1911148295040509095033079 := by
  unfold tailWord_3721948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67875297960012764478091249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90500397280017019304121665 67875297960012764478091249)
  ·
    refine ⟨50906473470009573358568437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67875297960012764478091249 50906473470009573358568437)
    ·
      refine ⟨4772481887813397502365791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50906473470009573358568437 4772481887813397502365791)
      ·
        refine ⟨7158722831720096253548687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4772481887813397502365791 7158722831720096253548687)
        ·
          refine ⟨10738084247580144380323031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158722831720096253548687 10738084247580144380323031)
          ·
            refine ⟨16107126371370216570484547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10738084247580144380323031 16107126371370216570484547)
            ·
              refine ⟨24160689557055324855726821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16107126371370216570484547 24160689557055324855726821)
              ·
                refine ⟨4530129291947873410448779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24160689557055324855726821 4530129291947873410448779)
                ·
                  refine ⟨6795193937921810115673169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530129291947873410448779 6795193937921810115673169)
                  ·
                    refine ⟨5096395453441357586754877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795193937921810115673169 5096395453441357586754877)
                    ·
                      refine ⟨1911148295040509095033079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096395453441357586754877 1911148295040509095033079)
                      ·
                        rfl

theorem cell23_3721948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3721948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721948 prefixEnd_3721948 := by exact prefixLift 3721948
  have htrace : WordTrace (prefixWord ++ tailWord_3721948) baseStart_3721948 baseEnd_3721948 := by
    simpa [prefixWord, tailWord_3721948, baseEnd_3721948] using wordTrace_append hprefix tailTrace_3721948
  have hstable : (prefixWord ++ tailWord_3721948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721948).length < 2 ^ (prefixWord ++ tailWord_3721948).sum := by decide
  have hdescent : baseEnd_3721948 < baseStart_3721948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721974 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3721974 : Nat := 118140960795 + 3721974 * 2 ^ 59
def prefixEnd_3721974 : Nat := 4983230072969 + 3 ^ 40 * 3721974 * 2
def baseEnd_3721974 : Nat := 1911161645537525993307959

theorem tailTrace_3721974 : CollatzResearch.WordTrace tailWord_3721974 prefixEnd_3721974 1911161645537525993307959 := by
  unfold tailWord_3721974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484471513620708462289311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90501029478620890264419317 8484471513620708462289311)
  ·
    refine ⟨12726707270431062693433967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8484471513620708462289311 12726707270431062693433967)
    ·
      refine ⟨19090060905646594040150951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12726707270431062693433967 19090060905646594040150951)
      ·
        refine ⟨28635091358469891060226427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19090060905646594040150951 28635091358469891060226427)
        ·
          refine ⟨42952637037704836590339641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635091358469891060226427 42952637037704836590339641)
          ·
            refine ⟨32214477778278627442754731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42952637037704836590339641 32214477778278627442754731)
            ·
              refine ⟨48321716667417941164132097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32214477778278627442754731 48321716667417941164132097)
              ·
                refine ⟨36241287500563455873099073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48321716667417941164132097 36241287500563455873099073)
                ·
                  refine ⟨27180965625422591904824305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36241287500563455873099073 27180965625422591904824305)
                  ·
                    refine ⟨20385724219066943928618229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27180965625422591904824305 20385724219066943928618229)
                    ·
                      refine ⟨1911161645537525993307959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20385724219066943928618229 1911161645537525993307959)
                      ·
                        rfl

theorem cell23_3721974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3721974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721974 prefixEnd_3721974 := by exact prefixLift 3721974
  have htrace : WordTrace (prefixWord ++ tailWord_3721974) baseStart_3721974 baseEnd_3721974 := by
    simpa [prefixWord, tailWord_3721974, baseEnd_3721974] using wordTrace_append hprefix tailTrace_3721974
  have hstable : (prefixWord ++ tailWord_3721974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721974).length < 2 ^ (prefixWord ++ tailWord_3721974).sum := by decide
  have hdescent : baseEnd_3721974 < baseStart_3721974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721977 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_3721977 : Nat := 118140960795 + 3721977 * 2 ^ 59
def prefixEnd_3721977 : Nat := 4983230072969 + 3 ^ 40 * 3721977 * 2
def baseEnd_3721977 : Nat := 637054395326496493856815

theorem tailTrace_3721977 : CollatzResearch.WordTrace tailWord_3721977 prefixEnd_3721977 637054395326496493856815 := by
  unfold tailWord_3721977
  simp only [CollatzResearch.WordTrace]
  refine ⟨135751653636920466908988185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90501102424613644605992123 135751653636920466908988185)
  ·
    refine ⟨101813740227690350181741139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135751653636920466908988185 101813740227690350181741139)
    ·
      refine ⟨152720610341535525272611709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101813740227690350181741139 152720610341535525272611709)
      ·
        refine ⟨57270228878075821977229391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152720610341535525272611709 57270228878075821977229391)
        ·
          refine ⟨85905343317113732965844087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57270228878075821977229391 85905343317113732965844087)
          ·
            refine ⟨128858014975670599448766131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85905343317113732965844087 128858014975670599448766131)
            ·
              refine ⟨193287022463505899173149197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128858014975670599448766131 193287022463505899173149197)
              ·
                refine ⟨72482633423814712189930949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193287022463505899173149197 72482633423814712189930949)
                ·
                  refine ⟨13590493766965258535612053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72482633423814712189930949 13590493766965258535612053)
                  ·
                    refine ⟨637054395326496493856815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13590493766965258535612053 637054395326496493856815)
                    ·
                      rfl

theorem cell23_3721977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_3721977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721977 prefixEnd_3721977 := by exact prefixLift 3721977
  have htrace : WordTrace (prefixWord ++ tailWord_3721977) baseStart_3721977 baseEnd_3721977 := by
    simpa [prefixWord, tailWord_3721977, baseEnd_3721977] using wordTrace_append hprefix tailTrace_3721977
  have hstable : (prefixWord ++ tailWord_3721977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721977).length < 2 ^ (prefixWord ++ tailWord_3721977).sum := by decide
  have hdescent : baseEnd_3721977 < baseStart_3721977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721984 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2]
def baseStart_3721984 : Nat := 118140960795 + 3721984 * 2 ^ 59
def prefixEnd_3721984 : Nat := 4983230072969 + 3 ^ 40 * 3721984 * 2
def baseEnd_3721984 : Nat := 1911166780344070954182913

theorem tailTrace_3721984 : CollatzResearch.WordTrace tailWord_3721984 prefixEnd_3721984 1911166780344070954182913 := by
  unfold tailWord_3721984
  simp only [CollatzResearch.WordTrace]
  refine ⟨67875954473947553552246503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90501272631930071402995337 67875954473947553552246503)
  ·
    refine ⟨101813931710921330328369755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67875954473947553552246503 101813931710921330328369755)
    ·
      refine ⟨152720897566381995492554633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101813931710921330328369755 152720897566381995492554633)
      ·
        refine ⟨114540673174786496619415975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152720897566381995492554633 114540673174786496619415975)
        ·
          refine ⟨171811009762179744929123963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114540673174786496619415975 171811009762179744929123963)
          ·
            refine ⟨257716514643269617393685945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171811009762179744929123963 257716514643269617393685945)
            ·
              refine ⟨193287385982452213045264459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257716514643269617393685945 193287385982452213045264459)
              ·
                refine ⟨289931078973678319567896689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193287385982452213045264459 289931078973678319567896689)
                ·
                  refine ⟨217448309230258739675922517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289931078973678319567896689 217448309230258739675922517)
                  ·
                    refine ⟨2548222373792094605577217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 217448309230258739675922517 2548222373792094605577217)
                    ·
                      refine ⟨1911166780344070954182913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548222373792094605577217 1911166780344070954182913)
                      ·
                        rfl

theorem cell23_3721984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_3721984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721984 prefixEnd_3721984 := by exact prefixLift 3721984
  have htrace : WordTrace (prefixWord ++ tailWord_3721984) baseStart_3721984 baseEnd_3721984 := by
    simpa [prefixWord, tailWord_3721984, baseEnd_3721984] using wordTrace_append hprefix tailTrace_3721984
  have hstable : (prefixWord ++ tailWord_3721984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721984).length < 2 ^ (prefixWord ++ tailWord_3721984).sum := by decide
  have hdescent : baseEnd_3721984 < baseStart_3721984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721987 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_3721987 : Nat := 118140960795 + 3721987 * 2 ^ 59
def prefixEnd_3721987 : Nat := 4983230072969 + 3 ^ 40 * 3721987 * 2
def baseEnd_3721987 : Nat := 1911168320786034442445399

theorem tailTrace_3721987 : CollatzResearch.WordTrace tailWord_3721987 prefixEnd_3721987 1911168320786034442445399 := by
  unfold tailWord_3721987
  simp only [CollatzResearch.WordTrace]
  refine ⟨135752018366884238616852215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90501345577922825744568143 135752018366884238616852215)
  ·
    refine ⟨203628027550326357925278323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135752018366884238616852215 203628027550326357925278323)
    ·
      refine ⟨305442041325489536887917485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203628027550326357925278323 305442041325489536887917485)
      ·
        refine ⟨114540765497058576332969057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305442041325489536887917485 114540765497058576332969057)
        ·
          refine ⟨85905574122793932249726793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114540765497058576332969057 85905574122793932249726793)
          ·
            refine ⟨64429180592095449187295095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85905574122793932249726793 64429180592095449187295095)
            ·
              refine ⟨96643770888143173780942643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64429180592095449187295095 96643770888143173780942643)
              ·
                refine ⟨144965656332214760671413965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96643770888143173780942643 144965656332214760671413965)
                ·
                  refine ⟨54362121124580535251780237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144965656332214760671413965 54362121124580535251780237)
                  ·
                    refine ⟨20385795421717700719417589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54362121124580535251780237 20385795421717700719417589)
                    ·
                      refine ⟨1911168320786034442445399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20385795421717700719417589 1911168320786034442445399)
                      ·
                        rfl

theorem cell23_3721987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_3721987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3721987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3721987 prefixEnd_3721987 := by exact prefixLift 3721987
  have htrace : WordTrace (prefixWord ++ tailWord_3721987) baseStart_3721987 baseEnd_3721987 := by
    simpa [prefixWord, tailWord_3721987, baseEnd_3721987] using wordTrace_append hprefix tailTrace_3721987
  have hstable : (prefixWord ++ tailWord_3721987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721987).length < 2 ^ (prefixWord ++ tailWord_3721987).sum := by decide
  have hdescent : baseEnd_3721987 < baseStart_3721987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722018 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_3722018 : Nat := 118140960795 + 3722018 * 2 ^ 59
def prefixEnd_3722018 : Nat := 4983230072969 + 3 ^ 40 * 3722018 * 2
def baseEnd_3722018 : Nat := 1911184238686323821157757

theorem tailTrace_3722018 : CollatzResearch.WordTrace tailWord_3722018 prefixEnd_3722018 1911184238686323821157757 := by
  unfold tailWord_3722018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938287257442982727807677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90502099353181287274153805 33938287257442982727807677)
  ·
    refine ⟨12726857721541118522927879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33938287257442982727807677 12726857721541118522927879)
    ·
      refine ⟨19090286582311677784391819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12726857721541118522927879 19090286582311677784391819)
      ·
        refine ⟨28635429873467516676587729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19090286582311677784391819 28635429873467516676587729)
        ·
          refine ⟨21476572405100637507440797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28635429873467516676587729 21476572405100637507440797)
          ·
            refine ⟨8053714651912739065290299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21476572405100637507440797 8053714651912739065290299)
            ·
              refine ⟨12080571977869108597935449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053714651912739065290299 12080571977869108597935449)
              ·
                refine ⟨9060428983401831448451587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12080571977869108597935449 9060428983401831448451587)
                ·
                  refine ⟨13590643475102747172677381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060428983401831448451587 13590643475102747172677381)
                  ·
                    refine ⟨2548245651581765094877009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13590643475102747172677381 2548245651581765094877009)
                    ·
                      refine ⟨1911184238686323821157757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548245651581765094877009 1911184238686323821157757)
                      ·
                        rfl

theorem cell23_3722018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_3722018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722018 prefixEnd_3722018 := by exact prefixLift 3722018
  have htrace : WordTrace (prefixWord ++ tailWord_3722018) baseStart_3722018 baseEnd_3722018 := by
    simpa [prefixWord, tailWord_3722018, baseEnd_3722018] using wordTrace_append hprefix tailTrace_3722018
  have hstable : (prefixWord ++ tailWord_3722018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722018).length < 2 ^ (prefixWord ++ tailWord_3722018).sum := by decide
  have hdescent : baseEnd_3722018 < baseStart_3722018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722035 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 2, 2, 2]
def baseStart_3722035 : Nat := 118140960795 + 3722035 * 2 ^ 59
def prefixEnd_3722035 : Nat := 4983230072969 + 3 ^ 40 * 3722035 * 2
def baseEnd_3722035 : Nat := 1911192967857450254645179

theorem tailTrace_3722035 : CollatzResearch.WordTrace tailWord_3722035 prefixEnd_3722035 1911192967857450254645179 := by
  unfold tailWord_3722035
  simp only [CollatzResearch.WordTrace]
  refine ⟨135753769070710342814599559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90502512713806895209733039 135753769070710342814599559)
  ·
    refine ⟨203630653606065514221899339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135753769070710342814599559 203630653606065514221899339)
    ·
      refine ⟨305445980409098271332849009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203630653606065514221899339 305445980409098271332849009)
      ·
        refine ⟨229084485306823703499636757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305445980409098271332849009 229084485306823703499636757)
        ·
          refine ⟨10738335248757361101545473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229084485306823703499636757 10738335248757361101545473)
          ·
            refine ⟨8053751436568020826159105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10738335248757361101545473 8053751436568020826159105)
            ·
              refine ⟨6040313577426015619619329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053751436568020826159105 6040313577426015619619329)
              ·
                refine ⟨4530235183069511714714497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040313577426015619619329 4530235183069511714714497)
                ·
                  refine ⟨3397676387302133786035873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4530235183069511714714497 3397676387302133786035873)
                  ·
                    refine ⟨2548257290476600339526905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397676387302133786035873 2548257290476600339526905)
                    ·
                      refine ⟨1911192967857450254645179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548257290476600339526905 1911192967857450254645179)
                      ·
                        rfl

theorem cell23_3722035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2, 2].length) (baseStart_3722035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722035 prefixEnd_3722035 := by exact prefixLift 3722035
  have htrace : WordTrace (prefixWord ++ tailWord_3722035) baseStart_3722035 baseEnd_3722035 := by
    simpa [prefixWord, tailWord_3722035, baseEnd_3722035] using wordTrace_append hprefix tailTrace_3722035
  have hstable : (prefixWord ++ tailWord_3722035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722035).length < 2 ^ (prefixWord ++ tailWord_3722035).sum := by decide
  have hdescent : baseEnd_3722035 < baseStart_3722035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722052 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3722052 : Nat := 118140960795 + 3722052 * 2 ^ 59
def prefixEnd_3722052 : Nat := 4983230072969 + 3 ^ 40 * 3722052 * 2
def baseEnd_3722052 : Nat := 1911201697028576688132601

theorem tailTrace_3722052 : CollatzResearch.WordTrace tailWord_3722052 prefixEnd_3722052 1911201697028576688132601 := by
  unfold tailWord_3722052
  simp only [CollatzResearch.WordTrace]
  refine ⟨67877194555824377358984205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90502926074432503145312273 67877194555824377358984205)
  ·
    refine ⟨25453947958434141509619077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67877194555824377358984205 25453947958434141509619077)
    ·
      refine ⟨4772615242206401533053577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25453947958434141509619077 4772615242206401533053577)
      ·
        refine ⟨3579461431654801149790183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4772615242206401533053577 3579461431654801149790183)
        ·
          refine ⟨5369192147482201724685275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579461431654801149790183 5369192147482201724685275)
          ·
            refine ⟨8053788221223302587027913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369192147482201724685275 8053788221223302587027913)
            ·
              refine ⟨6040341165917476940270935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053788221223302587027913 6040341165917476940270935)
              ·
                refine ⟨9060511748876215410406403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040341165917476940270935 9060511748876215410406403)
                ·
                  refine ⟨13590767623314323115609605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060511748876215410406403 13590767623314323115609605)
                  ·
                    refine ⟨2548268929371435584176801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13590767623314323115609605 2548268929371435584176801)
                    ·
                      refine ⟨1911201697028576688132601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548268929371435584176801 1911201697028576688132601)
                      ·
                        rfl

theorem cell23_3722052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3722052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722052 prefixEnd_3722052 := by exact prefixLift 3722052
  have htrace : WordTrace (prefixWord ++ tailWord_3722052) baseStart_3722052 baseEnd_3722052 := by
    simpa [prefixWord, tailWord_3722052, baseEnd_3722052] using wordTrace_append hprefix tailTrace_3722052
  have hstable : (prefixWord ++ tailWord_3722052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722052).length < 2 ^ (prefixWord ++ tailWord_3722052).sum := by decide
  have hdescent : baseEnd_3722052 < baseStart_3722052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722071 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 2, 5]
def baseStart_3722071 : Nat := 118140960795 + 3722071 * 2 ^ 59
def prefixEnd_3722071 : Nat := 4983230072969 + 3 ^ 40 * 3722071 * 2
def baseEnd_3722071 : Nat := 637070484387004037931671

theorem tailTrace_3722071 : CollatzResearch.WordTrace tailWord_3722071 prefixEnd_3722071 637070484387004037931671 := by
  unfold tailWord_3722071
  simp only [CollatzResearch.WordTrace]
  refine ⟨135755082098579920962910067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90503388065719947308606711 135755082098579920962910067)
  ·
    refine ⟨203632623147869881444365101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135755082098579920962910067 203632623147869881444365101)
    ·
      refine ⟨76362233680451205541636913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203632623147869881444365101 76362233680451205541636913)
      ·
        refine ⟨57271675260338404156227685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76362233680451205541636913 57271675260338404156227685)
        ·
          refine ⟨10738439111313450779292691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57271675260338404156227685 10738439111313450779292691)
          ·
            refine ⟨16107658666970176168939037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10738439111313450779292691 16107658666970176168939037)
            ·
              refine ⟨6040372000113816063352139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16107658666970176168939037 6040372000113816063352139)
              ·
                refine ⟨9060558000170724095028209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040372000113816063352139 9060558000170724095028209)
                ·
                  refine ⟨6795418500128043071271157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9060558000170724095028209 6795418500128043071271157)
                  ·
                    refine ⟨637070484387004037931671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6795418500128043071271157 637070484387004037931671)
                    ·
                      rfl

theorem cell23_3722071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_3722071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722071 prefixEnd_3722071 := by exact prefixLift 3722071
  have htrace : WordTrace (prefixWord ++ tailWord_3722071) baseStart_3722071 baseEnd_3722071 := by
    simpa [prefixWord, tailWord_3722071, baseEnd_3722071] using wordTrace_append hprefix tailTrace_3722071
  have hstable : (prefixWord ++ tailWord_3722071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722071).length < 2 ^ (prefixWord ++ tailWord_3722071).sum := by decide
  have hdescent : baseEnd_3722071 < baseStart_3722071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722091 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 2, 4, 2]
def baseStart_3722091 : Nat := 118140960795 + 3722091 * 2 ^ 59
def prefixEnd_3722091 : Nat := 4983230072969 + 3 ^ 40 * 3722091 * 2
def baseEnd_3722091 : Nat := 1911221722774102035544921

theorem tailTrace_3722091 : CollatzResearch.WordTrace tailWord_3722091 prefixEnd_3722091 1911221722774102035544921 := by
  unfold tailWord_3722091
  simp only [CollatzResearch.WordTrace]
  refine ⟨135755811558507464378638127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90503874372338309585758751 135755811558507464378638127)
  ·
    refine ⟨203633717337761196567957191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135755811558507464378638127 203633717337761196567957191)
    ·
      refine ⟨305450576006641794851935787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203633717337761196567957191 305450576006641794851935787)
      ·
        refine ⟨458175864009962692277903681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305450576006641794851935787 458175864009962692277903681)
        ·
          refine ⟨343631898007472019208427761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458175864009962692277903681 343631898007472019208427761)
          ·
            refine ⟨257723923505604014406320821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343631898007472019208427761 257723923505604014406320821)
            ·
              refine ⟨24161617828650376350592577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257723923505604014406320821 24161617828650376350592577)
              ·
                refine ⟨18121213371487782262944433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24161617828650376350592577 18121213371487782262944433)
                ·
                  refine ⟨13590910028615836697208325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18121213371487782262944433 13590910028615836697208325)
                  ·
                    refine ⟨2548295630365469380726561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13590910028615836697208325 2548295630365469380726561)
                    ·
                      refine ⟨1911221722774102035544921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548295630365469380726561 1911221722774102035544921)
                      ·
                        rfl

theorem cell23_3722091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 4, 2].length) (baseStart_3722091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722091 prefixEnd_3722091 := by exact prefixLift 3722091
  have htrace : WordTrace (prefixWord ++ tailWord_3722091) baseStart_3722091 baseEnd_3722091 := by
    simpa [prefixWord, tailWord_3722091, baseEnd_3722091] using wordTrace_append hprefix tailTrace_3722091
  have hstable : (prefixWord ++ tailWord_3722091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722091).length < 2 ^ (prefixWord ++ tailWord_3722091).sum := by decide
  have hdescent : baseEnd_3722091 < baseStart_3722091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722191 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 1, 6]
def baseStart_3722191 : Nat := 118140960795 + 3722191 * 2 ^ 59
def prefixEnd_3722191 : Nat := 4983230072969 + 3 ^ 40 * 3722191 * 2
def baseEnd_3722191 : Nat := 637091023613183881431487

theorem tailTrace_3722191 : CollatzResearch.WordTrace tailWord_3722191 prefixEnd_3722191 637091023613183881431487 := by
  unfold tailWord_3722191
  simp only [CollatzResearch.WordTrace]
  refine ⟨135759458858145181457278427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90506305905430120971518951 135759458858145181457278427)
  ·
    refine ⟨203639188287217772185917641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135759458858145181457278427 203639188287217772185917641)
    ·
      refine ⟨152729391215413329139438231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203639188287217772185917641 152729391215413329139438231)
      ·
        refine ⟨229094086823119993709157347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152729391215413329139438231 229094086823119993709157347)
        ·
          refine ⟨343641130234679990563736021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229094086823119993709157347 343641130234679990563736021)
          ·
            refine ⟨8054088989875312278837563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 343641130234679990563736021 8054088989875312278837563)
            ·
              refine ⟨12081133484812968418256345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054088989875312278837563 12081133484812968418256345)
              ·
                refine ⟨9060850113609726313692259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081133484812968418256345 9060850113609726313692259)
                ·
                  refine ⟨13591275170414589470538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060850113609726313692259 13591275170414589470538389)
                  ·
                    refine ⟨637091023613183881431487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13591275170414589470538389 637091023613183881431487)
                    ·
                      rfl

theorem cell23_3722191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_3722191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722191 prefixEnd_3722191 := by exact prefixLift 3722191
  have htrace : WordTrace (prefixWord ++ tailWord_3722191) baseStart_3722191 baseEnd_3722191 := by
    simpa [prefixWord, tailWord_3722191, baseEnd_3722191] using wordTrace_append hprefix tailTrace_3722191
  have hstable : (prefixWord ++ tailWord_3722191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722191).length < 2 ^ (prefixWord ++ tailWord_3722191).sum := by decide
  have hdescent : baseEnd_3722191 < baseStart_3722191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722211 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3722211 : Nat := 118140960795 + 3722211 * 2 ^ 59
def prefixEnd_3722211 : Nat := 4983230072969 + 3 ^ 40 * 3722211 * 2
def baseEnd_3722211 : Nat := 1911283340452641566044369

theorem tailTrace_3722211 : CollatzResearch.WordTrace tailWord_3722211 prefixEnd_3722211 1911283340452641566044369 := by
  unfold tailWord_3722211
  simp only [CollatzResearch.WordTrace]
  refine ⟨135760188318072724873006487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90506792212048483248670991 135760188318072724873006487)
  ·
    refine ⟨203640282477109087309509731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135760188318072724873006487 203640282477109087309509731)
    ·
      refine ⟨305460423715663630964264597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203640282477109087309509731 305460423715663630964264597)
      ·
        refine ⟨14318457361671732701449903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 305460423715663630964264597 14318457361671732701449903)
        ·
          refine ⟨21477686042507599052174855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14318457361671732701449903 21477686042507599052174855)
          ·
            refine ⟨32216529063761398578262283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21477686042507599052174855 32216529063761398578262283)
            ·
              refine ⟨48324793595642097867393425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32216529063761398578262283 48324793595642097867393425)
              ·
                refine ⟨36243595196731573400545069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48324793595642097867393425 36243595196731573400545069)
                ·
                  refine ⟨13591348198774340025204401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36243595196731573400545069 13591348198774340025204401)
                  ·
                    refine ⟨10193511149080755018903301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13591348198774340025204401 10193511149080755018903301)
                    ·
                      refine ⟨1911283340452641566044369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10193511149080755018903301 1911283340452641566044369)
                      ·
                        rfl

theorem cell23_3722211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3722211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722211 prefixEnd_3722211 := by exact prefixLift 3722211
  have htrace : WordTrace (prefixWord ++ tailWord_3722211) baseStart_3722211 baseEnd_3722211 := by
    simpa [prefixWord, tailWord_3722211, baseEnd_3722211] using wordTrace_append hprefix tailTrace_3722211
  have hstable : (prefixWord ++ tailWord_3722211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722211).length < 2 ^ (prefixWord ++ tailWord_3722211).sum := by decide
  have hdescent : baseEnd_3722211 < baseStart_3722211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722218 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_3722218 : Nat := 118140960795 + 3722218 * 2 ^ 59
def prefixEnd_3722218 : Nat := 4983230072969 + 3 ^ 40 * 3722218 * 2
def baseEnd_3722218 : Nat := 1911286934817223038656837

theorem tailTrace_3722218 : CollatzResearch.WordTrace tailWord_3722218 prefixEnd_3722218 1911286934817223038656837 := by
  unfold tailWord_3722218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33940110907261841267127827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90506962419364910045674205 33940110907261841267127827)
  ·
    refine ⟨50910166360892761900691741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33940110907261841267127827 50910166360892761900691741)
    ·
      refine ⟨19091312385334785712759403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50910166360892761900691741 19091312385334785712759403)
      ·
        refine ⟨28636968578002178569139105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19091312385334785712759403 28636968578002178569139105)
        ·
          refine ⟨21477726433501633926854329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28636968578002178569139105 21477726433501633926854329)
          ·
            refine ⟨16108294825126225445140747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21477726433501633926854329 16108294825126225445140747)
            ·
              refine ⟨24162442237689338167711121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16108294825126225445140747 24162442237689338167711121)
              ·
                refine ⟨18121831678267003625783341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24162442237689338167711121 18121831678267003625783341)
                ·
                  refine ⟨6795686879350126359668753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18121831678267003625783341 6795686879350126359668753)
                  ·
                    refine ⟨5096765159512594769751565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795686879350126359668753 5096765159512594769751565)
                    ·
                      refine ⟨1911286934817223038656837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096765159512594769751565 1911286934817223038656837)
                      ·
                        rfl

theorem cell23_3722218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_3722218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722218 prefixEnd_3722218 := by exact prefixLift 3722218
  have htrace : WordTrace (prefixWord ++ tailWord_3722218) baseStart_3722218 baseEnd_3722218 := by
    simpa [prefixWord, tailWord_3722218, baseEnd_3722218] using wordTrace_append hprefix tailTrace_3722218
  have hstable : (prefixWord ++ tailWord_3722218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722218).length < 2 ^ (prefixWord ++ tailWord_3722218).sum := by decide
  have hdescent : baseEnd_3722218 < baseStart_3722218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722248 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3722248 : Nat := 118140960795 + 3722248 * 2 ^ 59
def prefixEnd_3722248 : Nat := 4983230072969 + 3 ^ 40 * 3722248 * 2
def baseEnd_3722248 : Nat := 1911302339236857921281699

theorem tailTrace_3722248 : CollatzResearch.WordTrace tailWord_3722248 prefixEnd_3722248 1911302339236857921281699 := by
  unfold tailWord_3722248
  simp only [CollatzResearch.WordTrace]
  refine ⟨67880768909469340096051699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90507691879292453461402265 67880768909469340096051699)
  ·
    refine ⟨101821153364204010144077549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67880768909469340096051699 101821153364204010144077549)
    ·
      refine ⟨38182932511576503804029081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101821153364204010144077549 38182932511576503804029081)
      ·
        refine ⟨28637199383682377853021811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38182932511576503804029081 28637199383682377853021811)
        ·
          refine ⟨42955799075523566779532717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28637199383682377853021811 42955799075523566779532717)
          ·
            refine ⟨16108424653321337542324769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42955799075523566779532717 16108424653321337542324769)
            ·
              refine ⟨12081318489991003156743577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16108424653321337542324769 12081318489991003156743577)
              ·
                refine ⟨9060988867493252367557683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081318489991003156743577 9060988867493252367557683)
                ·
                  refine ⟨13591483301239878551336525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060988867493252367557683 13591483301239878551336525)
                  ·
                    refine ⟨5096806237964954456751197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13591483301239878551336525 5096806237964954456751197)
                    ·
                      refine ⟨1911302339236857921281699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096806237964954456751197 1911302339236857921281699)
                      ·
                        rfl

theorem cell23_3722248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3722248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722248 prefixEnd_3722248 := by exact prefixLift 3722248
  have htrace : WordTrace (prefixWord ++ tailWord_3722248) baseStart_3722248 baseEnd_3722248 := by
    simpa [prefixWord, tailWord_3722248, baseEnd_3722248] using wordTrace_append hprefix tailTrace_3722248
  have hstable : (prefixWord ++ tailWord_3722248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722248).length < 2 ^ (prefixWord ++ tailWord_3722248).sum := by decide
  have hdescent : baseEnd_3722248 < baseStart_3722248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722252 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_3722252 : Nat := 118140960795 + 3722252 * 2 ^ 59
def prefixEnd_3722252 : Nat := 4983230072969 + 3 ^ 40 * 3722252 * 2
def baseEnd_3722252 : Nat := 1911304393159475905631681

theorem tailTrace_3722252 : CollatzResearch.WordTrace tailWord_3722252 prefixEnd_3722252 1911304393159475905631681 := by
  unfold tailWord_3722252
  simp only [CollatzResearch.WordTrace]
  refine ⟨67880841855462094437624505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90507789140616125916832673 67880841855462094437624505)
  ·
    refine ⟨50910631391596570828218379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67880841855462094437624505 50910631391596570828218379)
    ·
      refine ⟨76365947087394856242327569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50910631391596570828218379 76365947087394856242327569)
      ·
        refine ⟨57274460315546142181745677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76365947087394856242327569 57274460315546142181745677)
        ·
          refine ⟨21477922618329803318154629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57274460315546142181745677 21477922618329803318154629)
          ·
            refine ⟨4027110490936838122153993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21477922618329803318154629 4027110490936838122153993)
            ·
              refine ⟨3020332868202628591615495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027110490936838122153993 3020332868202628591615495)
              ·
                refine ⟨4530499302303942887423243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020332868202628591615495 4530499302303942887423243)
                ·
                  refine ⟨6795748953455914331134865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530499302303942887423243 6795748953455914331134865)
                  ·
                    refine ⟨5096811715091935748351149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6795748953455914331134865 5096811715091935748351149)
                    ·
                      refine ⟨1911304393159475905631681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096811715091935748351149 1911304393159475905631681)
                      ·
                        rfl

theorem cell23_3722252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_3722252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722252 prefixEnd_3722252 := by exact prefixLift 3722252
  have htrace : WordTrace (prefixWord ++ tailWord_3722252) baseStart_3722252 baseEnd_3722252 := by
    simpa [prefixWord, tailWord_3722252, baseEnd_3722252] using wordTrace_append hprefix tailTrace_3722252
  have hstable : (prefixWord ++ tailWord_3722252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722252).length < 2 ^ (prefixWord ++ tailWord_3722252).sum := by decide
  have hdescent : baseEnd_3722252 < baseStart_3722252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722265 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 3]
def baseStart_3722265 : Nat := 118140960795 + 3722265 * 2 ^ 59
def prefixEnd_3722265 : Nat := 4983230072969 + 3 ^ 40 * 3722265 * 2
def baseEnd_3722265 : Nat := 1911311068407984354769121

theorem tailTrace_3722265 : CollatzResearch.WordTrace tailWord_3722265 prefixEnd_3722265 1911311068407984354769121 := by
  unfold tailWord_3722265
  simp only [CollatzResearch.WordTrace]
  refine ⟨135762157859877092095472249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90508105239918061396981499 135762157859877092095472249)
  ·
    refine ⟨101821618394907819071604187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135762157859877092095472249 101821618394907819071604187)
    ·
      refine ⟨152732427592361728607406281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101821618394907819071604187 152732427592361728607406281)
      ·
        refine ⟨114549320694271296455554711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152732427592361728607406281 114549320694271296455554711)
        ·
          refine ⟨171823981041406944683332067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114549320694271296455554711 171823981041406944683332067)
          ·
            refine ⟨257735971562110417024998101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171823981041406944683332067 257735971562110417024998101)
            ·
              refine ⟨6040686833486962899023393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257735971562110417024998101 6040686833486962899023393)
              ·
                refine ⟨4530515125115222174267545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040686833486962899023393 4530515125115222174267545)
                ·
                  refine ⟨3397886343836416630700659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4530515125115222174267545 3397886343836416630700659)
                  ·
                    refine ⟨5096829515754624946050989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397886343836416630700659 5096829515754624946050989)
                    ·
                      refine ⟨1911311068407984354769121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096829515754624946050989 1911311068407984354769121)
                      ·
                        rfl

theorem cell23_3722265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_3722265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722265 prefixEnd_3722265 := by exact prefixLift 3722265
  have htrace : WordTrace (prefixWord ++ tailWord_3722265) baseStart_3722265 baseEnd_3722265 := by
    simpa [prefixWord, tailWord_3722265, baseEnd_3722265] using wordTrace_append hprefix tailTrace_3722265
  have hstable : (prefixWord ++ tailWord_3722265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722265).length < 2 ^ (prefixWord ++ tailWord_3722265).sum := by decide
  have hdescent : baseEnd_3722265 < baseStart_3722265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722282 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3722282 : Nat := 118140960795 + 3722282 * 2 ^ 59
def prefixEnd_3722282 : Nat := 4983230072969 + 3 ^ 40 * 3722282 * 2
def baseEnd_3722282 : Nat := 1911319797579110788256543

theorem tailTrace_3722282 : CollatzResearch.WordTrace tailWord_3722282 prefixEnd_3722282 1911319797579110788256543 := by
  unfold tailWord_3722282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33940694475203875999710275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90508518600543669332560733 33940694475203875999710275)
  ·
    refine ⟨50911041712805813999565413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33940694475203875999710275 50911041712805813999565413)
    ·
      refine ⟨9545820321151090124918515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50911041712805813999565413 9545820321151090124918515)
      ·
        refine ⟨14318730481726635187377773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545820321151090124918515 14318730481726635187377773)
        ·
          refine ⟨5369523930647488195266665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14318730481726635187377773 5369523930647488195266665)
          ·
            refine ⟨4027142947985616146449999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5369523930647488195266665 4027142947985616146449999)
            ·
              refine ⟨6040714421978424219674999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027142947985616146449999 6040714421978424219674999)
              ·
                refine ⟨9061071632967636329512499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040714421978424219674999 9061071632967636329512499)
                ·
                  refine ⟨13591607449451454494268749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9061071632967636329512499 13591607449451454494268749)
                  ·
                    refine ⟨5096852793544295435350781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13591607449451454494268749 5096852793544295435350781)
                    ·
                      refine ⟨1911319797579110788256543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096852793544295435350781 1911319797579110788256543)
                      ·
                        rfl

theorem cell23_3722282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3722282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722282 prefixEnd_3722282 := by exact prefixLift 3722282
  have htrace : WordTrace (prefixWord ++ tailWord_3722282) baseStart_3722282 baseEnd_3722282 := by
    simpa [prefixWord, tailWord_3722282, baseEnd_3722282] using wordTrace_append hprefix tailTrace_3722282
  have hstable : (prefixWord ++ tailWord_3722282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722282).length < 2 ^ (prefixWord ++ tailWord_3722282).sum := by decide
  have hdescent : baseEnd_3722282 < baseStart_3722282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722291 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_3722291 : Nat := 118140960795 + 3722291 * 2 ^ 59
def prefixEnd_3722291 : Nat := 4983230072969 + 3 ^ 40 * 3722291 * 2
def baseEnd_3722291 : Nat := 1911324418905001253044001

theorem tailTrace_3722291 : CollatzResearch.WordTrace tailWord_3722291 prefixEnd_3722291 1911324418905001253044001 := by
  unfold tailWord_3722291
  simp only [CollatzResearch.WordTrace]
  refine ⟨135763106157782898535918727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90508737438521932357279151 135763106157782898535918727)
  ·
    refine ⟨203644659236674347803878091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135763106157782898535918727 203644659236674347803878091)
    ·
      refine ⟨305466988855011521705817137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203644659236674347803878091 305466988855011521705817137)
      ·
        refine ⟨229100241641258641279362853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305466988855011521705817137 229100241641258641279362853)
        ·
          refine ⟨42956295307735995239880535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229100241641258641279362853 42956295307735995239880535)
          ·
            refine ⟨64434442961603992859820803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42956295307735995239880535 64434442961603992859820803)
            ·
              refine ⟨96651664442405989289731205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64434442961603992859820803 96651664442405989289731205)
              ·
                refine ⟨18122187082951122991824601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96651664442405989289731205 18122187082951122991824601)
                ·
                  refine ⟨13591640312213342243868451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18122187082951122991824601 13591640312213342243868451)
                  ·
                    refine ⟨20387460468320013365802677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13591640312213342243868451 20387460468320013365802677)
                    ·
                      refine ⟨1911324418905001253044001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20387460468320013365802677 1911324418905001253044001)
                      ·
                        rfl

theorem cell23_3722291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_3722291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722291 prefixEnd_3722291 := by exact prefixLift 3722291
  have htrace : WordTrace (prefixWord ++ tailWord_3722291) baseStart_3722291 baseEnd_3722291 := by
    simpa [prefixWord, tailWord_3722291, baseEnd_3722291] using wordTrace_append hprefix tailTrace_3722291
  have hstable : (prefixWord ++ tailWord_3722291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722291).length < 2 ^ (prefixWord ++ tailWord_3722291).sum := by decide
  have hdescent : baseEnd_3722291 < baseStart_3722291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722322 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_3722322 : Nat := 118140960795 + 3722322 * 2 ^ 59
def prefixEnd_3722322 : Nat := 4983230072969 + 3 ^ 40 * 3722322 * 2
def baseEnd_3722322 : Nat := 1911340336805290631756359

theorem tailTrace_3722322 : CollatzResearch.WordTrace tailWord_3722322 prefixEnd_3722322 1911340336805290631756359 := by
  unfold tailWord_3722322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33941059205167647707574305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90509491213780393886864813 33941059205167647707574305)
  ·
    refine ⟨25455794403875735780680729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33941059205167647707574305 25455794403875735780680729)
    ·
      refine ⟨19091845802906801835510547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25455794403875735780680729 19091845802906801835510547)
      ·
        refine ⟨28637768704360202753265821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19091845802906801835510547 28637768704360202753265821)
        ·
          refine ⟨10739163264135076032474683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28637768704360202753265821 10739163264135076032474683)
          ·
            refine ⟨16108744896202614048712025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10739163264135076032474683 16108744896202614048712025)
            ·
              refine ⟨12081558672151960536534019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16108744896202614048712025 12081558672151960536534019)
              ·
                refine ⟨18122338008227940804801029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12081558672151960536534019 18122338008227940804801029)
                ·
                  refine ⟨3397938376542738900900193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18122338008227940804801029 3397938376542738900900193)
                  ·
                    refine ⟨2548453782407054175675145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3397938376542738900900193 2548453782407054175675145)
                    ·
                      refine ⟨1911340336805290631756359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548453782407054175675145 1911340336805290631756359)
                      ·
                        rfl

theorem cell23_3722322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_3722322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722322 prefixEnd_3722322 := by exact prefixLift 3722322
  have htrace : WordTrace (prefixWord ++ tailWord_3722322) baseStart_3722322 baseEnd_3722322 := by
    simpa [prefixWord, tailWord_3722322, baseEnd_3722322] using wordTrace_append hprefix tailTrace_3722322
  have hstable : (prefixWord ++ tailWord_3722322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722322).length < 2 ^ (prefixWord ++ tailWord_3722322).sum := by decide
  have hdescent : baseEnd_3722322 < baseStart_3722322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722333 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3722333 : Nat := 118140960795 + 3722333 * 2 ^ 59
def prefixEnd_3722333 : Nat := 4983230072969 + 3 ^ 40 * 3722333 * 2
def baseEnd_3722333 : Nat := 1911345985092490088718809

theorem tailTrace_3722333 : CollatzResearch.WordTrace tailWord_3722333 prefixEnd_3722333 1911345985092490088718809 := by
  unfold tailWord_3722333
  simp only [CollatzResearch.WordTrace]
  refine ⟨135764638023630739708947653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90509758682420493139298435 135764638023630739708947653)
  ·
    refine ⟨25455869629430763695427685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135764638023630739708947653 25455869629430763695427685)
    ·
      refine ⟨4772975555518268192892691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25455869629430763695427685 4772975555518268192892691)
      ·
        refine ⟨7159463333277402289339037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4772975555518268192892691 7159463333277402289339037)
        ·
          refine ⟨2684798749979025858502139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7159463333277402289339037 2684798749979025858502139)
          ·
            refine ⟨4027198124968538787753209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684798749979025858502139 4027198124968538787753209)
            ·
              refine ⟨3020398593726404090814907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027198124968538787753209 3020398593726404090814907)
              ·
                refine ⟨4530597890589606136222361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020398593726404090814907 4530597890589606136222361)
                ·
                  refine ⟨3397948417942204602166771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4530597890589606136222361 3397948417942204602166771)
                  ·
                    refine ⟨5096922626913306903250157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3397948417942204602166771 5096922626913306903250157)
                    ·
                      refine ⟨1911345985092490088718809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5096922626913306903250157 1911345985092490088718809)
                      ·
                        rfl

theorem cell23_3722333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3722333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722333 prefixEnd_3722333 := by exact prefixLift 3722333
  have htrace : WordTrace (prefixWord ++ tailWord_3722333) baseStart_3722333 baseEnd_3722333 := by
    simpa [prefixWord, tailWord_3722333, baseEnd_3722333] using wordTrace_append hprefix tailTrace_3722333
  have hstable : (prefixWord ++ tailWord_3722333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722333).length < 2 ^ (prefixWord ++ tailWord_3722333).sum := by decide
  have hdescent : baseEnd_3722333 < baseStart_3722333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722351 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_3722351 : Nat := 118140960795 + 3722351 * 2 ^ 59
def prefixEnd_3722351 : Nat := 4983230072969 + 3 ^ 40 * 3722351 * 2
def baseEnd_3722351 : Nat := 1911355227744271018293725

theorem tailTrace_3722351 : CollatzResearch.WordTrace tailWord_3722351 prefixEnd_3722351 1911355227744271018293725 := by
  unfold tailWord_3722351
  simp only [CollatzResearch.WordTrace]
  refine ⟨135765294537565528783102907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90510196358377019188735271 135765294537565528783102907)
  ·
    refine ⟨203647941806348293174654361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135765294537565528783102907 203647941806348293174654361)
    ·
      refine ⟨152735956354761219880990771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203647941806348293174654361 152735956354761219880990771)
      ·
        refine ⟨229103934532141829821486157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152735956354761219880990771 229103934532141829821486157)
        ·
          refine ⟨85913975449553186183057309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229103934532141829821486157 85913975449553186183057309)
          ·
            refine ⟨32217740793582444818646491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85913975449553186183057309 32217740793582444818646491)
            ·
              refine ⟨48326611190373667227969737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32217740793582444818646491 48326611190373667227969737)
              ·
                refine ⟨36244958392780250420977303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48326611190373667227969737 36244958392780250420977303)
                ·
                  refine ⟨54367437589170375631465955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36244958392780250420977303 54367437589170375631465955)
                  ·
                    refine ⟨81551156383755563447198933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54367437589170375631465955 81551156383755563447198933)
                    ·
                      refine ⟨1911355227744271018293725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81551156383755563447198933 1911355227744271018293725)
                      ·
                        rfl

theorem cell23_3722351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_3722351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722351 prefixEnd_3722351 := by exact prefixLift 3722351
  have htrace : WordTrace (prefixWord ++ tailWord_3722351) baseStart_3722351 baseEnd_3722351 := by
    simpa [prefixWord, tailWord_3722351, baseEnd_3722351] using wordTrace_append hprefix tailTrace_3722351
  have hstable : (prefixWord ++ tailWord_3722351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722351).length < 2 ^ (prefixWord ++ tailWord_3722351).sum := by decide
  have hdescent : baseEnd_3722351 < baseStart_3722351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722405 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_3722405 : Nat := 118140960795 + 3722405 * 2 ^ 59
def prefixEnd_3722405 : Nat := 4983230072969 + 3 ^ 40 * 3722405 * 2
def baseEnd_3722405 : Nat := 637127651899871269006159

theorem tailTrace_3722405 : CollatzResearch.WordTrace tailWord_3722405 prefixEnd_3722405 637127651899871269006159 := by
  unfold tailWord_3722405
  simp only [CollatzResearch.WordTrace]
  refine ⟨135767264079369896005568669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90511509386246597337045779 135767264079369896005568669)
  ·
    refine ⟨50912724029763711002088251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135767264079369896005568669 50912724029763711002088251)
    ·
      refine ⟨76369086044645566503132377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50912724029763711002088251 76369086044645566503132377)
      ·
        refine ⟨57276814533484174877349283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76369086044645566503132377 57276814533484174877349283)
        ·
          refine ⟨85915221800226262316023925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57276814533484174877349283 85915221800226262316023925)
          ·
            refine ⟨8054552043771212092127243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85915221800226262316023925 8054552043771212092127243)
            ·
              refine ⟨12081828065656818138190865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054552043771212092127243 12081828065656818138190865)
              ·
                refine ⟨9061371049242613603643149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081828065656818138190865 9061371049242613603643149)
                ·
                  refine ⟨3398014143465980101366181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9061371049242613603643149 3398014143465980101366181)
                  ·
                    refine ⟨637127651899871269006159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398014143465980101366181 637127651899871269006159)
                    ·
                      rfl

theorem cell23_3722405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_3722405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722405 prefixEnd_3722405 := by exact prefixLift 3722405
  have htrace : WordTrace (prefixWord ++ tailWord_3722405) baseStart_3722405 baseEnd_3722405 := by
    simpa [prefixWord, tailWord_3722405, baseEnd_3722405] using wordTrace_append hprefix tailTrace_3722405
  have hstable : (prefixWord ++ tailWord_3722405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722405).length < 2 ^ (prefixWord ++ tailWord_3722405).sum := by decide
  have hdescent : baseEnd_3722405 < baseStart_3722405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722415 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_3722415 : Nat := 118140960795 + 3722415 * 2 ^ 59
def prefixEnd_3722415 : Nat := 4983230072969 + 3 ^ 40 * 3722415 * 2
def baseEnd_3722415 : Nat := 1911388090506158767893431

theorem tailTrace_3722415 : CollatzResearch.WordTrace tailWord_3722415 prefixEnd_3722415 1911388090506158767893431 := by
  unfold tailWord_3722415
  simp only [CollatzResearch.WordTrace]
  refine ⟨135767628809333667713432699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90511752539555778475621799 135767628809333667713432699)
  ·
    refine ⟨203651443214000501570149049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135767628809333667713432699 203651443214000501570149049)
    ·
      refine ⟨152738582410500376177611787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203651443214000501570149049 152738582410500376177611787)
      ·
        refine ⟨229107873615750564266417681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152738582410500376177611787 229107873615750564266417681)
        ·
          refine ⟨171830905211812923199813261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229107873615750564266417681 171830905211812923199813261)
          ·
            refine ⟨64436589454429846199929973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171830905211812923199813261 64436589454429846199929973)
            ·
              refine ⟨6040930261352798081243435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64436589454429846199929973 6040930261352798081243435)
              ·
                refine ⟨9061395392029197121865153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040930261352798081243435 9061395392029197121865153)
                ·
                  refine ⟨6796046544021897841398865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061395392029197121865153 6796046544021897841398865)
                  ·
                    refine ⟨5097034908016423381049149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6796046544021897841398865 5097034908016423381049149)
                    ·
                      refine ⟨1911388090506158767893431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5097034908016423381049149 1911388090506158767893431)
                      ·
                        rfl

theorem cell23_3722415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_3722415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722415 prefixEnd_3722415 := by exact prefixLift 3722415
  have htrace : WordTrace (prefixWord ++ tailWord_3722415) baseStart_3722415 baseEnd_3722415 := by
    simpa [prefixWord, tailWord_3722415, baseEnd_3722415] using wordTrace_append hprefix tailTrace_3722415
  have hstable : (prefixWord ++ tailWord_3722415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722415).length < 2 ^ (prefixWord ++ tailWord_3722415).sum := by decide
  have hdescent : baseEnd_3722415 < baseStart_3722415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722455 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_3722455 : Nat := 118140960795 + 3722455 * 2 ^ 59
def prefixEnd_3722455 : Nat := 4983230072969 + 3 ^ 40 * 3722455 * 2
def baseEnd_3722455 : Nat := 1911408629732338611393247

theorem tailTrace_3722455 : CollatzResearch.WordTrace tailWord_3722455 prefixEnd_3722455 1911408629732338611393247 := by
  unfold tailWord_3722455
  simp only [CollatzResearch.WordTrace]
  refine ⟨135769087729188754544888819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90512725152792503029925879 135769087729188754544888819)
  ·
    refine ⟨203653631593783131817333229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135769087729188754544888819 203653631593783131817333229)
    ·
      refine ⟨76370111847668674431499961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203653631593783131817333229 76370111847668674431499961)
      ·
        refine ⟨57277583885751505823624971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76370111847668674431499961 57277583885751505823624971)
        ·
          refine ⟨85916375828627258735437457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57277583885751505823624971 85916375828627258735437457)
          ·
            refine ⟨64437281871470444051578093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85916375828627258735437457 64437281871470444051578093)
            ·
              refine ⟨24163980701801416519341785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64437281871470444051578093 24163980701801416519341785)
              ·
                refine ⟨18122985526351062389506339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24163980701801416519341785 18122985526351062389506339)
                ·
                  refine ⟨27184478289526593584259509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18122985526351062389506339 27184478289526593584259509)
                  ·
                    refine ⟨2548544839643118148524329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27184478289526593584259509 2548544839643118148524329)
                    ·
                      refine ⟨1911408629732338611393247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548544839643118148524329 1911408629732338611393247)
                      ·
                        rfl

theorem cell23_3722455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_3722455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722455 prefixEnd_3722455 := by exact prefixLift 3722455
  have htrace : WordTrace (prefixWord ++ tailWord_3722455) baseStart_3722455 baseEnd_3722455 := by
    simpa [prefixWord, tailWord_3722455, baseEnd_3722455] using wordTrace_append hprefix tailTrace_3722455
  have hstable : (prefixWord ++ tailWord_3722455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722455).length < 2 ^ (prefixWord ++ tailWord_3722455).sum := by decide
  have hdescent : baseEnd_3722455 < baseStart_3722455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722465 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3722465 : Nat := 118140960795 + 3722465 * 2 ^ 59
def prefixEnd_3722465 : Nat := 4983230072969 + 3 ^ 40 * 3722465 * 2
def baseEnd_3722465 : Nat := 637137921512961190756067

theorem tailTrace_3722465 : CollatzResearch.WordTrace tailWord_3722465 prefixEnd_3722465 637137921512961190756067 := by
  unfold tailWord_3722465
  simp only [CollatzResearch.WordTrace]
  refine ⟨135769452459152526252752849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90512968306101684168501899 135769452459152526252752849)
  ·
    refine ⟨101827089344364394689564637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135769452459152526252752849 101827089344364394689564637)
    ·
      refine ⟨38185158504136648008586739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101827089344364394689564637 38185158504136648008586739)
      ·
        refine ⟨57277737756204972012880109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38185158504136648008586739 57277737756204972012880109)
        ·
          refine ⟨21479151658576864504830041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57277737756204972012880109 21479151658576864504830041)
          ·
            refine ⟨16109363743932648378622531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21479151658576864504830041 16109363743932648378622531)
            ·
              refine ⟨24164045615898972567933797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16109363743932648378622531 24164045615898972567933797)
              ·
                refine ⟨4530758552981057356487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24164045615898972567933797 4530758552981057356487587)
                ·
                  refine ⟨6796137829471586034731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530758552981057356487587 6796137829471586034731381)
                  ·
                    refine ⟨637137921512961190756067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6796137829471586034731381 637137921512961190756067)
                    ·
                      rfl

theorem cell23_3722465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3722465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722465 prefixEnd_3722465 := by exact prefixLift 3722465
  have htrace : WordTrace (prefixWord ++ tailWord_3722465) baseStart_3722465 baseEnd_3722465 := by
    simpa [prefixWord, tailWord_3722465, baseEnd_3722465] using wordTrace_append hprefix tailTrace_3722465
  have hstable : (prefixWord ++ tailWord_3722465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722465).length < 2 ^ (prefixWord ++ tailWord_3722465).sum := by decide
  have hdescent : baseEnd_3722465 < baseStart_3722465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722472 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3722472 : Nat := 118140960795 + 3722472 * 2 ^ 59
def prefixEnd_3722472 : Nat := 4983230072969 + 3 ^ 40 * 3722472 * 2
def baseEnd_3722472 : Nat := 1911417358903465044880669

theorem tailTrace_3722472 : CollatzResearch.WordTrace tailWord_3722472 prefixEnd_3722472 1911417358903465044880669 := by
  unfold tailWord_3722472
  simp only [CollatzResearch.WordTrace]
  refine ⟨67884853885063583224128835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90513138513418110965505113 67884853885063583224128835)
  ·
    refine ⟨101827280827595374836193253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67884853885063583224128835 101827280827595374836193253)
    ·
      refine ⟨19092615155174132781786235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101827280827595374836193253 19092615155174132781786235)
      ·
        refine ⟨28638922732761199172679353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19092615155174132781786235 28638922732761199172679353)
        ·
          refine ⟨21479192049570899379509515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28638922732761199172679353 21479192049570899379509515)
          ·
            refine ⟨32218788074356349069264273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21479192049570899379509515 32218788074356349069264273)
            ·
              refine ⟨24164091055767261801948205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32218788074356349069264273 24164091055767261801948205)
              ·
                refine ⟨9061534145912723175730577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24164091055767261801948205 9061534145912723175730577)
                ·
                  refine ⟨6796150609434542381797933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061534145912723175730577 6796150609434542381797933)
                  ·
                    refine ⟨2548556478537953393174225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6796150609434542381797933 2548556478537953393174225)
                    ·
                      refine ⟨1911417358903465044880669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548556478537953393174225 1911417358903465044880669)
                      ·
                        rfl

theorem cell23_3722472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3722472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722472 prefixEnd_3722472 := by exact prefixLift 3722472
  have htrace : WordTrace (prefixWord ++ tailWord_3722472) baseStart_3722472 baseEnd_3722472 := by
    simpa [prefixWord, tailWord_3722472, baseEnd_3722472] using wordTrace_append hprefix tailTrace_3722472
  have hstable : (prefixWord ++ tailWord_3722472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722472).length < 2 ^ (prefixWord ++ tailWord_3722472).sum := by decide
  have hdescent : baseEnd_3722472 < baseStart_3722472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722495 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 4, 4]
def baseStart_3722495 : Nat := 118140960795 + 3722495 * 2 ^ 59
def prefixEnd_3722495 : Nat := 4983230072969 + 3 ^ 40 * 3722495 * 2
def baseEnd_3722495 : Nat := 637143056319506151631021

theorem tailTrace_3722495 : CollatzResearch.WordTrace tailWord_3722495 prefixEnd_3722495 637143056319506151631021 := by
  unfold tailWord_3722495
  simp only [CollatzResearch.WordTrace]
  refine ⟨135770546649043841376344939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90513697766029227584229959 135770546649043841376344939)
  ·
    refine ⟨203655819973565762064517409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135770546649043841376344939 203655819973565762064517409)
    ·
      refine ⟨152741864980174321548388057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203655819973565762064517409 152741864980174321548388057)
      ·
        refine ⟨114556398735130741161291043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152741864980174321548388057 114556398735130741161291043)
        ·
          refine ⟨171834598102696111741936565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114556398735130741161291043 171834598102696111741936565)
          ·
            refine ⟨16109493572127760475806553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171834598102696111741936565 16109493572127760475806553)
            ·
              refine ⟨12082120179095820356854915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16109493572127760475806553 12082120179095820356854915)
              ·
                refine ⟨18123180268643730535282373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082120179095820356854915 18123180268643730535282373)
                ·
                  refine ⟨3398096300370699475365445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18123180268643730535282373 3398096300370699475365445)
                  ·
                    refine ⟨637143056319506151631021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398096300370699475365445 637143056319506151631021)
                    ·
                      rfl

theorem cell23_3722495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_3722495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722495 prefixEnd_3722495 := by exact prefixLift 3722495
  have htrace : WordTrace (prefixWord ++ tailWord_3722495) baseStart_3722495 baseEnd_3722495 := by
    simpa [prefixWord, tailWord_3722495, baseEnd_3722495] using wordTrace_append hprefix tailTrace_3722495
  have hstable : (prefixWord ++ tailWord_3722495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722495).length < 2 ^ (prefixWord ++ tailWord_3722495).sum := by decide
  have hdescent : baseEnd_3722495 < baseStart_3722495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722505 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_3722505 : Nat := 118140960795 + 3722505 * 2 ^ 59
def prefixEnd_3722505 : Nat := 4983230072969 + 3 ^ 40 * 3722505 * 2
def baseEnd_3722505 : Nat := 1911434303765063415768017

theorem tailTrace_3722505 : CollatzResearch.WordTrace tailWord_3722505 prefixEnd_3722505 1911434303765063415768017 := by
  unfold tailWord_3722505
  simp only [CollatzResearch.WordTrace]
  refine ⟨135770911379007613084208969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90513940919338408722805979 135770911379007613084208969)
  ·
    refine ⟨101828183534255709813156727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135770911379007613084208969 101828183534255709813156727)
    ·
      refine ⟨152742275301383564719735091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101828183534255709813156727 152742275301383564719735091)
      ·
        refine ⟨229113412952075347079602637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152742275301383564719735091 229113412952075347079602637)
        ·
          refine ⟨85917529857028255154850989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229113412952075347079602637 85917529857028255154850989)
          ·
            refine ⟨32219073696385595683069121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85917529857028255154850989 32219073696385595683069121)
            ·
              refine ⟨24164305272289196762301841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32219073696385595683069121 24164305272289196762301841)
              ·
                refine ⟨18123228954216897571726381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24164305272289196762301841 18123228954216897571726381)
                ·
                  refine ⟨6796210857831336589397393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18123228954216897571726381 6796210857831336589397393)
                  ·
                    refine ⟨5097158143373502442048045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6796210857831336589397393 5097158143373502442048045)
                    ·
                      refine ⟨1911434303765063415768017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5097158143373502442048045 1911434303765063415768017)
                      ·
                        rfl

theorem cell23_3722505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_3722505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722505 prefixEnd_3722505 := by exact prefixLift 3722505
  have htrace : WordTrace (prefixWord ++ tailWord_3722505) baseStart_3722505 baseEnd_3722505 := by
    simpa [prefixWord, tailWord_3722505, baseEnd_3722505] using wordTrace_append hprefix tailTrace_3722505
  have hstable : (prefixWord ++ tailWord_3722505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722505).length < 2 ^ (prefixWord ++ tailWord_3722505).sum := by decide
  have hdescent : baseEnd_3722505 < baseStart_3722505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722508 : List Nat := [2, 2, 1, 2, 2, 3, 1, 10]
def baseStart_3722508 : Nat := 118140960795 + 3722508 * 2 ^ 59
def prefixEnd_3722508 : Nat := 4983230072969 + 3 ^ 40 * 3722508 * 2
def baseEnd_3722508 : Nat := 70793920155815811260389

theorem tailTrace_3722508 : CollatzResearch.WordTrace tailWord_3722508 prefixEnd_3722508 70793920155815811260389 := by
  unfold tailWord_3722508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67885510398998372298284089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90514013865331163064378785 67885510398998372298284089)
  ·
    refine ⟨50914132799248779223713067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67885510398998372298284089 50914132799248779223713067)
    ·
      refine ⟨76371199198873168835569601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50914132799248779223713067 76371199198873168835569601)
      ·
        refine ⟨57278399399154876626677201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76371199198873168835569601 57278399399154876626677201)
        ·
          refine ⟨42958799549366157470007901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57278399399154876626677201 42958799549366157470007901)
          ·
            refine ⟨16109549831012309051252963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42958799549366157470007901 16109549831012309051252963)
            ·
              refine ⟨24164324746518463576879445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16109549831012309051252963 24164324746518463576879445)
              ·
                refine ⟨70793920155815811260389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24164324746518463576879445 70793920155815811260389)
                ·
                  rfl

theorem cell23_3722508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 10].length) (baseStart_3722508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722508 prefixEnd_3722508 := by exact prefixLift 3722508
  have htrace : WordTrace (prefixWord ++ tailWord_3722508) baseStart_3722508 baseEnd_3722508 := by
    simpa [prefixWord, tailWord_3722508, baseEnd_3722508] using wordTrace_append hprefix tailTrace_3722508
  have hstable : (prefixWord ++ tailWord_3722508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722508).length < 2 ^ (prefixWord ++ tailWord_3722508).sum := by decide
  have hdescent : baseEnd_3722508 < baseStart_3722508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722522 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_3722522 : Nat := 118140960795 + 3722522 * 2 ^ 59
def prefixEnd_3722522 : Nat := 4983230072969 + 3 ^ 40 * 3722522 * 2
def baseEnd_3722522 : Nat := 1911443032936189849255439

theorem tailTrace_3722522 : CollatzResearch.WordTrace tailWord_3722522 prefixEnd_3722522 1911443032936189849255439 := by
  unfold tailWord_3722522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33942882854986506246894455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90514354279964016658385213 33942882854986506246894455)
  ·
    refine ⟨50914324282479759370341683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33942882854986506246894455 50914324282479759370341683)
    ·
      refine ⟨76371486423719639055512525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50914324282479759370341683 76371486423719639055512525)
      ·
        refine ⟨28639307408894864645817197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76371486423719639055512525 28639307408894864645817197)
        ·
          refine ⟨10739740278335574242181449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28639307408894864645817197 10739740278335574242181449)
          ·
            refine ⟨8054805208751680681636087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10739740278335574242181449 8054805208751680681636087)
            ·
              refine ⟨12082207813127521022454131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054805208751680681636087 12082207813127521022454131)
              ·
                refine ⟨18123311719691281533681197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082207813127521022454131 18123311719691281533681197)
                ·
                  refine ⟨6796241894884230575130449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18123311719691281533681197 6796241894884230575130449)
                  ·
                    refine ⟨5097181421163172931347837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6796241894884230575130449 5097181421163172931347837)
                    ·
                      refine ⟨1911443032936189849255439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5097181421163172931347837 1911443032936189849255439)
                      ·
                        rfl

theorem cell23_3722522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_3722522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722522 prefixEnd_3722522 := by exact prefixLift 3722522
  have htrace : WordTrace (prefixWord ++ tailWord_3722522) baseStart_3722522 baseEnd_3722522 := by
    simpa [prefixWord, tailWord_3722522, baseEnd_3722522] using wordTrace_append hprefix tailTrace_3722522
  have hstable : (prefixWord ++ tailWord_3722522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722522).length < 2 ^ (prefixWord ++ tailWord_3722522).sum := by decide
  have hdescent : baseEnd_3722522 < baseStart_3722522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722525 : List Nat := [1, 4, 2, 3, 1, 1, 2, 9]
def baseStart_3722525 : Nat := 118140960795 + 3722525 * 2 ^ 59
def prefixEnd_3722525 : Nat := 4983230072969 + 3 ^ 40 * 3722525 * 2
def baseEnd_3722525 : Nat := 70794243458450123611775

theorem tailTrace_3722525 : CollatzResearch.WordTrace tailWord_3722525 prefixEnd_3722525 70794243458450123611775 := by
  unfold tailWord_3722525
  simp only [CollatzResearch.WordTrace]
  refine ⟨135771640838935156499937029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90514427225956770999958019 135771640838935156499937029)
  ·
    refine ⟨25457182657300341843738193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135771640838935156499937029 25457182657300341843738193)
    ·
      refine ⟨19092886992975256382803645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25457182657300341843738193 19092886992975256382803645)
      ·
        refine ⟨7159832622365721143551367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19092886992975256382803645 7159832622365721143551367)
        ·
          refine ⟨10739748933548581715327051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159832622365721143551367 10739748933548581715327051)
          ·
            refine ⟨16109623400322872572990577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10739748933548581715327051 16109623400322872572990577)
            ·
              refine ⟨12082217550242154429742933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16109623400322872572990577 12082217550242154429742933)
              ·
                refine ⟨70794243458450123611775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12082217550242154429742933 70794243458450123611775)
                ·
                  rfl

theorem cell23_3722525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 9].length) (baseStart_3722525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722525 prefixEnd_3722525 := by exact prefixLift 3722525
  have htrace : WordTrace (prefixWord ++ tailWord_3722525) baseStart_3722525 baseEnd_3722525 := by
    simpa [prefixWord, tailWord_3722525, baseEnd_3722525] using wordTrace_append hprefix tailTrace_3722525
  have hstable : (prefixWord ++ tailWord_3722525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722525).length < 2 ^ (prefixWord ++ tailWord_3722525).sum := by decide
  have hdescent : baseEnd_3722525 < baseStart_3722525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722553 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3722553 : Nat := 118140960795 + 3722553 * 2 ^ 59
def prefixEnd_3722553 : Nat := 4983230072969 + 3 ^ 40 * 3722553 * 2
def baseEnd_3722553 : Nat := 1911458950836479227967797

theorem tailTrace_3722553 : CollatzResearch.WordTrace tailWord_3722553 prefixEnd_3722553 1911458950836479227967797 := by
  unfold tailWord_3722553
  simp only [CollatzResearch.WordTrace]
  refine ⟨135772662082833717281956313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90515108055222478187970875 135772662082833717281956313)
  ·
    refine ⟨101829496562125287961467235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135772662082833717281956313 101829496562125287961467235)
    ·
      refine ⟨152744244843187931942200853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101829496562125287961467235 152744244843187931942200853)
      ·
        refine ⟨7159886477024434309790665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152744244843187931942200853 7159886477024434309790665)
        ·
          refine ⟨5369914857768325732342999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7159886477024434309790665 5369914857768325732342999)
          ·
            refine ⟨8054872286652488598514499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369914857768325732342999 8054872286652488598514499)
            ·
              refine ⟨12082308429978732897771749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054872286652488598514499 12082308429978732897771749)
              ·
                refine ⟨2265432830621012418332203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12082308429978732897771749 2265432830621012418332203)
                ·
                  refine ⟨3398149245931518627498305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265432830621012418332203 3398149245931518627498305)
                  ·
                    refine ⟨2548611934448638970623729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398149245931518627498305 2548611934448638970623729)
                    ·
                      refine ⟨1911458950836479227967797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548611934448638970623729 1911458950836479227967797)
                      ·
                        rfl

theorem cell23_3722553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3722553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722553 prefixEnd_3722553 := by exact prefixLift 3722553
  have htrace : WordTrace (prefixWord ++ tailWord_3722553) baseStart_3722553 baseEnd_3722553 := by
    simpa [prefixWord, tailWord_3722553, baseEnd_3722553] using wordTrace_append hprefix tailTrace_3722553
  have hstable : (prefixWord ++ tailWord_3722553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722553).length < 2 ^ (prefixWord ++ tailWord_3722553).sum := by decide
  have hdescent : baseEnd_3722553 < baseStart_3722553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722596 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_3722596 : Nat := 118140960795 + 3722596 * 2 ^ 59
def prefixEnd_3722596 : Nat := 4983230072969 + 3 ^ 40 * 3722596 * 2
def baseEnd_3722596 : Nat := 1911481030504622559730099

theorem tailTrace_3722596 : CollatzResearch.WordTrace tailWord_3722596 prefixEnd_3722596 1911481030504622559730099 := by
  unfold tailWord_3722596
  simp only [CollatzResearch.WordTrace]
  refine ⟨67887115210838967812885821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90516153614451957083847761 67887115210838967812885821)
  ·
    refine ⟨25457668204064612929832183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67887115210838967812885821 25457668204064612929832183)
    ·
      refine ⟨38186502306096919394748275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25457668204064612929832183 38186502306096919394748275)
      ·
        refine ⟨57279753459145379092122413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38186502306096919394748275 57279753459145379092122413)
        ·
          refine ⟨21479907547179517159545905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57279753459145379092122413 21479907547179517159545905)
          ·
            refine ⟨16109930660384637869659429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21479907547179517159545905 16109930660384637869659429)
            ·
              refine ⟨3020611998822119600561143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16109930660384637869659429 3020611998822119600561143)
              ·
                refine ⟨4530917998233179400841715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020611998822119600561143 4530917998233179400841715)
                ·
                  refine ⟨6796376997349769101262573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530917998233179400841715 6796376997349769101262573)
                  ·
                    refine ⟨2548641374006163412973465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6796376997349769101262573 2548641374006163412973465)
                    ·
                      refine ⟨1911481030504622559730099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548641374006163412973465 1911481030504622559730099)
                      ·
                        rfl

theorem cell23_3722596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_3722596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722596 prefixEnd_3722596 := by exact prefixLift 3722596
  have htrace : WordTrace (prefixWord ++ tailWord_3722596) baseStart_3722596 baseEnd_3722596 := by
    simpa [prefixWord, tailWord_3722596, baseEnd_3722596] using wordTrace_append hprefix tailTrace_3722596
  have hstable : (prefixWord ++ tailWord_3722596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722596).length < 2 ^ (prefixWord ++ tailWord_3722596).sum := by decide
  have hdescent : baseEnd_3722596 < baseStart_3722596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722615 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 7]
def baseStart_3722615 : Nat := 118140960795 + 3722615 * 2 ^ 59
def prefixEnd_3722615 : Nat := 4983230072969 + 3 ^ 40 * 3722615 * 2
def baseEnd_3722615 : Nat := 212387865181895331710279

theorem tailTrace_3722615 : CollatzResearch.WordTrace tailWord_3722615 prefixEnd_3722615 212387865181895331710279 := by
  unfold tailWord_3722615
  simp only [CollatzResearch.WordTrace]
  refine ⟨135774923408609101870713299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90516615605739401247142199 135774923408609101870713299)
  ·
    refine ⟨203662385112913652806069949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135774923408609101870713299 203662385112913652806069949)
    ·
      refine ⟨76373394417342619802276231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203662385112913652806069949 76373394417342619802276231)
      ·
        refine ⟨114560091626013929703414347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76373394417342619802276231 114560091626013929703414347)
        ·
          refine ⟨171840137439020894555121521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114560091626013929703414347 171840137439020894555121521)
          ·
            refine ⟨128880103079265670916341141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171840137439020894555121521 128880103079265670916341141)
            ·
              refine ⟨6041254831840578324203491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128880103079265670916341141 6041254831840578324203491)
              ·
                refine ⟨9061882247760867486305237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041254831840578324203491 9061882247760867486305237)
                ·
                  refine ⟨212387865181895331710279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9061882247760867486305237 212387865181895331710279)
                  ·
                    rfl

theorem cell23_3722615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 7].length) (baseStart_3722615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722615 prefixEnd_3722615 := by exact prefixLift 3722615
  have htrace : WordTrace (prefixWord ++ tailWord_3722615) baseStart_3722615 baseEnd_3722615 := by
    simpa [prefixWord, tailWord_3722615, baseEnd_3722615] using wordTrace_append hprefix tailTrace_3722615
  have hstable : (prefixWord ++ tailWord_3722615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722615).length < 2 ^ (prefixWord ++ tailWord_3722615).sum := by decide
  have hdescent : baseEnd_3722615 < baseStart_3722615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722645 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3722645 : Nat := 118140960795 + 3722645 * 2 ^ 59
def prefixEnd_3722645 : Nat := 4983230072969 + 3 ^ 40 * 3722645 * 2
def baseEnd_3722645 : Nat := 637168730352230956005791

theorem tailTrace_3722645 : CollatzResearch.WordTrace tailWord_3722645 prefixEnd_3722645 637168730352230956005791 := by
  unfold tailWord_3722645
  simp only [CollatzResearch.WordTrace]
  refine ⟨135776017598500416994305389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90517345065666944662870259 135776017598500416994305389)
  ·
    refine ⟨50916006599437656372864521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135776017598500416994305389 50916006599437656372864521)
    ·
      refine ⟨38187004949578242279648391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50916006599437656372864521 38187004949578242279648391)
      ·
        refine ⟨57280507424367363419472587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38187004949578242279648391 57280507424367363419472587)
        ·
          refine ⟨85920761136551045129208881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57280507424367363419472587 85920761136551045129208881)
          ·
            refine ⟨64440570852413283846906661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85920761136551045129208881 64440570852413283846906661)
            ·
              refine ⟨12082607034827490721294999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64440570852413283846906661 12082607034827490721294999)
              ·
                refine ⟨18123910552241236081942499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082607034827490721294999 18123910552241236081942499)
                ·
                  refine ⟨27185865828361854122913749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18123910552241236081942499 27185865828361854122913749)
                  ·
                    refine ⟨637168730352230956005791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27185865828361854122913749 637168730352230956005791)
                    ·
                      rfl

theorem cell23_3722645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3722645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722645 prefixEnd_3722645 := by exact prefixLift 3722645
  have htrace : WordTrace (prefixWord ++ tailWord_3722645) baseStart_3722645 baseEnd_3722645 := by
    simpa [prefixWord, tailWord_3722645, baseEnd_3722645] using wordTrace_append hprefix tailTrace_3722645
  have hstable : (prefixWord ++ tailWord_3722645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722645).length < 2 ^ (prefixWord ++ tailWord_3722645).sum := by decide
  have hdescent : baseEnd_3722645 < baseStart_3722645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722649 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 5]
def baseStart_3722649 : Nat := 118140960795 + 3722649 * 2 ^ 59
def prefixEnd_3722649 : Nat := 4983230072969 + 3 ^ 40 * 3722649 * 2
def baseEnd_3722649 : Nat := 212389804997701205818595

theorem tailTrace_3722649 : CollatzResearch.WordTrace tailWord_3722649 prefixEnd_3722649 212389804997701205818595 := by
  unfold tailWord_3722649
  simp only [CollatzResearch.WordTrace]
  refine ⟨135776163490485925677451001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90517442326990617118300667 135776163490485925677451001)
  ·
    refine ⟨101832122617864444258088251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135776163490485925677451001 101832122617864444258088251)
    ·
      refine ⟨152748183926796666387132377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101832122617864444258088251 152748183926796666387132377)
      ·
        refine ⟨114561137945097499790349283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152748183926796666387132377 114561137945097499790349283)
        ·
          refine ⟨171841706917646249685523925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114561137945097499790349283 171841706917646249685523925)
          ·
            refine ⟨4027540005882333977004467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 171841706917646249685523925 4027540005882333977004467)
            ·
              refine ⟨6041310008823500965506701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027540005882333977004467 6041310008823500965506701)
              ·
                refine ⟨2265491253308812862065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6041310008823500965506701 2265491253308812862065013)
                ·
                  refine ⟨212389804997701205818595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2265491253308812862065013 212389804997701205818595)
                  ·
                    rfl

theorem cell23_3722649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 5].length) (baseStart_3722649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722649 prefixEnd_3722649 := by exact prefixLift 3722649
  have htrace : WordTrace (prefixWord ++ tailWord_3722649) baseStart_3722649 baseEnd_3722649 := by
    simpa [prefixWord, tailWord_3722649, baseEnd_3722649] using wordTrace_append hprefix tailTrace_3722649
  have hstable : (prefixWord ++ tailWord_3722649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722649).length < 2 ^ (prefixWord ++ tailWord_3722649).sum := by decide
  have hdescent : baseEnd_3722649 < baseStart_3722649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722702 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3722702 : Nat := 118140960795 + 3722702 * 2 ^ 59
def prefixEnd_3722702 : Nat := 4983230072969 + 3 ^ 40 * 3722702 * 2
def baseEnd_3722702 : Nat := 1911535459453999145004611

theorem tailTrace_3722702 : CollatzResearch.WordTrace tailWord_3722702 prefixEnd_3722702 1911535459453999145004611 := by
  unfold tailWord_3722702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16972262069911739466141295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90518731039529277152753573 16972262069911739466141295)
  ·
    refine ⟨25458393104867609199211943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16972262069911739466141295 25458393104867609199211943)
    ·
      refine ⟨38187589657301413798817915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25458393104867609199211943 38187589657301413798817915)
      ·
        refine ⟨57281384485952120698226873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38187589657301413798817915 57281384485952120698226873)
        ·
          refine ⟨42961038364464090523670155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57281384485952120698226873 42961038364464090523670155)
          ·
            refine ⟨64441557546696135785505233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42961038364464090523670155 64441557546696135785505233)
            ·
              refine ⟨48331168160022101839128925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64441557546696135785505233 48331168160022101839128925)
              ·
                refine ⟨18124188060008288189673347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48331168160022101839128925 18124188060008288189673347)
                ·
                  refine ⟨27186282090012432284510021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18124188060008288189673347 27186282090012432284510021)
                  ·
                    refine ⟨5097427891877331053345629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27186282090012432284510021 5097427891877331053345629)
                    ·
                      refine ⟨1911535459453999145004611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5097427891877331053345629 1911535459453999145004611)
                      ·
                        rfl

theorem cell23_3722702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3722702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722702 prefixEnd_3722702 := by exact prefixLift 3722702
  have htrace : WordTrace (prefixWord ++ tailWord_3722702) baseStart_3722702 baseEnd_3722702 := by
    simpa [prefixWord, tailWord_3722702, baseEnd_3722702] using wordTrace_append hprefix tailTrace_3722702
  have hstable : (prefixWord ++ tailWord_3722702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722702).length < 2 ^ (prefixWord ++ tailWord_3722702).sum := by decide
  have hdescent : baseEnd_3722702 < baseStart_3722702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722745 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3722745 : Nat := 118140960795 + 3722745 * 2 ^ 59
def prefixEnd_3722745 : Nat := 4983230072969 + 3 ^ 40 * 3722745 * 2
def baseEnd_3722745 : Nat := 1911557539122142476766913

theorem tailTrace_3722745 : CollatzResearch.WordTrace tailWord_3722745 prefixEnd_3722745 1911557539122142476766913 := by
  unfold tailWord_3722745
  simp only [CollatzResearch.WordTrace]
  refine ⟨135779664898138134072945689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90519776598758756048630459 135779664898138134072945689)
  ·
    refine ⟨101834748673603600554709267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135779664898138134072945689 101834748673603600554709267)
    ·
      refine ⟨152752123010405400832063901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101834748673603600554709267 152752123010405400832063901)
      ·
        refine ⟨57282046128902025312023963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152752123010405400832063901 57282046128902025312023963)
        ·
          refine ⟨85923069193353037968035945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57282046128902025312023963 85923069193353037968035945)
          ·
            refine ⟨64442301895014778476026959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85923069193353037968035945 64442301895014778476026959)
            ·
              refine ⟨96663452842522167714040439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64442301895014778476026959 96663452842522167714040439)
              ·
                refine ⟨144995179263783251571060659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96663452842522167714040439 144995179263783251571060659)
                ·
                  refine ⟨217492768895674877356590989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144995179263783251571060659 217492768895674877356590989)
                  ·
                    refine ⟨81559788335878079008721621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217492768895674877356590989 81559788335878079008721621)
                    ·
                      refine ⟨1911557539122142476766913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81559788335878079008721621 1911557539122142476766913)
                      ·
                        rfl

theorem cell23_3722745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3722745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722745 prefixEnd_3722745 := by exact prefixLift 3722745
  have htrace : WordTrace (prefixWord ++ tailWord_3722745) baseStart_3722745 baseEnd_3722745 := by
    simpa [prefixWord, tailWord_3722745, baseEnd_3722745] using wordTrace_append hprefix tailTrace_3722745
  have hstable : (prefixWord ++ tailWord_3722745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722745).length < 2 ^ (prefixWord ++ tailWord_3722745).sum := by decide
  have hdescent : baseEnd_3722745 < baseStart_3722745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722749 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_3722749 : Nat := 118140960795 + 3722749 * 2 ^ 59
def prefixEnd_3722749 : Nat := 4983230072969 + 3 ^ 40 * 3722749 * 2
def baseEnd_3722749 : Nat := 1911559593044760461116895

theorem tailTrace_3722749 : CollatzResearch.WordTrace tailWord_3722749 prefixEnd_3722749 1911559593044760461116895 := by
  unfold tailWord_3722749
  simp only [CollatzResearch.WordTrace]
  refine ⟨135779810790123642756091301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90519873860082428504060867 135779810790123642756091301)
  ·
    refine ⟨25458714523148183016767119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135779810790123642756091301 25458714523148183016767119)
    ·
      refine ⟨38188071784722274525150679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25458714523148183016767119 38188071784722274525150679)
      ·
        refine ⟨57282107677083411787726019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38188071784722274525150679 57282107677083411787726019)
        ·
          refine ⟨85923161515625117681589029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57282107677083411787726019 85923161515625117681589029)
          ·
            refine ⟨16110592784179709565297943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85923161515625117681589029 16110592784179709565297943)
            ·
              refine ⟨24165889176269564347946915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16110592784179709565297943 24165889176269564347946915)
              ·
                refine ⟨36248833764404346521920373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24165889176269564347946915 36248833764404346521920373)
                ·
                  refine ⟨3398328165412907486430035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36248833764404346521920373 3398328165412907486430035)
                  ·
                    refine ⟨5097492248119361229645053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3398328165412907486430035 5097492248119361229645053)
                    ·
                      refine ⟨1911559593044760461116895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5097492248119361229645053 1911559593044760461116895)
                      ·
                        rfl

theorem cell23_3722749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_3722749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722749 prefixEnd_3722749 := by exact prefixLift 3722749
  have htrace : WordTrace (prefixWord ++ tailWord_3722749) baseStart_3722749 baseEnd_3722749 := by
    simpa [prefixWord, tailWord_3722749, baseEnd_3722749] using wordTrace_append hprefix tailTrace_3722749
  have hstable : (prefixWord ++ tailWord_3722749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722749).length < 2 ^ (prefixWord ++ tailWord_3722749).sum := by decide
  have hdescent : baseEnd_3722749 < baseStart_3722749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722750 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3722750 : Nat := 118140960795 + 3722750 * 2 ^ 59
def prefixEnd_3722750 : Nat := 4983230072969 + 3 ^ 40 * 3722750 * 2
def baseEnd_3722750 : Nat := 1911560106525414957204391

theorem tailTrace_3722750 : CollatzResearch.WordTrace tailWord_3722750 prefixEnd_3722750 1911560106525414957204391 := by
  unfold tailWord_3722750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16972480907890002490859713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90519898175413346617918469 16972480907890002490859713)
  ·
    refine ⟨12729360680917501868144785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16972480907890002490859713 12729360680917501868144785)
    ·
      refine ⟨9547020510688126401108589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12729360680917501868144785 9547020510688126401108589)
      ·
        refine ⟨3580132691508047400415721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9547020510688126401108589 3580132691508047400415721)
        ·
          refine ⟨2685099518631035550311791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580132691508047400415721 2685099518631035550311791)
          ·
            refine ⟨4027649277946553325467687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685099518631035550311791 4027649277946553325467687)
            ·
              refine ⟨6041473916919829988201531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027649277946553325467687 6041473916919829988201531)
              ·
                refine ⟨9062210875379744982302297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041473916919829988201531 9062210875379744982302297)
                ·
                  refine ⟨6796658156534808736726723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062210875379744982302297 6796658156534808736726723)
                  ·
                    refine ⟨10194987234802213105090085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6796658156534808736726723 10194987234802213105090085)
                    ·
                      refine ⟨1911560106525414957204391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10194987234802213105090085 1911560106525414957204391)
                      ·
                        rfl

theorem cell23_3722750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3722750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722750 prefixEnd_3722750 := by exact prefixLift 3722750
  have htrace : WordTrace (prefixWord ++ tailWord_3722750) baseStart_3722750 baseEnd_3722750 := by
    simpa [prefixWord, tailWord_3722750, baseEnd_3722750] using wordTrace_append hprefix tailTrace_3722750
  have hstable : (prefixWord ++ tailWord_3722750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722750).length < 2 ^ (prefixWord ++ tailWord_3722750).sum := by decide
  have hdescent : baseEnd_3722750 < baseStart_3722750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722753 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_3722753 : Nat := 118140960795 + 3722753 * 2 ^ 59
def prefixEnd_3722753 : Nat := 4983230072969 + 3 ^ 40 * 3722753 * 2
def baseEnd_3722753 : Nat := 1911561646967378445466877

theorem tailTrace_3722753 : CollatzResearch.WordTrace tailWord_3722753 prefixEnd_3722753 1911561646967378445466877 := by
  unfold tailWord_3722753
  simp only [CollatzResearch.WordTrace]
  refine ⟨135779956682109151439236913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90519971121406100959491275 135779956682109151439236913)
  ·
    refine ⟨101834967511581863579427685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135779956682109151439236913 101834967511581863579427685)
    ·
      refine ⟨19094056408421599421142691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101834967511581863579427685 19094056408421599421142691)
      ·
        refine ⟨28641084612632399131714037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19094056408421599421142691 28641084612632399131714037)
        ·
          refine ⟨2685101682434287418598191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28641084612632399131714037 2685101682434287418598191)
          ·
            refine ⟨4027652523651431127897287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685101682434287418598191 4027652523651431127897287)
            ·
              refine ⟨6041478785477146691845931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027652523651431127897287 6041478785477146691845931)
              ·
                refine ⟨9062218178215720037768897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041478785477146691845931 9062218178215720037768897)
                ·
                  refine ⟨6796663633661790028326673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062218178215720037768897 6796663633661790028326673)
                  ·
                    refine ⟨5097497725246342521245005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6796663633661790028326673 5097497725246342521245005)
                    ·
                      refine ⟨1911561646967378445466877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5097497725246342521245005 1911561646967378445466877)
                      ·
                        rfl

theorem cell23_3722753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_3722753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722753 prefixEnd_3722753 := by exact prefixLift 3722753
  have htrace : WordTrace (prefixWord ++ tailWord_3722753) baseStart_3722753 baseEnd_3722753 := by
    simpa [prefixWord, tailWord_3722753, baseEnd_3722753] using wordTrace_append hprefix tailTrace_3722753
  have hstable : (prefixWord ++ tailWord_3722753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722753).length < 2 ^ (prefixWord ++ tailWord_3722753).sum := by decide
  have hdescent : baseEnd_3722753 < baseStart_3722753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722896 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2]
def baseStart_3722896 : Nat := 118140960795 + 3722896 * 2 ^ 59
def prefixEnd_3722896 : Nat := 4983230072969 + 3 ^ 40 * 3722896 * 2
def baseEnd_3722896 : Nat := 1911635074700971385978719

theorem tailTrace_3722896 : CollatzResearch.WordTrace tailWord_3722896 prefixEnd_3722896 1911635074700971385978719 := by
  unfold tailWord_3722896
  simp only [CollatzResearch.WordTrace]
  refine ⟨67892586160295543430846271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90523448213727391241128361 67892586160295543430846271)
  ·
    refine ⟨101838879240443315146269407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67892586160295543430846271 101838879240443315146269407)
    ·
      refine ⟨152758318860664972719404111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101838879240443315146269407 152758318860664972719404111)
      ·
        refine ⟨229137478290997459079106167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152758318860664972719404111 229137478290997459079106167)
        ·
          refine ⟨343706217436496188618659251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229137478290997459079106167 343706217436496188618659251)
          ·
            refine ⟨515559326154744282927988877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343706217436496188618659251 515559326154744282927988877)
            ·
              refine ⟨193334747308029106097995829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515559326154744282927988877 193334747308029106097995829)
              ·
                refine ⟨18125132560127728696687109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193334747308029106097995829 18125132560127728696687109)
                ·
                  refine ⟨3398462355023949130628833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18125132560127728696687109 3398462355023949130628833)
                  ·
                    refine ⟨2548846766267961847971625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398462355023949130628833 2548846766267961847971625)
                    ·
                      refine ⟨1911635074700971385978719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548846766267961847971625 1911635074700971385978719)
                      ·
                        rfl

theorem cell23_3722896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2].length) (baseStart_3722896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722896 prefixEnd_3722896 := by exact prefixLift 3722896
  have htrace : WordTrace (prefixWord ++ tailWord_3722896) baseStart_3722896 baseEnd_3722896 := by
    simpa [prefixWord, tailWord_3722896, baseEnd_3722896] using wordTrace_append hprefix tailTrace_3722896
  have hstable : (prefixWord ++ tailWord_3722896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722896).length < 2 ^ (prefixWord ++ tailWord_3722896).sum := by decide
  have hdescent : baseEnd_3722896 < baseStart_3722896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722913 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3722913 : Nat := 118140960795 + 3722913 * 2 ^ 59
def prefixEnd_3722913 : Nat := 4983230072969 + 3 ^ 40 * 3722913 * 2
def baseEnd_3722913 : Nat := 1911643803872097819466141

theorem tailTrace_3722913 : CollatzResearch.WordTrace tailWord_3722913 prefixEnd_3722913 1911643803872097819466141 := by
  unfold tailWord_3722913
  simp only [CollatzResearch.WordTrace]
  refine ⟨135785792361529498765061393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90523861574352999176707595 135785792361529498765061393)
  ·
    refine ⟨101839344271147124073796045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135785792361529498765061393 101839344271147124073796045)
    ·
      refine ⟨38189754101680171527673517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101839344271147124073796045 38189754101680171527673517)
      ·
        refine ⟨14321157788130064322877569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38189754101680171527673517 14321157788130064322877569)
        ·
          refine ⟨10740868341097548242158177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14321157788130064322877569 10740868341097548242158177)
          ·
            refine ⟨8055651255823161181618633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10740868341097548242158177 8055651255823161181618633)
            ·
              refine ⟨6041738441867370886213975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8055651255823161181618633 6041738441867370886213975)
              ·
                refine ⟨9062607662801056329320963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041738441867370886213975 9062607662801056329320963)
                ·
                  refine ⟨13593911494201584493981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9062607662801056329320963 13593911494201584493981445)
                  ·
                    refine ⟨2548858405162797092621521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13593911494201584493981445 2548858405162797092621521)
                    ·
                      refine ⟨1911643803872097819466141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548858405162797092621521 1911643803872097819466141)
                      ·
                        rfl

theorem cell23_3722913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3722913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722913 prefixEnd_3722913 := by exact prefixLift 3722913
  have htrace : WordTrace (prefixWord ++ tailWord_3722913) baseStart_3722913 baseEnd_3722913 := by
    simpa [prefixWord, tailWord_3722913, baseEnd_3722913] using wordTrace_append hprefix tailTrace_3722913
  have hstable : (prefixWord ++ tailWord_3722913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722913).length < 2 ^ (prefixWord ++ tailWord_3722913).sum := by decide
  have hdescent : baseEnd_3722913 < baseStart_3722913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722934 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3722934 : Nat := 118140960795 + 3722934 * 2 ^ 59
def prefixEnd_3722934 : Nat := 4983230072969 + 3 ^ 40 * 3722934 * 2
def baseEnd_3722934 : Nat := 1911654586965842237303545

theorem tailTrace_3722934 : CollatzResearch.WordTrace tailWord_3722934 prefixEnd_3722934 1911654586965842237303545 := by
  unfold tailWord_3722934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486659893403338709473491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90524372196302279567717237 8486659893403338709473491)
  ·
    refine ⟨12729989840105008064210237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8486659893403338709473491 12729989840105008064210237)
    ·
      refine ⟨4773746190039378024078839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12729989840105008064210237 4773746190039378024078839)
      ·
        refine ⟨7160619285059067036118259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773746190039378024078839 7160619285059067036118259)
        ·
          refine ⟨10740928927588600554177389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7160619285059067036118259 10740928927588600554177389)
          ·
            refine ⟨4027848347845725207816521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10740928927588600554177389 4027848347845725207816521)
            ·
              refine ⟨3020886260884293905862391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027848347845725207816521 3020886260884293905862391)
              ·
                refine ⟨4531329391326440858793587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020886260884293905862391 4531329391326440858793587)
                ·
                  refine ⟨6796994086989661288190381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531329391326440858793587 6796994086989661288190381)
                  ·
                    refine ⟨2548872782621122983071393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6796994086989661288190381 2548872782621122983071393)
                    ·
                      refine ⟨1911654586965842237303545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548872782621122983071393 1911654586965842237303545)
                      ·
                        rfl

theorem cell23_3722934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3722934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722934 prefixEnd_3722934 := by exact prefixLift 3722934
  have htrace : WordTrace (prefixWord ++ tailWord_3722934) baseStart_3722934 baseEnd_3722934 := by
    simpa [prefixWord, tailWord_3722934, baseEnd_3722934] using wordTrace_append hprefix tailTrace_3722934
  have hstable : (prefixWord ++ tailWord_3722934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722934).length < 2 ^ (prefixWord ++ tailWord_3722934).sum := by decide
  have hdescent : baseEnd_3722934 < baseStart_3722934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722969 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3722969 : Nat := 118140960795 + 3722969 * 2 ^ 59
def prefixEnd_3722969 : Nat := 4983230072969 + 3 ^ 40 * 3722969 * 2
def baseEnd_3722969 : Nat := 1911672558788749600365883

theorem tailTrace_3722969 : CollatzResearch.WordTrace tailWord_3722969 prefixEnd_3722969 1911672558788749600365883 := by
  unfold tailWord_3722969
  simp only [CollatzResearch.WordTrace]
  refine ⟨135787834849326620329099961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90525223232884413552733307 135787834849326620329099961)
  ·
    refine ⟨101840876136994965246824971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135787834849326620329099961 101840876136994965246824971)
    ·
      refine ⟨152761314205492447870237457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101840876136994965246824971 152761314205492447870237457)
      ·
        refine ⟨114570985654119335902678093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152761314205492447870237457 114570985654119335902678093)
        ·
          refine ⟨42964119620294750963504285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114570985654119335902678093 42964119620294750963504285)
          ·
            refine ⟨16111544857610531611314107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42964119620294750963504285 16111544857610531611314107)
            ·
              refine ⟨24167317286415797416971161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16111544857610531611314107 24167317286415797416971161)
              ·
                refine ⟨18125487964811848062728371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24167317286415797416971161 18125487964811848062728371)
                ·
                  refine ⟨27188231947217772094092557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18125487964811848062728371 27188231947217772094092557)
                  ·
                    refine ⟨10195586980206664535284709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27188231947217772094092557 10195586980206664535284709)
                    ·
                      refine ⟨1911672558788749600365883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10195586980206664535284709 1911672558788749600365883)
                      ·
                        rfl

theorem cell23_3722969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3722969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722969 prefixEnd_3722969 := by exact prefixLift 3722969
  have htrace : WordTrace (prefixWord ++ tailWord_3722969) baseStart_3722969 baseEnd_3722969 := by
    simpa [prefixWord, tailWord_3722969, baseEnd_3722969] using wordTrace_append hprefix tailTrace_3722969
  have hstable : (prefixWord ++ tailWord_3722969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722969).length < 2 ^ (prefixWord ++ tailWord_3722969).sum := by decide
  have hdescent : baseEnd_3722969 < baseStart_3722969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722986 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_3722986 : Nat := 118140960795 + 3722986 * 2 ^ 59
def prefixEnd_3722986 : Nat := 4983230072969 + 3 ^ 40 * 3722986 * 2
def baseEnd_3722986 : Nat := 1911681287959876033853305

theorem tailTrace_3722986 : CollatzResearch.WordTrace tailWord_3722986 prefixEnd_3722986 1911681287959876033853305 := by
  unfold tailWord_3722986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33947113722566258058117203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90525636593510021488312541 33947113722566258058117203)
  ·
    refine ⟨50920670583849387087175805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33947113722566258058117203 50920670583849387087175805)
    ·
      refine ⟨19095251468943520157690927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50920670583849387087175805 19095251468943520157690927)
      ·
        refine ⟨28642877203415280236536391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19095251468943520157690927 28642877203415280236536391)
        ·
          refine ⟨42964315805122920354804587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28642877203415280236536391 42964315805122920354804587)
          ·
            refine ⟨64446473707684380532206881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42964315805122920354804587 64446473707684380532206881)
            ·
              refine ⟨48334855280763285399155161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64446473707684380532206881 48334855280763285399155161)
              ·
                refine ⟨36251141460572464049366371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48334855280763285399155161 36251141460572464049366371)
                ·
                  refine ⟨54376712190858696074049557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36251141460572464049366371 54376712190858696074049557)
                  ·
                    refine ⟨2548908383946501378471073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54376712190858696074049557 2548908383946501378471073)
                    ·
                      refine ⟨1911681287959876033853305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2548908383946501378471073 1911681287959876033853305)
                      ·
                        rfl

theorem cell23_3722986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_3722986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3722986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3722986 prefixEnd_3722986 := by exact prefixLift 3722986
  have htrace : WordTrace (prefixWord ++ tailWord_3722986) baseStart_3722986 baseEnd_3722986 := by
    simpa [prefixWord, tailWord_3722986, baseEnd_3722986] using wordTrace_append hprefix tailTrace_3722986
  have hstable : (prefixWord ++ tailWord_3722986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722986).length < 2 ^ (prefixWord ++ tailWord_3722986).sum := by decide
  have hdescent : baseEnd_3722986 < baseStart_3722986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723009 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 8]
def baseStart_3723009 : Nat := 118140960795 + 3723009 * 2 ^ 59
def prefixEnd_3723009 : Nat := 4983230072969 + 3 ^ 40 * 3723009 * 2
def baseEnd_3723009 : Nat := 212410344223881049318411

theorem tailTrace_3723009 : CollatzResearch.WordTrace tailWord_3723009 prefixEnd_3723009 212410344223881049318411 := by
  unfold tailWord_3723009
  simp only [CollatzResearch.WordTrace]
  refine ⟨135789293769181707160556081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90526195846121138107037387 135789293769181707160556081)
  ·
    refine ⟨101841970326886280370417061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135789293769181707160556081 101841970326886280370417061)
    ·
      refine ⟨19095369436291177569453199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101841970326886280370417061 19095369436291177569453199)
      ·
        refine ⟨28643054154436766354179799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19095369436291177569453199 28643054154436766354179799)
        ·
          refine ⟨42964581231655149531269699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28643054154436766354179799 42964581231655149531269699)
          ·
            refine ⟨64446871847482724296904549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42964581231655149531269699 64446871847482724296904549)
            ·
              refine ⟨12083788471403010805669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64446871847482724296904549 12083788471403010805669603)
              ·
                refine ⟨18125682707104516208504405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12083788471403010805669603 18125682707104516208504405)
                ·
                  refine ⟨212410344223881049318411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18125682707104516208504405 212410344223881049318411)
                  ·
                    rfl

theorem cell23_3723009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_3723009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723009 prefixEnd_3723009 := by exact prefixLift 3723009
  have htrace : WordTrace (prefixWord ++ tailWord_3723009) baseStart_3723009 baseEnd_3723009 := by
    simpa [prefixWord, tailWord_3723009, baseEnd_3723009] using wordTrace_append hprefix tailTrace_3723009
  have hstable : (prefixWord ++ tailWord_3723009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723009).length < 2 ^ (prefixWord ++ tailWord_3723009).sum := by decide
  have hdescent : baseEnd_3723009 < baseStart_3723009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723086 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_3723086 : Nat := 118140960795 + 3723086 * 2 ^ 59
def prefixEnd_3723086 : Nat := 4983230072969 + 3 ^ 40 * 3723086 * 2
def baseEnd_3723086 : Nat := 637244212008441880867615

theorem tailTrace_3723086 : CollatzResearch.WordTrace tailWord_3723086 prefixEnd_3723086 637244212008441880867615 := by
  unfold tailWord_3723086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16974012773737843663888639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90528068126601832874072741 16974012773737843663888639)
  ·
    refine ⟨25461019160606765495832959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16974012773737843663888639 25461019160606765495832959)
    ·
      refine ⟨38191528740910148243749439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25461019160606765495832959 38191528740910148243749439)
      ·
        refine ⟨57287293111365222365624159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38191528740910148243749439 57287293111365222365624159)
        ·
          refine ⟨85930939667047833548436239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57287293111365222365624159 85930939667047833548436239)
          ·
            refine ⟨128896409500571750322654359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85930939667047833548436239 128896409500571750322654359)
            ·
              refine ⟨193344614250857625483981539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128896409500571750322654359 193344614250857625483981539)
              ·
                refine ⟨290016921376286438225972309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193344614250857625483981539 290016921376286438225972309)
                ·
                  refine ⟨3398635797378356697960613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 290016921376286438225972309 3398635797378356697960613)
                  ·
                    refine ⟨637244212008441880867615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398635797378356697960613 637244212008441880867615)
                    ·
                      rfl

theorem cell23_3723086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_3723086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723086 prefixEnd_3723086 := by exact prefixLift 3723086
  have htrace : WordTrace (prefixWord ++ tailWord_3723086) baseStart_3723086 baseEnd_3723086 := by
    simpa [prefixWord, tailWord_3723086, baseEnd_3723086] using wordTrace_append hprefix tailTrace_3723086
  have hstable : (prefixWord ++ tailWord_3723086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723086).length < 2 ^ (prefixWord ++ tailWord_3723086).sum := by decide
  have hdescent : baseEnd_3723086 < baseStart_3723086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723107 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 1, 5]
def baseStart_3723107 : Nat := 118140960795 + 3723107 * 2 ^ 59
def prefixEnd_3723107 : Nat := 4983230072969 + 3 ^ 40 * 3723107 * 2
def baseEnd_3723107 : Nat := 637247806373023353480083

theorem tailTrace_3723107 : CollatzResearch.WordTrace tailWord_3723107 prefixEnd_3723107 637247806373023353480083 := by
  unfold tailWord_3723107
  simp only [CollatzResearch.WordTrace]
  refine ⟨135792868122826669897623575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90528578748551113265082383 135792868122826669897623575)
  ·
    refine ⟨203689302184240004846435363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135792868122826669897623575 203689302184240004846435363)
    ·
      refine ⟨305533953276360007269653045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203689302184240004846435363 305533953276360007269653045)
      ·
        refine ⟨28643808119658750681529973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305533953276360007269653045 28643808119658750681529973)
        ·
          refine ⟨2685357011218007876393435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28643808119658750681529973 2685357011218007876393435)
          ·
            refine ⟨4028035516827011814590153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685357011218007876393435 4028035516827011814590153)
            ·
              refine ⟨3021026637620258860942615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4028035516827011814590153 3021026637620258860942615)
              ·
                refine ⟨4531539956430388291413923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021026637620258860942615 4531539956430388291413923)
                ·
                  refine ⟨6797309934645582437120885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531539956430388291413923 6797309934645582437120885)
                  ·
                    refine ⟨637247806373023353480083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6797309934645582437120885 637247806373023353480083)
                    ·
                      rfl

theorem cell23_3723107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 5].length) (baseStart_3723107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723107 prefixEnd_3723107 := by exact prefixLift 3723107
  have htrace : WordTrace (prefixWord ++ tailWord_3723107) baseStart_3723107 baseEnd_3723107 := by
    simpa [prefixWord, tailWord_3723107, baseEnd_3723107] using wordTrace_append hprefix tailTrace_3723107
  have hstable : (prefixWord ++ tailWord_3723107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723107).length < 2 ^ (prefixWord ++ tailWord_3723107).sum := by decide
  have hdescent : baseEnd_3723107 < baseStart_3723107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723119 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_3723119 : Nat := 118140960795 + 3723119 * 2 ^ 59
def prefixEnd_3723119 : Nat := 4983230072969 + 3 ^ 40 * 3723119 * 2
def baseEnd_3723119 : Nat := 1911749580886924013490193

theorem tailTrace_3723119 : CollatzResearch.WordTrace tailWord_3723119 prefixEnd_3723119 1911749580886924013490193 := by
  unfold tailWord_3723119
  simp only [CollatzResearch.WordTrace]
  refine ⟨135793305798783195947060411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90528870532522130631373607 135793305798783195947060411)
  ·
    refine ⟨203689958698174793920590617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135793305798783195947060411 203689958698174793920590617)
    ·
      refine ⟨152767469023631095440442963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203689958698174793920590617 152767469023631095440442963)
      ·
        refine ⟨229151203535446643160664445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152767469023631095440442963 229151203535446643160664445)
        ·
          refine ⟨85931701325792491185249167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229151203535446643160664445 85931701325792491185249167)
          ·
            refine ⟨128897551988688736777873751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85931701325792491185249167 128897551988688736777873751)
            ·
              refine ⟨193346327983033105166810627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128897551988688736777873751 193346327983033105166810627)
              ·
                refine ⟨290019491974549657750215941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193346327983033105166810627 290019491974549657750215941)
                ·
                  refine ⟨54378654745228060828165489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290019491974549657750215941 54378654745228060828165489)
                  ·
                    refine ⟨40783991058921045621124117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54378654745228060828165489 40783991058921045621124117)
                    ·
                      refine ⟨1911749580886924013490193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40783991058921045621124117 1911749580886924013490193)
                      ·
                        rfl

theorem cell23_3723119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_3723119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723119 prefixEnd_3723119 := by exact prefixLift 3723119
  have htrace : WordTrace (prefixWord ++ tailWord_3723119) baseStart_3723119 baseEnd_3723119 := by
    simpa [prefixWord, tailWord_3723119, baseEnd_3723119] using wordTrace_append hprefix tailTrace_3723119
  have hstable : (prefixWord ++ tailWord_3723119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723119).length < 2 ^ (prefixWord ++ tailWord_3723119).sum := by decide
  have hdescent : baseEnd_3723119 < baseStart_3723119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723137 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3723137 : Nat := 118140960795 + 3723137 * 2 ^ 59
def prefixEnd_3723137 : Nat := 4983230072969 + 3 ^ 40 * 3723137 * 2
def baseEnd_3723137 : Nat := 637252941179568314355037

theorem tailTrace_3723137 : CollatzResearch.WordTrace tailWord_3723137 prefixEnd_3723137 637252941179568314355037 := by
  unfold tailWord_3723137
  simp only [CollatzResearch.WordTrace]
  refine ⟨135793962312717985021215665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90529308208478656680810443 135793962312717985021215665)
  ·
    refine ⟨101845471734538488765911749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135793962312717985021215665 101845471734538488765911749)
    ·
      refine ⟨19096025950225966643608453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101845471734538488765911749 19096025950225966643608453)
      ·
        refine ⟨3580504865667368745676585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19096025950225966643608453 3580504865667368745676585)
        ·
          refine ⟨2685378649250526559257439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580504865667368745676585 2685378649250526559257439)
          ·
            refine ⟨4028067973875789838886159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685378649250526559257439 4028067973875789838886159)
            ·
              refine ⟨6042101960813684758329239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028067973875789838886159 6042101960813684758329239)
              ·
                refine ⟨9063152941220527137493859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042101960813684758329239 9063152941220527137493859)
                ·
                  refine ⟨13594729411830790706240789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063152941220527137493859 13594729411830790706240789)
                  ·
                    refine ⟨637252941179568314355037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13594729411830790706240789 637252941179568314355037)
                    ·
                      rfl

theorem cell23_3723137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3723137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723137 prefixEnd_3723137 := by exact prefixLift 3723137
  have htrace : WordTrace (prefixWord ++ tailWord_3723137) baseStart_3723137 baseEnd_3723137 := by
    simpa [prefixWord, tailWord_3723137, baseEnd_3723137] using wordTrace_append hprefix tailTrace_3723137
  have hstable : (prefixWord ++ tailWord_3723137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723137).length < 2 ^ (prefixWord ++ tailWord_3723137).sum := by decide
  have hdescent : baseEnd_3723137 < baseStart_3723137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723153 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_3723153 : Nat := 118140960795 + 3723153 * 2 ^ 59
def prefixEnd_3723153 : Nat := 4983230072969 + 3 ^ 40 * 3723153 * 2
def baseEnd_3723153 : Nat := 1911767039229176880465037

theorem tailTrace_3723153 : CollatzResearch.WordTrace tailWord_3723153 prefixEnd_3723153 1911767039229176880465037 := by
  unfold tailWord_3723153
  simp only [CollatzResearch.WordTrace]
  refine ⟨135794545880660019753798113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90529697253773346502532075 135794545880660019753798113)
  ·
    refine ⟨101845909410495014815348585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135794545880660019753798113 101845909410495014815348585)
    ·
      refine ⟨76384432057871261111511439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101845909410495014815348585 76384432057871261111511439)
      ·
        refine ⟨114576648086806891667267159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76384432057871261111511439 114576648086806891667267159)
        ·
          refine ⟨171864972130210337500900739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114576648086806891667267159 171864972130210337500900739)
          ·
            refine ⟨257797458195315506251351109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171864972130210337500900739 257797458195315506251351109)
            ·
              refine ⟨48337023411621657422128333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257797458195315506251351109 48337023411621657422128333)
              ·
                refine ⟨18126383779358121533298125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48337023411621657422128333 18126383779358121533298125)
                ·
                  refine ⟨6797393917259295574986797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18126383779358121533298125 6797393917259295574986797)
                  ·
                    refine ⟨2549022718972235840620049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6797393917259295574986797 2549022718972235840620049)
                    ·
                      refine ⟨1911767039229176880465037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549022718972235840620049 1911767039229176880465037)
                      ·
                        rfl

theorem cell23_3723153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_3723153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723153 prefixEnd_3723153 := by exact prefixLift 3723153
  have htrace : WordTrace (prefixWord ++ tailWord_3723153) baseStart_3723153 baseEnd_3723153 := by
    simpa [prefixWord, tailWord_3723153, baseEnd_3723153] using wordTrace_append hprefix tailTrace_3723153
  have hstable : (prefixWord ++ tailWord_3723153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723153).length < 2 ^ (prefixWord ++ tailWord_3723153).sum := by decide
  have hdescent : baseEnd_3723153 < baseStart_3723153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723223 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 5]
def baseStart_3723223 : Nat := 118140960795 + 3723223 * 2 ^ 59
def prefixEnd_3723223 : Nat := 4983230072969 + 3 ^ 40 * 3723223 * 2
def baseEnd_3723223 : Nat := 212422553652776845176635

theorem tailTrace_3723223 : CollatzResearch.WordTrace tailWord_3723223 prefixEnd_3723223 212422553652776845176635 := by
  unfold tailWord_3723223
  simp only [CollatzResearch.WordTrace]
  refine ⟨135797098990406421708846323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90531399326937614472564215 135797098990406421708846323)
  ·
    refine ⟨203695648485609632563269485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135797098990406421708846323 203695648485609632563269485)
    ·
      refine ⟨76385868182103612211226057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203695648485609632563269485 76385868182103612211226057)
      ·
        refine ⟨57289401136577709158419543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76385868182103612211226057 57289401136577709158419543)
        ·
          refine ⟨85934101704866563737629315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57289401136577709158419543 85934101704866563737629315)
          ·
            refine ⟨128901152557299845606443973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85934101704866563737629315 128901152557299845606443973)
            ·
              refine ⟨24168966104493721051208245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128901152557299845606443973 24168966104493721051208245)
              ·
                refine ⟨2265840572296286348550773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24168966104493721051208245 2265840572296286348550773)
                ·
                  refine ⟨212422553652776845176635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2265840572296286348550773 212422553652776845176635)
                  ·
                    rfl

theorem cell23_3723223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 5].length) (baseStart_3723223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723223 prefixEnd_3723223 := by exact prefixLift 3723223
  have htrace : WordTrace (prefixWord ++ tailWord_3723223) baseStart_3723223 baseEnd_3723223 := by
    simpa [prefixWord, tailWord_3723223, baseEnd_3723223] using wordTrace_append hprefix tailTrace_3723223
  have hstable : (prefixWord ++ tailWord_3723223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723223).length < 2 ^ (prefixWord ++ tailWord_3723223).sum := by decide
  have hdescent : baseEnd_3723223 < baseStart_3723223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723290 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_3723290 : Nat := 118140960795 + 3723290 * 2 ^ 59
def prefixEnd_3723290 : Nat := 4983230072969 + 3 ^ 40 * 3723290 * 2
def baseEnd_3723290 : Nat := 1911837386078842844451907

theorem tailTrace_3723290 : CollatzResearch.WordTrace tailWord_3723290 prefixEnd_3723290 1911837386078842844451907 := by
  unfold tailWord_3723290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33949885670290923037883831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90533028454109128101023549 33949885670290923037883831)
  ·
    refine ⟨50924828505436384556825747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33949885670290923037883831 50924828505436384556825747)
    ·
      refine ⟨76387242758154576835238621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50924828505436384556825747 76387242758154576835238621)
      ·
        refine ⟨28645216034307966313214483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76387242758154576835238621 28645216034307966313214483)
        ·
          refine ⟨42967824051461949469821725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28645216034307966313214483 42967824051461949469821725)
          ·
            refine ⟨16112934019298231051183147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42967824051461949469821725 16112934019298231051183147)
            ·
              refine ⟨24169401028947346576774721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16112934019298231051183147 24169401028947346576774721)
              ·
                refine ⟨18127050771710509932581041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24169401028947346576774721 18127050771710509932581041)
                ·
                  refine ⟨13595288078782882449435781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18127050771710509932581041 13595288078782882449435781)
                  ·
                    refine ⟨2549116514771790459269209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13595288078782882449435781 2549116514771790459269209)
                    ·
                      refine ⟨1911837386078842844451907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549116514771790459269209 1911837386078842844451907)
                      ·
                        rfl

theorem cell23_3723290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_3723290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723290 prefixEnd_3723290 := by exact prefixLift 3723290
  have htrace : WordTrace (prefixWord ++ tailWord_3723290) baseStart_3723290 baseEnd_3723290 := by
    simpa [prefixWord, tailWord_3723290, baseEnd_3723290] using wordTrace_append hprefix tailTrace_3723290
  have hstable : (prefixWord ++ tailWord_3723290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723290).length < 2 ^ (prefixWord ++ tailWord_3723290).sum := by decide
  have hdescent : baseEnd_3723290 < baseStart_3723290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723310 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3723310 : Nat := 118140960795 + 3723310 * 2 ^ 59
def prefixEnd_3723310 : Nat := 4983230072969 + 3 ^ 40 * 3723310 * 2
def baseEnd_3723310 : Nat := 1911847655691932766201815

theorem tailTrace_3723310 : CollatzResearch.WordTrace tailWord_3723310 prefixEnd_3723310 1911847655691932766201815 := by
  unfold tailWord_3723310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975034017636404445907923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90533514760727490378175589 16975034017636404445907923)
  ·
    refine ⟨25462551026454606668861885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16975034017636404445907923 25462551026454606668861885)
    ·
      refine ⟨9548456634920477500823207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25462551026454606668861885 9548456634920477500823207)
      ·
        refine ⟨14322684952380716251234811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548456634920477500823207 14322684952380716251234811)
        ·
          refine ⟨21484027428571074376852217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14322684952380716251234811 21484027428571074376852217)
          ·
            refine ⟨16113020571428305782639163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21484027428571074376852217 16113020571428305782639163)
            ·
              refine ⟨24169530857142458673958745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16113020571428305782639163 24169530857142458673958745)
              ·
                refine ⟨18127148142856844005469059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24169530857142458673958745 18127148142856844005469059)
                ·
                  refine ⟨27190722214285266008203589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18127148142856844005469059 27190722214285266008203589)
                  ·
                    refine ⟨5098260415178487376538173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27190722214285266008203589 5098260415178487376538173)
                    ·
                      refine ⟨1911847655691932766201815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5098260415178487376538173 1911847655691932766201815)
                      ·
                        rfl

theorem cell23_3723310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3723310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723310 prefixEnd_3723310 := by exact prefixLift 3723310
  have htrace : WordTrace (prefixWord ++ tailWord_3723310) baseStart_3723310 baseEnd_3723310 := by
    simpa [prefixWord, tailWord_3723310, baseEnd_3723310] using wordTrace_append hprefix tailTrace_3723310
  have hstable : (prefixWord ++ tailWord_3723310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723310).length < 2 ^ (prefixWord ++ tailWord_3723310).sum := by decide
  have hdescent : baseEnd_3723310 < baseStart_3723310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723340 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3723340 : Nat := 118140960795 + 3723340 * 2 ^ 59
def prefixEnd_3723340 : Nat := 4983230072969 + 3 ^ 40 * 3723340 * 2
def baseEnd_3723340 : Nat := 1911863060111567648826677

theorem tailTrace_3723340 : CollatzResearch.WordTrace tailWord_3723340 prefixEnd_3723340 1911863060111567648826677 := by
  unfold tailWord_3723340
  simp only [CollatzResearch.WordTrace]
  refine ⟨67900683165491275345427737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90534244220655033793903649 67900683165491275345427737)
  ·
    refine ⟨50925512374118456509070803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67900683165491275345427737 50925512374118456509070803)
    ·
      refine ⟨76388268561177684763606205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50925512374118456509070803 76388268561177684763606205)
      ·
        refine ⟨28645600710441631786352327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76388268561177684763606205 28645600710441631786352327)
        ·
          refine ⟨42968401065662447679528491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28645600710441631786352327 42968401065662447679528491)
          ·
            refine ⟨64452601598493671519292737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42968401065662447679528491 64452601598493671519292737)
            ·
              refine ⟨48339451198870253639469553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64452601598493671519292737 48339451198870253639469553)
              ·
                refine ⟨36254588399152690229602165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48339451198870253639469553 36254588399152690229602165)
                ·
                  refine ⟨3398867662420564709025203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36254588399152690229602165 3398867662420564709025203)
                  ·
                    refine ⟨5098301493630847063537805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3398867662420564709025203 5098301493630847063537805)
                    ·
                      refine ⟨1911863060111567648826677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5098301493630847063537805 1911863060111567648826677)
                      ·
                        rfl

theorem cell23_3723340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3723340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723340 prefixEnd_3723340 := by exact prefixLift 3723340
  have htrace : WordTrace (prefixWord ++ tailWord_3723340) baseStart_3723340 baseEnd_3723340 := by
    simpa [prefixWord, tailWord_3723340, baseEnd_3723340] using wordTrace_append hprefix tailTrace_3723340
  have hstable : (prefixWord ++ tailWord_3723340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723340).length < 2 ^ (prefixWord ++ tailWord_3723340).sum := by decide
  have hdescent : baseEnd_3723340 < baseStart_3723340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723410 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3723410 : Nat := 118140960795 + 3723410 * 2 ^ 59
def prefixEnd_3723410 : Nat := 4983230072969 + 3 ^ 40 * 3723410 * 2
def baseEnd_3723410 : Nat := 1911899003757382374951355

theorem tailTrace_3723410 : CollatzResearch.WordTrace tailWord_3723410 prefixEnd_3723410 1911899003757382374951355 := by
  unfold tailWord_3723410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950979860182238161475921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90535946293819301763935789 33950979860182238161475921)
  ·
    refine ⟨25463234895136678621106941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33950979860182238161475921 25463234895136678621106941)
    ·
      refine ⟨9548713085676254482915103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25463234895136678621106941 9548713085676254482915103)
      ·
        refine ⟨14323069628514381724372655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548713085676254482915103 14323069628514381724372655)
        ·
          refine ⟨21484604442771572586558983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323069628514381724372655 21484604442771572586558983)
          ·
            refine ⟨32226906664157358879838475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21484604442771572586558983 32226906664157358879838475)
            ·
              refine ⟨48340359996236038319757713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32226906664157358879838475 48340359996236038319757713)
              ·
                refine ⟨36255269997177028739818285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48340359996236038319757713 36255269997177028739818285)
                ·
                  refine ⟨13595726248941385777431857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36255269997177028739818285 13595726248941385777431857)
                  ·
                    refine ⟨10196794686706039333073893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13595726248941385777431857 10196794686706039333073893)
                    ·
                      refine ⟨1911899003757382374951355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10196794686706039333073893 1911899003757382374951355)
                      ·
                        rfl

theorem cell23_3723410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3723410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723410 prefixEnd_3723410 := by exact prefixLift 3723410
  have htrace : WordTrace (prefixWord ++ tailWord_3723410) baseStart_3723410 baseEnd_3723410 := by
    simpa [prefixWord, tailWord_3723410, baseEnd_3723410] using wordTrace_append hprefix tailTrace_3723410
  have hstable : (prefixWord ++ tailWord_3723410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723410).length < 2 ^ (prefixWord ++ tailWord_3723410).sum := by decide
  have hdescent : baseEnd_3723410 < baseStart_3723410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723431 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3723431 : Nat := 118140960795 + 3723431 * 2 ^ 59
def prefixEnd_3723431 : Nat := 4983230072969 + 3 ^ 40 * 3723431 * 2
def baseEnd_3723431 : Nat := 1911909786851126792788759

theorem tailTrace_3723431 : CollatzResearch.WordTrace tailWord_3723431 prefixEnd_3723431 1911909786851126792788759 := by
  unfold tailWord_3723431
  simp only [CollatzResearch.WordTrace]
  refine ⟨135804685373652873232418147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90536456915768582154945431 135804685373652873232418147)
  ·
    refine ⟨203707028060479309848627221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135804685373652873232418147 203707028060479309848627221)
    ·
      refine ⟨9548766940334967649154401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203707028060479309848627221 9548766940334967649154401)
      ·
        refine ⟨7161575205251225736865801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9548766940334967649154401 7161575205251225736865801)
        ·
          refine ⟨5371181403938419302649351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7161575205251225736865801 5371181403938419302649351)
          ·
            refine ⟨8056772105907628953974027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371181403938419302649351 8056772105907628953974027)
            ·
              refine ⟨12085158158861443430961041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056772105907628953974027 12085158158861443430961041)
              ·
                refine ⟨9063868619146082573220781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085158158861443430961041 9063868619146082573220781)
                ·
                  refine ⟨3398950732179780964957793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9063868619146082573220781 3398950732179780964957793)
                  ·
                    refine ⟨2549213049134835723718345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3398950732179780964957793 2549213049134835723718345)
                    ·
                      refine ⟨1911909786851126792788759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549213049134835723718345 1911909786851126792788759)
                      ·
                        rfl

theorem cell23_3723431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3723431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723431 prefixEnd_3723431 := by exact prefixLift 3723431
  have htrace : WordTrace (prefixWord ++ tailWord_3723431) baseStart_3723431 baseEnd_3723431 := by
    simpa [prefixWord, tailWord_3723431, baseEnd_3723431] using wordTrace_append hprefix tailTrace_3723431
  have hstable : (prefixWord ++ tailWord_3723431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723431).length < 2 ^ (prefixWord ++ tailWord_3723431).sum := by decide
  have hdescent : baseEnd_3723431 < baseStart_3723431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723437 : List Nat := [1, 5, 2, 1, 2, 2, 3, 7]
def baseStart_3723437 : Nat := 118140960795 + 3723437 * 2 ^ 59
def prefixEnd_3723437 : Nat := 4983230072969 + 3 ^ 40 * 3723437 * 2
def baseEnd_3723437 : Nat := 70811587693890880344953

theorem tailTrace_3723437 : CollatzResearch.WordTrace tailWord_3723437 prefixEnd_3723437 70811587693890880344953 := by
  unfold tailWord_3723437
  simp only [CollatzResearch.WordTrace]
  refine ⟨135804904211631136257136565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90536602807754090838091043 135804904211631136257136565)
  ·
    refine ⟨12731709769840419024106553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135804904211631136257136565 12731709769840419024106553)
    ·
      refine ⟨9548782327380314268079915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12731709769840419024106553 9548782327380314268079915)
      ·
        refine ⟨14323173491070471402119873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548782327380314268079915 14323173491070471402119873)
        ·
          refine ⟨10742380118302853551589905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14323173491070471402119873 10742380118302853551589905)
          ·
            refine ⟨8056785088727140163692429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10742380118302853551589905 8056785088727140163692429)
            ·
              refine ⟨3021294408272677561384661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8056785088727140163692429 3021294408272677561384661)
              ·
                refine ⟨70811587693890880344953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3021294408272677561384661 70811587693890880344953)
                ·
                  rfl

theorem cell23_3723437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 7].length) (baseStart_3723437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723437 prefixEnd_3723437 := by exact prefixLift 3723437
  have htrace : WordTrace (prefixWord ++ tailWord_3723437) baseStart_3723437 baseEnd_3723437 := by
    simpa [prefixWord, tailWord_3723437, baseEnd_3723437] using wordTrace_append hprefix tailTrace_3723437
  have hstable : (prefixWord ++ tailWord_3723437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723437).length < 2 ^ (prefixWord ++ tailWord_3723437).sum := by decide
  have hdescent : baseEnd_3723437 < baseStart_3723437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723443 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_3723443 : Nat := 118140960795 + 3723443 * 2 ^ 59
def prefixEnd_3723443 : Nat := 4983230072969 + 3 ^ 40 * 3723443 * 2
def baseEnd_3723443 : Nat := 1911915948618980745838703

theorem tailTrace_3723443 : CollatzResearch.WordTrace tailWord_3723443 prefixEnd_3723443 1911915948618980745838703 := by
  unfold tailWord_3723443
  simp only [CollatzResearch.WordTrace]
  refine ⟨135805123049609399281854983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90536748699739599521236655 135805123049609399281854983)
  ·
    refine ⟨203707684574414098922782475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135805123049609399281854983 203707684574414098922782475)
    ·
      refine ⟨305561526861621148384173713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203707684574414098922782475 305561526861621148384173713)
      ·
        refine ⟨229171145146215861288130285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305561526861621148384173713 229171145146215861288130285)
        ·
          refine ⟨85939179429830947983048857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229171145146215861288130285 85939179429830947983048857)
          ·
            refine ⟨64454384572373210987286643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85939179429830947983048857 64454384572373210987286643)
            ·
              refine ⟨96681576858559816480929965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64454384572373210987286643 96681576858559816480929965)
              ·
                refine ⟨36255591321959931180348737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96681576858559816480929965 36255591321959931180348737)
                ·
                  refine ⟨27191693491469948385261553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36255591321959931180348737 27191693491469948385261553)
                  ·
                    refine ⟨20393770118602461288946165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27191693491469948385261553 20393770118602461288946165)
                    ·
                      refine ⟨1911915948618980745838703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20393770118602461288946165 1911915948618980745838703)
                      ·
                        rfl

theorem cell23_3723443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_3723443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723443 prefixEnd_3723443 := by exact prefixLift 3723443
  have htrace : WordTrace (prefixWord ++ tailWord_3723443) baseStart_3723443 baseEnd_3723443 := by
    simpa [prefixWord, tailWord_3723443, baseEnd_3723443] using wordTrace_append hprefix tailTrace_3723443
  have hstable : (prefixWord ++ tailWord_3723443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723443).length < 2 ^ (prefixWord ++ tailWord_3723443).sum := by decide
  have hdescent : baseEnd_3723443 < baseStart_3723443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723458 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3723458 : Nat := 118140960795 + 3723458 * 2 ^ 59
def prefixEnd_3723458 : Nat := 4983230072969 + 3 ^ 40 * 3723458 * 2
def baseEnd_3723458 : Nat := 637307883609599395717045

theorem tailTrace_3723458 : CollatzResearch.WordTrace tailWord_3723458 prefixEnd_3723458 637307883609599395717045 := by
  unfold tailWord_3723458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951417536138764210912757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90537113429703371229100685 33951417536138764210912757)
  ·
    refine ⟨3182945394013009144773071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33951417536138764210912757 3182945394013009144773071)
    ·
      refine ⟨4774418091019513717159607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182945394013009144773071 4774418091019513717159607)
      ·
        refine ⟨7161627136529270575739411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774418091019513717159607 7161627136529270575739411)
        ·
          refine ⟨10742440704793905863609117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161627136529270575739411 10742440704793905863609117)
          ·
            refine ⟨4028415264297714698853419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10742440704793905863609117 4028415264297714698853419)
            ·
              refine ⟨6042622896446572048280129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028415264297714698853419 6042622896446572048280129)
              ·
                refine ⟨4531967172334929036210097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042622896446572048280129 4531967172334929036210097)
                ·
                  refine ⟨3398975379251196777157573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4531967172334929036210097 3398975379251196777157573)
                  ·
                    refine ⟨637307883609599395717045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398975379251196777157573 637307883609599395717045)
                    ·
                      rfl

theorem cell23_3723458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3723458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723458 prefixEnd_3723458 := by exact prefixLift 3723458
  have htrace : WordTrace (prefixWord ++ tailWord_3723458) baseStart_3723458 baseEnd_3723458 := by
    simpa [prefixWord, tailWord_3723458, baseEnd_3723458] using wordTrace_append hprefix tailTrace_3723458
  have hstable : (prefixWord ++ tailWord_3723458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723458).length < 2 ^ (prefixWord ++ tailWord_3723458).sum := by decide
  have hdescent : baseEnd_3723458 < baseStart_3723458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723480 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_3723480 : Nat := 118140960795 + 3723480 * 2 ^ 59
def prefixEnd_3723480 : Nat := 4983230072969 + 3 ^ 40 * 3723480 * 2
def baseEnd_3723480 : Nat := 637311649134399033692011

theorem tailTrace_3723480 : CollatzResearch.WordTrace tailWord_3723480 prefixEnd_3723480 637311649134399033692011 := by
  unfold tailWord_3723480
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903236275237677300475947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90537648366983569733967929 67903236275237677300475947)
  ·
    refine ⟨101854854412856515950713921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67903236275237677300475947 101854854412856515950713921)
    ·
      refine ⟨76391140809642386963035441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101854854412856515950713921 76391140809642386963035441)
      ·
        refine ⟨57293355607231790222276581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76391140809642386963035441 57293355607231790222276581)
        ·
          refine ⟨10742504176355960666676859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57293355607231790222276581 10742504176355960666676859)
          ·
            refine ⟨16113756264533941000015289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742504176355960666676859 16113756264533941000015289)
            ·
              refine ⟨12085317198400455750011467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16113756264533941000015289 12085317198400455750011467)
              ·
                refine ⟨18127975797600683625017201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12085317198400455750011467 18127975797600683625017201)
                ·
                  refine ⟨13595981848200512718762901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18127975797600683625017201 13595981848200512718762901)
                  ·
                    refine ⟨637311649134399033692011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13595981848200512718762901 637311649134399033692011)
                    ·
                      rfl

theorem cell23_3723480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_3723480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723480 prefixEnd_3723480 := by exact prefixLift 3723480
  have htrace : WordTrace (prefixWord ++ tailWord_3723480) baseStart_3723480 baseEnd_3723480 := by
    simpa [prefixWord, tailWord_3723480, baseEnd_3723480] using wordTrace_append hprefix tailTrace_3723480
  have hstable : (prefixWord ++ tailWord_3723480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723480).length < 2 ^ (prefixWord ++ tailWord_3723480).sum := by decide
  have hdescent : baseEnd_3723480 < baseStart_3723480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723510 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3723510 : Nat := 118140960795 + 3723510 * 2 ^ 59
def prefixEnd_3723510 : Nat := 4983230072969 + 3 ^ 40 * 3723510 * 2
def baseEnd_3723510 : Nat := 212438927980314664855655

theorem tailTrace_3723510 : CollatzResearch.WordTrace tailWord_3723510 prefixEnd_3723510 212438927980314664855655 := by
  unfold tailWord_3723510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487972921272916857783999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90538377826911113149695989 8487972921272916857783999)
  ·
    refine ⟨12731959381909375286675999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8487972921272916857783999 12731959381909375286675999)
    ·
      refine ⟨19097939072864062930013999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12731959381909375286675999 19097939072864062930013999)
      ·
        refine ⟨28646908609296094395020999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097939072864062930013999 28646908609296094395020999)
        ·
          refine ⟨42970362913944141592531499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646908609296094395020999 42970362913944141592531499)
          ·
            refine ⟨64455544370916212388797249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42970362913944141592531499 64455544370916212388797249)
            ·
              refine ⟨48341658278187159291597937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64455544370916212388797249 48341658278187159291597937)
              ·
                refine ⟨36256243708640369468698453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48341658278187159291597937 36256243708640369468698453)
                ·
                  refine ⟨212438927980314664855655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36256243708640369468698453 212438927980314664855655)
                  ·
                    rfl

theorem cell23_3723510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3723510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723510 prefixEnd_3723510 := by exact prefixLift 3723510
  have htrace : WordTrace (prefixWord ++ tailWord_3723510) baseStart_3723510 baseEnd_3723510 := by
    simpa [prefixWord, tailWord_3723510, baseEnd_3723510] using wordTrace_append hprefix tailTrace_3723510
  have hstable : (prefixWord ++ tailWord_3723510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723510).length < 2 ^ (prefixWord ++ tailWord_3723510).sum := by decide
  have hdescent : baseEnd_3723510 < baseStart_3723510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723520 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_3723520 : Nat := 118140960795 + 3723520 * 2 ^ 59
def prefixEnd_3723520 : Nat := 4983230072969 + 3 ^ 40 * 3723520 * 2
def baseEnd_3723520 : Nat := 1911955486629376944575849

theorem tailTrace_3723520 : CollatzResearch.WordTrace tailWord_3723520 prefixEnd_3723520 1911955486629376944575849 := by
  unfold tailWord_3723520
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903965735165220716204007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90538620980220294288272009 67903965735165220716204007)
  ·
    refine ⟨101855948602747831074306011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67903965735165220716204007 101855948602747831074306011)
    ·
      refine ⟨152783922904121746611459017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101855948602747831074306011 152783922904121746611459017)
      ·
        refine ⟨114587942178091309958594263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152783922904121746611459017 114587942178091309958594263)
        ·
          refine ⟨171881913267136964937891395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114587942178091309958594263 171881913267136964937891395)
          ·
            refine ⟨257822869900705447406837093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171881913267136964937891395 257822869900705447406837093)
            ·
              refine ⟨48341788106382271388781955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257822869900705447406837093 48341788106382271388781955)
              ·
                refine ⟨72512682159573407083172933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48341788106382271388781955 72512682159573407083172933)
                ·
                  refine ⟨13596127904920013828094925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72512682159573407083172933 13596127904920013828094925)
                  ·
                    refine ⟨5098547964345005185535597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13596127904920013828094925 5098547964345005185535597)
                    ·
                      refine ⟨1911955486629376944575849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5098547964345005185535597 1911955486629376944575849)
                      ·
                        rfl

theorem cell23_3723520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_3723520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723520 prefixEnd_3723520 := by exact prefixLift 3723520
  have htrace : WordTrace (prefixWord ++ tailWord_3723520) baseStart_3723520 baseEnd_3723520 := by
    simpa [prefixWord, tailWord_3723520, baseEnd_3723520] using wordTrace_append hprefix tailTrace_3723520
  have hstable : (prefixWord ++ tailWord_3723520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723520).length < 2 ^ (prefixWord ++ tailWord_3723520).sum := by decide
  have hdescent : baseEnd_3723520 < baseStart_3723520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723580 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3723580 : Nat := 118140960795 + 3723580 * 2 ^ 59
def prefixEnd_3723580 : Nat := 4983230072969 + 3 ^ 40 * 3723580 * 2
def baseEnd_3723580 : Nat := 1911986295468646709825573

theorem tailTrace_3723580 : CollatzResearch.WordTrace tailWord_3723580 prefixEnd_3723580 1911986295468646709825573 := by
  unfold tailWord_3723580
  simp only [CollatzResearch.WordTrace]
  refine ⟨67905059925056535839796097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90540079900075381119728129 67905059925056535839796097)
  ·
    refine ⟨50928794943792401879847073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67905059925056535839796097 50928794943792401879847073)
    ·
      refine ⟨38196596207844301409885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50928794943792401879847073 38196596207844301409885305)
      ·
        refine ⟨28647447155883226057413979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38196596207844301409885305 28647447155883226057413979)
        ·
          refine ⟨42971170733824839086120969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647447155883226057413979 42971170733824839086120969)
          ·
            refine ⟨32228378050368629314590727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42971170733824839086120969 32228378050368629314590727)
            ·
              refine ⟨48342567075552943971886091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32228378050368629314590727 48342567075552943971886091)
              ·
                refine ⟨72513850613329415957829137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48342567075552943971886091 72513850613329415957829137)
                ·
                  refine ⟨54385387959997061968371853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72513850613329415957829137 54385387959997061968371853)
                  ·
                    refine ⟨20394520484998898238139445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54385387959997061968371853 20394520484998898238139445)
                    ·
                      refine ⟨1911986295468646709825573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20394520484998898238139445 1911986295468646709825573)
                      ·
                        rfl

theorem cell23_3723580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3723580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723580 prefixEnd_3723580 := by exact prefixLift 3723580
  have htrace : WordTrace (prefixWord ++ tailWord_3723580) baseStart_3723580 baseEnd_3723580 := by
    simpa [prefixWord, tailWord_3723580, baseEnd_3723580] using wordTrace_append hprefix tailTrace_3723580
  have hstable : (prefixWord ++ tailWord_3723580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723580).length < 2 ^ (prefixWord ++ tailWord_3723580).sum := by decide
  have hdescent : baseEnd_3723580 < baseStart_3723580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723604 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_3723604 : Nat := 118140960795 + 3723604 * 2 ^ 59
def prefixEnd_3723604 : Nat := 4983230072969 + 3 ^ 40 * 3723604 * 2
def baseEnd_3723604 : Nat := 637332873001451538641821

theorem tailTrace_3723604 : CollatzResearch.WordTrace tailWord_3723604 prefixEnd_3723604 637332873001451538641821 := by
  unfold tailWord_3723604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67905497601013061889232933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90540663468017415852310577 67905497601013061889232933)
  ·
    refine ⟨12732280800189949104231175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67905497601013061889232933 12732280800189949104231175)
    ·
      refine ⟨19098421200284923656346763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732280800189949104231175 19098421200284923656346763)
      ·
        refine ⟨28647631800427385484520145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098421200284923656346763 28647631800427385484520145)
        ·
          refine ⟨21485723850320539113390109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28647631800427385484520145 21485723850320539113390109)
          ·
            refine ⟨8057146443870202167521291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21485723850320539113390109 8057146443870202167521291)
            ·
              refine ⟨12085719665805303251281937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057146443870202167521291 12085719665805303251281937)
              ·
                refine ⟨9064289749353977438461453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085719665805303251281937 9064289749353977438461453)
                ·
                  refine ⟨3399108656007741539423045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9064289749353977438461453 3399108656007741539423045)
                  ·
                    refine ⟨637332873001451538641821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399108656007741539423045 637332873001451538641821)
                    ·
                      rfl

theorem cell23_3723604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_3723604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723604 prefixEnd_3723604 := by exact prefixLift 3723604
  have htrace : WordTrace (prefixWord ++ tailWord_3723604) baseStart_3723604 baseEnd_3723604 := by
    simpa [prefixWord, tailWord_3723604, baseEnd_3723604] using wordTrace_append hprefix tailTrace_3723604
  have hstable : (prefixWord ++ tailWord_3723604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723604).length < 2 ^ (prefixWord ++ tailWord_3723604).sum := by decide
  have hdescent : baseEnd_3723604 < baseStart_3723604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723621 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_3723621 : Nat := 118140960795 + 3723621 * 2 ^ 59
def prefixEnd_3723621 : Nat := 4983230072969 + 3 ^ 40 * 3723621 * 2
def baseEnd_3723621 : Nat := 637335782725160349804295

theorem tailTrace_3723621 : CollatzResearch.WordTrace tailWord_3723621 prefixEnd_3723621 637335782725160349804295 := by
  unfold tailWord_3723621
  simp only [CollatzResearch.WordTrace]
  refine ⟨135811615242964535681834717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90541076828643023787889811 135811615242964535681834717)
  ·
    refine ⟨50929355716111700880688019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135811615242964535681834717 50929355716111700880688019)
    ·
      refine ⟨76394033574167551321032029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50929355716111700880688019 76394033574167551321032029)
      ·
        refine ⟨28647762590312831745387011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76394033574167551321032029 28647762590312831745387011)
        ·
          refine ⟨42971643885469247618080517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647762590312831745387011 42971643885469247618080517)
          ·
            refine ⟨8057183228525483928390097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42971643885469247618080517 8057183228525483928390097)
            ·
              refine ⟨6042887421394112946292573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8057183228525483928390097 6042887421394112946292573)
              ·
                refine ⟨2266082783022792354859715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6042887421394112946292573 2266082783022792354859715)
                ·
                  refine ⟨3399124174534188532289573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266082783022792354859715 3399124174534188532289573)
                  ·
                    refine ⟨637335782725160349804295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399124174534188532289573 637335782725160349804295)
                    ·
                      rfl

theorem cell23_3723621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_3723621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723621 prefixEnd_3723621 := by exact prefixLift 3723621
  have htrace : WordTrace (prefixWord ++ tailWord_3723621) baseStart_3723621 baseEnd_3723621 := by
    simpa [prefixWord, tailWord_3723621, baseEnd_3723621] using wordTrace_append hprefix tailTrace_3723621
  have hstable : (prefixWord ++ tailWord_3723621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723621).length < 2 ^ (prefixWord ++ tailWord_3723621).sum := by decide
  have hdescent : baseEnd_3723621 < baseStart_3723621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723634 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_3723634 : Nat := 118140960795 + 3723634 * 2 ^ 59
def prefixEnd_3723634 : Nat := 4983230072969 + 3 ^ 40 * 3723634 * 2
def baseEnd_3723634 : Nat := 212446002602665499838925

theorem tailTrace_3723634 : CollatzResearch.WordTrace tailWord_3723634 prefixEnd_3723634 212446002602665499838925 := by
  unfold tailWord_3723634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33953022347979359725514489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90541392927944959268038637 33953022347979359725514489)
  ·
    refine ⟨25464766760984519794135867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33953022347979359725514489 25464766760984519794135867)
    ·
      refine ⟨38197150141476779691203801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25464766760984519794135867 38197150141476779691203801)
      ·
        refine ⟨28647862606107584768402851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38197150141476779691203801 28647862606107584768402851)
        ·
          refine ⟨42971793909161377152604277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647862606107584768402851 42971793909161377152604277)
          ·
            refine ⟨4028605678983879108056651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42971793909161377152604277 4028605678983879108056651)
            ·
              refine ⟨6042908518475818662084977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028605678983879108056651 6042908518475818662084977)
              ·
                refine ⟨4532181388856863996563733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042908518475818662084977 4532181388856863996563733)
                ·
                  refine ⟨212446002602665499838925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4532181388856863996563733 212446002602665499838925)
                  ·
                    rfl

theorem cell23_3723634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_3723634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723634 prefixEnd_3723634 := by exact prefixLift 3723634
  have htrace : WordTrace (prefixWord ++ tailWord_3723634) baseStart_3723634 baseEnd_3723634 := by
    simpa [prefixWord, tailWord_3723634, baseEnd_3723634] using wordTrace_append hprefix tailTrace_3723634
  have hstable : (prefixWord ++ tailWord_3723634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723634).length < 2 ^ (prefixWord ++ tailWord_3723634).sum := by decide
  have hdescent : baseEnd_3723634 < baseStart_3723634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723637 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3723637 : Nat := 118140960795 + 3723637 * 2 ^ 59
def prefixEnd_3723637 : Nat := 4983230072969 + 3 ^ 40 * 3723637 * 2
def baseEnd_3723637 : Nat := 1912015563865952986812811

theorem tailTrace_3723637 : CollatzResearch.WordTrace tailWord_3723637 prefixEnd_3723637 1912015563865952986812811 := by
  unfold tailWord_3723637
  simp only [CollatzResearch.WordTrace]
  refine ⟨135812198810906570414417165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90541465873937713609611443 135812198810906570414417165)
  ·
    refine ⟨50929574554089963905406437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135812198810906570414417165 50929574554089963905406437)
    ·
      refine ⟨9549295228891868232263707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50929574554089963905406437 9549295228891868232263707)
      ·
        refine ⟨14323942843337802348395561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9549295228891868232263707 14323942843337802348395561)
        ·
          refine ⟨10742957132503351761296671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14323942843337802348395561 10742957132503351761296671)
          ·
            refine ⟨16114435698755027641945007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742957132503351761296671 16114435698755027641945007)
            ·
              refine ⟨24171653548132541462917511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114435698755027641945007 24171653548132541462917511)
              ·
                refine ⟨36257480322198812194376267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24171653548132541462917511 36257480322198812194376267)
                ·
                  refine ⟨54386220483298218291564401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36257480322198812194376267 54386220483298218291564401)
                  ·
                    refine ⟨40789665362473663718673301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54386220483298218291564401 40789665362473663718673301)
                    ·
                      refine ⟨1912015563865952986812811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40789665362473663718673301 1912015563865952986812811)
                      ·
                        rfl

theorem cell23_3723637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3723637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723637 prefixEnd_3723637 := by exact prefixLift 3723637
  have htrace : WordTrace (prefixWord ++ tailWord_3723637) baseStart_3723637 baseEnd_3723637 := by
    simpa [prefixWord, tailWord_3723637, baseEnd_3723637] using wordTrace_append hprefix tailTrace_3723637
  have hstable : (prefixWord ++ tailWord_3723637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723637).length < 2 ^ (prefixWord ++ tailWord_3723637).sum := by decide
  have hdescent : baseEnd_3723637 < baseStart_3723637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723638 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_3723638 : Nat := 118140960795 + 3723638 * 2 ^ 59
def prefixEnd_3723638 : Nat := 4983230072969 + 3 ^ 40 * 3723638 * 2
def baseEnd_3723638 : Nat := 637338692448869160966769

theorem tailTrace_3723638 : CollatzResearch.WordTrace tailWord_3723638 prefixEnd_3723638 637338692448869160966769 := by
  unfold tailWord_3723638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488264705243934224075223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90541490189268631723469045 8488264705243934224075223)
  ·
    refine ⟨12732397057865901336112835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8488264705243934224075223 12732397057865901336112835)
    ·
      refine ⟨19098595586798852004169253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732397057865901336112835 19098595586798852004169253)
      ·
        refine ⟨3580986672524784750781735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19098595586798852004169253 3580986672524784750781735)
        ·
          refine ⟨5371480008787177126172603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580986672524784750781735 5371480008787177126172603)
          ·
            refine ⟨8057220013180765689258905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371480008787177126172603 8057220013180765689258905)
            ·
              refine ⟨6042915009885574266944179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8057220013180765689258905 6042915009885574266944179)
              ·
                refine ⟨9064372514828361400416269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042915009885574266944179 9064372514828361400416269)
                ·
                  refine ⟨3399139693060635525156101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9064372514828361400416269 3399139693060635525156101)
                  ·
                    refine ⟨637338692448869160966769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399139693060635525156101 637338692448869160966769)
                    ·
                      rfl

theorem cell23_3723638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_3723638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723638 prefixEnd_3723638 := by exact prefixLift 3723638
  have htrace : WordTrace (prefixWord ++ tailWord_3723638) baseStart_3723638 baseEnd_3723638 := by
    simpa [prefixWord, tailWord_3723638, baseEnd_3723638] using wordTrace_append hprefix tailTrace_3723638
  have hstable : (prefixWord ++ tailWord_3723638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723638).length < 2 ^ (prefixWord ++ tailWord_3723638).sum := by decide
  have hdescent : baseEnd_3723638 < baseStart_3723638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723684 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3723684 : Nat := 118140960795 + 3723684 * 2 ^ 59
def prefixEnd_3723684 : Nat := 4983230072969 + 3 ^ 40 * 3723684 * 2
def baseEnd_3723684 : Nat := 1912039697456714302925095

theorem tailTrace_3723684 : CollatzResearch.WordTrace tailWord_3723684 prefixEnd_3723684 1912039697456714302925095 := by
  unfold tailWord_3723684
  simp only [CollatzResearch.WordTrace]
  refine ⟨67906956520868148720689053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90542608694490864960918737 67906956520868148720689053)
  ·
    refine ⟨25465108695325555770258395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67906956520868148720689053 25465108695325555770258395)
    ·
      refine ⟨38197663042988333655387593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25465108695325555770258395 38197663042988333655387593)
      ·
        refine ⟨28648247282241250241540695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38197663042988333655387593 28648247282241250241540695)
        ·
          refine ⟨42972370923361875362311043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648247282241250241540695 42972370923361875362311043)
          ·
            refine ⟨64458556385042813043466565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42972370923361875362311043 64458556385042813043466565)
            ·
              refine ⟨12085979322195527445649981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64458556385042813043466565 12085979322195527445649981)
              ·
                refine ⟨4532242245823322792118743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12085979322195527445649981 4532242245823322792118743)
                ·
                  refine ⟨6798363368734984188178115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532242245823322792118743 6798363368734984188178115)
                  ·
                    refine ⟨10197545053102476282267173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6798363368734984188178115 10197545053102476282267173)
                    ·
                      refine ⟨1912039697456714302925095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10197545053102476282267173 1912039697456714302925095)
                      ·
                        rfl

theorem cell23_3723684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3723684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723684 prefixEnd_3723684 := by exact prefixLift 3723684
  have htrace : WordTrace (prefixWord ++ tailWord_3723684) baseStart_3723684 baseEnd_3723684 := by
    simpa [prefixWord, tailWord_3723684, baseEnd_3723684] using wordTrace_append hprefix tailTrace_3723684
  have hstable : (prefixWord ++ tailWord_3723684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723684).length < 2 ^ (prefixWord ++ tailWord_3723684).sum := by decide
  have hdescent : baseEnd_3723684 < baseStart_3723684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723688 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3723688 : Nat := 118140960795 + 3723688 * 2 ^ 59
def prefixEnd_3723688 : Nat := 4983230072969 + 3 ^ 40 * 3723688 * 2
def baseEnd_3723688 : Nat := 1912041751379332287275077

theorem tailTrace_3723688 : CollatzResearch.WordTrace tailWord_3723688 prefixEnd_3723688 1912041751379332287275077 := by
  unfold tailWord_3723688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67907029466860903062261859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90542705955814537416349145 67907029466860903062261859)
  ·
    refine ⟨101860544200291354593392789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67907029466860903062261859 101860544200291354593392789)
    ·
      refine ⟨4774713009388657246565287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101860544200291354593392789 4774713009388657246565287)
      ·
        refine ⟨7162069514082985869847931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774713009388657246565287 7162069514082985869847931)
        ·
          refine ⟨10743104271124478804771897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162069514082985869847931 10743104271124478804771897)
          ·
            refine ⟨8057328203343359103578923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10743104271124478804771897 8057328203343359103578923)
            ·
              refine ⟨12085992305015038655368385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057328203343359103578923 12085992305015038655368385)
              ·
                refine ⟨9064494228761278991526289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085992305015038655368385 9064494228761278991526289)
                ·
                  refine ⟨6798370671570959243644717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9064494228761278991526289 6798370671570959243644717)
                  ·
                    refine ⟨2549389001839109716366769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6798370671570959243644717 2549389001839109716366769)
                    ·
                      refine ⟨1912041751379332287275077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549389001839109716366769 1912041751379332287275077)
                      ·
                        rfl

theorem cell23_3723688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3723688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723688 prefixEnd_3723688 := by exact prefixLift 3723688
  have htrace : WordTrace (prefixWord ++ tailWord_3723688) baseStart_3723688 baseEnd_3723688 := by
    simpa [prefixWord, tailWord_3723688, baseEnd_3723688] using wordTrace_append hprefix tailTrace_3723688
  have hstable : (prefixWord ++ tailWord_3723688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723688).length < 2 ^ (prefixWord ++ tailWord_3723688).sum := by decide
  have hdescent : baseEnd_3723688 < baseStart_3723688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723697 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3723697 : Nat := 118140960795 + 3723697 * 2 ^ 59
def prefixEnd_3723697 : Nat := 4983230072969 + 3 ^ 40 * 3723697 * 2
def baseEnd_3723697 : Nat := 1912046372705222752062535

theorem tailTrace_3723697 : CollatzResearch.WordTrace tailWord_3723697 prefixEnd_3723697 1912046372705222752062535 := by
  unfold tailWord_3723697
  simp only [CollatzResearch.WordTrace]
  refine ⟨135814387190689200661601345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90542924793792800441067563 135814387190689200661601345)
  ·
    refine ⟨101860790393016900496201009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135814387190689200661601345 101860790393016900496201009)
    ·
      refine ⟨76395592794762675372150757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101860790393016900496201009 76395592794762675372150757)
      ·
        refine ⟨14324173649018001632278267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76395592794762675372150757 14324173649018001632278267)
        ·
          refine ⟨21486260473527002448417401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14324173649018001632278267 21486260473527002448417401)
          ·
            refine ⟨16114695355145251836313051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21486260473527002448417401 16114695355145251836313051)
            ·
              refine ⟨24172043032717877754469577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114695355145251836313051 24172043032717877754469577)
              ·
                refine ⟨18129032274538408315852183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24172043032717877754469577 18129032274538408315852183)
                ·
                  refine ⟨27193548411807612473778275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18129032274538408315852183 27193548411807612473778275)
                  ·
                    refine ⟨40790322617711418710667413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27193548411807612473778275 40790322617711418710667413)
                    ·
                      refine ⟨1912046372705222752062535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40790322617711418710667413 1912046372705222752062535)
                      ·
                        rfl

theorem cell23_3723697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3723697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723697 prefixEnd_3723697 := by exact prefixLift 3723697
  have htrace : WordTrace (prefixWord ++ tailWord_3723697) baseStart_3723697 baseEnd_3723697 := by
    simpa [prefixWord, tailWord_3723697, baseEnd_3723697] using wordTrace_append hprefix tailTrace_3723697
  have hstable : (prefixWord ++ tailWord_3723697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723697).length < 2 ^ (prefixWord ++ tailWord_3723697).sum := by decide
  have hdescent : baseEnd_3723697 < baseStart_3723697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723717 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_3723717 : Nat := 118140960795 + 3723717 * 2 ^ 59
def prefixEnd_3723717 : Nat := 4983230072969 + 3 ^ 40 * 3723717 * 2
def baseEnd_3723717 : Nat := 1912056642318312673812443

theorem tailTrace_3723717 : CollatzResearch.WordTrace tailWord_3723717 prefixEnd_3723717 1912056642318312673812443 := by
  unfold tailWord_3723717
  simp only [CollatzResearch.WordTrace]
  refine ⟨135815116650616744077329405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90543411100411162718219603 135815116650616744077329405)
  ·
    refine ⟨50930668743981279028998527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135815116650616744077329405 50930668743981279028998527)
    ·
      refine ⟨76396003115971918543497791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50930668743981279028998527 76396003115971918543497791)
      ·
        refine ⟨114594004673957877815246687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76396003115971918543497791 114594004673957877815246687)
        ·
          refine ⟨171891007010936816722870031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114594004673957877815246687 171891007010936816722870031)
          ·
            refine ⟨257836510516405225084305047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171891007010936816722870031 257836510516405225084305047)
            ·
              refine ⟨386754765774607837626457571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257836510516405225084305047 386754765774607837626457571)
              ·
                refine ⟨580132148661911756439686357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386754765774607837626457571 580132148661911756439686357)
                ·
                  refine ⟨13596847234263556791555149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 580132148661911756439686357 13596847234263556791555149)
                  ·
                    refine ⟨5098817712848833796833181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13596847234263556791555149 5098817712848833796833181)
                    ·
                      refine ⟨1912056642318312673812443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5098817712848833796833181 1912056642318312673812443)
                      ·
                        rfl

theorem cell23_3723717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_3723717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723717 prefixEnd_3723717 := by exact prefixLift 3723717
  have htrace : WordTrace (prefixWord ++ tailWord_3723717) baseStart_3723717 baseEnd_3723717 := by
    simpa [prefixWord, tailWord_3723717, baseEnd_3723717] using wordTrace_append hprefix tailTrace_3723717
  have hstable : (prefixWord ++ tailWord_3723717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723717).length < 2 ^ (prefixWord ++ tailWord_3723717).sum := by decide
  have hdescent : baseEnd_3723717 < baseStart_3723717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723746 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3723746 : Nat := 118140960795 + 3723746 * 2 ^ 59
def prefixEnd_3723746 : Nat := 4983230072969 + 3 ^ 40 * 3723746 * 2
def baseEnd_3723746 : Nat := 1912071533257293060349811

theorem tailTrace_3723746 : CollatzResearch.WordTrace tailWord_3723746 prefixEnd_3723746 1912071533257293060349811 := by
  unfold tailWord_3723746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954043591877920507533773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90544116245007788020090061 33954043591877920507533773)
  ·
    refine ⟨12732766346954220190325165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33954043591877920507533773 12732766346954220190325165)
    ·
      refine ⟨4774787380107832571371937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12732766346954220190325165 4774787380107832571371937)
      ·
        refine ⟨3581090535080874428528953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774787380107832571371937 3581090535080874428528953)
        ·
          refine ⟨2685817901310655821396715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3581090535080874428528953 2685817901310655821396715)
          ·
            refine ⟨4028726851965983732095073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685817901310655821396715 4028726851965983732095073)
            ·
              refine ⟨3021545138974487799071305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4028726851965983732095073 3021545138974487799071305)
              ·
                refine ⟨2266158854230865849303479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021545138974487799071305 2266158854230865849303479)
                ·
                  refine ⟨3399238281346298773955219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266158854230865849303479 3399238281346298773955219)
                  ·
                    refine ⟨5098857422019448160932829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3399238281346298773955219 5098857422019448160932829)
                    ·
                      refine ⟨1912071533257293060349811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5098857422019448160932829 1912071533257293060349811)
                      ·
                        rfl

theorem cell23_3723746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3723746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723746 prefixEnd_3723746 := by exact prefixLift 3723746
  have htrace : WordTrace (prefixWord ++ tailWord_3723746) baseStart_3723746 baseEnd_3723746 := by
    simpa [prefixWord, tailWord_3723746, baseEnd_3723746] using wordTrace_append hprefix tailTrace_3723746
  have hstable : (prefixWord ++ tailWord_3723746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723746).length < 2 ^ (prefixWord ++ tailWord_3723746).sum := by decide
  have hdescent : baseEnd_3723746 < baseStart_3723746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723752 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3723752 : Nat := 118140960795 + 3723752 * 2 ^ 59
def prefixEnd_3723752 : Nat := 4983230072969 + 3 ^ 40 * 3723752 * 2
def baseEnd_3723752 : Nat := 1912074614141220036874783

theorem tailTrace_3723752 : CollatzResearch.WordTrace tailWord_3723752 prefixEnd_3723752 1912074614141220036874783 := by
  unfold tailWord_3723752
  simp only [CollatzResearch.WordTrace]
  refine ⟨67908196602744972527426755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90544262136993296703235673 67908196602744972527426755)
  ·
    refine ⟨101862294904117458791140133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67908196602744972527426755 101862294904117458791140133)
    ·
      refine ⟨19099180294522023523338775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101862294904117458791140133 19099180294522023523338775)
      ·
        refine ⟨28648770441783035285008163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19099180294522023523338775 28648770441783035285008163)
        ·
          refine ⟨42973155662674552927512245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648770441783035285008163 42973155662674552927512245)
          ·
            refine ⟨4028733343375739336954273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42973155662674552927512245 4028733343375739336954273)
            ·
              refine ⟨3021550007531804502715705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4028733343375739336954273 3021550007531804502715705)
              ·
                refine ⟨2266162505648853377036779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021550007531804502715705 2266162505648853377036779)
                ·
                  refine ⟨3399243758473280065555169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266162505648853377036779 3399243758473280065555169)
                  ·
                    refine ⟨2549432818854960049166377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3399243758473280065555169 2549432818854960049166377)
                    ·
                      refine ⟨1912074614141220036874783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549432818854960049166377 1912074614141220036874783)
                      ·
                        rfl

theorem cell23_3723752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3723752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723752 prefixEnd_3723752 := by exact prefixLift 3723752
  have htrace : WordTrace (prefixWord ++ tailWord_3723752) baseStart_3723752 baseEnd_3723752 := by
    simpa [prefixWord, tailWord_3723752, baseEnd_3723752] using wordTrace_append hprefix tailTrace_3723752
  have hstable : (prefixWord ++ tailWord_3723752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723752).length < 2 ^ (prefixWord ++ tailWord_3723752).sum := by decide
  have hdescent : baseEnd_3723752 < baseStart_3723752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723797 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 9]
def baseStart_3723797 : Nat := 118140960795 + 3723797 * 2 ^ 59
def prefixEnd_3723797 : Nat := 4983230072969 + 3 ^ 40 * 3723797 * 2
def baseEnd_3723797 : Nat := 212455302307852484534675

theorem tailTrace_3723797 : CollatzResearch.WordTrace tailWord_3723797 prefixEnd_3723797 212455302307852484534675 := by
  unfold tailWord_3723797
  simp only [CollatzResearch.WordTrace]
  refine ⟨135818034490326917740241645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90545356326884611826827763 135818034490326917740241645)
  ·
    refine ⟨50931762933872594152590617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135818034490326917740241645 50931762933872594152590617)
    ·
      refine ⟨38198822200404445614442963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50931762933872594152590617 38198822200404445614442963)
      ·
        refine ⟨57298233300606668421664445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38198822200404445614442963 57298233300606668421664445)
        ·
          refine ⟨21486837487727500658124167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57298233300606668421664445 21486837487727500658124167)
          ·
            refine ⟨32230256231591250987186251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21486837487727500658124167 32230256231591250987186251)
            ·
              refine ⟨48345384347386876480779377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32230256231591250987186251 48345384347386876480779377)
              ·
                refine ⟨36259038260540157360584533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48345384347386876480779377 36259038260540157360584533)
                ·
                  refine ⟨212455302307852484534675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36259038260540157360584533 212455302307852484534675)
                  ·
                    rfl

theorem cell23_3723797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_3723797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723797 prefixEnd_3723797 := by exact prefixLift 3723797
  have htrace : WordTrace (prefixWord ++ tailWord_3723797) baseStart_3723797 baseEnd_3723797 := by
    simpa [prefixWord, tailWord_3723797, baseEnd_3723797] using wordTrace_append hprefix tailTrace_3723797
  have hstable : (prefixWord ++ tailWord_3723797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723797).length < 2 ^ (prefixWord ++ tailWord_3723797).sum := by decide
  have hdescent : baseEnd_3723797 < baseStart_3723797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723804 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3723804 : Nat := 118140960795 + 3723804 * 2 ^ 59
def prefixEnd_3723804 : Nat := 4983230072969 + 3 ^ 40 * 3723804 * 2
def baseEnd_3723804 : Nat := 1912101315135253833424543

theorem tailTrace_3723804 : CollatzResearch.WordTrace tailWord_3723804 prefixEnd_3723804 1912101315135253833424543 := by
  unfold tailWord_3723804
  simp only [CollatzResearch.WordTrace]
  refine ⟨67909144900650778967873233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90545526534201038623830977 67909144900650778967873233)
  ·
    refine ⟨50931858675488084225904925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67909144900650778967873233 50931858675488084225904925)
    ·
      refine ⟨19099447003308031584714347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50931858675488084225904925 19099447003308031584714347)
      ·
        refine ⟨28649170504962047377071521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19099447003308031584714347 28649170504962047377071521)
        ·
          refine ⟨21486877878721535532803641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28649170504962047377071521 21486877878721535532803641)
          ·
            refine ⟨16115158409041151649602731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21486877878721535532803641 16115158409041151649602731)
            ·
              refine ⟨24172737613561727474404097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115158409041151649602731 24172737613561727474404097)
              ·
                refine ⟨18129553210171295605803073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24172737613561727474404097 18129553210171295605803073)
                ·
                  refine ⟨13597164907628471704352305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18129553210171295605803073 13597164907628471704352305)
                  ·
                    refine ⟨10197873680721353778264229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13597164907628471704352305 10197873680721353778264229)
                    ·
                      refine ⟨1912101315135253833424543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10197873680721353778264229 1912101315135253833424543)
                      ·
                        rfl

theorem cell23_3723804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3723804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723804 prefixEnd_3723804 := by exact prefixLift 3723804
  have htrace : WordTrace (prefixWord ++ tailWord_3723804) baseStart_3723804 baseEnd_3723804 := by
    simpa [prefixWord, tailWord_3723804, baseEnd_3723804] using wordTrace_append hprefix tailTrace_3723804
  have hstable : (prefixWord ++ tailWord_3723804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723804).length < 2 ^ (prefixWord ++ tailWord_3723804).sum := by decide
  have hdescent : baseEnd_3723804 < baseStart_3723804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723824 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_3723824 : Nat := 118140960795 + 3723824 * 2 ^ 59
def prefixEnd_3723824 : Nat := 4983230072969 + 3 ^ 40 * 3723824 * 2
def baseEnd_3723824 : Nat := 1912111584748343755174451

theorem tailTrace_3723824 : CollatzResearch.WordTrace tailWord_3723824 prefixEnd_3723824 1912111584748343755174451 := by
  unfold tailWord_3723824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67909509630614550675737263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90546012840819400900983017 67909509630614550675737263)
  ·
    refine ⟨101864264445921826013605895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67909509630614550675737263 101864264445921826013605895)
    ·
      refine ⟨152796396668882739020408843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101864264445921826013605895 152796396668882739020408843)
      ·
        refine ⟨229194595003324108530613265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152796396668882739020408843 229194595003324108530613265)
        ·
          refine ⟨171895946252493081397959949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229194595003324108530613265 171895946252493081397959949)
          ·
            refine ⟨64460979844684905524234981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171895946252493081397959949 64460979844684905524234981)
            ·
              refine ⟨12086433720878419785794059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64460979844684905524234981 12086433720878419785794059)
              ·
                refine ⟨18129650581317629678691089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12086433720878419785794059 18129650581317629678691089)
                ·
                  refine ⟨13597237935988222259018317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18129650581317629678691089 13597237935988222259018317)
                  ·
                    refine ⟨5098964225995583347131869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13597237935988222259018317 5098964225995583347131869)
                    ·
                      refine ⟨1912111584748343755174451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5098964225995583347131869 1912111584748343755174451)
                      ·
                        rfl

theorem cell23_3723824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_3723824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723824 prefixEnd_3723824 := by exact prefixLift 3723824
  have htrace : WordTrace (prefixWord ++ tailWord_3723824) baseStart_3723824 baseEnd_3723824 := by
    simpa [prefixWord, tailWord_3723824, baseEnd_3723824] using wordTrace_append hprefix tailTrace_3723824
  have hstable : (prefixWord ++ tailWord_3723824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723824).length < 2 ^ (prefixWord ++ tailWord_3723824).sum := by decide
  have hdescent : baseEnd_3723824 < baseStart_3723824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723827 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 7]
def baseStart_3723827 : Nat := 118140960795 + 3723827 * 2 ^ 59
def prefixEnd_3723827 : Nat := 4983230072969 + 3 ^ 40 * 3723827 * 2
def baseEnd_3723827 : Nat := 637371041730102414478979

theorem tailTrace_3723827 : CollatzResearch.WordTrace tailWord_3723827 prefixEnd_3723827 637371041730102414478979 := by
  unfold tailWord_3723827
  simp only [CollatzResearch.WordTrace]
  refine ⟨135819128680218232863833735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90546085786812155242555823 135819128680218232863833735)
  ·
    refine ⟨203728693020327349295750603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135819128680218232863833735 203728693020327349295750603)
    ·
      refine ⟨305593039530491023943625905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203728693020327349295750603 305593039530491023943625905)
      ·
        refine ⟨229194779647868267957719429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305593039530491023943625905 229194779647868267957719429)
        ·
          refine ⟨42974021183975300242072393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229194779647868267957719429 42974021183975300242072393)
          ·
            refine ⟨32230515887981475181554295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42974021183975300242072393 32230515887981475181554295)
            ·
              refine ⟨48345773831972212772331443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32230515887981475181554295 48345773831972212772331443)
              ·
                refine ⟨72518660747958319158497165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48345773831972212772331443 72518660747958319158497165)
                ·
                  refine ⟨27194497780484369684436437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72518660747958319158497165 27194497780484369684436437)
                  ·
                    refine ⟨637371041730102414478979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27194497780484369684436437 637371041730102414478979)
                    ·
                      rfl

theorem cell23_3723827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_3723827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723827 prefixEnd_3723827 := by exact prefixLift 3723827
  have htrace : WordTrace (prefixWord ++ tailWord_3723827) baseStart_3723827 baseEnd_3723827 := by
    simpa [prefixWord, tailWord_3723827, baseEnd_3723827] using wordTrace_append hprefix tailTrace_3723827
  have hstable : (prefixWord ++ tailWord_3723827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723827).length < 2 ^ (prefixWord ++ tailWord_3723827).sum := by decide
  have hdescent : baseEnd_3723827 < baseStart_3723827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723864 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3723864 : Nat := 118140960795 + 3723864 * 2 ^ 59
def prefixEnd_3723864 : Nat := 4983230072969 + 3 ^ 40 * 3723864 * 2
def baseEnd_3723864 : Nat := 1912132123974523598674267

theorem tailTrace_3723864 : CollatzResearch.WordTrace tailWord_3723864 prefixEnd_3723864 1912132123974523598674267 := by
  unfold tailWord_3723864
  simp only [CollatzResearch.WordTrace]
  refine ⟨67910239090542094091465323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90546985454056125455287097 67910239090542094091465323)
  ·
    refine ⟨101865358635813141137197985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67910239090542094091465323 101865358635813141137197985)
    ·
      refine ⟨76399018976859855852898489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101865358635813141137197985 76399018976859855852898489)
      ·
        refine ⟨57299264232644891889673867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76399018976859855852898489 57299264232644891889673867)
        ·
          refine ⟨85948896348967337834510801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57299264232644891889673867 85948896348967337834510801)
          ·
            refine ⟨64461672261725503375883101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85948896348967337834510801 64461672261725503375883101)
            ·
              refine ⟨24173127098147063765956163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64461672261725503375883101 24173127098147063765956163)
              ·
                refine ⟨36259690647220595648934245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24173127098147063765956163 36259690647220595648934245)
                ·
                  refine ⟨6798691996353861684175171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36259690647220595648934245 6798691996353861684175171)
                  ·
                    refine ⟨10198037994530792526262757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6798691996353861684175171 10198037994530792526262757)
                    ·
                      refine ⟨1912132123974523598674267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10198037994530792526262757 1912132123974523598674267)
                      ·
                        rfl

theorem cell23_3723864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3723864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723864 prefixEnd_3723864 := by exact prefixLift 3723864
  have htrace : WordTrace (prefixWord ++ tailWord_3723864) baseStart_3723864 baseEnd_3723864 := by
    simpa [prefixWord, tailWord_3723864, baseEnd_3723864] using wordTrace_append hprefix tailTrace_3723864
  have hstable : (prefixWord ++ tailWord_3723864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723864).length < 2 ^ (prefixWord ++ tailWord_3723864).sum := by decide
  have hdescent : baseEnd_3723864 < baseStart_3723864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723884 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_3723884 : Nat := 118140960795 + 3723884 * 2 ^ 59
def prefixEnd_3723884 : Nat := 4983230072969 + 3 ^ 40 * 3723884 * 2
def baseEnd_3723884 : Nat := 1912142393587613520424175

theorem tailTrace_3723884 : CollatzResearch.WordTrace tailWord_3723884 prefixEnd_3723884 1912142393587613520424175 := by
  unfold tailWord_3723884
  simp only [CollatzResearch.WordTrace]
  refine ⟨67910603820505865799329353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90547471760674487732439137 67910603820505865799329353)
  ·
    refine ⟨50932952865379399349497015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67910603820505865799329353 50932952865379399349497015)
    ·
      refine ⟨76399429298069099024245523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50932952865379399349497015 76399429298069099024245523)
      ·
        refine ⟨114599143947103648536368285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76399429298069099024245523 114599143947103648536368285)
        ·
          refine ⟨42974678980163868201138107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114599143947103648536368285 42974678980163868201138107)
          ·
            refine ⟨64462018470245802301707161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42974678980163868201138107 64462018470245802301707161)
            ·
              refine ⟨48346513852684351726280371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64462018470245802301707161 48346513852684351726280371)
              ·
                refine ⟨72519770779026527589420557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48346513852684351726280371 72519770779026527589420557)
                ·
                  refine ⟨27194914042134947846032709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72519770779026527589420557 27194914042134947846032709)
                  ·
                    refine ⟨5099046382900302721131133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27194914042134947846032709 5099046382900302721131133)
                    ·
                      refine ⟨1912142393587613520424175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5099046382900302721131133 1912142393587613520424175)
                      ·
                        rfl

theorem cell23_3723884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_3723884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723884 prefixEnd_3723884 := by exact prefixLift 3723884
  have htrace : WordTrace (prefixWord ++ tailWord_3723884) baseStart_3723884 baseEnd_3723884 := by
    simpa [prefixWord, tailWord_3723884, baseEnd_3723884] using wordTrace_append hprefix tailTrace_3723884
  have hstable : (prefixWord ++ tailWord_3723884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723884).length < 2 ^ (prefixWord ++ tailWord_3723884).sum := by decide
  have hdescent : baseEnd_3723884 < baseStart_3723884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723941 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_3723941 : Nat := 118140960795 + 3723941 * 2 ^ 59
def prefixEnd_3723941 : Nat := 4983230072969 + 3 ^ 40 * 3723941 * 2
def baseEnd_3723941 : Nat := 1912171661984919797411413

theorem tailTrace_3723941 : CollatzResearch.WordTrace tailWord_3723941 prefixEnd_3723941 1912171661984919797411413 := by
  unfold tailWord_3723941
  simp only [CollatzResearch.WordTrace]
  refine ⟨135823286601805230333483677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90548857734536820222322451 135823286601805230333483677)
  ·
    refine ⟨50933732475676961375056379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135823286601805230333483677 50933732475676961375056379)
    ·
      refine ⟨76400598713515442062584569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50933732475676961375056379 76400598713515442062584569)
      ·
        refine ⟨57300449035136581546938427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76400598713515442062584569 57300449035136581546938427)
        ·
          refine ⟨85950673552704872320407641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57300449035136581546938427 85950673552704872320407641)
          ·
            refine ⟨64463005164528654240305731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85950673552704872320407641 64463005164528654240305731)
            ·
              refine ⟨96694507746792981360458597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64463005164528654240305731 96694507746792981360458597)
              ·
                refine ⟨18130220202523684005085987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96694507746792981360458597 18130220202523684005085987)
                ·
                  refine ⟨27195330303785526007628981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18130220202523684005085987 27195330303785526007628981)
                  ·
                    refine ⟨2549562215979893063215217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27195330303785526007628981 2549562215979893063215217)
                    ·
                      refine ⟨1912171661984919797411413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549562215979893063215217 1912171661984919797411413)
                      ·
                        rfl

theorem cell23_3723941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_3723941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723941 prefixEnd_3723941 := by exact prefixLift 3723941
  have htrace : WordTrace (prefixWord ++ tailWord_3723941) baseStart_3723941 baseEnd_3723941 := by
    simpa [prefixWord, tailWord_3723941, baseEnd_3723941] using wordTrace_append hprefix tailTrace_3723941
  have hstable : (prefixWord ++ tailWord_3723941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723941).length < 2 ^ (prefixWord ++ tailWord_3723941).sum := by decide
  have hdescent : baseEnd_3723941 < baseStart_3723941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723965 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3723965 : Nat := 118140960795 + 3723965 * 2 ^ 59
def prefixEnd_3723965 : Nat := 4983230072969 + 3 ^ 40 * 3723965 * 2
def baseEnd_3723965 : Nat := 1912183985520627703511303

theorem tailTrace_3723965 : CollatzResearch.WordTrace tailWord_3723965 prefixEnd_3723965 1912183985520627703511303 := by
  unfold tailWord_3723965
  simp only [CollatzResearch.WordTrace]
  refine ⟨135824161953718282432357349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90549441302478854954904899 135824161953718282432357349)
  ·
    refine ⟨25467030366322177956067003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135824161953718282432357349 25467030366322177956067003)
    ·
      refine ⟨38200545549483266934100505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467030366322177956067003 38200545549483266934100505)
      ·
        refine ⟨28650409162112450200575379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38200545549483266934100505 28650409162112450200575379)
        ·
          refine ⟨42975613743168675300863069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28650409162112450200575379 42975613743168675300863069)
          ·
            refine ⟨16115855153688253237823651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42975613743168675300863069 16115855153688253237823651)
            ·
              refine ⟨24173782730532379856735477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115855153688253237823651 24173782730532379856735477)
              ·
                refine ⟨2266292130987410611568951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24173782730532379856735477 2266292130987410611568951)
                ·
                  refine ⟨3399438196481115917353427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266292130987410611568951 3399438196481115917353427)
                  ·
                    refine ⟨5099157294721673876030141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3399438196481115917353427 5099157294721673876030141)
                    ·
                      refine ⟨1912183985520627703511303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5099157294721673876030141 1912183985520627703511303)
                      ·
                        rfl

theorem cell23_3723965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3723965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723965 prefixEnd_3723965 := by exact prefixLift 3723965
  have htrace : WordTrace (prefixWord ++ tailWord_3723965) baseStart_3723965 baseEnd_3723965 := by
    simpa [prefixWord, tailWord_3723965, baseEnd_3723965] using wordTrace_append hprefix tailTrace_3723965
  have hstable : (prefixWord ++ tailWord_3723965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723965).length < 2 ^ (prefixWord ++ tailWord_3723965).sum := by decide
  have hdescent : baseEnd_3723965 < baseStart_3723965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723968 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 1, 5]
def baseStart_3723968 : Nat := 118140960795 + 3723968 * 2 ^ 59
def prefixEnd_3723968 : Nat := 4983230072969 + 3 ^ 40 * 3723968 * 2
def baseEnd_3723968 : Nat := 637395175320863730591263

theorem tailTrace_3723968 : CollatzResearch.WordTrace tailWord_3723968 prefixEnd_3723968 637395175320863730591263 := by
  unfold tailWord_3723968
  simp only [CollatzResearch.WordTrace]
  refine ⟨67912135686353706972358279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90549514248471609296477705 67912135686353706972358279)
  ·
    refine ⟨101868203529530560458537419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67912135686353706972358279 101868203529530560458537419)
    ·
      refine ⟨152802305294295840687806129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101868203529530560458537419 152802305294295840687806129)
      ·
        refine ⟨114601728970721880515854597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152802305294295840687806129 114601728970721880515854597)
        ·
          refine ⟨21487824182010352596722737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114601728970721880515854597 21487824182010352596722737)
          ·
            refine ⟨16115868136507764447542053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21487824182010352596722737 16115868136507764447542053)
            ·
              refine ⟨3021725275595205833914135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16115868136507764447542053 3021725275595205833914135)
              ·
                refine ⟨4532587913392808750871203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021725275595205833914135 4532587913392808750871203)
                ·
                  refine ⟨6798881870089213126306805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532587913392808750871203 6798881870089213126306805)
                  ·
                    refine ⟨637395175320863730591263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6798881870089213126306805 637395175320863730591263)
                    ·
                      rfl

theorem cell23_3723968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_3723968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723968 prefixEnd_3723968 := by exact prefixLift 3723968
  have htrace : WordTrace (prefixWord ++ tailWord_3723968) baseStart_3723968 baseEnd_3723968 := by
    simpa [prefixWord, tailWord_3723968, baseEnd_3723968] using wordTrace_append hprefix tailTrace_3723968
  have hstable : (prefixWord ++ tailWord_3723968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723968).length < 2 ^ (prefixWord ++ tailWord_3723968).sum := by decide
  have hdescent : baseEnd_3723968 < baseStart_3723968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723991 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_3723991 : Nat := 118140960795 + 3723991 * 2 ^ 59
def prefixEnd_3723991 : Nat := 4983230072969 + 3 ^ 40 * 3723991 * 2
def baseEnd_3723991 : Nat := 1912197336017644601786183

theorem tailTrace_3723991 : CollatzResearch.WordTrace tailWord_3723991 prefixEnd_3723991 1912197336017644601786183 := by
  unfold tailWord_3723991
  simp only [CollatzResearch.WordTrace]
  refine ⟨135825110251624088872803827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90550073501082725915202551 135825110251624088872803827)
  ·
    refine ⟨203737665377436133309205741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135825110251624088872803827 203737665377436133309205741)
    ·
      refine ⟨76401624516538549990952153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203737665377436133309205741 76401624516538549990952153)
      ·
        refine ⟨57301218387403912493214115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76401624516538549990952153 57301218387403912493214115)
        ·
          refine ⟨85951827581105868739821173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57301218387403912493214115 85951827581105868739821173)
          ·
            refine ⟨8057983835728675194358235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85951827581105868739821173 8057983835728675194358235)
            ·
              refine ⟨12086975753593012791537353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057983835728675194358235 12086975753593012791537353)
              ·
                refine ⟨9065231815194759593653015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12086975753593012791537353 9065231815194759593653015)
                ·
                  refine ⟨13597847722792139390479523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9065231815194759593653015 13597847722792139390479523)
                  ·
                    refine ⟨20396771584188209085719285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13597847722792139390479523 20396771584188209085719285)
                    ·
                      refine ⟨1912197336017644601786183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20396771584188209085719285 1912197336017644601786183)
                      ·
                        rfl

theorem cell23_3723991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_3723991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723991 prefixEnd_3723991 := by exact prefixLift 3723991
  have htrace : WordTrace (prefixWord ++ tailWord_3723991) baseStart_3723991 baseEnd_3723991 := by
    simpa [prefixWord, tailWord_3723991, baseEnd_3723991] using wordTrace_append hprefix tailTrace_3723991
  have hstable : (prefixWord ++ tailWord_3723991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723991).length < 2 ^ (prefixWord ++ tailWord_3723991).sum := by decide
  have hdescent : baseEnd_3723991 < baseStart_3723991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723994 : List Nat := [3, 1, 1, 2, 2, 2, 2, 10]
def baseStart_3723994 : Nat := 118140960795 + 3723994 * 2 ^ 59
def prefixEnd_3723994 : Nat := 4983230072969 + 3 ^ 40 * 3723994 * 2
def baseEnd_3723994 : Nat := 70822180609615114446247

theorem tailTrace_3723994 : CollatzResearch.WordTrace tailWord_3723994 prefixEnd_3723994 70822180609615114446247 := by
  unfold tailWord_3723994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33956304917653305096290759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90550146447075480256775357 33956304917653305096290759)
  ·
    refine ⟨50934457376479957644436139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33956304917653305096290759 50934457376479957644436139)
    ·
      refine ⟨76401686064719936466654209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50934457376479957644436139 76401686064719936466654209)
      ·
        refine ⟨57301264548539952349990657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76401686064719936466654209 57301264548539952349990657)
        ·
          refine ⟨42975948411404964262492993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57301264548539952349990657 42975948411404964262492993)
          ·
            refine ⟨32231961308553723196869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42975948411404964262492993 32231961308553723196869745)
            ·
              refine ⟨24173970981415292397652309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32231961308553723196869745 24173970981415292397652309)
              ·
                refine ⟨70822180609615114446247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24173970981415292397652309 70822180609615114446247)
                ·
                  rfl

theorem cell23_3723994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_3723994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3723994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3723994 prefixEnd_3723994 := by exact prefixLift 3723994
  have htrace : WordTrace (prefixWord ++ tailWord_3723994) baseStart_3723994 baseEnd_3723994 := by
    simpa [prefixWord, tailWord_3723994, baseEnd_3723994] using wordTrace_append hprefix tailTrace_3723994
  have hstable : (prefixWord ++ tailWord_3723994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723994).length < 2 ^ (prefixWord ++ tailWord_3723994).sum := by decide
  have hdescent : baseEnd_3723994 < baseStart_3723994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724001 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3724001 : Nat := 118140960795 + 3724001 * 2 ^ 59
def prefixEnd_3724001 : Nat := 4983230072969 + 3 ^ 40 * 3724001 * 2
def baseEnd_3724001 : Nat := 1912202470824189562661137

theorem tailTrace_3724001 : CollatzResearch.WordTrace tailWord_3724001 prefixEnd_3724001 1912202470824189562661137 := by
  unfold tailWord_3724001
  simp only [CollatzResearch.WordTrace]
  refine ⟨135825474981587860580667857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90550316654391907053778571 135825474981587860580667857)
  ·
    refine ⟨101869106236190895435500893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135825474981587860580667857 101869106236190895435500893)
    ·
      refine ⟨38200914838571585788312835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101869106236190895435500893 38200914838571585788312835)
      ·
        refine ⟨57301372257857378682469253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38200914838571585788312835 57301372257857378682469253)
        ·
          refine ⟨10744007298348258502962985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57301372257857378682469253 10744007298348258502962985)
          ·
            refine ⟨8058005473761193877222239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10744007298348258502962985 8058005473761193877222239)
            ·
              refine ⟨12087008210641790815833359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058005473761193877222239 12087008210641790815833359)
              ·
                refine ⟨18130512315962686223750039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12087008210641790815833359 18130512315962686223750039)
                ·
                  refine ⟨27195768473944029335625059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18130512315962686223750039 27195768473944029335625059)
                  ·
                    refine ⟨40793652710916044003437589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27195768473944029335625059 40793652710916044003437589)
                    ·
                      refine ⟨1912202470824189562661137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40793652710916044003437589 1912202470824189562661137)
                      ·
                        rfl

theorem cell23_3724001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3724001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724001 prefixEnd_3724001 := by exact prefixLift 3724001
  have htrace : WordTrace (prefixWord ++ tailWord_3724001) baseStart_3724001 baseEnd_3724001 := by
    simpa [prefixWord, tailWord_3724001, baseEnd_3724001] using wordTrace_append hprefix tailTrace_3724001
  have hstable : (prefixWord ++ tailWord_3724001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724001).length < 2 ^ (prefixWord ++ tailWord_3724001).sum := by decide
  have hdescent : baseEnd_3724001 < baseStart_3724001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724005 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_3724005 : Nat := 118140960795 + 3724005 * 2 ^ 59
def prefixEnd_3724005 : Nat := 4983230072969 + 3 ^ 40 * 3724005 * 2
def baseEnd_3724005 : Nat := 1912204524746807547011119

theorem tailTrace_3724005 : CollatzResearch.WordTrace tailWord_3724005 prefixEnd_3724005 1912204524746807547011119 := by
  unfold tailWord_3724005
  simp only [CollatzResearch.WordTrace]
  refine ⟨135825620873573369263813469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90550413915715579509208979 135825620873573369263813469)
  ·
    refine ⟨50934607827590013473930051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135825620873573369263813469 50934607827590013473930051)
    ·
      refine ⟨76401911741385020210895077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50934607827590013473930051 76401911741385020210895077)
      ·
        refine ⟨14325358451509691289542827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76401911741385020210895077 14325358451509691289542827)
        ·
          refine ⟨21488037677264536934314241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14325358451509691289542827 21488037677264536934314241)
          ·
            refine ⟨16116028257948402700735681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21488037677264536934314241 16116028257948402700735681)
            ·
              refine ⟨12087021193461302025551761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16116028257948402700735681 12087021193461302025551761)
              ·
                refine ⟨9065265895095976519163821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12087021193461302025551761 9065265895095976519163821)
                ·
                  refine ⟨3399474710660991194686433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9065265895095976519163821 3399474710660991194686433)
                  ·
                    refine ⟨2549606032995743396014825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3399474710660991194686433 2549606032995743396014825)
                    ·
                      refine ⟨1912204524746807547011119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549606032995743396014825 1912204524746807547011119)
                      ·
                        rfl

theorem cell23_3724005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_3724005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724005 prefixEnd_3724005 := by exact prefixLift 3724005
  have htrace : WordTrace (prefixWord ++ tailWord_3724005) baseStart_3724005 baseEnd_3724005 := by
    simpa [prefixWord, tailWord_3724005, baseEnd_3724005] using wordTrace_append hprefix tailTrace_3724005
  have hstable : (prefixWord ++ tailWord_3724005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724005).length < 2 ^ (prefixWord ++ tailWord_3724005).sum := by decide
  have hdescent : baseEnd_3724005 < baseStart_3724005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724081 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3724081 : Nat := 118140960795 + 3724081 * 2 ^ 59
def prefixEnd_3724081 : Nat := 4983230072969 + 3 ^ 40 * 3724081 * 2
def baseEnd_3724081 : Nat := 1912243549276549249660769

theorem tailTrace_3724081 : CollatzResearch.WordTrace tailWord_3724081 prefixEnd_3724081 1912243549276549249660769 := by
  unfold tailWord_3724081
  simp only [CollatzResearch.WordTrace]
  refine ⟨135828392821298034243580097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90552261880865356162386731 135828392821298034243580097)
  ·
    refine ⟨101871294615973525682685073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135828392821298034243580097 101871294615973525682685073)
    ·
      refine ⟨76403470961980144262013805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101871294615973525682685073 76403470961980144262013805)
      ·
        refine ⟨28651301610742554098255177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76403470961980144262013805 28651301610742554098255177)
        ·
          refine ⟨21488476208056915573691383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28651301610742554098255177 21488476208056915573691383)
          ·
            refine ⟨32232714312085373360537075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21488476208056915573691383 32232714312085373360537075)
            ·
              refine ⟨48349071468128060040805613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32232714312085373360537075 48349071468128060040805613)
              ·
                refine ⟨18130901800548022515302105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48349071468128060040805613 18130901800548022515302105)
                ·
                  refine ⟨13598176350411016886476579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18130901800548022515302105 13598176350411016886476579)
                  ·
                    refine ⟨20397264525616525329714869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13598176350411016886476579 20397264525616525329714869)
                    ·
                      refine ⟨1912243549276549249660769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20397264525616525329714869 1912243549276549249660769)
                      ·
                        rfl

theorem cell23_3724081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3724081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724081 prefixEnd_3724081 := by exact prefixLift 3724081
  have htrace : WordTrace (prefixWord ++ tailWord_3724081) baseStart_3724081 baseEnd_3724081 := by
    simpa [prefixWord, tailWord_3724081, baseEnd_3724081] using wordTrace_append hprefix tailTrace_3724081
  have hstable : (prefixWord ++ tailWord_3724081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724081).length < 2 ^ (prefixWord ++ tailWord_3724081).sum := by decide
  have hdescent : baseEnd_3724081 < baseStart_3724081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724082 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_3724082 : Nat := 118140960795 + 3724082 * 2 ^ 59
def prefixEnd_3724082 : Nat := 4983230072969 + 3 ^ 40 * 3724082 * 2
def baseEnd_3724082 : Nat := 1912244062757203745748265

theorem tailTrace_3724082 : CollatzResearch.WordTrace tailWord_3724082 prefixEnd_3724082 1912244062757203745748265 := by
  unfold tailWord_3724082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33957107323573602853591625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90552286196196274276244333 33957107323573602853591625)
  ·
    refine ⟨25467830492680202140193719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33957107323573602853591625 25467830492680202140193719)
    ·
      refine ⟨38201745739020303210290579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467830492680202140193719 38201745739020303210290579)
      ·
        refine ⟨57302618608530454815435869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38201745739020303210290579 57302618608530454815435869)
        ·
          refine ⟨21488481978198920555788451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57302618608530454815435869 21488481978198920555788451)
          ·
            refine ⟨32232722967298380833682677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21488481978198920555788451 32232722967298380833682677)
            ·
              refine ⟨3021817778184223203157751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32232722967298380833682677 3021817778184223203157751)
              ·
                refine ⟨4532726667276334804736627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021817778184223203157751 4532726667276334804736627)
                ·
                  refine ⟨6799090000914502207104941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532726667276334804736627 6799090000914502207104941)
                  ·
                    refine ⟨2549658750342938327664353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6799090000914502207104941 2549658750342938327664353)
                    ·
                      refine ⟨1912244062757203745748265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549658750342938327664353 1912244062757203745748265)
                      ·
                        rfl

theorem cell23_3724082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_3724082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724082 prefixEnd_3724082 := by exact prefixLift 3724082
  have htrace : WordTrace (prefixWord ++ tailWord_3724082) baseStart_3724082 baseEnd_3724082 := by
    simpa [prefixWord, tailWord_3724082, baseEnd_3724082] using wordTrace_append hprefix tailTrace_3724082
  have hstable : (prefixWord ++ tailWord_3724082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724082).length < 2 ^ (prefixWord ++ tailWord_3724082).sum := by decide
  have hdescent : baseEnd_3724082 < baseStart_3724082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724108 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3724108 : Nat := 118140960795 + 3724108 * 2 ^ 59
def prefixEnd_3724108 : Nat := 4983230072969 + 3 ^ 40 * 3724108 * 2
def baseEnd_3724108 : Nat := 1912257413254220644023145

theorem tailTrace_3724108 : CollatzResearch.WordTrace tailWord_3724108 prefixEnd_3724108 1912257413254220644023145 := by
  unfold tailWord_3724108
  simp only [CollatzResearch.WordTrace]
  refine ⟨67914688796100108927406489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90552918394800145236541985 67914688796100108927406489)
  ·
    refine ⟨50936016597075081695554867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67914688796100108927406489 50936016597075081695554867)
    ·
      refine ⟨76404024895612622543332301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50936016597075081695554867 76404024895612622543332301)
      ·
        refine ⟨28651509335854733453749613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76404024895612622543332301 28651509335854733453749613)
        ·
          refine ⟨10744316000945525045156105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28651509335854733453749613 10744316000945525045156105)
          ·
            refine ⟨8058237000709143783867079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10744316000945525045156105 8058237000709143783867079)
            ·
              refine ⟨12087355501063715675800619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058237000709143783867079 12087355501063715675800619)
              ·
                refine ⟨18131033251595573513700929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12087355501063715675800619 18131033251595573513700929)
                ·
                  refine ⟨13598274938696680135275697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18131033251595573513700929 13598274938696680135275697)
                  ·
                    refine ⟨10198706204022510101456773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13598274938696680135275697 10198706204022510101456773)
                    ·
                      refine ⟨1912257413254220644023145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10198706204022510101456773 1912257413254220644023145)
                      ·
                        rfl

theorem cell23_3724108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3724108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724108 prefixEnd_3724108 := by exact prefixLift 3724108
  have htrace : WordTrace (prefixWord ++ tailWord_3724108) baseStart_3724108 baseEnd_3724108 := by
    simpa [prefixWord, tailWord_3724108, baseEnd_3724108] using wordTrace_append hprefix tailTrace_3724108
  have hstable : (prefixWord ++ tailWord_3724108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724108).length < 2 ^ (prefixWord ++ tailWord_3724108).sum := by decide
  have hdescent : baseEnd_3724108 < baseStart_3724108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724135 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 5]
def baseStart_3724135 : Nat := 118140960795 + 3724135 * 2 ^ 59
def prefixEnd_3724135 : Nat := 4983230072969 + 3 ^ 40 * 3724135 * 2
def baseEnd_3724135 : Nat := 212474586359099115376169

theorem tailTrace_3724135 : CollatzResearch.WordTrace tailWord_3724135 prefixEnd_3724135 212474586359099115376169 := by
  unfold tailWord_3724135
  simp only [CollatzResearch.WordTrace]
  refine ⟨135830362363102401466045859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90553574908734934310697239 135830362363102401466045859)
  ·
    refine ⟨203745543544653602199068789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135830362363102401466045859 203745543544653602199068789)
    ·
      refine ⟨19101144707311275206162699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203745543544653602199068789 19101144707311275206162699)
      ·
        refine ⟨28651717060966912809244049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19101144707311275206162699 28651717060966912809244049)
        ·
          refine ⟨21488787795725184606933037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28651717060966912809244049 21488787795725184606933037)
          ·
            refine ⟨8058295423396944227599889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21488787795725184606933037 8058295423396944227599889)
            ·
              refine ⟨6043721567547708170699917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8058295423396944227599889 6043721567547708170699917)
              ·
                refine ⟨2266395587830390564012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6043721567547708170699917 2266395587830390564012469)
                ·
                  refine ⟨212474586359099115376169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2266395587830390564012469 212474586359099115376169)
                  ·
                    rfl

theorem cell23_3724135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 5].length) (baseStart_3724135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724135 prefixEnd_3724135 := by exact prefixLift 3724135
  have htrace : WordTrace (prefixWord ++ tailWord_3724135) baseStart_3724135 baseEnd_3724135 := by
    simpa [prefixWord, tailWord_3724135, baseEnd_3724135] using wordTrace_append hprefix tailTrace_3724135
  have hstable : (prefixWord ++ tailWord_3724135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724135).length < 2 ^ (prefixWord ++ tailWord_3724135).sum := by decide
  have hdescent : baseEnd_3724135 < baseStart_3724135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724168 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3724168 : Nat := 118140960795 + 3724168 * 2 ^ 59
def prefixEnd_3724168 : Nat := 4983230072969 + 3 ^ 40 * 3724168 * 2
def baseEnd_3724168 : Nat := 1912288222093490409272869

theorem tailTrace_3724168 : CollatzResearch.WordTrace tailWord_3724168 prefixEnd_3724168 1912288222093490409272869 := by
  unfold tailWord_3724168
  simp only [CollatzResearch.WordTrace]
  refine ⟨67915782985991424050998579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90554377314655232067998105 67915782985991424050998579)
  ·
    refine ⟨101873674478987136076497869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67915782985991424050998579 101873674478987136076497869)
    ·
      refine ⟨38202627929620176028686701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101873674478987136076497869 38202627929620176028686701)
      ·
        refine ⟨14325985473607566010757513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38202627929620176028686701 14325985473607566010757513)
        ·
          refine ⟨10744489105205674508068135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14325985473607566010757513 10744489105205674508068135)
          ·
            refine ⟨16116733657808511762102203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10744489105205674508068135 16116733657808511762102203)
            ·
              refine ⟨24175100486712767643153305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16116733657808511762102203 24175100486712767643153305)
              ·
                refine ⟨18131325365034575732364979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24175100486712767643153305 18131325365034575732364979)
                ·
                  refine ⟨27196988047551863598547469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18131325365034575732364979 27196988047551863598547469)
                  ·
                    refine ⟨10198870517831948849455301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27196988047551863598547469 10198870517831948849455301)
                    ·
                      refine ⟨1912288222093490409272869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10198870517831948849455301 1912288222093490409272869)
                      ·
                        rfl

theorem cell23_3724168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3724168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724168 prefixEnd_3724168 := by exact prefixLift 3724168
  have htrace : WordTrace (prefixWord ++ tailWord_3724168) baseStart_3724168 baseEnd_3724168 := by
    simpa [prefixWord, tailWord_3724168, baseEnd_3724168] using wordTrace_append hprefix tailTrace_3724168
  have hstable : (prefixWord ++ tailWord_3724168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724168).length < 2 ^ (prefixWord ++ tailWord_3724168).sum := by decide
  have hdescent : baseEnd_3724168 < baseStart_3724168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724182 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3724182 : Nat := 118140960795 + 3724182 * 2 ^ 59
def prefixEnd_3724182 : Nat := 4983230072969 + 3 ^ 40 * 3724182 * 2
def baseEnd_3724182 : Nat := 637431803607551118165935

theorem tailTrace_3724182 : CollatzResearch.WordTrace tailWord_3724182 prefixEnd_3724182 637431803607551118165935 := by
  unfold tailWord_3724182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489504787120758030812925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90554717729288085662004533 8489504787120758030812925)
  ·
    refine ⟨3183564295170284261554847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8489504787120758030812925 3183564295170284261554847)
    ·
      refine ⟨4775346442755426392332271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183564295170284261554847 4775346442755426392332271)
      ·
        refine ⟨7163019664133139588498407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775346442755426392332271 7163019664133139588498407)
        ·
          refine ⟨10744529496199709382747611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163019664133139588498407 10744529496199709382747611)
          ·
            refine ⟨16116794244299564074121417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10744529496199709382747611 16116794244299564074121417)
            ·
              refine ⟨12087595683224673055591063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16116794244299564074121417 12087595683224673055591063)
              ·
                refine ⟨18131393524837009583386595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12087595683224673055591063 18131393524837009583386595)
                ·
                  refine ⟨27197090287255514375079893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18131393524837009583386595 27197090287255514375079893)
                  ·
                    refine ⟨637431803607551118165935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27197090287255514375079893 637431803607551118165935)
                    ·
                      rfl

theorem cell23_3724182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3724182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724182 prefixEnd_3724182 := by exact prefixLift 3724182
  have htrace : WordTrace (prefixWord ++ tailWord_3724182) baseStart_3724182 baseEnd_3724182 := by
    simpa [prefixWord, tailWord_3724182, baseEnd_3724182] using wordTrace_append hprefix tailTrace_3724182
  have hstable : (prefixWord ++ tailWord_3724182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724182).length < 2 ^ (prefixWord ++ tailWord_3724182).sum := by decide
  have hdescent : baseEnd_3724182 < baseStart_3724182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724211 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_3724211 : Nat := 118140960795 + 3724211 * 2 ^ 59
def prefixEnd_3724211 : Nat := 4983230072969 + 3 ^ 40 * 3724211 * 2
def baseEnd_3724211 : Nat := 1912310301761633741035171

theorem tailTrace_3724211 : CollatzResearch.WordTrace tailWord_3724211 prefixEnd_3724211 1912310301761633741035171 := by
  unfold tailWord_3724211
  simp only [CollatzResearch.WordTrace]
  refine ⟨135833134310827066445812487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90555422873884710963874991 135833134310827066445812487)
  ·
    refine ⟨203749701466240599668718731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135833134310827066445812487 203749701466240599668718731)
    ·
      refine ⟨305624552199360899503078097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203749701466240599668718731 305624552199360899503078097)
      ·
        refine ⟨229218414149520674627308573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305624552199360899503078097 229218414149520674627308573)
        ·
          refine ⟨85956905306070252985240715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229218414149520674627308573 85956905306070252985240715)
          ·
            refine ⟨128935357959105379477861073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85956905306070252985240715 128935357959105379477861073)
            ·
              refine ⟨96701518469329034608395805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128935357959105379477861073 96701518469329034608395805)
              ·
                refine ⟨36263069425998387978148427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96701518469329034608395805 36263069425998387978148427)
                ·
                  refine ⟨54394604138997581967222641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36263069425998387978148427 54394604138997581967222641)
                  ·
                    refine ⟨40795953104248186475416981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54394604138997581967222641 40795953104248186475416981)
                    ·
                      refine ⟨1912310301761633741035171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40795953104248186475416981 1912310301761633741035171)
                      ·
                        rfl

theorem cell23_3724211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_3724211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724211 prefixEnd_3724211 := by exact prefixLift 3724211
  have htrace : WordTrace (prefixWord ++ tailWord_3724211) baseStart_3724211 baseEnd_3724211 := by
    simpa [prefixWord, tailWord_3724211, baseEnd_3724211] using wordTrace_append hprefix tailTrace_3724211
  have hstable : (prefixWord ++ tailWord_3724211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724211).length < 2 ^ (prefixWord ++ tailWord_3724211).sum := by decide
  have hdescent : baseEnd_3724211 < baseStart_3724211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724295 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3724295 : Nat := 118140960795 + 3724295 * 2 ^ 59
def prefixEnd_3724295 : Nat := 4983230072969 + 3 ^ 40 * 3724295 * 2
def baseEnd_3724295 : Nat := 1912353434136611412384785

theorem tailTrace_3724295 : CollatzResearch.WordTrace tailWord_3724295 prefixEnd_3724295 1912353434136611412384785 := by
  unfold tailWord_3724295
  simp only [CollatzResearch.WordTrace]
  refine ⟨135836198042522748791870339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90557465361681832527913559 135836198042522748791870339)
  ·
    refine ⟨203754297063784123187805509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135836198042522748791870339 203754297063784123187805509)
    ·
      refine ⟨38203930699459523097713533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203754297063784123187805509 38203930699459523097713533)
      ·
        refine ⟨14326474012297321161642575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38203930699459523097713533 14326474012297321161642575)
        ·
          refine ⟨21489711018445981742463863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14326474012297321161642575 21489711018445981742463863)
          ·
            refine ⟨32234566527668972613695795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21489711018445981742463863 32234566527668972613695795)
            ·
              refine ⟨48351849791503458920543693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32234566527668972613695795 48351849791503458920543693)
              ·
                refine ⟨18131943671813797095203885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48351849791503458920543693 18131943671813797095203885)
                ·
                  refine ⟨6799478876930173910701457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18131943671813797095203885 6799478876930173910701457)
                  ·
                    refine ⟨5099609157697630433026093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799478876930173910701457 5099609157697630433026093)
                    ·
                      refine ⟨1912353434136611412384785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5099609157697630433026093 1912353434136611412384785)
                      ·
                        rfl

theorem cell23_3724295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3724295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724295 prefixEnd_3724295 := by exact prefixLift 3724295
  have htrace : WordTrace (prefixWord ++ tailWord_3724295) baseStart_3724295 baseEnd_3724295 := by
    simpa [prefixWord, tailWord_3724295, baseEnd_3724295] using wordTrace_append hprefix tailTrace_3724295
  have hstable : (prefixWord ++ tailWord_3724295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724295).length < 2 ^ (prefixWord ++ tailWord_3724295).sum := by decide
  have hdescent : baseEnd_3724295 < baseStart_3724295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724306 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3724306 : Nat := 118140960795 + 3724306 * 2 ^ 59
def prefixEnd_3724306 : Nat := 4983230072969 + 3 ^ 40 * 3724306 * 2
def baseEnd_3724306 : Nat := 637453027474603623115745

theorem tailTrace_3724306 : CollatzResearch.WordTrace tailWord_3724306 prefixEnd_3724306 637453027474603623115745 := by
  unfold tailWord_3724306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33959149811370724417630193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90557732830321931780347181 33959149811370724417630193)
  ·
    refine ⟨25469362358528043313222645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33959149811370724417630193 25469362358528043313222645)
    ·
      refine ⟨2387752721112004060614623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25469362358528043313222645 2387752721112004060614623)
      ·
        refine ⟨3581629081668006090921935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387752721112004060614623 3581629081668006090921935)
        ·
          refine ⟨5372443622502009136382903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581629081668006090921935 5372443622502009136382903)
          ·
            refine ⟨8058665433753013704574355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372443622502009136382903 8058665433753013704574355)
            ·
              refine ⟨12087998150629520556861533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058665433753013704574355 12087998150629520556861533)
              ·
                refine ⟨4532999306486070208823075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12087998150629520556861533 4532999306486070208823075)
                ·
                  refine ⟨6799498959729105313234613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532999306486070208823075 6799498959729105313234613)
                  ·
                    refine ⟨637453027474603623115745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6799498959729105313234613 637453027474603623115745)
                    ·
                      rfl

theorem cell23_3724306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3724306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724306 prefixEnd_3724306 := by exact prefixLift 3724306
  have htrace : WordTrace (prefixWord ++ tailWord_3724306) baseStart_3724306 baseEnd_3724306 := by
    simpa [prefixWord, tailWord_3724306, baseEnd_3724306] using wordTrace_append hprefix tailTrace_3724306
  have hstable : (prefixWord ++ tailWord_3724306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724306).length < 2 ^ (prefixWord ++ tailWord_3724306).sum := by decide
  have hdescent : baseEnd_3724306 < baseStart_3724306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724309 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_3724309 : Nat := 118140960795 + 3724309 * 2 ^ 59
def prefixEnd_3724309 : Nat := 4983230072969 + 3 ^ 40 * 3724309 * 2
def baseEnd_3724309 : Nat := 1912360622865774357609721

theorem tailTrace_3724309 : CollatzResearch.WordTrace tailWord_3724309 prefixEnd_3724309 1912360622865774357609721 := by
  unfold tailWord_3724309
  simp only [CollatzResearch.WordTrace]
  refine ⟨135836708664472029182879981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90557805776314686121919987 135836708664472029182879981)
  ·
    refine ⟨50938765749177010943579993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135836708664472029182879981 50938765749177010943579993)
    ·
      refine ⟨38204074311882758207684995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50938765749177010943579993 38204074311882758207684995)
      ·
        refine ⟨57306111467824137311527493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38204074311882758207684995 57306111467824137311527493)
        ·
          refine ⟨10744895900217025745911405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57306111467824137311527493 10744895900217025745911405)
          ·
            refine ⟨4029335962581384654716777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10744895900217025745911405 4029335962581384654716777)
            ·
              refine ⟨3022001971936038491037583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029335962581384654716777 3022001971936038491037583)
              ·
                refine ⟨4533002957904057736556375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022001971936038491037583 4533002957904057736556375)
                ·
                  refine ⟨6799504436856086604834563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533002957904057736556375 6799504436856086604834563)
                  ·
                    refine ⟨10199256655284129907251845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799504436856086604834563 10199256655284129907251845)
                    ·
                      refine ⟨1912360622865774357609721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10199256655284129907251845 1912360622865774357609721)
                      ·
                        rfl

theorem cell23_3724309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_3724309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724309 prefixEnd_3724309 := by exact prefixLift 3724309
  have htrace : WordTrace (prefixWord ++ tailWord_3724309) baseStart_3724309 baseEnd_3724309 := by
    simpa [prefixWord, tailWord_3724309, baseEnd_3724309] using wordTrace_append hprefix tailTrace_3724309
  have hstable : (prefixWord ++ tailWord_3724309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724309).length < 2 ^ (prefixWord ++ tailWord_3724309).sum := by decide
  have hdescent : baseEnd_3724309 < baseStart_3724309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724312 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3724312 : Nat := 118140960795 + 3724312 * 2 ^ 59
def prefixEnd_3724312 : Nat := 4983230072969 + 3 ^ 40 * 3724312 * 2
def baseEnd_3724312 : Nat := 1912362163307737845872207

theorem tailTrace_3724312 : CollatzResearch.WordTrace tailWord_3724312 prefixEnd_3724312 1912362163307737845872207 := by
  unfold tailWord_3724312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67918409041730580347619595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90557878722307440463492793 67918409041730580347619595)
  ·
    refine ⟨101877613562595870521429393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67918409041730580347619595 101877613562595870521429393)
    ·
      refine ⟨76408210171946902891072045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101877613562595870521429393 76408210171946902891072045)
      ·
        refine ⟨28653078814480088584152017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76408210171946902891072045 28653078814480088584152017)
        ·
          refine ⟨21489809110860066438114013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28653078814480088584152017 21489809110860066438114013)
          ·
            refine ⟨8058678416572524914292755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21489809110860066438114013 8058678416572524914292755)
            ·
              refine ⟨12088017624858787371439133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058678416572524914292755 12088017624858787371439133)
              ·
                refine ⟨4533006609322045264289675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12088017624858787371439133 4533006609322045264289675)
                ·
                  refine ⟨6799509913983067896434513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533006609322045264289675 6799509913983067896434513)
                  ·
                    refine ⟨5099632435487300922325885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799509913983067896434513 5099632435487300922325885)
                    ·
                      refine ⟨1912362163307737845872207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5099632435487300922325885 1912362163307737845872207)
                      ·
                        rfl

theorem cell23_3724312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3724312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724312 prefixEnd_3724312 := by exact prefixLift 3724312
  have htrace : WordTrace (prefixWord ++ tailWord_3724312) baseStart_3724312 baseEnd_3724312 := by
    simpa [prefixWord, tailWord_3724312, baseEnd_3724312] using wordTrace_append hprefix tailTrace_3724312
  have hstable : (prefixWord ++ tailWord_3724312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724312).length < 2 ^ (prefixWord ++ tailWord_3724312).sum := by decide
  have hdescent : baseEnd_3724312 < baseStart_3724312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724378 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3724378 : Nat := 118140960795 + 3724378 * 2 ^ 59
def prefixEnd_3724378 : Nat := 4983230072969 + 3 ^ 40 * 3724378 * 2
def baseEnd_3724378 : Nat := 1912396053030934587646903

theorem tailTrace_3724378 : CollatzResearch.WordTrace tailWord_3724378 prefixEnd_3724378 1912396053030934587646903 := by
  unfold tailWord_3724378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33959806325305513491785447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90559483534148035978094525 33959806325305513491785447)
  ·
    refine ⟨50939709487958270237678171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33959806325305513491785447 50939709487958270237678171)
    ·
      refine ⟨76409564231937405356517257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50939709487958270237678171 76409564231937405356517257)
      ·
        refine ⟨57307173173953054017387943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76409564231937405356517257 57307173173953054017387943)
        ·
          refine ⟨85960759760929581026081915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57307173173953054017387943 85960759760929581026081915)
          ·
            refine ⟨128941139641394371539122873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85960759760929581026081915 128941139641394371539122873)
            ·
              refine ⟨96705854731045778654342155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128941139641394371539122873 96705854731045778654342155)
              ·
                refine ⟨145058782096568667981513233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96705854731045778654342155 145058782096568667981513233)
                ·
                  refine ⟨108794086572426500986134925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145058782096568667981513233 108794086572426500986134925)
                  ·
                    refine ⟨40797782464659937869800597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108794086572426500986134925 40797782464659937869800597)
                    ·
                      refine ⟨1912396053030934587646903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40797782464659937869800597 1912396053030934587646903)
                      ·
                        rfl

theorem cell23_3724378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3724378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724378 prefixEnd_3724378 := by exact prefixLift 3724378
  have htrace : WordTrace (prefixWord ++ tailWord_3724378) baseStart_3724378 baseEnd_3724378 := by
    simpa [prefixWord, tailWord_3724378, baseEnd_3724378] using wordTrace_append hprefix tailTrace_3724378
  have hstable : (prefixWord ++ tailWord_3724378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724378).length < 2 ^ (prefixWord ++ tailWord_3724378).sum := by decide
  have hdescent : baseEnd_3724378 < baseStart_3724378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724399 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 2, 2, 2]
def baseStart_3724399 : Nat := 118140960795 + 3724399 * 2 ^ 59
def prefixEnd_3724399 : Nat := 4983230072969 + 3 ^ 40 * 3724399 * 2
def baseEnd_3724399 : Nat := 1912406836124679005484307

theorem tailTrace_3724399 : CollatzResearch.WordTrace tailWord_3724399 prefixEnd_3724399 1912406836124679005484307 := by
  unfold tailWord_3724399
  simp only [CollatzResearch.WordTrace]
  refine ⟨135839991234145974553656251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90559994156097316369104167 135839991234145974553656251)
  ·
    refine ⟨203759986851218961830484377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135839991234145974553656251 203759986851218961830484377)
    ·
      refine ⟨152819990138414221372863283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203759986851218961830484377 152819990138414221372863283)
      ·
        refine ⟨229229985207621332059294925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152819990138414221372863283 229229985207621332059294925)
        ·
          refine ⟨85961244452857999522235597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229229985207621332059294925 85961244452857999522235597)
          ·
            refine ⟨32235466669821749820838349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85961244452857999522235597 32235466669821749820838349)
            ·
              refine ⟨12088300001183156182814381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32235466669821749820838349 12088300001183156182814381)
              ·
                refine ⟨4533112500443683568555393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12088300001183156182814381 4533112500443683568555393)
                ·
                  refine ⟨3399834375332762676416545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533112500443683568555393 3399834375332762676416545)
                  ·
                    refine ⟨2549875781499572007312409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3399834375332762676416545 2549875781499572007312409)
                    ·
                      refine ⟨1912406836124679005484307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549875781499572007312409 1912406836124679005484307)
                      ·
                        rfl

theorem cell23_3724399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 2, 2].length) (baseStart_3724399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724399 prefixEnd_3724399 := by exact prefixLift 3724399
  have htrace : WordTrace (prefixWord ++ tailWord_3724399) baseStart_3724399 baseEnd_3724399 := by
    simpa [prefixWord, tailWord_3724399, baseEnd_3724399] using wordTrace_append hprefix tailTrace_3724399
  have hstable : (prefixWord ++ tailWord_3724399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724399).length < 2 ^ (prefixWord ++ tailWord_3724399).sum := by decide
  have hdescent : baseEnd_3724399 < baseStart_3724399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724435 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 2, 5]
def baseStart_3724435 : Nat := 118140960795 + 3724435 * 2 ^ 59
def prefixEnd_3724435 : Nat := 4983230072969 + 3 ^ 40 * 3724435 * 2
def baseEnd_3724435 : Nat := 637475107142746954878047

theorem tailTrace_3724435 : CollatzResearch.WordTrace tailWord_3724435 prefixEnd_3724435 637475107142746954878047 := by
  unfold tailWord_3724435
  simp only [CollatzResearch.WordTrace]
  refine ⟨135841304262015552701966759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90560869508010368467977839 135841304262015552701966759)
  ·
    refine ⟨203761956393023329052950139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135841304262015552701966759 203761956393023329052950139)
    ·
      refine ⟨305642934589534993579425209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203761956393023329052950139 305642934589534993579425209)
      ·
        refine ⟨229232200942151245184568907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305642934589534993579425209 229232200942151245184568907)
        ·
          refine ⟨343848301413226867776853361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229232200942151245184568907 343848301413226867776853361)
          ·
            refine ⟨257886226059920150832640021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343848301413226867776853361 257886226059920150832640021)
            ·
              refine ⟨12088416846558757070280001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 257886226059920150832640021 12088416846558757070280001)
              ·
                refine ⟨9066312634919067802710001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12088416846558757070280001 9066312634919067802710001)
                ·
                  refine ⟨6799734476189300852032501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066312634919067802710001 6799734476189300852032501)
                  ·
                    refine ⟨637475107142746954878047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6799734476189300852032501 637475107142746954878047)
                    ·
                      rfl

theorem cell23_3724435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 5].length) (baseStart_3724435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724435 prefixEnd_3724435 := by exact prefixLift 3724435
  have htrace : WordTrace (prefixWord ++ tailWord_3724435) baseStart_3724435 baseEnd_3724435 := by
    simpa [prefixWord, tailWord_3724435, baseEnd_3724435] using wordTrace_append hprefix tailTrace_3724435
  have hstable : (prefixWord ++ tailWord_3724435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724435).length < 2 ^ (prefixWord ++ tailWord_3724435).sum := by decide
  have hdescent : baseEnd_3724435 < baseStart_3724435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724439 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 5]
def baseStart_3724439 : Nat := 118140960795 + 3724439 * 2 ^ 59
def prefixEnd_3724439 : Nat := 4983230072969 + 3 ^ 40 * 3724439 * 2
def baseEnd_3724439 : Nat := 212491930594539872109347

theorem tailTrace_3724439 : CollatzResearch.WordTrace tailWord_3724439 prefixEnd_3724439 212491930594539872109347 := by
  unfold tailWord_3724439
  simp only [CollatzResearch.WordTrace]
  refine ⟨135841450154001061385112371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90560966769334040923408247 135841450154001061385112371)
  ·
    refine ⟨203762175231001592077668557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135841450154001061385112371 203762175231001592077668557)
    ·
      refine ⟨76410815711625597029125709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203762175231001592077668557 76410815711625597029125709)
      ·
        refine ⟨28654055891859598885922141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76410815711625597029125709 28654055891859598885922141)
        ·
          refine ⟨10745270959447349582220803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28654055891859598885922141 10745270959447349582220803)
          ·
            refine ⟨16117906439171024373331205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745270959447349582220803 16117906439171024373331205)
            ·
              refine ⟨3022107457344567069999601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16117906439171024373331205 3022107457344567069999601)
              ·
                refine ⟨2266580593008425302499701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022107457344567069999601 2266580593008425302499701)
                ·
                  refine ⟨212491930594539872109347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2266580593008425302499701 212491930594539872109347)
                  ·
                    rfl

theorem cell23_3724439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 5].length) (baseStart_3724439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724439 prefixEnd_3724439 := by exact prefixLift 3724439
  have htrace : WordTrace (prefixWord ++ tailWord_3724439) baseStart_3724439 baseEnd_3724439 := by
    simpa [prefixWord, tailWord_3724439, baseEnd_3724439] using wordTrace_append hprefix tailTrace_3724439
  have hstable : (prefixWord ++ tailWord_3724439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724439).length < 2 ^ (prefixWord ++ tailWord_3724439).sum := by decide
  have hdescent : baseEnd_3724439 < baseStart_3724439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724445 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3724445 : Nat := 118140960795 + 3724445 * 2 ^ 59
def prefixEnd_3724445 : Nat := 4983230072969 + 3 ^ 40 * 3724445 * 2
def baseEnd_3724445 : Nat := 1912430456234785825509095

theorem tailTrace_3724445 : CollatzResearch.WordTrace tailWord_3724445 prefixEnd_3724445 1912430456234785825509095 := by
  unfold tailWord_3724445
  simp only [CollatzResearch.WordTrace]
  refine ⟨135841668991979324409830789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90561112661319549606553859 135841668991979324409830789)
  ·
    refine ⟨25470312935996123326843273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135841668991979324409830789 25470312935996123326843273)
    ·
      refine ⟨19102734701997092495132455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25470312935996123326843273 19102734701997092495132455)
      ·
        refine ⟨28654102052995638742698683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19102734701997092495132455 28654102052995638742698683)
        ·
          refine ⟨42981153079493458114048025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28654102052995638742698683 42981153079493458114048025)
          ·
            refine ⟨32235864809620093585536019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42981153079493458114048025 32235864809620093585536019)
            ·
              refine ⟨48353797214430140378304029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32235864809620093585536019 48353797214430140378304029)
              ·
                refine ⟨18132673955411302641864011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48353797214430140378304029 18132673955411302641864011)
                ·
                  refine ⟨27199010933116953962796017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132673955411302641864011 27199010933116953962796017)
                  ·
                    refine ⟨20399258199837715472097013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27199010933116953962796017 20399258199837715472097013)
                    ·
                      refine ⟨1912430456234785825509095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20399258199837715472097013 1912430456234785825509095)
                      ·
                        rfl

theorem cell23_3724445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3724445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724445 prefixEnd_3724445 := by exact prefixLift 3724445
  have htrace : WordTrace (prefixWord ++ tailWord_3724445) baseStart_3724445 baseEnd_3724445 := by
    simpa [prefixWord, tailWord_3724445, baseEnd_3724445] using wordTrace_append hprefix tailTrace_3724445
  have hstable : (prefixWord ++ tailWord_3724445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724445).length < 2 ^ (prefixWord ++ tailWord_3724445).sum := by decide
  have hdescent : baseEnd_3724445 < baseStart_3724445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724495 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 6]
def baseStart_3724495 : Nat := 118140960795 + 3724495 * 2 ^ 59
def prefixEnd_3724495 : Nat := 4983230072969 + 3 ^ 40 * 3724495 * 2
def baseEnd_3724495 : Nat := 212495125585278958875985

theorem tailTrace_3724495 : CollatzResearch.WordTrace tailWord_3724495 prefixEnd_3724495 212495125585278958875985 := by
  unfold tailWord_3724495
  simp only [CollatzResearch.WordTrace]
  refine ⟨135843492641798182949150939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90562328427865455299433959 135843492641798182949150939)
  ·
    refine ⟨203765238962697274423726409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135843492641798182949150939 203765238962697274423726409)
    ·
      refine ⟨152823929222022955817794807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203765238962697274423726409 152823929222022955817794807)
      ·
        refine ⟨229235893833034433726692211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152823929222022955817794807 229235893833034433726692211)
        ·
          refine ⟨343853840749551650590038317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229235893833034433726692211 343853840749551650590038317)
          ·
            refine ⟨128945190281081868971264369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343853840749551650590038317 128945190281081868971264369)
            ·
              refine ⟨96708892710811401728448277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128945190281081868971264369 96708892710811401728448277)
              ·
                refine ⟨4533229345819284456021013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96708892710811401728448277 4533229345819284456021013)
                ·
                  refine ⟨212495125585278958875985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4533229345819284456021013 212495125585278958875985)
                  ·
                    rfl

theorem cell23_3724495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 6].length) (baseStart_3724495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724495 prefixEnd_3724495 := by exact prefixLift 3724495
  have htrace : WordTrace (prefixWord ++ tailWord_3724495) baseStart_3724495 baseEnd_3724495 := by
    simpa [prefixWord, tailWord_3724495, baseEnd_3724495] using wordTrace_append hprefix tailTrace_3724495
  have hstable : (prefixWord ++ tailWord_3724495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724495).length < 2 ^ (prefixWord ++ tailWord_3724495).sum := by decide
  have hdescent : baseEnd_3724495 < baseStart_3724495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724549 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_3724549 : Nat := 118140960795 + 3724549 * 2 ^ 59
def prefixEnd_3724549 : Nat := 4983230072969 + 3 ^ 40 * 3724549 * 2
def baseEnd_3724549 : Nat := 1912483858222853418608617

theorem tailTrace_3724549 : CollatzResearch.WordTrace tailWord_3724549 prefixEnd_3724549 1912483858222853418608617 := by
  unfold tailWord_3724549
  simp only [CollatzResearch.WordTrace]
  refine ⟨135845462183602550171616701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90563641455735033447744467 135845462183602550171616701)
  ·
    refine ⟨50942048318850956314356263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135845462183602550171616701 50942048318850956314356263)
    ·
      refine ⟨76413072478276434471534395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50942048318850956314356263 76413072478276434471534395)
      ·
        refine ⟨114619608717414651707301593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76413072478276434471534395 114619608717414651707301593)
        ·
          refine ⟨85964706538060988780476195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114619608717414651707301593 85964706538060988780476195)
          ·
            refine ⟨128947059807091483170714293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85964706538060988780476195 128947059807091483170714293)
            ·
              refine ⟨12088786856914826547254465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128947059807091483170714293 12088786856914826547254465)
              ·
                refine ⟨9066590142686119910440849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12088786856914826547254465 9066590142686119910440849)
                ·
                  refine ⟨6799942607014589932830637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066590142686119910440849 6799942607014589932830637)
                  ·
                    refine ⟨2549978477630471224811489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6799942607014589932830637 2549978477630471224811489)
                    ·
                      refine ⟨1912483858222853418608617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2549978477630471224811489 1912483858222853418608617)
                      ·
                        rfl

theorem cell23_3724549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_3724549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724549 prefixEnd_3724549 := by exact prefixLift 3724549
  have htrace : WordTrace (prefixWord ++ tailWord_3724549) baseStart_3724549 baseEnd_3724549 := by
    simpa [prefixWord, tailWord_3724549, baseEnd_3724549] using wordTrace_append hprefix tailTrace_3724549
  have hstable : (prefixWord ++ tailWord_3724549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724549).length < 2 ^ (prefixWord ++ tailWord_3724549).sum := by decide
  have hdescent : baseEnd_3724549 < baseStart_3724549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724556 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_3724556 : Nat := 118140960795 + 3724556 * 2 ^ 59
def prefixEnd_3724556 : Nat := 4983230072969 + 3 ^ 40 * 3724556 * 2
def baseEnd_3724556 : Nat := 1912487452587434891221085

theorem tailTrace_3724556 : CollatzResearch.WordTrace tailWord_3724556 prefixEnd_3724556 1912487452587434891221085 := by
  unfold tailWord_3724556
  simp only [CollatzResearch.WordTrace]
  refine ⟨67922858747288595183560761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90563811663051460244747681 67922858747288595183560761)
  ·
    refine ⟨50942144060466446387670571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67922858747288595183560761 50942144060466446387670571)
    ·
      refine ⟨76413216090699669581505857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50942144060466446387670571 76413216090699669581505857)
      ·
        refine ⟨57309912068024752186129393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76413216090699669581505857 57309912068024752186129393)
        ·
          refine ⟨42982434051018564139597045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57309912068024752186129393 42982434051018564139597045)
          ·
            refine ⟨4029603192282990388087223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42982434051018564139597045 4029603192282990388087223)
            ·
              refine ⟨6044404788424485582130835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029603192282990388087223 6044404788424485582130835)
              ·
                refine ⟨9066607182636728373196253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044404788424485582130835 9066607182636728373196253)
                ·
                  refine ⟨3399977693488773139948595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9066607182636728373196253 3399977693488773139948595)
                  ·
                    refine ⟨5099966540233159709922893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3399977693488773139948595 5099966540233159709922893)
                    ·
                      refine ⟨1912487452587434891221085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5099966540233159709922893 1912487452587434891221085)
                      ·
                        rfl

theorem cell23_3724556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_3724556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724556 prefixEnd_3724556 := by exact prefixLift 3724556
  have htrace : WordTrace (prefixWord ++ tailWord_3724556) baseStart_3724556 baseEnd_3724556 := by
    simpa [prefixWord, tailWord_3724556, baseEnd_3724556] using wordTrace_append hprefix tailTrace_3724556
  have hstable : (prefixWord ++ tailWord_3724556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724556).length < 2 ^ (prefixWord ++ tailWord_3724556).sum := by decide
  have hdescent : baseEnd_3724556 < baseStart_3724556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724576 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_3724576 : Nat := 118140960795 + 3724576 * 2 ^ 59
def prefixEnd_3724576 : Nat := 4983230072969 + 3 ^ 40 * 3724576 * 2
def baseEnd_3724576 : Nat := 637499240733508270990331

theorem tailTrace_3724576 : CollatzResearch.WordTrace tailWord_3724576 prefixEnd_3724576 637499240733508270990331 := by
  unfold tailWord_3724576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67923223477252366891424791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90564297969669822521899721 67923223477252366891424791)
  ·
    refine ⟨101884835215878550337137187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67923223477252366891424791 101884835215878550337137187)
    ·
      refine ⟨152827252823817825505705781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101884835215878550337137187 152827252823817825505705781)
      ·
        refine ⟨14327554952232921141159917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152827252823817825505705781 14327554952232921141159917)
        ·
          refine ⟨5372833107087345427934969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14327554952232921141159917 5372833107087345427934969)
          ·
            refine ⟨4029624830315509070951227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5372833107087345427934969 4029624830315509070951227)
            ·
              refine ⟨6044437245473263606426841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029624830315509070951227 6044437245473263606426841)
              ·
                refine ⟨4533327934104947704820131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044437245473263606426841 4533327934104947704820131)
                ·
                  refine ⟨6799991901157421557230197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533327934104947704820131 6799991901157421557230197)
                  ·
                    refine ⟨637499240733508270990331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6799991901157421557230197 637499240733508270990331)
                    ·
                      rfl

theorem cell23_3724576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_3724576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724576 prefixEnd_3724576 := by exact prefixLift 3724576
  have htrace : WordTrace (prefixWord ++ tailWord_3724576) baseStart_3724576 baseEnd_3724576 := by
    simpa [prefixWord, tailWord_3724576, baseEnd_3724576] using wordTrace_append hprefix tailTrace_3724576
  have hstable : (prefixWord ++ tailWord_3724576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724576).length < 2 ^ (prefixWord ++ tailWord_3724576).sum := by decide
  have hdescent : baseEnd_3724576 < baseStart_3724576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724579 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 4]
def baseStart_3724579 : Nat := 118140960795 + 3724579 * 2 ^ 59
def prefixEnd_3724579 : Nat := 4983230072969 + 3 ^ 40 * 3724579 * 2
def baseEnd_3724579 : Nat := 1912499262642488301233479

theorem tailTrace_3724579 : CollatzResearch.WordTrace tailWord_3724579 prefixEnd_3724579 1912499262642488301233479 := by
  unfold tailWord_3724579
  simp only [CollatzResearch.WordTrace]
  refine ⟨135846556373493865295208791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90564370915662576863472527 135846556373493865295208791)
  ·
    refine ⟨203769834560240797942813187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135846556373493865295208791 203769834560240797942813187)
    ·
      refine ⟨305654751840361196914219781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203769834560240797942813187 305654751840361196914219781)
      ·
        refine ⟨57310265970067724421416209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305654751840361196914219781 57310265970067724421416209)
        ·
          refine ⟨42982699477550793316062157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57310265970067724421416209 42982699477550793316062157)
          ·
            refine ⟨16118512304081547493523309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42982699477550793316062157 16118512304081547493523309)
            ·
              refine ⟨6044442114030580310071241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16118512304081547493523309 6044442114030580310071241)
              ·
                refine ⟨4533331585522935232553431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044442114030580310071241 4533331585522935232553431)
                ·
                  refine ⟨6799997378284402848830147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533331585522935232553431 6799997378284402848830147)
                  ·
                    refine ⟨10199996067426604273245221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799997378284402848830147 10199996067426604273245221)
                    ·
                      refine ⟨1912499262642488301233479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10199996067426604273245221 1912499262642488301233479)
                      ·
                        rfl

theorem cell23_3724579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_3724579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724579 prefixEnd_3724579 := by exact prefixLift 3724579
  have htrace : WordTrace (prefixWord ++ tailWord_3724579) baseStart_3724579 baseEnd_3724579 := by
    simpa [prefixWord, tailWord_3724579, baseEnd_3724579] using wordTrace_append hprefix tailTrace_3724579
  have hstable : (prefixWord ++ tailWord_3724579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724579).length < 2 ^ (prefixWord ++ tailWord_3724579).sum := by decide
  have hdescent : baseEnd_3724579 < baseStart_3724579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724589 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3724589 : Nat := 118140960795 + 3724589 * 2 ^ 59
def prefixEnd_3724589 : Nat := 4983230072969 + 3 ^ 40 * 3724589 * 2
def baseEnd_3724589 : Nat := 637501465816344420702811

theorem tailTrace_3724589 : CollatzResearch.WordTrace tailWord_3724589 prefixEnd_3724589 637501465816344420702811 := by
  unfold tailWord_3724589
  simp only [CollatzResearch.WordTrace]
  refine ⟨135846921103457637003072821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90564614068971758002048547 135846921103457637003072821)
  ·
    refine ⟨12735648853449153469038077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135846921103457637003072821 12735648853449153469038077)
    ·
      refine ⟨4775868320043432550889279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12735648853449153469038077 4775868320043432550889279)
      ·
        refine ⟨7163802480065148826333919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775868320043432550889279 7163802480065148826333919)
        ·
          refine ⟨10745703720097723239500879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163802480065148826333919 10745703720097723239500879)
          ·
            refine ⟨16118555580146584859251319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745703720097723239500879 16118555580146584859251319)
            ·
              refine ⟨24177833370219877288876979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16118555580146584859251319 24177833370219877288876979)
              ·
                refine ⟨36266750055329815933315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24177833370219877288876979 36266750055329815933315469)
                ·
                  refine ⟨13600031270748680974993301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36266750055329815933315469 13600031270748680974993301)
                  ·
                    refine ⟨637501465816344420702811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13600031270748680974993301 637501465816344420702811)
                    ·
                      rfl

theorem cell23_3724589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3724589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724589 prefixEnd_3724589 := by exact prefixLift 3724589
  have htrace : WordTrace (prefixWord ++ tailWord_3724589) baseStart_3724589 baseEnd_3724589 := by
    simpa [prefixWord, tailWord_3724589, baseEnd_3724589] using wordTrace_append hprefix tailTrace_3724589
  have hstable : (prefixWord ++ tailWord_3724589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724589).length < 2 ^ (prefixWord ++ tailWord_3724589).sum := by decide
  have hdescent : baseEnd_3724589 < baseStart_3724589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724592 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_3724592 : Nat := 118140960795 + 3724592 * 2 ^ 59
def prefixEnd_3724592 : Nat := 4983230072969 + 3 ^ 40 * 3724592 * 2
def baseEnd_3724592 : Nat := 1912505937890996750370919

theorem tailTrace_3724592 : CollatzResearch.WordTrace tailWord_3724592 prefixEnd_3724592 1912505937890996750370919 := by
  unfold tailWord_3724592
  simp only [CollatzResearch.WordTrace]
  refine ⟨67923515261223384257716015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90564687014964512343621353 67923515261223384257716015)
  ·
    refine ⟨101885272891835076386574023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67923515261223384257716015 101885272891835076386574023)
    ·
      refine ⟨152827909337752614579861035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101885272891835076386574023 152827909337752614579861035)
      ·
        refine ⟨229241864006628921869791553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152827909337752614579861035 229241864006628921869791553)
        ·
          refine ⟨171931398004971691402343665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229241864006628921869791553 171931398004971691402343665)
          ·
            refine ⟨128948548503728768551757749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171931398004971691402343665 128948548503728768551757749)
            ·
              refine ⟨12088926422224572051727289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128948548503728768551757749 12088926422224572051727289)
              ·
                refine ⟨9066694816668429038795467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12088926422224572051727289 9066694816668429038795467)
                ·
                  refine ⟨13600042225002643558193201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066694816668429038795467 13600042225002643558193201)
                  ·
                    refine ⟨10200031668751982668644901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13600042225002643558193201 10200031668751982668644901)
                    ·
                      refine ⟨1912505937890996750370919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10200031668751982668644901 1912505937890996750370919)
                      ·
                        rfl

theorem cell23_3724592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_3724592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724592 prefixEnd_3724592 := by exact prefixLift 3724592
  have htrace : WordTrace (prefixWord ++ tailWord_3724592) baseStart_3724592 baseEnd_3724592 := by
    simpa [prefixWord, tailWord_3724592, baseEnd_3724592] using wordTrace_append hprefix tailTrace_3724592
  have hstable : (prefixWord ++ tailWord_3724592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724592).length < 2 ^ (prefixWord ++ tailWord_3724592).sum := by decide
  have hdescent : baseEnd_3724592 < baseStart_3724592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724606 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3724606 : Nat := 118140960795 + 3724606 * 2 ^ 59
def prefixEnd_3724606 : Nat := 4983230072969 + 3 ^ 40 * 3724606 * 2
def baseEnd_3724606 : Nat := 637504375540053231865285

theorem tailTrace_3724606 : CollatzResearch.WordTrace tailWord_3724606 prefixEnd_3724606 637504375540053231865285 := by
  unfold tailWord_3724606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980942643049506113305209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90565027429597365937627781 16980942643049506113305209)
  ·
    refine ⟨12735706982287129584978907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16980942643049506113305209 12735706982287129584978907)
    ·
      refine ⟨19103560473430694377468361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12735706982287129584978907 19103560473430694377468361)
      ·
        refine ⟨14327670355073020783101271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19103560473430694377468361 14327670355073020783101271)
        ·
          refine ⟨21491505532609531174651907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327670355073020783101271 21491505532609531174651907)
          ·
            refine ⟨32237258298914296761977861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21491505532609531174651907 32237258298914296761977861)
            ·
              refine ⟨6044485931046430642870849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32237258298914296761977861 6044485931046430642870849)
              ·
                refine ⟨4533364448284822982153137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044485931046430642870849 4533364448284822982153137)
                ·
                  refine ⟨3400023336213617236614853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533364448284822982153137 3400023336213617236614853)
                  ·
                    refine ⟨637504375540053231865285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400023336213617236614853 637504375540053231865285)
                    ·
                      rfl

theorem cell23_3724606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3724606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724606 prefixEnd_3724606 := by exact prefixLift 3724606
  have htrace : WordTrace (prefixWord ++ tailWord_3724606) baseStart_3724606 baseEnd_3724606 := by
    simpa [prefixWord, tailWord_3724606, baseEnd_3724606] using wordTrace_append hprefix tailTrace_3724606
  have hstable : (prefixWord ++ tailWord_3724606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724606).length < 2 ^ (prefixWord ++ tailWord_3724606).sum := by decide
  have hdescent : baseEnd_3724606 < baseStart_3724606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724629 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3724629 : Nat := 118140960795 + 3724629 * 2 ^ 59
def prefixEnd_3724629 : Nat := 4983230072969 + 3 ^ 40 * 3724629 * 2
def baseEnd_3724629 : Nat := 1912524936675213105608249

theorem tailTrace_3724629 : CollatzResearch.WordTrace tailWord_3724629 prefixEnd_3724629 1912524936675213105608249 := by
  unfold tailWord_3724629
  simp only [CollatzResearch.WordTrace]
  refine ⟨135848380023312723834528941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90565586682208482556352627 135848380023312723834528941)
  ·
    refine ⟨50943142508742271437948353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135848380023312723834528941 50943142508742271437948353)
    ·
      refine ⟨38207356881556703578461265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50943142508742271437948353 38207356881556703578461265)
      ·
        refine ⟨28655517661167527683845949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38207356881556703578461265 28655517661167527683845949)
        ·
          refine ⟨10745819122937822881442231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28655517661167527683845949 10745819122937822881442231)
          ·
            refine ⟨16118728684406734322163347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745819122937822881442231 16118728684406734322163347)
            ·
              refine ⟨24178093026610101483245021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16118728684406734322163347 24178093026610101483245021)
              ·
                refine ⟨9066784884978788056216883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24178093026610101483245021 9066784884978788056216883)
                ·
                  refine ⟨13600177327468182084325325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066784884978788056216883 13600177327468182084325325)
                  ·
                    refine ⟨5100066497800568281621997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13600177327468182084325325 5100066497800568281621997)
                    ·
                      refine ⟨1912524936675213105608249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100066497800568281621997 1912524936675213105608249)
                      ·
                        rfl

theorem cell23_3724629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3724629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724629 prefixEnd_3724629 := by exact prefixLift 3724629
  have htrace : WordTrace (prefixWord ++ tailWord_3724629) baseStart_3724629 baseEnd_3724629 := by
    simpa [prefixWord, tailWord_3724629, baseEnd_3724629] using wordTrace_append hprefix tailTrace_3724629
  have hstable : (prefixWord ++ tailWord_3724629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724629).length < 2 ^ (prefixWord ++ tailWord_3724629).sum := by decide
  have hdescent : baseEnd_3724629 < baseStart_3724629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724650 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3724650 : Nat := 118140960795 + 3724650 * 2 ^ 59
def prefixEnd_3724650 : Nat := 4983230072969 + 3 ^ 40 * 3724650 * 2
def baseEnd_3724650 : Nat := 1912535719768957523445653

theorem tailTrace_3724650 : CollatzResearch.WordTrace tailWord_3724650 prefixEnd_3724650 1912535719768957523445653 := by
  unfold tailWord_3724650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33962286489059161105260851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90566097304157762947362269 33962286489059161105260851)
  ·
    refine ⟨50943429733588741657891277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33962286489059161105260851 50943429733588741657891277)
    ·
      refine ⟨19103786150095778121709229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50943429733588741657891277 19103786150095778121709229)
      ·
        refine ⟨7163919806285916795640961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19103786150095778121709229 7163919806285916795640961)
        ·
          refine ⟨5372939854714437596730721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7163919806285916795640961 5372939854714437596730721)
          ·
            refine ⟨4029704891035828197548041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5372939854714437596730721 4029704891035828197548041)
            ·
              refine ⟨3022278668276871148161031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029704891035828197548041 3022278668276871148161031)
              ·
                refine ⟨4533418002415306722241547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022278668276871148161031 4533418002415306722241547)
                ·
                  refine ⟨6800127003622960083362321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533418002415306722241547 6800127003622960083362321)
                  ·
                    refine ⟨5100095252717220062521741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800127003622960083362321 5100095252717220062521741)
                    ·
                      refine ⟨1912535719768957523445653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100095252717220062521741 1912535719768957523445653)
                      ·
                        rfl

theorem cell23_3724650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3724650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724650 prefixEnd_3724650 := by exact prefixLift 3724650
  have htrace : WordTrace (prefixWord ++ tailWord_3724650) baseStart_3724650 baseEnd_3724650 := by
    simpa [prefixWord, tailWord_3724650, baseEnd_3724650] using wordTrace_append hprefix tailTrace_3724650
  have hstable : (prefixWord ++ tailWord_3724650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724650).length < 2 ^ (prefixWord ++ tailWord_3724650).sum := by decide
  have hdescent : baseEnd_3724650 < baseStart_3724650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724656 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2]
def baseStart_3724656 : Nat := 118140960795 + 3724656 * 2 ^ 59
def prefixEnd_3724656 : Nat := 4983230072969 + 3 ^ 40 * 3724656 * 2
def baseEnd_3724656 : Nat := 1912538800652884499970625

theorem tailTrace_3724656 : CollatzResearch.WordTrace tailWord_3724656 prefixEnd_3724656 1912538800652884499970625 := by
  unfold tailWord_3724656
  simp only [CollatzResearch.WordTrace]
  refine ⟨67924682397107453722880911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90566243196143271630507881 67924682397107453722880911)
  ·
    refine ⟨101887023595661180584321367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67924682397107453722880911 101887023595661180584321367)
    ·
      refine ⟨152830535393491770876482051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101887023595661180584321367 152830535393491770876482051)
      ·
        refine ⟨229245803090237656314723077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152830535393491770876482051 229245803090237656314723077)
        ·
          refine ⟨42983588079419560559010577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229245803090237656314723077 42983588079419560559010577)
          ·
            refine ⟨32237691059564670419257933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42983588079419560559010577 32237691059564670419257933)
            ·
              refine ⟨12089134147336751407221725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32237691059564670419257933 12089134147336751407221725)
              ·
                refine ⟨4533425305251281777708147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12089134147336751407221725 4533425305251281777708147)
                ·
                  refine ⟨6800137957876922666562221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533425305251281777708147 6800137957876922666562221)
                  ·
                    refine ⟨2550051734203845999960833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6800137957876922666562221 2550051734203845999960833)
                    ·
                      refine ⟨1912538800652884499970625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550051734203845999960833 1912538800652884499970625)
                      ·
                        rfl

theorem cell23_3724656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2].length) (baseStart_3724656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724656 prefixEnd_3724656 := by exact prefixLift 3724656
  have htrace : WordTrace (prefixWord ++ tailWord_3724656) baseStart_3724656 baseEnd_3724656 := by
    simpa [prefixWord, tailWord_3724656, baseEnd_3724656] using wordTrace_append hprefix tailTrace_3724656
  have hstable : (prefixWord ++ tailWord_3724656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724656).length < 2 ^ (prefixWord ++ tailWord_3724656).sum := by decide
  have hdescent : baseEnd_3724656 < baseStart_3724656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724672 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_3724672 : Nat := 118140960795 + 3724672 * 2 ^ 59
def prefixEnd_3724672 : Nat := 4983230072969 + 3 ^ 40 * 3724672 * 2
def baseEnd_3724672 : Nat := 1912547016343356437370551

theorem tailTrace_3724672 : CollatzResearch.WordTrace tailWord_3724672 prefixEnd_3724672 1912547016343356437370551 := by
  unfold tailWord_3724672
  simp only [CollatzResearch.WordTrace]
  refine ⟨67924974181078471089172135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90566632241437961452229513 67924974181078471089172135)
  ·
    refine ⟨101887461271617706633758203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67924974181078471089172135 101887461271617706633758203)
    ·
      refine ⟨152831191907426559950637305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101887461271617706633758203 152831191907426559950637305)
      ·
        refine ⟨114623393930569919962977979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152831191907426559950637305 114623393930569919962977979)
        ·
          refine ⟨171935090895854879944466969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114623393930569919962977979 171935090895854879944466969)
          ·
            refine ⟨128951318171891159958350227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171935090895854879944466969 128951318171891159958350227)
            ·
              refine ⟨193426977257836739937525341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128951318171891159958350227 193426977257836739937525341)
              ·
                refine ⟨72535116471688777476572003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193426977257836739937525341 72535116471688777476572003)
                ·
                  refine ⟨108802674707533166214858005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72535116471688777476572003 108802674707533166214858005)
                  ·
                    refine ⟨5100125376915617166321469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108802674707533166214858005 5100125376915617166321469)
                    ·
                      refine ⟨1912547016343356437370551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100125376915617166321469 1912547016343356437370551)
                      ·
                        rfl

theorem cell23_3724672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_3724672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724672 prefixEnd_3724672 := by exact prefixLift 3724672
  have htrace : WordTrace (prefixWord ++ tailWord_3724672) baseStart_3724672 baseEnd_3724672 := by
    simpa [prefixWord, tailWord_3724672, baseEnd_3724672] using wordTrace_append hprefix tailTrace_3724672
  have hstable : (prefixWord ++ tailWord_3724672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724672).length < 2 ^ (prefixWord ++ tailWord_3724672).sum := by decide
  have hdescent : baseEnd_3724672 < baseStart_3724672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724709 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 5]
def baseStart_3724709 : Nat := 118140960795 + 3724709 * 2 ^ 59
def prefixEnd_3724709 : Nat := 4983230072969 + 3 ^ 40 * 3724709 * 2
def baseEnd_3724709 : Nat := 212507335014174754734209

theorem tailTrace_3724709 : CollatzResearch.WordTrace tailWord_3724709 prefixEnd_3724709 212507335014174754734209 := by
  unfold tailWord_3724709
  simp only [CollatzResearch.WordTrace]
  refine ⟨135851297863022897497441181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90567531908681931664960787 135851297863022897497441181)
  ·
    refine ⟨50944236698633586561540443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135851297863022897497441181 50944236698633586561540443)
    ·
      refine ⟨76416355047950379842310665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50944236698633586561540443 76416355047950379842310665)
      ·
        refine ⟨57312266285962784881732999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76416355047950379842310665 57312266285962784881732999)
        ·
          refine ⟨85968399428944177322599499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57312266285962784881732999 85968399428944177322599499)
          ·
            refine ⟨128952599143416265983899249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85968399428944177322599499 128952599143416265983899249)
            ·
              refine ⟨96714449357562199487924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128952599143416265983899249 96714449357562199487924437)
              ·
                refine ⟨2266744906817864050498229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96714449357562199487924437 2266744906817864050498229)
                ·
                  refine ⟨212507335014174754734209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2266744906817864050498229 212507335014174754734209)
                  ·
                    rfl

theorem cell23_3724709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_3724709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724709 prefixEnd_3724709 := by exact prefixLift 3724709
  have htrace : WordTrace (prefixWord ++ tailWord_3724709) baseStart_3724709 baseEnd_3724709 := by
    simpa [prefixWord, tailWord_3724709, baseEnd_3724709] using wordTrace_append hprefix tailTrace_3724709
  have hstable : (prefixWord ++ tailWord_3724709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724709).length < 2 ^ (prefixWord ++ tailWord_3724709).sum := by decide
  have hdescent : baseEnd_3724709 < baseStart_3724709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724722 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3724722 : Nat := 118140960795 + 3724722 * 2 ^ 59
def prefixEnd_3724722 : Nat := 4983230072969 + 3 ^ 40 * 3724722 * 2
def baseEnd_3724722 : Nat := 637524230125360413915107

theorem tailTrace_3724722 : CollatzResearch.WordTrace tailWord_3724722 prefixEnd_3724722 637524230125360413915107 := by
  unfold tailWord_3724722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33962943002993950179416105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90567848007983867145109613 33962943002993950179416105)
  ·
    refine ⟨25472207252245462634562079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33962943002993950179416105 25472207252245462634562079)
    ·
      refine ⟨38208310878368193951843119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25472207252245462634562079 38208310878368193951843119)
      ·
        refine ⟨57312466317552290927764679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38208310878368193951843119 57312466317552290927764679)
        ·
          refine ⟨85968699476328436391647019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57312466317552290927764679 85968699476328436391647019)
          ·
            refine ⟨128953049214492654587470529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85968699476328436391647019 128953049214492654587470529)
            ·
              refine ⟨96714786910869490940602897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128953049214492654587470529 96714786910869490940602897)
              ·
                refine ⟨72536090183152118205452173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96714786910869490940602897 72536090183152118205452173)
                ·
                  refine ⟨27201033818682044327044565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72536090183152118205452173 27201033818682044327044565)
                  ·
                    refine ⟨637524230125360413915107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27201033818682044327044565 637524230125360413915107)
                    ·
                      rfl

theorem cell23_3724722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3724722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724722 prefixEnd_3724722 := by exact prefixLift 3724722
  have htrace : WordTrace (prefixWord ++ tailWord_3724722) baseStart_3724722 baseEnd_3724722 := by
    simpa [prefixWord, tailWord_3724722, baseEnd_3724722] using wordTrace_append hprefix tailTrace_3724722
  have hstable : (prefixWord ++ tailWord_3724722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724722).length < 2 ^ (prefixWord ++ tailWord_3724722).sum := by decide
  have hdescent : baseEnd_3724722 < baseStart_3724722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724776 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3724776 : Nat := 118140960795 + 3724776 * 2 ^ 59
def prefixEnd_3724776 : Nat := 4983230072969 + 3 ^ 40 * 3724776 * 2
def baseEnd_3724776 : Nat := 1912600418331424030470073

theorem tailTrace_3724776 : CollatzResearch.WordTrace tailWord_3724776 prefixEnd_3724776 1912600418331424030470073 := by
  unfold tailWord_3724776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67926870776890083970065091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90569161035853445293420121 67926870776890083970065091)
  ·
    refine ⟨101890306165335125955097637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67926870776890083970065091 101890306165335125955097637)
    ·
      refine ⟨19104432406000336116580807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101890306165335125955097637 19104432406000336116580807)
      ·
        refine ⟨28656648609000504174871211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19104432406000336116580807 28656648609000504174871211)
        ·
          refine ⟨42984972913500756262306817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28656648609000504174871211 42984972913500756262306817)
          ·
            refine ⟨32238729685125567196730113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42984972913500756262306817 32238729685125567196730113)
            ·
              refine ⟨24179047263844175397547585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32238729685125567196730113 24179047263844175397547585)
              ·
                refine ⟨18134285447883131548160689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24179047263844175397547585 18134285447883131548160689)
                ·
                  refine ⟨13600714085912348661120517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18134285447883131548160689 13600714085912348661120517)
                  ·
                    refine ⟨2550133891108565373960097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13600714085912348661120517 2550133891108565373960097)
                    ·
                      refine ⟨1912600418331424030470073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550133891108565373960097 1912600418331424030470073)
                      ·
                        rfl

theorem cell23_3724776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3724776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724776 prefixEnd_3724776 := by exact prefixLift 3724776
  have htrace : WordTrace (prefixWord ++ tailWord_3724776) baseStart_3724776 baseEnd_3724776 := by
    simpa [prefixWord, tailWord_3724776, baseEnd_3724776] using wordTrace_append hprefix tailTrace_3724776
  have hstable : (prefixWord ++ tailWord_3724776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724776).length < 2 ^ (prefixWord ++ tailWord_3724776).sum := by decide
  have hdescent : baseEnd_3724776 < baseStart_3724776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724779 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3]
def baseStart_3724779 : Nat := 118140960795 + 3724779 * 2 ^ 59
def prefixEnd_3724779 : Nat := 4983230072969 + 3 ^ 40 * 3724779 * 2
def baseEnd_3724779 : Nat := 1912601958773387518732559

theorem tailTrace_3724779 : CollatzResearch.WordTrace tailWord_3724779 prefixEnd_3724779 1912601958773387518732559 := by
  unfold tailWord_3724779
  simp only [CollatzResearch.WordTrace]
  refine ⟨135853850972769299452489391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90569233981846199634992927 135853850972769299452489391)
  ·
    refine ⟨203780776459153949178734087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135853850972769299452489391 203780776459153949178734087)
    ·
      refine ⟨305671164688730923768101131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203780776459153949178734087 305671164688730923768101131)
      ·
        refine ⟨458506747033096385652151697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305671164688730923768101131 458506747033096385652151697)
        ·
          refine ⟨343880060274822289239113773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458506747033096385652151697 343880060274822289239113773)
          ·
            refine ⟨128955022603058358464667665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343880060274822289239113773 128955022603058358464667665)
            ·
              refine ⟨96716266952293768848500749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128955022603058358464667665 96716266952293768848500749)
              ·
                refine ⟨36268600107110163318187781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96716266952293768848500749 36268600107110163318187781)
                ·
                  refine ⟨6800362520083155622160209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36268600107110163318187781 6800362520083155622160209)
                  ·
                    refine ⟨5100271890062366716620157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800362520083155622160209 5100271890062366716620157)
                    ·
                      refine ⟨1912601958773387518732559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100271890062366716620157 1912601958773387518732559)
                      ·
                        rfl

theorem cell23_3724779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 3].length) (baseStart_3724779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724779 prefixEnd_3724779 := by exact prefixLift 3724779
  have htrace : WordTrace (prefixWord ++ tailWord_3724779) baseStart_3724779 baseEnd_3724779 := by
    simpa [prefixWord, tailWord_3724779, baseEnd_3724779] using wordTrace_append hprefix tailTrace_3724779
  have hstable : (prefixWord ++ tailWord_3724779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724779).length < 2 ^ (prefixWord ++ tailWord_3724779).sum := by decide
  have hdescent : baseEnd_3724779 < baseStart_3724779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724826 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_3724826 : Nat := 118140960795 + 3724826 * 2 ^ 59
def prefixEnd_3724826 : Nat := 4983230072969 + 3 ^ 40 * 3724826 * 2
def baseEnd_3724826 : Nat := 1912626092364148834844843

theorem tailTrace_3724826 : CollatzResearch.WordTrace tailWord_3724826 prefixEnd_3724826 1912626092364148834844843 := by
  unfold tailWord_3724826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963891300899756619862583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90570376802399350986300221 33963891300899756619862583)
  ·
    refine ⟨50945836951349634929793875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33963891300899756619862583 50945836951349634929793875)
    ·
      refine ⟨76418755427024452394690813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50945836951349634929793875 76418755427024452394690813)
      ·
        refine ⟨28657033285134169648009055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76418755427024452394690813 28657033285134169648009055)
        ·
          refine ⟨42985549927701254472013583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28657033285134169648009055 42985549927701254472013583)
          ·
            refine ⟨64478324891551881708020375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42985549927701254472013583 64478324891551881708020375)
            ·
              refine ⟨96717487337327822562030563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64478324891551881708020375 96717487337327822562030563)
              ·
                refine ⟨145076231005991733843045845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96717487337327822562030563 145076231005991733843045845)
                ·
                  refine ⟨3400224164202931261946387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145076231005991733843045845 3400224164202931261946387)
                  ·
                    refine ⟨5100336246304396892919581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3400224164202931261946387 5100336246304396892919581)
                    ·
                      refine ⟨1912626092364148834844843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100336246304396892919581 1912626092364148834844843)
                      ·
                        rfl

theorem cell23_3724826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_3724826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724826 prefixEnd_3724826 := by exact prefixLift 3724826
  have htrace : WordTrace (prefixWord ++ tailWord_3724826) baseStart_3724826 baseEnd_3724826 := by
    simpa [prefixWord, tailWord_3724826, baseEnd_3724826] using wordTrace_append hprefix tailTrace_3724826
  have hstable : (prefixWord ++ tailWord_3724826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724826).length < 2 ^ (prefixWord ++ tailWord_3724826).sum := by decide
  have hdescent : baseEnd_3724826 < baseStart_3724826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724869 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3724869 : Nat := 118140960795 + 3724869 * 2 ^ 59
def prefixEnd_3724869 : Nat := 4983230072969 + 3 ^ 40 * 3724869 * 2
def baseEnd_3724869 : Nat := 1912648172032292166607145

theorem tailTrace_3724869 : CollatzResearch.WordTrace tailWord_3724869 prefixEnd_3724869 1912648172032292166607145 := by
  unfold tailWord_3724869
  simp only [CollatzResearch.WordTrace]
  refine ⟨135857133542443244823265661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90571422361628829882177107 135857133542443244823265661)
  ·
    refine ⟨50946425078416216808724623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135857133542443244823265661 50946425078416216808724623)
    ·
      refine ⟨76419637617624325213086935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946425078416216808724623 76419637617624325213086935)
      ·
        refine ⟨114629456426436487819630403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76419637617624325213086935 114629456426436487819630403)
        ·
          refine ⟨171944184639654731729445605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114629456426436487819630403 171944184639654731729445605)
          ·
            refine ⟨32239534619935262199271051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171944184639654731729445605 32239534619935262199271051)
            ·
              refine ⟨48359301929902893298906577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32239534619935262199271051 48359301929902893298906577)
              ·
                refine ⟨36269476447427169974179933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48359301929902893298906577 36269476447427169974179933)
                ·
                  refine ⟨13601053667785188740317475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36269476447427169974179933 13601053667785188740317475)
                  ·
                    refine ⟨20401580501677783110476213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13601053667785188740317475 20401580501677783110476213)
                    ·
                      refine ⟨1912648172032292166607145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20401580501677783110476213 1912648172032292166607145)
                      ·
                        rfl

theorem cell23_3724869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3724869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724869 prefixEnd_3724869 := by exact prefixLift 3724869
  have htrace : WordTrace (prefixWord ++ tailWord_3724869) baseStart_3724869 baseEnd_3724869 := by
    simpa [prefixWord, tailWord_3724869, baseEnd_3724869] using wordTrace_append hprefix tailTrace_3724869
  have hstable : (prefixWord ++ tailWord_3724869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724869).length < 2 ^ (prefixWord ++ tailWord_3724869).sum := by decide
  have hdescent : baseEnd_3724869 < baseStart_3724869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724876 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_3724876 : Nat := 118140960795 + 3724876 * 2 ^ 59
def prefixEnd_3724876 : Nat := 4983230072969 + 3 ^ 40 * 3724876 * 2
def baseEnd_3724876 : Nat := 637550588798957879739871

theorem tailTrace_3724876 : CollatzResearch.WordTrace tailWord_3724876 prefixEnd_3724876 637550588798957879739871 := by
  unfold tailWord_3724876
  simp only [CollatzResearch.WordTrace]
  refine ⟨67928694426708942509385241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90571592568945256679180321 67928694426708942509385241)
  ·
    refine ⟨50946520820031706882038931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67928694426708942509385241 50946520820031706882038931)
    ·
      refine ⟨76419781230047560323058397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946520820031706882038931 76419781230047560323058397)
      ·
        refine ⟨28657417961267835121146899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76419781230047560323058397 28657417961267835121146899)
        ·
          refine ⟨42986126941901752681720349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28657417961267835121146899 42986126941901752681720349)
          ·
            refine ⟨16119797603213157255645131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42986126941901752681720349 16119797603213157255645131)
            ·
              refine ⟨24179696404819735883467697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16119797603213157255645131 24179696404819735883467697)
              ·
                refine ⟨18134772303614801912600773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24179696404819735883467697 18134772303614801912600773)
                ·
                  refine ⟨3400269806927775358612645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18134772303614801912600773 3400269806927775358612645)
                  ·
                    refine ⟨637550588798957879739871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400269806927775358612645 637550588798957879739871)
                    ·
                      rfl

theorem cell23_3724876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_3724876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724876 prefixEnd_3724876 := by exact prefixLift 3724876
  have htrace : WordTrace (prefixWord ++ tailWord_3724876) baseStart_3724876 baseEnd_3724876 := by
    simpa [prefixWord, tailWord_3724876, baseEnd_3724876] using wordTrace_append hprefix tailTrace_3724876
  have hstable : (prefixWord ++ tailWord_3724876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724876).length < 2 ^ (prefixWord ++ tailWord_3724876).sum := by decide
  have hdescent : baseEnd_3724876 < baseStart_3724876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724879 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_3724879 : Nat := 118140960795 + 3724879 * 2 ^ 59
def prefixEnd_3724879 : Nat := 4983230072969 + 3 ^ 40 * 3724879 * 2
def baseEnd_3724879 : Nat := 1912653306838837127482099

theorem tailTrace_3724879 : CollatzResearch.WordTrace tailWord_3724879 prefixEnd_3724879 1912653306838837127482099 := by
  unfold tailWord_3724879
  simp only [CollatzResearch.WordTrace]
  refine ⟨135857498272407016531129691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90571665514938011020753127 135857498272407016531129691)
  ·
    refine ⟨203786247408610524796694537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135857498272407016531129691 203786247408610524796694537)
    ·
      refine ⟨152839685556457893597520903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203786247408610524796694537 152839685556457893597520903)
      ·
        refine ⟨229259528334686840396281355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152839685556457893597520903 229259528334686840396281355)
        ·
          refine ⟨343889292502030260594422033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229259528334686840396281355 343889292502030260594422033)
          ·
            refine ⟨257916969376522695445816525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343889292502030260594422033 257916969376522695445816525)
            ·
              refine ⟨96718863516196010792181197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257916969376522695445816525 96718863516196010792181197)
              ·
                refine ⟨36269573818573504047067949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96718863516196010792181197 36269573818573504047067949)
                ·
                  refine ⟨13601090181965064017650481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36269573818573504047067949 13601090181965064017650481)
                  ·
                    refine ⟨10200817636473798013237861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13601090181965064017650481 10200817636473798013237861)
                    ·
                      refine ⟨1912653306838837127482099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10200817636473798013237861 1912653306838837127482099)
                      ·
                        rfl

theorem cell23_3724879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_3724879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724879 prefixEnd_3724879 := by exact prefixLift 3724879
  have htrace : WordTrace (prefixWord ++ tailWord_3724879) baseStart_3724879 baseEnd_3724879 := by
    simpa [prefixWord, tailWord_3724879, baseEnd_3724879] using wordTrace_append hprefix tailTrace_3724879
  have hstable : (prefixWord ++ tailWord_3724879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724879).length < 2 ^ (prefixWord ++ tailWord_3724879).sum := by decide
  have hdescent : baseEnd_3724879 < baseStart_3724879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724900 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_3724900 : Nat := 118140960795 + 3724900 * 2 ^ 59
def prefixEnd_3724900 : Nat := 4983230072969 + 3 ^ 40 * 3724900 * 2
def baseEnd_3724900 : Nat := 1912664089932581545319503

theorem tailTrace_3724900 : CollatzResearch.WordTrace tailWord_3724900 prefixEnd_3724900 1912664089932581545319503 := by
  unfold tailWord_3724900
  simp only [CollatzResearch.WordTrace]
  refine ⟨67929132102665468558822077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90572176136887291411762769 67929132102665468558822077)
  ·
    refine ⟨25473424538499550709558279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67929132102665468558822077 25473424538499550709558279)
    ·
      refine ⟨38210136807749326064337419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25473424538499550709558279 38210136807749326064337419)
      ·
        refine ⟨57315205211623989096506129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38210136807749326064337419 57315205211623989096506129)
        ·
          refine ⟨42986403908717991822379597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57315205211623989096506129 42986403908717991822379597)
          ·
            refine ⟨16119901465769246933392349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42986403908717991822379597 16119901465769246933392349)
            ·
              refine ⟨6044963049663467600022131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16119901465769246933392349 6044963049663467600022131)
              ·
                refine ⟨9067444574495201400033197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044963049663467600022131 9067444574495201400033197)
                ·
                  refine ⟨3400291715435700525012449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9067444574495201400033197 3400291715435700525012449)
                  ·
                    refine ⟨2550218786576775393759337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3400291715435700525012449 2550218786576775393759337)
                    ·
                      refine ⟨1912664089932581545319503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550218786576775393759337 1912664089932581545319503)
                      ·
                        rfl

theorem cell23_3724900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_3724900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724900 prefixEnd_3724900 := by exact prefixLift 3724900
  have htrace : WordTrace (prefixWord ++ tailWord_3724900) baseStart_3724900 baseEnd_3724900 := by
    simpa [prefixWord, tailWord_3724900, baseEnd_3724900] using wordTrace_append hprefix tailTrace_3724900
  have hstable : (prefixWord ++ tailWord_3724900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724900).length < 2 ^ (prefixWord ++ tailWord_3724900).sum := by decide
  have hdescent : baseEnd_3724900 < baseStart_3724900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724906 : List Nat := [3, 1, 3, 2, 1, 3, 2, 8]
def baseStart_3724906 : Nat := 118140960795 + 3724906 * 2 ^ 59
def prefixEnd_3724906 : Nat := 4983230072969 + 3 ^ 40 * 3724906 * 2
def baseEnd_3724906 : Nat := 70839524845055871179425

theorem tailTrace_3724906 : CollatzResearch.WordTrace tailWord_3724906 prefixEnd_3724906 70839524845055871179425 := by
  unfold tailWord_3724906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33964620760827300035590643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90572322028872800094908381 33964620760827300035590643)
  ·
    refine ⟨50946931141240950053385965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33964620760827300035590643 50946931141240950053385965)
    ·
      refine ⟨19105099177965356270019737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50946931141240950053385965 19105099177965356270019737)
      ·
        refine ⟨14328824383474017202514803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19105099177965356270019737 14328824383474017202514803)
        ·
          refine ⟨21493236575211025803772205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14328824383474017202514803 21493236575211025803772205)
          ·
            refine ⟨8059963715704134676414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21493236575211025803772205 8059963715704134676414577)
            ·
              refine ⟨6044972786778101007310933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8059963715704134676414577 6044972786778101007310933)
              ·
                refine ⟨70839524845055871179425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6044972786778101007310933 70839524845055871179425)
                ·
                  rfl

theorem cell23_3724906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_3724906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724906 prefixEnd_3724906 := by exact prefixLift 3724906
  have htrace : WordTrace (prefixWord ++ tailWord_3724906) baseStart_3724906 baseEnd_3724906 := by
    simpa [prefixWord, tailWord_3724906, baseEnd_3724906] using wordTrace_append hprefix tailTrace_3724906
  have hstable : (prefixWord ++ tailWord_3724906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724906).length < 2 ^ (prefixWord ++ tailWord_3724906).sum := by decide
  have hdescent : baseEnd_3724906 < baseStart_3724906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724910 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3724910 : Nat := 118140960795 + 3724910 * 2 ^ 59
def prefixEnd_3724910 : Nat := 4983230072969 + 3 ^ 40 * 3724910 * 2
def baseEnd_3724910 : Nat := 637556408246375502064819

theorem tailTrace_3724910 : CollatzResearch.WordTrace tailWord_3724910 prefixEnd_3724910 637556408246375502064819 := by
  unfold tailWord_3724910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982328616911838603188523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90572419290196472550338789 16982328616911838603188523)
  ·
    refine ⟨25473492925367757904782785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16982328616911838603188523 25473492925367757904782785)
    ·
      refine ⟨19105119694025818428587089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25473492925367757904782785 19105119694025818428587089)
      ·
        refine ⟨14328839770519363821440317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19105119694025818428587089 14328839770519363821440317)
        ·
          refine ⟨5373314913944761433040119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14328839770519363821440317 5373314913944761433040119)
          ·
            refine ⟨8059972370917142149560179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373314913944761433040119 8059972370917142149560179)
            ·
              refine ⟨12089958556375713224340269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059972370917142149560179 12089958556375713224340269)
              ·
                refine ⟨4533734458640892459127601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12089958556375713224340269 4533734458640892459127601)
                ·
                  refine ⟨3400300843980669344345701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533734458640892459127601 3400300843980669344345701)
                  ·
                    refine ⟨637556408246375502064819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400300843980669344345701 637556408246375502064819)
                    ·
                      rfl

theorem cell23_3724910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3724910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724910 prefixEnd_3724910 := by exact prefixLift 3724910
  have htrace : WordTrace (prefixWord ++ tailWord_3724910) baseStart_3724910 baseEnd_3724910 := by
    simpa [prefixWord, tailWord_3724910, baseEnd_3724910] using wordTrace_append hprefix tailTrace_3724910
  have hstable : (prefixWord ++ tailWord_3724910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724910).length < 2 ^ (prefixWord ++ tailWord_3724910).sum := by decide
  have hdescent : baseEnd_3724910 < baseStart_3724910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724949 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3724949 : Nat := 118140960795 + 3724949 * 2 ^ 59
def prefixEnd_3724949 : Nat := 4983230072969 + 3 ^ 40 * 3724949 * 2
def baseEnd_3724949 : Nat := 637563083494883951202259

theorem tailTrace_3724949 : CollatzResearch.WordTrace tailWord_3724949 prefixEnd_3724949 637563083494883951202259 := by
  unfold tailWord_3724949
  simp only [CollatzResearch.WordTrace]
  refine ⟨135860051382153418486177901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90573367588102278990785267 135860051382153418486177901)
  ·
    refine ⟨50947519268307531932316713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135860051382153418486177901 50947519268307531932316713)
    ·
      refine ⟨38210639451230648949237535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50947519268307531932316713 38210639451230648949237535)
      ·
        refine ⟨57315959176845973423856303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38210639451230648949237535 57315959176845973423856303)
        ·
          refine ⟨85973938765268960135784455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57315959176845973423856303 85973938765268960135784455)
          ·
            refine ⟨128960908147903440203676683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85973938765268960135784455 128960908147903440203676683)
            ·
              refine ⟨193441362221855160305515025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128960908147903440203676683 193441362221855160305515025)
              ·
                refine ⟨145081021666391370229136269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193441362221855160305515025 145081021666391370229136269)
                ·
                  refine ⟨54405383124896763835926101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145081021666391370229136269 54405383124896763835926101)
                  ·
                    refine ⟨637563083494883951202259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54405383124896763835926101 637563083494883951202259)
                    ·
                      rfl

theorem cell23_3724949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3724949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724949 prefixEnd_3724949 := by exact prefixLift 3724949
  have htrace : WordTrace (prefixWord ++ tailWord_3724949) baseStart_3724949 baseEnd_3724949 := by
    simpa [prefixWord, tailWord_3724949, baseEnd_3724949] using wordTrace_append hprefix tailTrace_3724949
  have hstable : (prefixWord ++ tailWord_3724949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724949).length < 2 ^ (prefixWord ++ tailWord_3724949).sum := by decide
  have hdescent : baseEnd_3724949 < baseStart_3724949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724990 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_3724990 : Nat := 118140960795 + 3724990 * 2 ^ 59
def prefixEnd_3724990 : Nat := 4983230072969 + 3 ^ 40 * 3724990 * 2
def baseEnd_3724990 : Nat := 1912710303191486193194089

theorem tailTrace_3724990 : CollatzResearch.WordTrace tailWord_3724990 prefixEnd_3724990 1912710303191486193194089 := by
  unfold tailWord_3724990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982693346875610311052553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90574364516669921658946949 16982693346875610311052553)
  ·
    refine ⟨12737020010156707733289415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16982693346875610311052553 12737020010156707733289415)
    ·
      refine ⟨19105530015235061599934123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12737020010156707733289415 19105530015235061599934123)
      ·
        refine ⟨28658295022852592399901185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19105530015235061599934123 28658295022852592399901185)
        ·
          refine ⟨21493721267139444299925889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28658295022852592399901185 21493721267139444299925889)
          ·
            refine ⟨16120290950354583224944417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21493721267139444299925889 16120290950354583224944417)
            ·
              refine ⟨12090218212765937418708313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16120290950354583224944417 12090218212765937418708313)
              ·
                refine ⟨9067663659574453064031235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12090218212765937418708313 9067663659574453064031235)
                ·
                  refine ⟨13601495489361679596046853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067663659574453064031235 13601495489361679596046853)
                  ·
                    refine ⟨2550280404255314924258785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13601495489361679596046853 2550280404255314924258785)
                    ·
                      refine ⟨1912710303191486193194089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550280404255314924258785 1912710303191486193194089)
                      ·
                        rfl

theorem cell23_3724990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_3724990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724990 prefixEnd_3724990 := by exact prefixLift 3724990
  have htrace : WordTrace (prefixWord ++ tailWord_3724990) baseStart_3724990 baseEnd_3724990 := by
    simpa [prefixWord, tailWord_3724990, baseEnd_3724990] using wordTrace_append hprefix tailTrace_3724990
  have hstable : (prefixWord ++ tailWord_3724990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724990).length < 2 ^ (prefixWord ++ tailWord_3724990).sum := by decide
  have hdescent : baseEnd_3724990 < baseStart_3724990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724996 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 9]
def baseStart_3724996 : Nat := 118140960795 + 3724996 * 2 ^ 59
def prefixEnd_3724996 : Nat := 4983230072969 + 3 ^ 40 * 3724996 * 2
def baseEnd_3724996 : Nat := 212523709341712574413229

theorem tailTrace_3724996 : CollatzResearch.WordTrace tailWord_3724996 prefixEnd_3724996 212523709341712574413229 := by
  unfold tailWord_3724996
  simp only [CollatzResearch.WordTrace]
  refine ⟨67930882806491572756569421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90574510408655430342092561 67930882806491572756569421)
  ·
    refine ⟨25474081052434339783713533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67930882806491572756569421 25474081052434339783713533)
    ·
      refine ⟨9552780394662877418892575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25474081052434339783713533 9552780394662877418892575)
      ·
        refine ⟨14329170591994316128338863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9552780394662877418892575 14329170591994316128338863)
        ·
          refine ⟨21493755887991474192508295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329170591994316128338863 21493755887991474192508295)
          ·
            refine ⟨32240633831987211288762443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21493755887991474192508295 32240633831987211288762443)
            ·
              refine ⟨48360950747980816933143665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32240633831987211288762443 48360950747980816933143665)
              ·
                refine ⟨36270713060985612699857749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48360950747980816933143665 36270713060985612699857749)
                ·
                  refine ⟨212523709341712574413229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36270713060985612699857749 212523709341712574413229)
                  ·
                    rfl

theorem cell23_3724996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_3724996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3724996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3724996 prefixEnd_3724996 := by exact prefixLift 3724996
  have htrace : WordTrace (prefixWord ++ tailWord_3724996) baseStart_3724996 baseEnd_3724996 := by
    simpa [prefixWord, tailWord_3724996, baseEnd_3724996] using wordTrace_append hprefix tailTrace_3724996
  have hstable : (prefixWord ++ tailWord_3724996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724996).length < 2 ^ (prefixWord ++ tailWord_3724996).sum := by decide
  have hdescent : baseEnd_3724996 < baseStart_3724996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725100 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_3725100 : Nat := 118140960795 + 3725100 * 2 ^ 59
def prefixEnd_3725100 : Nat := 4983230072969 + 3 ^ 40 * 3725100 * 2
def baseEnd_3725100 : Nat := 1912766786063480762818583

theorem tailTrace_3725100 : CollatzResearch.WordTrace tailWord_3725100 prefixEnd_3725100 1912766786063480762818583 := by
  unfold tailWord_3725100
  simp only [CollatzResearch.WordTrace]
  refine ⟨67932779402303185637462377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90577039203070914183283169 67932779402303185637462377)
  ·
    refine ⟨50949584551727389228096783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67932779402303185637462377 50949584551727389228096783)
    ·
      refine ⟨76424376827591083842145175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50949584551727389228096783 76424376827591083842145175)
      ·
        refine ⟨114636565241386625763217763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76424376827591083842145175 114636565241386625763217763)
        ·
          refine ⟨171954847862079938644826645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114636565241386625763217763 171954847862079938644826645)
          ·
            refine ⟨8060383493534997123976249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171954847862079938644826645 8060383493534997123976249)
            ·
              refine ⟨6045287620151247842982187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060383493534997123976249 6045287620151247842982187)
              ·
                refine ⟨9067931430226871764473281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045287620151247842982187 9067931430226871764473281)
                ·
                  refine ⟨6800948572670153823354961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9067931430226871764473281 6800948572670153823354961)
                  ·
                    refine ⟨5100711429502615367516221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800948572670153823354961 5100711429502615367516221)
                    ·
                      refine ⟨1912766786063480762818583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100711429502615367516221 1912766786063480762818583)
                      ·
                        rfl

theorem cell23_3725100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_3725100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725100 prefixEnd_3725100 := by exact prefixLift 3725100
  have htrace : WordTrace (prefixWord ++ tailWord_3725100) baseStart_3725100 baseEnd_3725100 := by
    simpa [prefixWord, tailWord_3725100, baseEnd_3725100] using wordTrace_append hprefix tailTrace_3725100
  have hstable : (prefixWord ++ tailWord_3725100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725100).length < 2 ^ (prefixWord ++ tailWord_3725100).sum := by decide
  have hdescent : baseEnd_3725100 < baseStart_3725100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725130 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_3725130 : Nat := 118140960795 + 3725130 * 2 ^ 59
def prefixEnd_3725130 : Nat := 4983230072969 + 3 ^ 40 * 3725130 * 2
def baseEnd_3725130 : Nat := 1912782190483115645443445

theorem tailTrace_3725130 : CollatzResearch.WordTrace tailWord_3725130 prefixEnd_3725130 1912782190483115645443445 := by
  unfold tailWord_3725130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33966663248624421599629211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90577768662998457599011229 33966663248624421599629211)
  ·
    refine ⟨50949994872936632399443817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33966663248624421599629211 50949994872936632399443817)
    ·
      refine ⟨38212496154702474299582863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50949994872936632399443817 38212496154702474299582863)
      ·
        refine ⟨57318744232053711449374295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38212496154702474299582863 57318744232053711449374295)
        ·
          refine ⟨85978116348080567174061443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57318744232053711449374295 85978116348080567174061443)
          ·
            refine ⟨128967174522120850761092165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85978116348080567174061443 128967174522120850761092165)
            ·
              refine ⟨24181345222897659517704781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128967174522120850761092165 24181345222897659517704781)
              ·
                refine ⟨9068004458586622319139293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24181345222897659517704781 9068004458586622319139293)
                ·
                  refine ⟨3400501671969983369677235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9068004458586622319139293 3400501671969983369677235)
                  ·
                    refine ⟨5100752507954975054515853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3400501671969983369677235 5100752507954975054515853)
                    ·
                      refine ⟨1912782190483115645443445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100752507954975054515853 1912782190483115645443445)
                      ·
                        rfl

theorem cell23_3725130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_3725130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725130 prefixEnd_3725130 := by exact prefixLift 3725130
  have htrace : WordTrace (prefixWord ++ tailWord_3725130) baseStart_3725130 baseEnd_3725130 := by
    simpa [prefixWord, tailWord_3725130, baseEnd_3725130] using wordTrace_append hprefix tailTrace_3725130
  have hstable : (prefixWord ++ tailWord_3725130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725130).length < 2 ^ (prefixWord ++ tailWord_3725130).sum := by decide
  have hdescent : baseEnd_3725130 < baseStart_3725130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725153 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3725153 : Nat := 118140960795 + 3725153 * 2 ^ 59
def prefixEnd_3725153 : Nat := 4983230072969 + 3 ^ 40 * 3725153 * 2
def baseEnd_3725153 : Nat := 1912794000538169055455839

theorem tailTrace_3725153 : CollatzResearch.WordTrace tailWord_3725153 prefixEnd_3725153 1912794000538169055455839 := by
  unfold tailWord_3725153
  simp only [CollatzResearch.WordTrace]
  refine ⟨135867491873414361326604113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90578327915609574217736075 135867491873414361326604113)
  ·
    refine ⟨101900618905060770994953085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135867491873414361326604113 101900618905060770994953085)
    ·
      refine ⟨38212732089397789123107407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101900618905060770994953085 38212732089397789123107407)
      ·
        refine ⟨57319098134096683684661111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38212732089397789123107407 57319098134096683684661111)
        ·
          refine ⟨85978647201145025526991667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57319098134096683684661111 85978647201145025526991667)
          ·
            refine ⟨128967970801717538290487501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85978647201145025526991667 128967970801717538290487501)
            ·
              refine ⟨48362989050644076858932813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128967970801717538290487501 48362989050644076858932813)
              ·
                refine ⟨18136120893991528822099805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48362989050644076858932813 18136120893991528822099805)
                ·
                  refine ⟨6801045335246823308287427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18136120893991528822099805 6801045335246823308287427)
                  ·
                    refine ⟨10201568002870234962431141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801045335246823308287427 10201568002870234962431141)
                    ·
                      refine ⟨1912794000538169055455839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10201568002870234962431141 1912794000538169055455839)
                      ·
                        rfl

theorem cell23_3725153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3725153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725153 prefixEnd_3725153 := by exact prefixLift 3725153
  have htrace : WordTrace (prefixWord ++ tailWord_3725153) baseStart_3725153 baseEnd_3725153 := by
    simpa [prefixWord, tailWord_3725153, baseEnd_3725153] using wordTrace_append hprefix tailTrace_3725153
  have hstable : (prefixWord ++ tailWord_3725153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725153).length < 2 ^ (prefixWord ++ tailWord_3725153).sum := by decide
  have hdescent : baseEnd_3725153 < baseStart_3725153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725163 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 4, 4]
def baseStart_3725163 : Nat := 118140960795 + 3725163 * 2 ^ 59
def prefixEnd_3725163 : Nat := 4983230072969 + 3 ^ 40 * 3725163 * 2
def baseEnd_3725163 : Nat := 637599711781571338776931

theorem tailTrace_3725163 : CollatzResearch.WordTrace tailWord_3725163 prefixEnd_3725163 637599711781571338776931 := by
  unfold tailWord_3725163
  simp only [CollatzResearch.WordTrace]
  refine ⟨135867856603378133034468143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90578571068918755356312095 135867856603378133034468143)
  ·
    refine ⟨203801784905067199551702215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135867856603378133034468143 203801784905067199551702215)
    ·
      refine ⟨305702677357600799327553323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203801784905067199551702215 305702677357600799327553323)
      ·
        refine ⟨458554016036401198991329985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305702677357600799327553323 458554016036401198991329985)
        ·
          refine ⟨343915512027300899243497489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458554016036401198991329985 343915512027300899243497489)
          ·
            refine ⟨257936634020475674432623117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343915512027300899243497489 257936634020475674432623117)
            ·
              refine ⟨96726237757678377912233669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257936634020475674432623117 96726237757678377912233669)
              ·
                refine ⟨18136169579564695858543813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96726237757678377912233669 18136169579564695858543813)
                ·
                  refine ⟨3400531796168380473476965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18136169579564695858543813 3400531796168380473476965)
                  ·
                    refine ⟨637599711781571338776931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400531796168380473476965 637599711781571338776931)
                    ·
                      rfl

theorem cell23_3725163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 4].length) (baseStart_3725163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725163 prefixEnd_3725163 := by exact prefixLift 3725163
  have htrace : WordTrace (prefixWord ++ tailWord_3725163) baseStart_3725163 baseEnd_3725163 := by
    simpa [prefixWord, tailWord_3725163, baseEnd_3725163] using wordTrace_append hprefix tailTrace_3725163
  have hstable : (prefixWord ++ tailWord_3725163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725163).length < 2 ^ (prefixWord ++ tailWord_3725163).sum := by decide
  have hdescent : baseEnd_3725163 < baseStart_3725163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725164 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 1, 1, 3]
def baseStart_3725164 : Nat := 118140960795 + 3725164 * 2 ^ 59
def prefixEnd_3725164 : Nat := 4983230072969 + 3 ^ 40 * 3725164 * 2
def baseEnd_3725164 : Nat := 1912799648825368512418289

theorem tailTrace_3725164 : CollatzResearch.WordTrace tailWord_3725164 prefixEnd_3725164 1912799648825368512418289 := by
  unfold tailWord_3725164
  simp only [CollatzResearch.WordTrace]
  refine ⟨67933946538187255102627273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90578595384249673470169697 67933946538187255102627273)
  ·
    refine ⟨50950459903640441326970455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67933946538187255102627273 50950459903640441326970455)
    ·
      refine ⟨76425689855460661990455683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50950459903640441326970455 76425689855460661990455683)
      ·
        refine ⟨114638534783190992985683525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76425689855460661990455683 114638534783190992985683525)
        ·
          refine ⟨21494725271848311184815661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114638534783190992985683525 21494725271848311184815661)
          ·
            refine ⟨8060521976943116694305873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21494725271848311184815661 8060521976943116694305873)
            ·
              refine ⟨6045391482707337520729405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060521976943116694305873 6045391482707337520729405)
              ·
                refine ⟨2267021806015251570273527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045391482707337520729405 2267021806015251570273527)
                ·
                  refine ⟨3400532709022877355410291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267021806015251570273527 3400532709022877355410291)
                  ·
                    refine ⟨5100799063534316033115437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3400532709022877355410291 5100799063534316033115437)
                    ·
                      refine ⟨1912799648825368512418289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100799063534316033115437 1912799648825368512418289)
                      ·
                        rfl

theorem cell23_3725164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_3725164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725164 prefixEnd_3725164 := by exact prefixLift 3725164
  have htrace : WordTrace (prefixWord ++ tailWord_3725164) baseStart_3725164 baseEnd_3725164 := by
    simpa [prefixWord, tailWord_3725164, baseEnd_3725164] using wordTrace_append hprefix tailTrace_3725164
  have hstable : (prefixWord ++ tailWord_3725164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725164).length < 2 ^ (prefixWord ++ tailWord_3725164).sum := by decide
  have hdescent : baseEnd_3725164 < baseStart_3725164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725187 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 3, 2, 2]
def baseStart_3725187 : Nat := 118140960795 + 3725187 * 2 ^ 59
def prefixEnd_3725187 : Nat := 4983230072969 + 3 ^ 40 * 3725187 * 2
def baseEnd_3725187 : Nat := 1912811458880421922430683

theorem tailTrace_3725187 : CollatzResearch.WordTrace tailWord_3725187 prefixEnd_3725187 1912811458880421922430683 := by
  unfold tailWord_3725187
  simp only [CollatzResearch.WordTrace]
  refine ⟨135868731955291185133341815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90579154636860790088894543 135868731955291185133341815)
  ·
    refine ⟨203803097932936777700012723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135868731955291185133341815 203803097932936777700012723)
    ·
      refine ⟨305704646899405166550019085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203803097932936777700012723 305704646899405166550019085)
      ·
        refine ⟨114639242587276937456257157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305704646899405166550019085 114639242587276937456257157)
        ·
          refine ⟨21494857985114425773048217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114639242587276937456257157 21494857985114425773048217)
          ·
            refine ⟨16121143488835819329786163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21494857985114425773048217 16121143488835819329786163)
            ·
              refine ⟨24181715233253728994679245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16121143488835819329786163 24181715233253728994679245)
              ·
                refine ⟨9068143212470148373004717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24181715233253728994679245 9068143212470148373004717)
                ·
                  refine ⟨3400553704676305639876769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9068143212470148373004717 3400553704676305639876769)
                  ·
                    refine ⟨2550415278507229229907577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3400553704676305639876769 2550415278507229229907577)
                    ·
                      refine ⟨1912811458880421922430683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550415278507229229907577 1912811458880421922430683)
                      ·
                        rfl

theorem cell23_3725187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_3725187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725187 prefixEnd_3725187 := by exact prefixLift 3725187
  have htrace : WordTrace (prefixWord ++ tailWord_3725187) baseStart_3725187 baseEnd_3725187 := by
    simpa [prefixWord, tailWord_3725187, baseEnd_3725187] using wordTrace_append hprefix tailTrace_3725187
  have hstable : (prefixWord ++ tailWord_3725187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725187).length < 2 ^ (prefixWord ++ tailWord_3725187).sum := by decide
  have hdescent : baseEnd_3725187 < baseStart_3725187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725204 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_3725204 : Nat := 118140960795 + 3725204 * 2 ^ 59
def prefixEnd_3725204 : Nat := 4983230072969 + 3 ^ 40 * 3725204 * 2
def baseEnd_3725204 : Nat := 1912820188051548355918105

theorem tailTrace_3725204 : CollatzResearch.WordTrace tailWord_3725204 prefixEnd_3725204 1912820188051548355918105 := by
  unfold tailWord_3725204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67934675998114798518355333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90579567997486398024473777 67934675998114798518355333)
  ·
    refine ⟨12737751749646524722191625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67934675998114798518355333 12737751749646524722191625)
    ·
      refine ⟨9553313812234893541643719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12737751749646524722191625 9553313812234893541643719)
      ·
        refine ⟨14329970718352340312465579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553313812234893541643719 14329970718352340312465579)
        ·
          refine ⟨21494956077528510468698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329970718352340312465579 21494956077528510468698369)
          ·
            refine ⟨16121217058146382851523777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21494956077528510468698369 16121217058146382851523777)
            ·
              refine ⟨12090912793609787138642833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16121217058146382851523777 12090912793609787138642833)
              ·
                refine ⟨9068184595207340353982125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12090912793609787138642833 9068184595207340353982125)
                ·
                  refine ⟨3400569223202752632743297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9068184595207340353982125 3400569223202752632743297)
                  ·
                    refine ⟨2550426917402064474557473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3400569223202752632743297 2550426917402064474557473)
                    ·
                      refine ⟨1912820188051548355918105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550426917402064474557473 1912820188051548355918105)
                      ·
                        rfl

theorem cell23_3725204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_3725204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725204 prefixEnd_3725204 := by exact prefixLift 3725204
  have htrace : WordTrace (prefixWord ++ tailWord_3725204) baseStart_3725204 baseEnd_3725204 := by
    simpa [prefixWord, tailWord_3725204, baseEnd_3725204] using wordTrace_append hprefix tailTrace_3725204
  have hstable : (prefixWord ++ tailWord_3725204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725204).length < 2 ^ (prefixWord ++ tailWord_3725204).sum := by decide
  have hdescent : baseEnd_3725204 < baseStart_3725204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725207 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_3725207 : Nat := 118140960795 + 3725207 * 2 ^ 59
def prefixEnd_3725207 : Nat := 4983230072969 + 3 ^ 40 * 3725207 * 2
def baseEnd_3725207 : Nat := 1912821728493511844180591

theorem tailTrace_3725207 : CollatzResearch.WordTrace tailWord_3725207 prefixEnd_3725207 1912821728493511844180591 := by
  unfold tailWord_3725207
  simp only [CollatzResearch.WordTrace]
  refine ⟨135869461415218728549069875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90579640943479152366046583 135869461415218728549069875)
  ·
    refine ⟨203804192122828092823604813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135869461415218728549069875 203804192122828092823604813)
    ·
      refine ⟨76426572046060534808851805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203804192122828092823604813 76426572046060534808851805)
      ·
        refine ⟨28659964517272700553319427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76426572046060534808851805 28659964517272700553319427)
        ·
          refine ⟨42989946775909050829979141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28659964517272700553319427 42989946775909050829979141)
          ·
            refine ⟨8060615020482947030621089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42989946775909050829979141 8060615020482947030621089)
            ·
              refine ⟨6045461265362210272965817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060615020482947030621089 6045461265362210272965817)
              ·
                refine ⟨4534095949021657704724363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045461265362210272965817 4534095949021657704724363)
                ·
                  refine ⟨6801143923532486557086545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534095949021657704724363 6801143923532486557086545)
                  ·
                    refine ⟨5100857942649364917814909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801143923532486557086545 5100857942649364917814909)
                    ·
                      refine ⟨1912821728493511844180591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100857942649364917814909 1912821728493511844180591)
                      ·
                        rfl

theorem cell23_3725207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_3725207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725207 prefixEnd_3725207 := by exact prefixLift 3725207
  have htrace : WordTrace (prefixWord ++ tailWord_3725207) baseStart_3725207 baseEnd_3725207 := by
    simpa [prefixWord, tailWord_3725207, baseEnd_3725207] using wordTrace_append hprefix tailTrace_3725207
  have hstable : (prefixWord ++ tailWord_3725207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725207).length < 2 ^ (prefixWord ++ tailWord_3725207).sum := by decide
  have hdescent : baseEnd_3725207 < baseStart_3725207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725210 : List Nat := [3, 1, 1, 4, 2, 1, 4, 7]
def baseStart_3725210 : Nat := 118140960795 + 3725210 * 2 ^ 59
def prefixEnd_3725210 : Nat := 4983230072969 + 3 ^ 40 * 3725210 * 2
def baseEnd_3725210 : Nat := 70845306256869456757151

theorem tailTrace_3725210 : CollatzResearch.WordTrace tailWord_3725210 prefixEnd_3725210 70845306256869456757151 := by
  unfold tailWord_3725210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33967392708551965015357271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90579713889471906707619389 33967392708551965015357271)
  ·
    refine ⟨50951089062827947523035907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33967392708551965015357271 50951089062827947523035907)
    ·
      refine ⟨76426633594241921284553861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50951089062827947523035907 76426633594241921284553861)
      ·
        refine ⟨14329993798920360240853849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76426633594241921284553861 14329993798920360240853849)
        ·
          refine ⟨10747495349190270180640387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14329993798920360240853849 10747495349190270180640387)
          ·
            refine ⟨16121243023785405270960581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10747495349190270180640387 16121243023785405270960581)
            ·
              refine ⟨3022733066959763488305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16121243023785405270960581 3022733066959763488305109)
              ·
                refine ⟨70845306256869456757151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3022733066959763488305109 70845306256869456757151)
                ·
                  rfl

theorem cell23_3725210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_3725210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725210 prefixEnd_3725210 := by exact prefixLift 3725210
  have htrace : WordTrace (prefixWord ++ tailWord_3725210) baseStart_3725210 baseEnd_3725210 := by
    simpa [prefixWord, tailWord_3725210, baseEnd_3725210] using wordTrace_append hprefix tailTrace_3725210
  have hstable : (prefixWord ++ tailWord_3725210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725210).length < 2 ^ (prefixWord ++ tailWord_3725210).sum := by decide
  have hdescent : baseEnd_3725210 < baseStart_3725210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725224 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3725224 : Nat := 118140960795 + 3725224 * 2 ^ 59
def prefixEnd_3725224 : Nat := 4983230072969 + 3 ^ 40 * 3725224 * 2
def baseEnd_3725224 : Nat := 1912830457664638277668013

theorem tailTrace_3725224 : CollatzResearch.WordTrace tailWord_3725224 prefixEnd_3725224 1912830457664638277668013 := by
  unfold tailWord_3725224
  simp only [CollatzResearch.WordTrace]
  refine ⟨67935040728078570226219363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90580054304104760301625817 67935040728078570226219363)
  ·
    refine ⟨101902561092117855339329045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67935040728078570226219363 101902561092117855339329045)
    ·
      refine ⟨4776682551193024469031049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101902561092117855339329045 4776682551193024469031049)
      ·
        refine ⟨3582511913394768351773287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4776682551193024469031049 3582511913394768351773287)
        ·
          refine ⟨5373767870092152527659931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582511913394768351773287 5373767870092152527659931)
          ·
            refine ⟨8060651805138228791489897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373767870092152527659931 8060651805138228791489897)
            ·
              refine ⟨6045488853853671593617423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060651805138228791489897 6045488853853671593617423)
              ·
                refine ⟨9068233280780507390426135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045488853853671593617423 9068233280780507390426135)
                ·
                  refine ⟨13602349921170761085639203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9068233280780507390426135 13602349921170761085639203)
                  ·
                    refine ⟨20403524881756141628458805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13602349921170761085639203 20403524881756141628458805)
                    ·
                      refine ⟨1912830457664638277668013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20403524881756141628458805 1912830457664638277668013)
                      ·
                        rfl

theorem cell23_3725224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3725224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725224 prefixEnd_3725224 := by exact prefixLift 3725224
  have htrace : WordTrace (prefixWord ++ tailWord_3725224) baseStart_3725224 baseEnd_3725224 := by
    simpa [prefixWord, tailWord_3725224, baseEnd_3725224] using wordTrace_append hprefix tailTrace_3725224
  have hstable : (prefixWord ++ tailWord_3725224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725224).length < 2 ^ (prefixWord ++ tailWord_3725224).sum := by decide
  have hdescent : baseEnd_3725224 < baseStart_3725224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725237 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3725237 : Nat := 118140960795 + 3725237 * 2 ^ 59
def prefixEnd_3725237 : Nat := 4983230072969 + 3 ^ 40 * 3725237 * 2
def baseEnd_3725237 : Nat := 1912837132913146726805453

theorem tailTrace_3725237 : CollatzResearch.WordTrace tailWord_3725237 prefixEnd_3725237 1912837132913146726805453 := by
  unfold tailWord_3725237
  simp only [CollatzResearch.WordTrace]
  refine ⟨135870555605110043672661965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90580370403406695781774643 135870555605110043672661965)
  ·
    refine ⟨50951458351916266377248237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135870555605110043672661965 50951458351916266377248237)
    ·
      refine ⟨19106796881968599891468089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50951458351916266377248237 19106796881968599891468089)
      ·
        refine ⟨14330097661476449918601067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19106796881968599891468089 14330097661476449918601067)
        ·
          refine ⟨21495146492214674877901601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14330097661476449918601067 21495146492214674877901601)
          ·
            refine ⟨16121359869161006158426201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21495146492214674877901601 16121359869161006158426201)
            ·
              refine ⟨12091019901870754618819651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16121359869161006158426201 12091019901870754618819651)
              ·
                refine ⟨18136529852806131928229477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091019901870754618819651 18136529852806131928229477)
                ·
                  refine ⟨3400599347401149736543027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18136529852806131928229477 3400599347401149736543027)
                  ·
                    refine ⟨5100899021101724604814541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3400599347401149736543027 5100899021101724604814541)
                    ·
                      refine ⟨1912837132913146726805453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5100899021101724604814541 1912837132913146726805453)
                      ·
                        rfl

theorem cell23_3725237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3725237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725237 prefixEnd_3725237 := by exact prefixLift 3725237
  have htrace : WordTrace (prefixWord ++ tailWord_3725237) baseStart_3725237 baseEnd_3725237 := by
    simpa [prefixWord, tailWord_3725237, baseEnd_3725237] using wordTrace_append hprefix tailTrace_3725237
  have hstable : (prefixWord ++ tailWord_3725237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725237).length < 2 ^ (prefixWord ++ tailWord_3725237).sum := by decide
  have hdescent : baseEnd_3725237 < baseStart_3725237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725263 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_3725263 : Nat := 118140960795 + 3725263 * 2 ^ 59
def prefixEnd_3725263 : Nat := 4983230072969 + 3 ^ 40 * 3725263 * 2
def baseEnd_3725263 : Nat := 1912850483410163625080333

theorem tailTrace_3725263 : CollatzResearch.WordTrace tailWord_3725263 prefixEnd_3725263 1912850483410163625080333 := by
  unfold tailWord_3725263
  simp only [CollatzResearch.WordTrace]
  refine ⟨135871503903015850113108443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90581002602010566742072295 135871503903015850113108443)
  ·
    refine ⟨203807255854523775169662665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135871503903015850113108443 203807255854523775169662665)
    ·
      refine ⟨152855441890892831377246999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203807255854523775169662665 152855441890892831377246999)
      ·
        refine ⟨229283162836339247065870499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152855441890892831377246999 229283162836339247065870499)
        ·
          refine ⟨343924744254508870598805749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229283162836339247065870499 343924744254508870598805749)
          ·
            refine ⟨32242944773860206618638039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343924744254508870598805749 32242944773860206618638039)
            ·
              refine ⟨48364417160790309927957059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32242944773860206618638039 48364417160790309927957059)
              ·
                refine ⟨72546625741185464891935589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48364417160790309927957059 72546625741185464891935589)
                ·
                  refine ⟨13602492326472274667237923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72546625741185464891935589 13602492326472274667237923)
                  ·
                    refine ⟨20403738489708412000856885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13602492326472274667237923 20403738489708412000856885)
                    ·
                      refine ⟨1912850483410163625080333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20403738489708412000856885 1912850483410163625080333)
                      ·
                        rfl

theorem cell23_3725263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_3725263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725263 prefixEnd_3725263 := by exact prefixLift 3725263
  have htrace : WordTrace (prefixWord ++ tailWord_3725263) baseStart_3725263 baseEnd_3725263 := by
    simpa [prefixWord, tailWord_3725263, baseEnd_3725263] using wordTrace_append hprefix tailTrace_3725263
  have hstable : (prefixWord ++ tailWord_3725263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725263).length < 2 ^ (prefixWord ++ tailWord_3725263).sum := by decide
  have hdescent : baseEnd_3725263 < baseStart_3725263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725290 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3725290 : Nat := 118140960795 + 3725290 * 2 ^ 59
def prefixEnd_3725290 : Nat := 4983230072969 + 3 ^ 40 * 3725290 * 2
def baseEnd_3725290 : Nat := 1912864347387835019442709

theorem tailTrace_3725290 : CollatzResearch.WordTrace tailWord_3725290 prefixEnd_3725290 1912864347387835019442709 := by
  unfold tailWord_3725290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968122168479508431085331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90581659115945355816227549 33968122168479508431085331)
  ·
    refine ⟨50952183252719262646627997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33968122168479508431085331 50952183252719262646627997)
    ·
      refine ⟨19107068719769723492485499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50952183252719262646627997 19107068719769723492485499)
      ·
        refine ⟨28660603079654585238728249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107068719769723492485499 28660603079654585238728249)
        ·
          refine ⟨21495452309740938929046187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28660603079654585238728249 21495452309740938929046187)
          ·
            refine ⟨32243178464611408393569281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21495452309740938929046187 32243178464611408393569281)
            ·
              refine ⟨24182383848458556295176961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32243178464611408393569281 24182383848458556295176961)
              ·
                refine ⟨18136787886343917221382721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24182383848458556295176961 18136787886343917221382721)
                ·
                  refine ⟨13602590914757937916037041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18136787886343917221382721 13602590914757937916037041)
                  ·
                    refine ⟨10201943186068453437027781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13602590914757937916037041 10201943186068453437027781)
                    ·
                      refine ⟨1912864347387835019442709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10201943186068453437027781 1912864347387835019442709)
                      ·
                        rfl

theorem cell23_3725290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3725290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725290 prefixEnd_3725290 := by exact prefixLift 3725290
  have htrace : WordTrace (prefixWord ++ tailWord_3725290) baseStart_3725290 baseEnd_3725290 := by
    simpa [prefixWord, tailWord_3725290, baseEnd_3725290] using wordTrace_append hprefix tailTrace_3725290
  have hstable : (prefixWord ++ tailWord_3725290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725290).length < 2 ^ (prefixWord ++ tailWord_3725290).sum := by decide
  have hdescent : baseEnd_3725290 < baseStart_3725290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725332 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3725332 : Nat := 118140960795 + 3725332 * 2 ^ 59
def prefixEnd_3725332 : Nat := 4983230072969 + 3 ^ 40 * 3725332 * 2
def baseEnd_3725332 : Nat := 1912885913575323855117517

theorem tailTrace_3725332 : CollatzResearch.WordTrace tailWord_3725332 prefixEnd_3725332 1912885913575323855117517 := by
  unfold tailWord_3725332
  simp only [CollatzResearch.WordTrace]
  refine ⟨67937010269882937448685125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90582680359843916598246833 67937010269882937448685125)
  ·
    refine ⟨12738189425603050771628461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67937010269882937448685125 12738189425603050771628461)
    ·
      refine ⟨4776821034601144039360673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12738189425603050771628461 4776821034601144039360673)
      ·
        refine ⟨3582615775950858029520505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4776821034601144039360673 3582615775950858029520505)
        ·
          refine ⟨2686961831963143522140379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3582615775950858029520505 2686961831963143522140379)
          ·
            refine ⟨4030442747944715283210569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686961831963143522140379 4030442747944715283210569)
            ·
              refine ⟨3022832060958536462407927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030442747944715283210569 3022832060958536462407927)
              ·
                refine ⟨4534248091437804693611891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022832060958536462407927 4534248091437804693611891)
                ·
                  refine ⟨6801372137156707040417837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534248091437804693611891 6801372137156707040417837)
                  ·
                    refine ⟨2550514551433765140156689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6801372137156707040417837 2550514551433765140156689)
                    ·
                      refine ⟨1912885913575323855117517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550514551433765140156689 1912885913575323855117517)
                      ·
                        rfl

theorem cell23_3725332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3725332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725332 prefixEnd_3725332 := by exact prefixLift 3725332
  have htrace : WordTrace (prefixWord ++ tailWord_3725332) baseStart_3725332 baseEnd_3725332 := by
    simpa [prefixWord, tailWord_3725332, baseEnd_3725332] using wordTrace_append hprefix tailTrace_3725332
  have hstable : (prefixWord ++ tailWord_3725332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725332).length < 2 ^ (prefixWord ++ tailWord_3725332).sum := by decide
  have hdescent : baseEnd_3725332 < baseStart_3725332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725367 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_3725367 : Nat := 118140960795 + 3725367 * 2 ^ 59
def prefixEnd_3725367 : Nat := 4983230072969 + 3 ^ 40 * 3725367 * 2
def baseEnd_3725367 : Nat := 1912903885398231218179855

theorem tailTrace_3725367 : CollatzResearch.WordTrace tailWord_3725367 prefixEnd_3725367 1912903885398231218179855 := by
  unfold tailWord_3725367
  simp only [CollatzResearch.WordTrace]
  refine ⟨135875297094639075874894355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90583531396426050583262903 135875297094639075874894355)
  ·
    refine ⟨203812945641958613812341533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135875297094639075874894355 203812945641958613812341533)
    ·
      refine ⟨76429854615734480179628075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203812945641958613812341533 76429854615734480179628075)
      ·
        refine ⟨114644781923601720269442113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76429854615734480179628075 114644781923601720269442113)
        ·
          refine ⟨85983586442701290202081585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114644781923601720269442113 85983586442701290202081585)
          ·
            refine ⟨64487689832025967651561189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85983586442701290202081585 64487689832025967651561189)
            ·
              refine ⟨12091441843504868934667723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64487689832025967651561189 12091441843504868934667723)
              ·
                refine ⟨18137162765257303402001585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091441843504868934667723 18137162765257303402001585)
                ·
                  refine ⟨13602872073942977551501189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18137162765257303402001585 13602872073942977551501189)
                  ·
                    refine ⟨2550538513864308290906473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13602872073942977551501189 2550538513864308290906473)
                    ·
                      refine ⟨1912903885398231218179855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550538513864308290906473 1912903885398231218179855)
                      ·
                        rfl

theorem cell23_3725367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_3725367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725367 prefixEnd_3725367 := by exact prefixLift 3725367
  have htrace : WordTrace (prefixWord ++ tailWord_3725367) baseStart_3725367 baseEnd_3725367 := by
    simpa [prefixWord, tailWord_3725367, baseEnd_3725367] using wordTrace_append hprefix tailTrace_3725367
  have hstable : (prefixWord ++ tailWord_3725367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725367).length < 2 ^ (prefixWord ++ tailWord_3725367).sum := by decide
  have hdescent : baseEnd_3725367 < baseStart_3725367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725390 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_3725390 : Nat := 118140960795 + 3725390 * 2 ^ 59
def prefixEnd_3725390 : Nat := 4983230072969 + 3 ^ 40 * 3725390 * 2
def baseEnd_3725390 : Nat := 212546188383698292021361

theorem tailTrace_3725390 : CollatzResearch.WordTrace tailWord_3725390 prefixEnd_3725390 212546188383698292021361 := by
  unfold tailWord_3725390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984516996694468850372703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90584090649037167201987749 16984516996694468850372703)
  ·
    refine ⟨25476775495041703275559055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16984516996694468850372703 25476775495041703275559055)
    ·
      refine ⟨38215163242562554913338583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25476775495041703275559055 38215163242562554913338583)
      ·
        refine ⟨57322744863843832370007875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38215163242562554913338583 57322744863843832370007875)
        ·
          refine ⟨85984117295765748555011813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57322744863843832370007875 85984117295765748555011813)
          ·
            refine ⟨16122021992956077854064715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85984117295765748555011813 16122021992956077854064715)
            ·
              refine ⟨24183032989434116781097073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16122021992956077854064715 24183032989434116781097073)
              ·
                refine ⟨18137274742075587585822805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24183032989434116781097073 18137274742075587585822805)
                ·
                  refine ⟨212546188383698292021361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18137274742075587585822805 212546188383698292021361)
                  ·
                    rfl

theorem cell23_3725390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_3725390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725390 prefixEnd_3725390 := by exact prefixLift 3725390
  have htrace : WordTrace (prefixWord ++ tailWord_3725390) baseStart_3725390 baseEnd_3725390 := by
    simpa [prefixWord, tailWord_3725390, baseEnd_3725390] using wordTrace_append hprefix tailTrace_3725390
  have hstable : (prefixWord ++ tailWord_3725390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725390).length < 2 ^ (prefixWord ++ tailWord_3725390).sum := by decide
  have hdescent : baseEnd_3725390 < baseStart_3725390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725404 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3725404 : Nat := 118140960795 + 3725404 * 2 ^ 59
def prefixEnd_3725404 : Nat := 4983230072969 + 3 ^ 40 * 3725404 * 2
def baseEnd_3725404 : Nat := 1912922884182447573417185

theorem tailTrace_3725404 : CollatzResearch.WordTrace tailWord_3725404 prefixEnd_3725404 1912922884182447573417185 := by
  unfold tailWord_3725404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67938323297752515596995633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90584431063670020795994177 67938323297752515596995633)
  ·
    refine ⟨50953742473314386697746725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67938323297752515596995633 50953742473314386697746725)
    ·
      refine ⟨9553826713746447505827511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50953742473314386697746725 9553826713746447505827511)
      ·
        refine ⟨14330740070619671258741267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553826713746447505827511 14330740070619671258741267)
        ·
          refine ⟨21496110105929506888111901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14330740070619671258741267 21496110105929506888111901)
          ·
            refine ⟨8061041289723565083041963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21496110105929506888111901 8061041289723565083041963)
            ·
              refine ⟨12091561934585347624562945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061041289723565083041963 12091561934585347624562945)
              ·
                refine ⟨9068671450939010718422209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12091561934585347624562945 9068671450939010718422209)
                ·
                  refine ⟨6801503588204258038816657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9068671450939010718422209 6801503588204258038816657)
                  ·
                    refine ⟨5101127691153193529112493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801503588204258038816657 5101127691153193529112493)
                    ·
                      refine ⟨1912922884182447573417185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5101127691153193529112493 1912922884182447573417185)
                      ·
                        rfl

theorem cell23_3725404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3725404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725404 prefixEnd_3725404 := by exact prefixLift 3725404
  have htrace : WordTrace (prefixWord ++ tailWord_3725404) baseStart_3725404 baseEnd_3725404 := by
    simpa [prefixWord, tailWord_3725404, baseEnd_3725404] using wordTrace_append hprefix tailTrace_3725404
  have hstable : (prefixWord ++ tailWord_3725404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725404).length < 2 ^ (prefixWord ++ tailWord_3725404).sum := by decide
  have hdescent : baseEnd_3725404 < baseStart_3725404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725424 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 6]
def baseStart_3725424 : Nat := 118140960795 + 3725424 * 2 ^ 59
def prefixEnd_3725424 : Nat := 4983230072969 + 3 ^ 40 * 3725424 * 2
def baseEnd_3725424 : Nat := 212548128199504166129677

theorem tailTrace_3725424 : CollatzResearch.WordTrace tailWord_3725424 prefixEnd_3725424 212548128199504166129677 := by
  unfold tailWord_3725424
  simp only [CollatzResearch.WordTrace]
  refine ⟨67938688027716287304859663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90584917370288383073146217 67938688027716287304859663)
  ·
    refine ⟨101908032041574430957289495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67938688027716287304859663 101908032041574430957289495)
    ·
      refine ⟨152862048062361646435934243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101908032041574430957289495 152862048062361646435934243)
      ·
        refine ⟨229293072093542469653901365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152862048062361646435934243 229293072093542469653901365)
        ·
          refine ⟨21496225508769606530053253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229293072093542469653901365 21496225508769606530053253)
          ·
            refine ⟨4030542282894301224384985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21496225508769606530053253 4030542282894301224384985)
            ·
              refine ⟨3022906712170725918288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030542282894301224384985 3022906712170725918288739)
              ·
                refine ⟨4534360068256088877433109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022906712170725918288739 4534360068256088877433109)
                ·
                  refine ⟨212548128199504166129677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4534360068256088877433109 212548128199504166129677)
                  ·
                    rfl

theorem cell23_3725424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 6].length) (baseStart_3725424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725424 prefixEnd_3725424 := by exact prefixLift 3725424
  have htrace : WordTrace (prefixWord ++ tailWord_3725424) baseStart_3725424 baseEnd_3725424 := by
    simpa [prefixWord, tailWord_3725424, baseEnd_3725424] using wordTrace_append hprefix tailTrace_3725424
  have hstable : (prefixWord ++ tailWord_3725424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725424).length < 2 ^ (prefixWord ++ tailWord_3725424).sum := by decide
  have hdescent : baseEnd_3725424 < baseStart_3725424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725437 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_3725437 : Nat := 118140960795 + 3725437 * 2 ^ 59
def prefixEnd_3725437 : Nat := 4983230072969 + 3 ^ 40 * 3725437 * 2
def baseEnd_3725437 : Nat := 637646609681348648101511

theorem tailTrace_3725437 : CollatzResearch.WordTrace tailWord_3725437 prefixEnd_3725437 637646609681348648101511 := by
  unfold tailWord_3725437
  simp only [CollatzResearch.WordTrace]
  refine ⟨135877850204385477829942565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90585233469590318553295043 135877850204385477829942565)
  ·
    refine ⟨25477096913322277093114231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135877850204385477829942565 25477096913322277093114231)
    ·
      refine ⟨38215645369983415639671347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25477096913322277093114231 38215645369983415639671347)
      ·
        refine ⟨57323468054975123459507021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38215645369983415639671347 57323468054975123459507021)
        ·
          refine ⟨21496300520615671297315133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57323468054975123459507021 21496300520615671297315133)
          ·
            refine ⟨8061112695230876736493175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21496300520615671297315133 8061112695230876736493175)
            ·
              refine ⟨12091669042846315104739763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061112695230876736493175 12091669042846315104739763)
              ·
                refine ⟨18137503564269472657109645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091669042846315104739763 18137503564269472657109645)
                ·
                  refine ⟨6801563836601052246416117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18137503564269472657109645 6801563836601052246416117)
                  ·
                    refine ⟨637646609681348648101511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6801563836601052246416117 637646609681348648101511)
                    ·
                      rfl

theorem cell23_3725437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_3725437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725437 prefixEnd_3725437 := by exact prefixLift 3725437
  have htrace : WordTrace (prefixWord ++ tailWord_3725437) baseStart_3725437 baseEnd_3725437 := by
    simpa [prefixWord, tailWord_3725437, baseEnd_3725437] using wordTrace_append hprefix tailTrace_3725437
  have hstable : (prefixWord ++ tailWord_3725437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725437).length < 2 ^ (prefixWord ++ tailWord_3725437).sum := by decide
  have hdescent : baseEnd_3725437 < baseStart_3725437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725474 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3725474 : Nat := 118140960795 + 3725474 * 2 ^ 59
def prefixEnd_3725474 : Nat := 4983230072969 + 3 ^ 40 * 3725474 * 2
def baseEnd_3725474 : Nat := 1912958827828262299541863

theorem tailTrace_3725474 : CollatzResearch.WordTrace tailWord_3725474 prefixEnd_3725474 1912958827828262299541863 := by
  unfold tailWord_3725474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33969799926312858287259869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90586133136834288766026317 33969799926312858287259869)
  ·
    refine ⟨12738674972367321857722451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33969799926312858287259869 12738674972367321857722451)
    ·
      refine ⟨19108012458550982786583677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738674972367321857722451 19108012458550982786583677)
      ·
        refine ⟨7165504671956618544968879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19108012458550982786583677 7165504671956618544968879)
        ·
          refine ⟨10748257007934927817453319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165504671956618544968879 10748257007934927817453319)
          ·
            refine ⟨16122385511902391726179979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748257007934927817453319 16122385511902391726179979)
            ·
              refine ⟨24183578267853587589269969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16122385511902391726179979 24183578267853587589269969)
              ·
                refine ⟨18137683700890190691952477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24183578267853587589269969 18137683700890190691952477)
                ·
                  refine ⟨6801631387833821509482179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18137683700890190691952477 6801631387833821509482179)
                  ·
                    refine ⟨10202447081750732264223269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801631387833821509482179 10202447081750732264223269)
                    ·
                      refine ⟨1912958827828262299541863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10202447081750732264223269 1912958827828262299541863)
                      ·
                        rfl

theorem cell23_3725474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3725474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725474 prefixEnd_3725474 := by exact prefixLift 3725474
  have htrace : WordTrace (prefixWord ++ tailWord_3725474) baseStart_3725474 baseEnd_3725474 := by
    simpa [prefixWord, tailWord_3725474, baseEnd_3725474] using wordTrace_append hprefix tailTrace_3725474
  have hstable : (prefixWord ++ tailWord_3725474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725474).length < 2 ^ (prefixWord ++ tailWord_3725474).sum := by decide
  have hdescent : baseEnd_3725474 < baseStart_3725474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725477 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_3725477 : Nat := 118140960795 + 3725477 * 2 ^ 59
def prefixEnd_3725477 : Nat := 4983230072969 + 3 ^ 40 * 3725477 * 2
def baseEnd_3725477 : Nat := 1912960368270225787804349

theorem tailTrace_3725477 : CollatzResearch.WordTrace tailWord_3725477 prefixEnd_3725477 1912960368270225787804349 := by
  unfold tailWord_3725477
  simp only [CollatzResearch.WordTrace]
  refine ⟨135879309124240564661398685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90586206082827043107599123 135879309124240564661398685)
  ·
    refine ⟨50954740921590211748024507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135879309124240564661398685 50954740921590211748024507)
    ·
      refine ⟨76432111382385317622036761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50954740921590211748024507 76432111382385317622036761)
      ·
        refine ⟨57324083536788988216527571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76432111382385317622036761 57324083536788988216527571)
        ·
          refine ⟨85986125305183482324791357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57324083536788988216527571 85986125305183482324791357)
          ·
            refine ⟨32244796989443805871796759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85986125305183482324791357 32244796989443805871796759)
            ·
              refine ⟨48367195484165708807695139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32244796989443805871796759 48367195484165708807695139)
              ·
                refine ⟨72550793226248563211542709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48367195484165708807695139 72550793226248563211542709)
                ·
                  refine ⟨6801636864960802801082129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72550793226248563211542709 6801636864960802801082129)
                  ·
                    refine ⟨5101227648720602100811597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801636864960802801082129 5101227648720602100811597)
                    ·
                      refine ⟨1912960368270225787804349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5101227648720602100811597 1912960368270225787804349)
                      ·
                        rfl

theorem cell23_3725477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_3725477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725477 prefixEnd_3725477 := by exact prefixLift 3725477
  have htrace : WordTrace (prefixWord ++ tailWord_3725477) baseStart_3725477 baseEnd_3725477 := by
    simpa [prefixWord, tailWord_3725477, baseEnd_3725477] using wordTrace_append hprefix tailTrace_3725477
  have hstable : (prefixWord ++ tailWord_3725477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725477).length < 2 ^ (prefixWord ++ tailWord_3725477).sum := by decide
  have hdescent : baseEnd_3725477 < baseStart_3725477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725497 : List Nat := [1, 2, 1, 4, 1, 2, 5, 7]
def baseStart_3725497 : Nat := 118140960795 + 3725497 * 2 ^ 59
def prefixEnd_3725497 : Nat := 4983230072969 + 3 ^ 40 * 3725497 * 2
def baseEnd_3725497 : Nat := 70850764366048729983491

theorem tailTrace_3725497 : CollatzResearch.WordTrace tailWord_3725497 prefixEnd_3725497 70850764366048729983491 := by
  unfold tailWord_3725497
  simp only [CollatzResearch.WordTrace]
  refine ⟨135880038584168108077126745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90586692389445405384751163 135880038584168108077126745)
  ·
    refine ⟨101910028938126081057845059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135880038584168108077126745 101910028938126081057845059)
    ·
      refine ⟨152865043407189121586767589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101910028938126081057845059 152865043407189121586767589)
      ·
        refine ⟨28662195638847960297518923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152865043407189121586767589 28662195638847960297518923)
        ·
          refine ⟨42993293458271940446278385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28662195638847960297518923 42993293458271940446278385)
          ·
            refine ⟨32244970093703955334708789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42993293458271940446278385 32244970093703955334708789)
            ·
              refine ⟨3022965946284745812628949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32244970093703955334708789 3022965946284745812628949)
              ·
                refine ⟨70850764366048729983491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3022965946284745812628949 70850764366048729983491)
                ·
                  rfl

theorem cell23_3725497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 7].length) (baseStart_3725497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725497 prefixEnd_3725497 := by exact prefixLift 3725497
  have htrace : WordTrace (prefixWord ++ tailWord_3725497) baseStart_3725497 baseEnd_3725497 := by
    simpa [prefixWord, tailWord_3725497, baseEnd_3725497] using wordTrace_append hprefix tailTrace_3725497
  have hstable : (prefixWord ++ tailWord_3725497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725497).length < 2 ^ (prefixWord ++ tailWord_3725497).sum := by decide
  have hdescent : baseEnd_3725497 < baseStart_3725497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725505 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3725505 : Nat := 118140960795 + 3725505 * 2 ^ 59
def prefixEnd_3725505 : Nat := 4983230072969 + 3 ^ 40 * 3725505 * 2
def baseEnd_3725505 : Nat := 637658248576183892751407

theorem tailTrace_3725505 : CollatzResearch.WordTrace tailWord_3725505 prefixEnd_3725505 637658248576183892751407 := by
  unfold tailWord_3725505
  simp only [CollatzResearch.WordTrace]
  refine ⟨135880330368139125443417969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90586886912092750295611979 135880330368139125443417969)
  ·
    refine ⟨101910247776104344082563477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135880330368139125443417969 101910247776104344082563477)
    ·
      refine ⟨4777042864504891128870163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101910247776104344082563477 4777042864504891128870163)
      ·
        refine ⟨7165564296757336693305245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777042864504891128870163 7165564296757336693305245)
        ·
          refine ⟨2687086611284001259989467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7165564296757336693305245 2687086611284001259989467)
          ·
            refine ⟨4030629916926001889984201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687086611284001259989467 4030629916926001889984201)
            ·
              refine ⟨3022972437694501417488151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030629916926001889984201 3022972437694501417488151)
              ·
                refine ⟨4534458656541752126232227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022972437694501417488151 4534458656541752126232227)
                ·
                  refine ⟨6801687984812628189348341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534458656541752126232227 6801687984812628189348341)
                  ·
                    refine ⟨637658248576183892751407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6801687984812628189348341 637658248576183892751407)
                    ·
                      rfl

theorem cell23_3725505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3725505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725505 prefixEnd_3725505 := by exact prefixLift 3725505
  have htrace : WordTrace (prefixWord ++ tailWord_3725505) baseStart_3725505 baseEnd_3725505 := by
    simpa [prefixWord, tailWord_3725505, baseEnd_3725505] using wordTrace_append hprefix tailTrace_3725505
  have hstable : (prefixWord ++ tailWord_3725505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725505).length < 2 ^ (prefixWord ++ tailWord_3725505).sum := by decide
  have hdescent : baseEnd_3725505 < baseStart_3725505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725508 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_3725508 : Nat := 118140960795 + 3725508 * 2 ^ 59
def prefixEnd_3725508 : Nat := 4983230072969 + 3 ^ 40 * 3725508 * 2
def baseEnd_3725508 : Nat := 1912976286170515166516707

theorem tailTrace_3725508 : CollatzResearch.WordTrace tailWord_3725508 prefixEnd_3725508 1912976286170515166516707 := by
  unfold tailWord_3725508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67940219893564128477888589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90586959858085504637184785 67940219893564128477888589)
  ·
    refine ⟨25477582460086548179208221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67940219893564128477888589 25477582460086548179208221)
    ·
      refine ⟨9554093422532455567203083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25477582460086548179208221 9554093422532455567203083)
      ·
        refine ⟨14331140133798683350804625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9554093422532455567203083 14331140133798683350804625)
        ·
          refine ⟨10748355100349012513103469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14331140133798683350804625 10748355100349012513103469)
          ·
            refine ⟨4030633162630879692413801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10748355100349012513103469 4030633162630879692413801)
            ·
              refine ⟨3022974871973159769310351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030633162630879692413801 3022974871973159769310351)
              ·
                refine ⟨4534462307959739653965527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022974871973159769310351 4534462307959739653965527)
                ·
                  refine ⟨6801693461939609480948291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534462307959739653965527 6801693461939609480948291)
                  ·
                    refine ⟨10202540192909414221422437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801693461939609480948291 10202540192909414221422437)
                    ·
                      refine ⟨1912976286170515166516707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10202540192909414221422437 1912976286170515166516707)
                      ·
                        rfl

theorem cell23_3725508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_3725508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725508 prefixEnd_3725508 := by exact prefixLift 3725508
  have htrace : WordTrace (prefixWord ++ tailWord_3725508) baseStart_3725508 baseEnd_3725508 := by
    simpa [prefixWord, tailWord_3725508, baseEnd_3725508] using wordTrace_append hprefix tailTrace_3725508
  have hstable : (prefixWord ++ tailWord_3725508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725508).length < 2 ^ (prefixWord ++ tailWord_3725508).sum := by decide
  have hdescent : baseEnd_3725508 < baseStart_3725508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725538 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3725538 : Nat := 118140960795 + 3725538 * 2 ^ 59
def prefixEnd_3725538 : Nat := 4983230072969 + 3 ^ 40 * 3725538 * 2
def baseEnd_3725538 : Nat := 1912991690590150049141569

theorem tailTrace_3725538 : CollatzResearch.WordTrace tailWord_3725538 prefixEnd_3725538 1912991690590150049141569 := by
  unfold tailWord_3725538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970383494254893019842317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90587689318013048052912845 33970383494254893019842317)
  ·
    refine ⟨12738893810345584882440869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33970383494254893019842317 12738893810345584882440869)
    ·
      refine ⟨2388542589439797165457663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12738893810345584882440869 2388542589439797165457663)
      ·
        refine ⟨3582813884159695748186495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388542589439797165457663 3582813884159695748186495)
        ·
          refine ⟨5374220826239543622279743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582813884159695748186495 5374220826239543622279743)
          ·
            refine ⟨8061331239359315433419615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374220826239543622279743 8061331239359315433419615)
            ·
              refine ⟨12091996859038973150129423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061331239359315433419615 12091996859038973150129423)
              ·
                refine ⟨18137995288558459725194135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091996859038973150129423 18137995288558459725194135)
                ·
                  refine ⟨27206992932837689587791203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18137995288558459725194135 27206992932837689587791203)
                  ·
                    refine ⟨40810489399256534381686805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27206992932837689587791203 40810489399256534381686805)
                    ·
                      refine ⟨1912991690590150049141569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40810489399256534381686805 1912991690590150049141569)
                      ·
                        rfl

theorem cell23_3725538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3725538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725538 prefixEnd_3725538 := by exact prefixLift 3725538
  have htrace : WordTrace (prefixWord ++ tailWord_3725538) baseStart_3725538 baseEnd_3725538 := by
    simpa [prefixWord, tailWord_3725538, baseEnd_3725538] using wordTrace_append hprefix tailTrace_3725538
  have hstable : (prefixWord ++ tailWord_3725538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725538).length < 2 ^ (prefixWord ++ tailWord_3725538).sum := by decide
  have hdescent : baseEnd_3725538 < baseStart_3725538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725541 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3725541 : Nat := 118140960795 + 3725541 * 2 ^ 59
def prefixEnd_3725541 : Nat := 4983230072969 + 3 ^ 40 * 3725541 * 2
def baseEnd_3725541 : Nat := 1912993231032113537404055

theorem tailTrace_3725541 : CollatzResearch.WordTrace tailWord_3725541 prefixEnd_3725541 1912993231032113537404055 := by
  unfold tailWord_3725541
  simp only [CollatzResearch.WordTrace]
  refine ⟨135881643396008703591728477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90587762264005802394485651 135881643396008703591728477)
  ·
    refine ⟨50955616273503263846898179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135881643396008703591728477 50955616273503263846898179)
    ·
      refine ⟨76433424410254895770347269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50955616273503263846898179 76433424410254895770347269)
      ·
        refine ⟨14331267076922792956940113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76433424410254895770347269 14331267076922792956940113)
        ·
          refine ⟨10748450307692094717705085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14331267076922792956940113 10748450307692094717705085)
          ·
            refine ⟨4030668865384535519139407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10748450307692094717705085 4030668865384535519139407)
            ·
              refine ⟨6046003298076803278709111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030668865384535519139407 6046003298076803278709111)
              ·
                refine ⟨9069004947115204918063667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046003298076803278709111 9069004947115204918063667)
                ·
                  refine ⟨13603507420672807377095501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069004947115204918063667 13603507420672807377095501)
                  ·
                    refine ⟨5101315282752302766410813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13603507420672807377095501 5101315282752302766410813)
                    ·
                      refine ⟨1912993231032113537404055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5101315282752302766410813 1912993231032113537404055)
                      ·
                        rfl

theorem cell23_3725541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3725541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725541 prefixEnd_3725541 := by exact prefixLift 3725541
  have htrace : WordTrace (prefixWord ++ tailWord_3725541) baseStart_3725541 baseEnd_3725541 := by
    simpa [prefixWord, tailWord_3725541, baseEnd_3725541] using wordTrace_append hprefix tailTrace_3725541
  have hstable : (prefixWord ++ tailWord_3725541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725541).length < 2 ^ (prefixWord ++ tailWord_3725541).sum := by decide
  have hdescent : baseEnd_3725541 < baseStart_3725541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725551 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 1, 3, 2]
def baseStart_3725551 : Nat := 118140960795 + 3725551 * 2 ^ 59
def prefixEnd_3725551 : Nat := 4983230072969 + 3 ^ 40 * 3725551 * 2
def baseEnd_3725551 : Nat := 1912998365838658498279009

theorem tailTrace_3725551 : CollatzResearch.WordTrace tailWord_3725551 prefixEnd_3725551 1912998365838658498279009 := by
  unfold tailWord_3725551
  simp only [CollatzResearch.WordTrace]
  refine ⟨135882008125972475299592507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90588005417314983533061671 135882008125972475299592507)
  ·
    refine ⟨203823012188958712949388761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135882008125972475299592507 203823012188958712949388761)
    ·
      refine ⟨152867259141719034712041571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203823012188958712949388761 152867259141719034712041571)
      ·
        refine ⟨229300888712578552068062357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152867259141719034712041571 229300888712578552068062357)
        ·
          refine ⟨10748479158402119628190423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229300888712578552068062357 10748479158402119628190423)
          ·
            refine ⟨16122718737603179442285635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748479158402119628190423 16122718737603179442285635)
            ·
              refine ⟨24184078106404769163428453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16122718737603179442285635 24184078106404769163428453)
              ·
                refine ⟨4534514644950894218142835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24184078106404769163428453 4534514644950894218142835)
                ·
                  refine ⟨6801771967426341327214253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534514644950894218142835 6801771967426341327214253)
                  ·
                    refine ⟨2550664487784877997705345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6801771967426341327214253 2550664487784877997705345)
                    ·
                      refine ⟨1912998365838658498279009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550664487784877997705345 1912998365838658498279009)
                      ·
                        rfl

theorem cell23_3725551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 3, 2].length) (baseStart_3725551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725551 prefixEnd_3725551 := by exact prefixLift 3725551
  have htrace : WordTrace (prefixWord ++ tailWord_3725551) baseStart_3725551 baseEnd_3725551 := by
    simpa [prefixWord, tailWord_3725551, baseEnd_3725551] using wordTrace_append hprefix tailTrace_3725551
  have hstable : (prefixWord ++ tailWord_3725551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725551).length < 2 ^ (prefixWord ++ tailWord_3725551).sum := by decide
  have hdescent : baseEnd_3725551 < baseStart_3725551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725567 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_3725567 : Nat := 118140960795 + 3725567 * 2 ^ 59
def prefixEnd_3725567 : Nat := 4983230072969 + 3 ^ 40 * 3725567 * 2
def baseEnd_3725567 : Nat := 1913006581529130435678935

theorem tailTrace_3725567 : CollatzResearch.WordTrace tailWord_3725567 prefixEnd_3725567 1913006581529130435678935 := by
  unfold tailWord_3725567
  simp only [CollatzResearch.WordTrace]
  refine ⟨135882591693914510032174955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90588394462609673354783303 135882591693914510032174955)
  ·
    refine ⟨203823887540871765048262433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135882591693914510032174955 203823887540871765048262433)
    ·
      refine ⟨152867915655653823786196825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203823887540871765048262433 152867915655653823786196825)
      ·
        refine ⟨114650936741740367839647619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152867915655653823786196825 114650936741740367839647619)
        ·
          refine ⟨171976405112610551759471429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114650936741740367839647619 171976405112610551759471429)
          ·
            refine ⟨32245575958614478454900893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171976405112610551759471429 32245575958614478454900893)
            ·
              refine ⟨12092090984480429420587835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32245575958614478454900893 12092090984480429420587835)
              ·
                refine ⟨18138136476720644130881753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092090984480429420587835 18138136476720644130881753)
                ·
                  refine ⟨13603602357540483098161315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18138136476720644130881753 13603602357540483098161315)
                  ·
                    refine ⟨20405403536310724647241973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13603602357540483098161315 20405403536310724647241973)
                    ·
                      refine ⟨1913006581529130435678935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20405403536310724647241973 1913006581529130435678935)
                      ·
                        rfl

theorem cell23_3725567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_3725567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725567 prefixEnd_3725567 := by exact prefixLift 3725567
  have htrace : WordTrace (prefixWord ++ tailWord_3725567) baseStart_3725567 baseEnd_3725567 := by
    simpa [prefixWord, tailWord_3725567, baseEnd_3725567] using wordTrace_append hprefix tailTrace_3725567
  have hstable : (prefixWord ++ tailWord_3725567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725567).length < 2 ^ (prefixWord ++ tailWord_3725567).sum := by decide
  have hdescent : baseEnd_3725567 < baseStart_3725567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725637 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3725637 : Nat := 118140960795 + 3725637 * 2 ^ 59
def prefixEnd_3725637 : Nat := 4983230072969 + 3 ^ 40 * 3725637 * 2
def baseEnd_3725637 : Nat := 1913042525174945161803613

theorem tailTrace_3725637 : CollatzResearch.WordTrace tailWord_3725637 prefixEnd_3725637 1913042525174945161803613 := by
  unfold tailWord_3725637
  simp only [CollatzResearch.WordTrace]
  refine ⟨135885144803660911987223165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90590096535773941324815443 135885144803660911987223165)
  ·
    refine ⟨50956929301372841995208687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135885144803660911987223165 50956929301372841995208687)
    ·
      refine ⟨76435393952059262992813031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50956929301372841995208687 76435393952059262992813031)
      ·
        refine ⟨114653090928088894489219547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76435393952059262992813031 114653090928088894489219547)
        ·
          refine ⟨171979636392133341733829321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114653090928088894489219547 171979636392133341733829321)
          ·
            refine ⟨128984727294100006300371991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171979636392133341733829321 128984727294100006300371991)
            ·
              refine ⟨193477090941150009450557987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128984727294100006300371991 193477090941150009450557987)
              ·
                refine ⟨290215636411725014175836981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193477090941150009450557987 290215636411725014175836981)
                ·
                  refine ⟨27207715913599220078984717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290215636411725014175836981 27207715913599220078984717)
                  ·
                    refine ⟨10202893467599707529619269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27207715913599220078984717 10202893467599707529619269)
                    ·
                      refine ⟨1913042525174945161803613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10202893467599707529619269 1913042525174945161803613)
                      ·
                        rfl

theorem cell23_3725637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3725637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725637 prefixEnd_3725637 := by exact prefixLift 3725637
  have htrace : WordTrace (prefixWord ++ tailWord_3725637) baseStart_3725637 baseEnd_3725637 := by
    simpa [prefixWord, tailWord_3725637, baseEnd_3725637] using wordTrace_append hprefix tailTrace_3725637
  have hstable : (prefixWord ++ tailWord_3725637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725637).length < 2 ^ (prefixWord ++ tailWord_3725637).sum := by decide
  have hdescent : baseEnd_3725637 < baseStart_3725637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725671 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_3725671 : Nat := 118140960795 + 3725671 * 2 ^ 59
def prefixEnd_3725671 : Nat := 4983230072969 + 3 ^ 40 * 3725671 * 2
def baseEnd_3725671 : Nat := 1913059983517198028778457

theorem tailTrace_3725671 : CollatzResearch.WordTrace tailWord_3725671 prefixEnd_3725671 1913059983517198028778457 := by
  unfold tailWord_3725671
  simp only [CollatzResearch.WordTrace]
  refine ⟨135886384885537735793960867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90590923257025157195973911 135886384885537735793960867)
  ·
    refine ⟨203829577328306603690941301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135886384885537735793960867 203829577328306603690941301)
    ·
      refine ⟨19109022874528744096025747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203829577328306603690941301 19109022874528744096025747)
      ·
        refine ⟨28663534311793116144038621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19109022874528744096025747 28663534311793116144038621)
        ·
          refine ⟨10748825366922418554014483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28663534311793116144038621 10748825366922418554014483)
          ·
            refine ⟨16123238050383627831021725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748825366922418554014483 16123238050383627831021725)
            ·
              refine ⟨6046214268893860436633147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16123238050383627831021725 6046214268893860436633147)
              ·
                refine ⟨9069321403340790654949721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046214268893860436633147 9069321403340790654949721)
                ·
                  refine ⟨6801991052505592991212291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9069321403340790654949721 6801991052505592991212291)
                  ·
                    refine ⟨10202986578758389486818437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801991052505592991212291 10202986578758389486818437)
                    ·
                      refine ⟨1913059983517198028778457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10202986578758389486818437 1913059983517198028778457)
                      ·
                        rfl

theorem cell23_3725671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_3725671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725671 prefixEnd_3725671 := by exact prefixLift 3725671
  have htrace : WordTrace (prefixWord ++ tailWord_3725671) baseStart_3725671 baseEnd_3725671 := by
    simpa [prefixWord, tailWord_3725671, baseEnd_3725671] using wordTrace_append hprefix tailTrace_3725671
  have hstable : (prefixWord ++ tailWord_3725671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725671).length < 2 ^ (prefixWord ++ tailWord_3725671).sum := by decide
  have hdescent : baseEnd_3725671 < baseStart_3725671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725721 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 3]
def baseStart_3725721 : Nat := 118140960795 + 3725721 * 2 ^ 59
def prefixEnd_3725721 : Nat := 4983230072969 + 3 ^ 40 * 3725721 * 2
def baseEnd_3725721 : Nat := 1913085657549922833153227

theorem tailTrace_3725721 : CollatzResearch.WordTrace tailWord_3725721 prefixEnd_3725721 1913085657549922833153227 := by
  unfold tailWord_3725721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135888208535356594333281017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90592139023571062888854011 135888208535356594333281017)
  ·
    refine ⟨101916156401517445749960763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135888208535356594333281017 101916156401517445749960763)
    ·
      refine ⟨152874234602276168624941145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101916156401517445749960763 152874234602276168624941145)
      ·
        refine ⟨114655675951707126468705859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152874234602276168624941145 114655675951707126468705859)
        ·
          refine ⟨171983513927560689703058789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114655675951707126468705859 171983513927560689703058789)
          ·
            refine ⟨32246908861417629319323523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171983513927560689703058789 32246908861417629319323523)
            ·
              refine ⟨48370363292126443978985285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32246908861417629319323523 48370363292126443978985285)
              ·
                refine ⟨9069443117273708246059741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48370363292126443978985285 9069443117273708246059741)
                ·
                  refine ⟨3401041168977640592272403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9069443117273708246059741 3401041168977640592272403)
                  ·
                    refine ⟨5101561753466460888408605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3401041168977640592272403 5101561753466460888408605)
                    ·
                      refine ⟨1913085657549922833153227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5101561753466460888408605 1913085657549922833153227)
                      ·
                        rfl

theorem cell23_3725721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_3725721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725721 prefixEnd_3725721 := by exact prefixLift 3725721
  have htrace : WordTrace (prefixWord ++ tailWord_3725721) baseStart_3725721 baseEnd_3725721 := by
    simpa [prefixWord, tailWord_3725721, baseEnd_3725721] using wordTrace_append hprefix tailTrace_3725721
  have hstable : (prefixWord ++ tailWord_3725721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725721).length < 2 ^ (prefixWord ++ tailWord_3725721).sum := by decide
  have hdescent : baseEnd_3725721 < baseStart_3725721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
