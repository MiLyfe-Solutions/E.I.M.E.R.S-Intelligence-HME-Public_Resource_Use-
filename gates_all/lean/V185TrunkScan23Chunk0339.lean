import V185TrunkScan23Chunk0338

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2004769 : List Nat := [1, 2, 3, 2, 1, 4, 2, 8]
def baseStart_2004769 : Nat := 118140960795 + 2004769 * 2 ^ 59
def prefixEnd_2004769 : Nat := 4983230072969 + 3 ^ 40 * 2004769 * 2
def baseEnd_2004769 : Nat := 38126299934576743176583

theorem tailTrace_2004769 : CollatzResearch.WordTrace tailWord_2004769 prefixEnd_2004769 38126299934576743176583 := by
  unfold tailWord_2004769
  simp only [CollatzResearch.WordTrace]
  refine ⟨73119932474071775131465361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48746621649381183420976907 73119932474071775131465361)
  ·
    refine ⟨54839949355553831348599021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73119932474071775131465361 54839949355553831348599021)
    ·
      refine ⟨20564981008332686755724633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54839949355553831348599021 20564981008332686755724633)
      ·
        refine ⟨15423735756249515066793475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20564981008332686755724633 15423735756249515066793475)
        ·
          refine ⟨23135603634374272600190213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423735756249515066793475 23135603634374272600190213)
          ·
            refine ⟨4337925681445176112535665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23135603634374272600190213 4337925681445176112535665)
            ·
              refine ⟨3253444261083882084401749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337925681445176112535665 3253444261083882084401749)
              ·
                refine ⟨38126299934576743176583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3253444261083882084401749 38126299934576743176583)
                ·
                  rfl

theorem cell23_2004769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 8].length) (baseStart_2004769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004769 prefixEnd_2004769 := by exact prefixLift 2004769
  have htrace : WordTrace (prefixWord ++ tailWord_2004769) baseStart_2004769 baseEnd_2004769 := by
    simpa [prefixWord, tailWord_2004769, baseEnd_2004769] using wordTrace_append hprefix tailTrace_2004769
  have hstable : (prefixWord ++ tailWord_2004769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004769).length < 2 ^ (prefixWord ++ tailWord_2004769).sum := by decide
  have hdescent : baseEnd_2004769 < baseStart_2004769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004773 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 2, 4]
def baseStart_2004773 : Nat := 118140960795 + 2004773 * 2 ^ 59
def prefixEnd_2004773 : Nat := 4983230072969 + 3 ^ 40 * 2004773 * 2
def baseEnd_2004773 : Nat := 343137384052063350039241

theorem tailTrace_2004773 : CollatzResearch.WordTrace tailWord_2004773 prefixEnd_2004773 343137384052063350039241 := by
  unfold tailWord_2004773
  simp only [CollatzResearch.WordTrace]
  refine ⟨73120078366057283814610973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48746718910704855876407315 73120078366057283814610973)
  ·
    refine ⟨27420029387271481430479115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73120078366057283814610973 27420029387271481430479115)
    ·
      refine ⟨41130044080907222145718673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27420029387271481430479115 41130044080907222145718673)
      ·
        refine ⟨30847533060680416609289005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41130044080907222145718673 30847533060680416609289005)
        ·
          refine ⟨11567824897755156228483377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30847533060680416609289005 11567824897755156228483377)
          ·
            refine ⟨8675868673316367171362533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567824897755156228483377 8675868673316367171362533)
            ·
              refine ⟨1626725376246818844630475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8675868673316367171362533 1626725376246818844630475)
              ·
                refine ⟨2440088064370228266945713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626725376246818844630475 2440088064370228266945713)
                ·
                  refine ⟨1830066048277671200209285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440088064370228266945713 1830066048277671200209285)
                  ·
                    refine ⟨343137384052063350039241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830066048277671200209285 343137384052063350039241)
                    ·
                      rfl

theorem cell23_2004773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_2004773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004773 prefixEnd_2004773 := by exact prefixLift 2004773
  have htrace : WordTrace (prefixWord ++ tailWord_2004773) baseStart_2004773 baseEnd_2004773 := by
    simpa [prefixWord, tailWord_2004773, baseEnd_2004773] using wordTrace_append hprefix tailTrace_2004773
  have hstable : (prefixWord ++ tailWord_2004773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004773).length < 2 ^ (prefixWord ++ tailWord_2004773).sum := by decide
  have hdescent : baseEnd_2004773 < baseStart_2004773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004793 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2004793 : Nat := 118140960795 + 2004793 * 2 ^ 59
def prefixEnd_2004793 : Nat := 4983230072969 + 3 ^ 40 * 2004793 * 2
def baseEnd_2004793 : Nat := 1029422421769279971867631

theorem tailTrace_2004793 : CollatzResearch.WordTrace tailWord_2004793 prefixEnd_2004793 1029422421769279971867631 := by
  unfold tailWord_2004793
  simp only [CollatzResearch.WordTrace]
  refine ⟨73120807825984827230339033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48747205217323218153559355 73120807825984827230339033)
  ·
    refine ⟨54840605869488620422754275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73120807825984827230339033 54840605869488620422754275)
    ·
      refine ⟨82260908804232930634131413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54840605869488620422754275 82260908804232930634131413)
      ·
        refine ⟨1927990050099209311737455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82260908804232930634131413 1927990050099209311737455)
        ·
          refine ⟨2891985075148813967606183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927990050099209311737455 2891985075148813967606183)
          ·
            refine ⟨4337977612723220951409275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891985075148813967606183 4337977612723220951409275)
            ·
              refine ⟨6506966419084831427113913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337977612723220951409275 6506966419084831427113913)
              ·
                refine ⟨4880224814313623570335435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6506966419084831427113913 4880224814313623570335435)
                ·
                  refine ⟨7320337221470435355503153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880224814313623570335435 7320337221470435355503153)
                  ·
                    refine ⟨5490252916102826516627365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7320337221470435355503153 5490252916102826516627365)
                    ·
                      refine ⟨1029422421769279971867631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5490252916102826516627365 1029422421769279971867631)
                      ·
                        rfl

theorem cell23_2004793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2004793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004793 prefixEnd_2004793 := by exact prefixLift 2004793
  have htrace : WordTrace (prefixWord ++ tailWord_2004793) baseStart_2004793 baseEnd_2004793 := by
    simpa [prefixWord, tailWord_2004793, baseEnd_2004793] using wordTrace_append hprefix tailTrace_2004793
  have hstable : (prefixWord ++ tailWord_2004793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004793).length < 2 ^ (prefixWord ++ tailWord_2004793).sum := by decide
  have hdescent : baseEnd_2004793 < baseStart_2004793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004796 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_2004796 : Nat := 118140960795 + 2004796 * 2 ^ 59
def prefixEnd_2004796 : Nat := 4983230072969 + 3 ^ 40 * 2004796 * 2
def baseEnd_2004796 : Nat := 1029423962211243460130117

theorem tailTrace_2004796 : CollatzResearch.WordTrace tailWord_2004796 prefixEnd_2004796 1029423962211243460130117 := by
  unfold tailWord_2004796
  simp only [CollatzResearch.WordTrace]
  refine ⟨36560458622486979371349121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48747278163315972495132161 36560458622486979371349121)
  ·
    refine ⟨27420343966865234528511841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36560458622486979371349121 27420343966865234528511841)
    ·
      refine ⟨20565257975148925896383881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27420343966865234528511841 20565257975148925896383881)
      ·
        refine ⟨15423943481361694422287911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20565257975148925896383881 15423943481361694422287911)
        ·
          refine ⟨23135915222042541633431867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423943481361694422287911 23135915222042541633431867)
          ·
            refine ⟨34703872833063812450147801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23135915222042541633431867 34703872833063812450147801)
            ·
              refine ⟨26027904624797859337610851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34703872833063812450147801 26027904624797859337610851)
              ·
                refine ⟨39041856937196789006416277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26027904624797859337610851 39041856937196789006416277)
                ·
                  refine ⟨1830087043931099484675763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39041856937196789006416277 1830087043931099484675763)
                  ·
                    refine ⟨2745130565896649227013645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830087043931099484675763 2745130565896649227013645)
                    ·
                      refine ⟨1029423962211243460130117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745130565896649227013645 1029423962211243460130117)
                      ·
                        rfl

theorem cell23_2004796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_2004796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004796 prefixEnd_2004796 := by exact prefixLift 2004796
  have htrace : WordTrace (prefixWord ++ tailWord_2004796) baseStart_2004796 baseEnd_2004796 := by
    simpa [prefixWord, tailWord_2004796, baseEnd_2004796] using wordTrace_append hprefix tailTrace_2004796
  have hstable : (prefixWord ++ tailWord_2004796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004796).length < 2 ^ (prefixWord ++ tailWord_2004796).sum := by decide
  have hdescent : baseEnd_2004796 < baseStart_2004796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004849 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_2004849 : Nat := 118140960795 + 2004849 * 2 ^ 59
def prefixEnd_2004849 : Nat := 4983230072969 + 3 ^ 40 * 2004849 * 2
def baseEnd_2004849 : Nat := 1029451176685931752767373

theorem tailTrace_2004849 : CollatzResearch.WordTrace tailWord_2004849 prefixEnd_2004849 1029451176685931752767373 := by
  unfold tailWord_2004849
  simp only [CollatzResearch.WordTrace]
  refine ⟨73122850313781948794377601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48748566875854632529585067 73122850313781948794377601)
  ·
    refine ⟨54842137735336461595783201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73122850313781948794377601 54842137735336461595783201)
    ·
      refine ⟨41131603301502346196837401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54842137735336461595783201 41131603301502346196837401)
      ·
        refine ⟨30848702476126759647628051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41131603301502346196837401 30848702476126759647628051)
        ·
          refine ⟨46273053714190139471442077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30848702476126759647628051 46273053714190139471442077)
          ·
            refine ⟨17352395142821302301790779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46273053714190139471442077 17352395142821302301790779)
            ·
              refine ⟨26028592714231953452686169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17352395142821302301790779 26028592714231953452686169)
              ·
                refine ⟨19521444535673965089514627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26028592714231953452686169 19521444535673965089514627)
                ·
                  refine ⟨29282166803510947634271941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521444535673965089514627 29282166803510947634271941)
                  ·
                    refine ⟨5490406275658302681425989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29282166803510947634271941 5490406275658302681425989)
                    ·
                      refine ⟨1029451176685931752767373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5490406275658302681425989 1029451176685931752767373)
                      ·
                        rfl

theorem cell23_2004849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_2004849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004849 prefixEnd_2004849 := by exact prefixLift 2004849
  have htrace : WordTrace (prefixWord ++ tailWord_2004849) baseStart_2004849 baseEnd_2004849 := by
    simpa [prefixWord, tailWord_2004849, baseEnd_2004849] using wordTrace_append hprefix tailTrace_2004849
  have hstable : (prefixWord ++ tailWord_2004849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004849).length < 2 ^ (prefixWord ++ tailWord_2004849).sum := by decide
  have hdescent : baseEnd_2004849 < baseStart_2004849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004853 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_2004853 : Nat := 118140960795 + 2004853 * 2 ^ 59
def prefixEnd_2004853 : Nat := 4983230072969 + 3 ^ 40 * 2004853 * 2
def baseEnd_2004853 : Nat := 1029453230608549737117355

theorem tailTrace_2004853 : CollatzResearch.WordTrace tailWord_2004853 prefixEnd_2004853 1029453230608549737117355 := by
  unfold tailWord_2004853
  simp only [CollatzResearch.WordTrace]
  refine ⟨73122996205767457477523213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48748664137178304985015475 73122996205767457477523213)
  ·
    refine ⟨27421123577162796554071205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73122996205767457477523213 27421123577162796554071205)
    ·
      refine ⟨5141460670718024353888351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27421123577162796554071205 5141460670718024353888351)
      ·
        refine ⟨7712191006077036530832527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141460670718024353888351 7712191006077036530832527)
        ·
          refine ⟨11568286509115554796248791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712191006077036530832527 11568286509115554796248791)
          ·
            refine ⟨17352429763673332194373187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11568286509115554796248791 17352429763673332194373187)
            ·
              refine ⟨26028644645509998291559781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17352429763673332194373187 26028644645509998291559781)
              ·
                refine ⟨4880370871033124679667459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26028644645509998291559781 4880370871033124679667459)
                ·
                  refine ⟨7320556306549687019501189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880370871033124679667459 7320556306549687019501189)
                  ·
                    refine ⟨1372604307478066316156473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320556306549687019501189 1372604307478066316156473)
                    ·
                      refine ⟨1029453230608549737117355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372604307478066316156473 1029453230608549737117355)
                      ·
                        rfl

theorem cell23_2004853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_2004853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004853 prefixEnd_2004853 := by exact prefixLift 2004853
  have htrace : WordTrace (prefixWord ++ tailWord_2004853) baseStart_2004853 baseEnd_2004853 := by
    simpa [prefixWord, tailWord_2004853, baseEnd_2004853] using wordTrace_append hprefix tailTrace_2004853
  have hstable : (prefixWord ++ tailWord_2004853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004853).length < 2 ^ (prefixWord ++ tailWord_2004853).sum := by decide
  have hdescent : baseEnd_2004853 < baseStart_2004853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004887 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_2004887 : Nat := 118140960795 + 2004887 * 2 ^ 59
def prefixEnd_2004887 : Nat := 4983230072969 + 3 ^ 40 * 2004887 * 2
def baseEnd_2004887 : Nat := 1029470688950802604092199

theorem tailTrace_2004887 : CollatzResearch.WordTrace tailWord_2004887 prefixEnd_2004887 1029470688950802604092199 := by
  unfold tailWord_2004887
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124236287644281284260915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48749490858429520856173943 73124236287644281284260915)
  ·
    refine ⟨109686354431466421926391373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124236287644281284260915 109686354431466421926391373)
    ·
      refine ⟨41132382911799908222396765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109686354431466421926391373 41132382911799908222396765)
      ·
        refine ⟨15424643591924965583398787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41132382911799908222396765 15424643591924965583398787)
        ·
          refine ⟨23136965387887448375098181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15424643591924965583398787 23136965387887448375098181)
          ·
            refine ⟨4338181010228896570330909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23136965387887448375098181 4338181010228896570330909)
            ·
              refine ⟨1626817878835836213874091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4338181010228896570330909 1626817878835836213874091)
              ·
                refine ⟨2440226818253754320811137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626817878835836213874091 2440226818253754320811137)
                ·
                  refine ⟨1830170113690315740608353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440226818253754320811137 1830170113690315740608353)
                  ·
                    refine ⟨1372627585267736805456265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830170113690315740608353 1372627585267736805456265)
                    ·
                      refine ⟨1029470688950802604092199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372627585267736805456265 1029470688950802604092199)
                      ·
                        rfl

theorem cell23_2004887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_2004887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004887 prefixEnd_2004887 := by exact prefixLift 2004887
  have htrace : WordTrace (prefixWord ++ tailWord_2004887) baseStart_2004887 baseEnd_2004887 := by
    simpa [prefixWord, tailWord_2004887, baseEnd_2004887] using wordTrace_append hprefix tailTrace_2004887
  have hstable : (prefixWord ++ tailWord_2004887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004887).length < 2 ^ (prefixWord ++ tailWord_2004887).sum := by decide
  have hdescent : baseEnd_2004887 < baseStart_2004887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004889 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_2004889 : Nat := 118140960795 + 2004889 * 2 ^ 59
def prefixEnd_2004889 : Nat := 4983230072969 + 3 ^ 40 * 2004889 * 2
def baseEnd_2004889 : Nat := 343157238637370532089063

theorem tailTrace_2004889 : CollatzResearch.WordTrace tailWord_2004889 prefixEnd_2004889 343157238637370532089063 := by
  unfold tailWord_2004889
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124309233637035625833721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48749539489091357083889147 73124309233637035625833721)
  ·
    refine ⟨54843231925227776719375291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73124309233637035625833721 54843231925227776719375291)
    ·
      refine ⟨82264847887841665079062937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54843231925227776719375291 82264847887841665079062937)
      ·
        refine ⟨61698635915881248809297203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82264847887841665079062937 61698635915881248809297203)
        ·
          refine ⟨92547953873821873213945805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61698635915881248809297203 92547953873821873213945805)
          ·
            refine ⟨34705482702683202455229677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92547953873821873213945805 34705482702683202455229677)
            ·
              refine ⟨13014556013506200920711129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34705482702683202455229677 13014556013506200920711129)
              ·
                refine ⟨9760917010129650690533347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13014556013506200920711129 9760917010129650690533347)
                ·
                  refine ⟨14641375515194476035800021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760917010129650690533347 14641375515194476035800021)
                  ·
                    refine ⟨343157238637370532089063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14641375515194476035800021 343157238637370532089063)
                    ·
                      rfl

theorem cell23_2004889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_2004889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004889 prefixEnd_2004889 := by exact prefixLift 2004889
  have htrace : WordTrace (prefixWord ++ tailWord_2004889) baseStart_2004889 baseEnd_2004889 := by
    simpa [prefixWord, tailWord_2004889, baseEnd_2004889] using wordTrace_append hprefix tailTrace_2004889
  have hstable : (prefixWord ++ tailWord_2004889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004889).length < 2 ^ (prefixWord ++ tailWord_2004889).sum := by decide
  have hdescent : baseEnd_2004889 < baseStart_2004889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004899 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2004899 : Nat := 118140960795 + 2004899 * 2 ^ 59
def prefixEnd_2004899 : Nat := 4983230072969 + 3 ^ 40 * 2004899 * 2
def baseEnd_2004899 : Nat := 1029476850718656557142143

theorem tailTrace_2004899 : CollatzResearch.WordTrace tailWord_2004899 prefixEnd_2004899 1029476850718656557142143 := by
  unfold tailWord_2004899
  simp only [CollatzResearch.WordTrace]
  refine ⟨73124673963600807333697751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48749782642400538222465167 73124673963600807333697751)
  ·
    refine ⟨109687010945401211000546627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73124673963600807333697751 109687010945401211000546627)
    ·
      refine ⟨164530516418101816500819941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109687010945401211000546627 164530516418101816500819941)
      ·
        refine ⟨30849471828394090593903739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164530516418101816500819941 30849471828394090593903739)
        ·
          refine ⟨46274207742591135890855609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30849471828394090593903739 46274207742591135890855609)
          ·
            refine ⟨34705655806943351918141707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46274207742591135890855609 34705655806943351918141707)
            ·
              refine ⟨52058483710415027877212561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34705655806943351918141707 52058483710415027877212561)
              ·
                refine ⟨39043862782811270907909421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52058483710415027877212561 39043862782811270907909421)
                ·
                  refine ⟨14641448543554226590466033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39043862782811270907909421 14641448543554226590466033)
                  ·
                    refine ⟨10981086407665669942849525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14641448543554226590466033 10981086407665669942849525)
                    ·
                      refine ⟨1029476850718656557142143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10981086407665669942849525 1029476850718656557142143)
                      ·
                        rfl

theorem cell23_2004899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2004899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004899 prefixEnd_2004899 := by exact prefixLift 2004899
  have htrace : WordTrace (prefixWord ++ tailWord_2004899) baseStart_2004899 baseEnd_2004899 := by
    simpa [prefixWord, tailWord_2004899, baseEnd_2004899] using wordTrace_append hprefix tailTrace_2004899
  have hstable : (prefixWord ++ tailWord_2004899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004899).length < 2 ^ (prefixWord ++ tailWord_2004899).sum := by decide
  have hdescent : baseEnd_2004899 < baseStart_2004899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004963 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2004963 : Nat := 118140960795 + 2004963 * 2 ^ 59
def prefixEnd_2004963 : Nat := 4983230072969 + 3 ^ 40 * 2004963 * 2
def baseEnd_2004963 : Nat := 1029509713480544306741849

theorem tailTrace_2004963 : CollatzResearch.WordTrace tailWord_2004963 prefixEnd_2004963 1029509713480544306741849 := by
  unfold tailWord_2004963
  simp only [CollatzResearch.WordTrace]
  refine ⟨73127008235368946264027543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48751338823579297509351695 73127008235368946264027543)
  ·
    refine ⟨109690512353053419396041315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73127008235368946264027543 109690512353053419396041315)
    ·
      refine ⟨164535768529580129094061973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109690512353053419396041315 164535768529580129094061973)
      ·
        refine ⟨7712614149824068551284155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164535768529580129094061973 7712614149824068551284155)
        ·
          refine ⟨11568921224736102826926233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712614149824068551284155 11568921224736102826926233)
          ·
            refine ⟨8676690918552077120194675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11568921224736102826926233 8676690918552077120194675)
            ·
              refine ⟨13015036377828115680292013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676690918552077120194675 13015036377828115680292013)
              ·
                refine ⟨4880638641685543380109505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13015036377828115680292013 4880638641685543380109505)
                ·
                  refine ⟨3660478981264157535082129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4880638641685543380109505 3660478981264157535082129)
                  ·
                    refine ⟨2745359235948118151311597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660478981264157535082129 2745359235948118151311597)
                    ·
                      refine ⟨1029509713480544306741849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745359235948118151311597 1029509713480544306741849)
                      ·
                        rfl

theorem cell23_2004963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2004963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004963 prefixEnd_2004963 := by exact prefixLift 2004963
  have htrace : WordTrace (prefixWord ++ tailWord_2004963) baseStart_2004963 baseEnd_2004963 := by
    simpa [prefixWord, tailWord_2004963, baseEnd_2004963] using wordTrace_append hprefix tailTrace_2004963
  have hstable : (prefixWord ++ tailWord_2004963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004963).length < 2 ^ (prefixWord ++ tailWord_2004963).sum := by decide
  have hdescent : baseEnd_2004963 < baseStart_2004963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004970 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2004970 : Nat := 118140960795 + 2004970 * 2 ^ 59
def prefixEnd_2004970 : Nat := 4983230072969 + 3 ^ 40 * 2004970 * 2
def baseEnd_2004970 : Nat := 343171102615041926451439

theorem tailTrace_2004970 : CollatzResearch.WordTrace tailWord_2004970 prefixEnd_2004970 343171102615041926451439 := by
  unfold tailWord_2004970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281815886585896614883091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48751509030895724306354909 18281815886585896614883091)
  ·
    refine ⟨27422723829878844922324637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18281815886585896614883091 27422723829878844922324637)
    ·
      refine ⟨10283521436204566845871739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27422723829878844922324637 10283521436204566845871739)
      ·
        refine ⟨15425282154306850268807609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283521436204566845871739 15425282154306850268807609)
        ·
          refine ⟨11568961615730137701605707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15425282154306850268807609 11568961615730137701605707)
          ·
            refine ⟨17353442423595206552408561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11568961615730137701605707 17353442423595206552408561)
            ·
              refine ⟨13015081817696404914306421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17353442423595206552408561 13015081817696404914306421)
              ·
                refine ⟨1220163920409037960716227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13015081817696404914306421 1220163920409037960716227)
                ·
                  refine ⟨1830245880613556941074341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220163920409037960716227 1830245880613556941074341)
                  ·
                    refine ⟨343171102615041926451439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830245880613556941074341 343171102615041926451439)
                    ·
                      rfl

theorem cell23_2004970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2004970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004970 prefixEnd_2004970 := by exact prefixLift 2004970
  have htrace : WordTrace (prefixWord ++ tailWord_2004970) baseStart_2004970 baseEnd_2004970 := by
    simpa [prefixWord, tailWord_2004970, baseEnd_2004970] using wordTrace_append hprefix tailTrace_2004970
  have hstable : (prefixWord ++ tailWord_2004970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004970).length < 2 ^ (prefixWord ++ tailWord_2004970).sum := by decide
  have hdescent : baseEnd_2004970 < baseStart_2004970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005003 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 5, 2]
def baseStart_2005003 : Nat := 118140960795 + 2005003 * 2 ^ 59
def prefixEnd_2005003 : Nat := 4983230072969 + 3 ^ 40 * 2005003 * 2
def baseEnd_2005003 : Nat := 1029530252706724150241665

theorem tailTrace_2005003 : CollatzResearch.WordTrace tailWord_2005003 prefixEnd_2005003 1029530252706724150241665 := by
  unfold tailWord_2005003
  simp only [CollatzResearch.WordTrace]
  refine ⟨73128467155224033095483663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48752311436816022063655775 73128467155224033095483663)
  ·
    refine ⟨109692700732836049643225495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73128467155224033095483663 109692700732836049643225495)
    ·
      refine ⟨164539051099254074464838243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109692700732836049643225495 164539051099254074464838243)
      ·
        refine ⟨246808576648881111697257365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164539051099254074464838243 246808576648881111697257365)
        ·
          refine ⟨11569152030416302110808939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246808576648881111697257365 11569152030416302110808939)
          ·
            refine ⟨17353728045624453166213409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569152030416302110808939 17353728045624453166213409)
            ·
              refine ⟨13015296034218339874660057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17353728045624453166213409 13015296034218339874660057)
              ·
                refine ⟨9761472025663754905995043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13015296034218339874660057 9761472025663754905995043)
                ·
                  refine ⟨14642208038495632358992565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761472025663754905995043 14642208038495632358992565)
                  ·
                    refine ⟨1372707003608965533655553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14642208038495632358992565 1372707003608965533655553)
                    ·
                      refine ⟨1029530252706724150241665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372707003608965533655553 1029530252706724150241665)
                      ·
                        rfl

theorem cell23_2005003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5, 2].length) (baseStart_2005003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005003 prefixEnd_2005003 := by exact prefixLift 2005003
  have htrace : WordTrace (prefixWord ++ tailWord_2005003) baseStart_2005003 baseEnd_2005003 := by
    simpa [prefixWord, tailWord_2005003, baseEnd_2005003] using wordTrace_append hprefix tailTrace_2005003
  have hstable : (prefixWord ++ tailWord_2005003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005003).length < 2 ^ (prefixWord ++ tailWord_2005003).sum := by decide
  have hdescent : baseEnd_2005003 < baseStart_2005003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005006 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2005006 : Nat := 118140960795 + 2005006 * 2 ^ 59
def prefixEnd_2005006 : Nat := 4983230072969 + 3 ^ 40 * 2005006 * 2
def baseEnd_2005006 : Nat := 1029531793148687638504151

theorem tailTrace_2005006 : CollatzResearch.WordTrace tailWord_2005006 prefixEnd_2005006 1029531793148687638504151 := by
  unfold tailWord_2005006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141072071776645575980359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48752384382808776405228581 9141072071776645575980359)
  ·
    refine ⟨13711608107664968363970539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141072071776645575980359 13711608107664968363970539)
    ·
      refine ⟨20567412161497452545955809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13711608107664968363970539 20567412161497452545955809)
      ·
        refine ⟨15425559121123089409466857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20567412161497452545955809 15425559121123089409466857)
        ·
          refine ⟨11569169340842317057100143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15425559121123089409466857 11569169340842317057100143)
          ·
            refine ⟨17353754011263475585650215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569169340842317057100143 17353754011263475585650215)
            ·
              refine ⟨26030631016895213378475323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17353754011263475585650215 26030631016895213378475323)
              ·
                refine ⟨39045946525342820067712985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26030631016895213378475323 39045946525342820067712985)
                ·
                  refine ⟨29284459894007115050784739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39045946525342820067712985 29284459894007115050784739)
                  ·
                    refine ⟨43926689841010672576177109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29284459894007115050784739 43926689841010672576177109)
                    ·
                      refine ⟨1029531793148687638504151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43926689841010672576177109 1029531793148687638504151)
                      ·
                        rfl

theorem cell23_2005006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2005006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005006 prefixEnd_2005006 := by exact prefixLift 2005006
  have htrace : WordTrace (prefixWord ++ tailWord_2005006) baseStart_2005006 baseEnd_2005006 := by
    simpa [prefixWord, tailWord_2005006, baseEnd_2005006] using wordTrace_append hprefix tailTrace_2005006
  have hstable : (prefixWord ++ tailWord_2005006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005006).length < 2 ^ (prefixWord ++ tailWord_2005006).sum := by decide
  have hdescent : baseEnd_2005006 < baseStart_2005006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005020 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_2005020 : Nat := 118140960795 + 2005020 * 2 ^ 59
def prefixEnd_2005020 : Nat := 4983230072969 + 3 ^ 40 * 2005020 * 2
def baseEnd_2005020 : Nat := 1029538981877850583729087

theorem tailTrace_2005020 : CollatzResearch.WordTrace tailWord_2005020 prefixEnd_2005020 1029538981877850583729087 := by
  unfold tailWord_2005020
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564543598081222499426257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48752724797441629999235009 36564543598081222499426257)
  ·
    refine ⟨27423407698560916874569693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36564543598081222499426257 27423407698560916874569693)
    ·
      refine ⟨10283777886960343827963635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27423407698560916874569693 10283777886960343827963635)
      ·
        refine ⟨15425666830440515741945453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283777886960343827963635 15425666830440515741945453)
        ·
          refine ⟨5784625061415193403229545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15425666830440515741945453 5784625061415193403229545)
          ·
            refine ⟨4338468796061395052422159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784625061415193403229545 4338468796061395052422159)
            ·
              refine ⟨6507703194092092578633239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338468796061395052422159 6507703194092092578633239)
              ·
                refine ⟨9761554791138138867949859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507703194092092578633239 9761554791138138867949859)
                ·
                  refine ⟨14642332186707208301924789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9761554791138138867949859 14642332186707208301924789)
                  ·
                    refine ⟨1372718642503800778305449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14642332186707208301924789 1372718642503800778305449)
                    ·
                      refine ⟨1029538981877850583729087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372718642503800778305449 1029538981877850583729087)
                      ·
                        rfl

theorem cell23_2005020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_2005020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005020 prefixEnd_2005020 := by exact prefixLift 2005020
  have htrace : WordTrace (prefixWord ++ tailWord_2005020) baseStart_2005020 baseEnd_2005020 := by
    simpa [prefixWord, tailWord_2005020, baseEnd_2005020] using wordTrace_append hprefix tailTrace_2005020
  have hstable : (prefixWord ++ tailWord_2005020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005020).length < 2 ^ (prefixWord ++ tailWord_2005020).sum := by decide
  have hdescent : baseEnd_2005020 < baseStart_2005020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005027 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 1, 1, 3]
def baseStart_2005027 : Nat := 118140960795 + 2005027 * 2 ^ 59
def prefixEnd_2005027 : Nat := 4983230072969 + 3 ^ 40 * 2005027 * 2
def baseEnd_2005027 : Nat := 1029542576242432056341555

theorem tailTrace_2005027 : CollatzResearch.WordTrace tailWord_2005027 prefixEnd_2005027 1029542576242432056341555 := by
  unfold tailWord_2005027
  simp only [CollatzResearch.WordTrace]
  refine ⟨73129342507137085194357335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48752895004758056796238223 73129342507137085194357335)
  ·
    refine ⟨109694013760705627791536003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73129342507137085194357335 109694013760705627791536003)
    ·
      refine ⟨164541020641058441687304005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109694013760705627791536003 164541020641058441687304005)
      ·
        refine ⟨30851441370198457816369501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164541020641058441687304005 30851441370198457816369501)
        ·
          refine ⟨11569290513824421681138563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30851441370198457816369501 11569290513824421681138563)
          ·
            refine ⟨17353935770736632521707845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569290513824421681138563 17353935770736632521707845)
            ·
              refine ⟨3253862957013118597820221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17353935770736632521707845 3253862957013118597820221)
              ·
                refine ⟨1220198608879919474182583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3253862957013118597820221 1220198608879919474182583)
                ·
                  refine ⟨1830297913319879211273875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220198608879919474182583 1830297913319879211273875)
                  ·
                    refine ⟨2745446869979818816910813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830297913319879211273875 2745446869979818816910813)
                    ·
                      refine ⟨1029542576242432056341555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745446869979818816910813 1029542576242432056341555)
                      ·
                        rfl

theorem cell23_2005027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_2005027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005027 prefixEnd_2005027 := by exact prefixLift 2005027
  have htrace : WordTrace (prefixWord ++ tailWord_2005027) baseStart_2005027 baseEnd_2005027 := by
    simpa [prefixWord, tailWord_2005027, baseEnd_2005027] using wordTrace_append hprefix tailTrace_2005027
  have hstable : (prefixWord ++ tailWord_2005027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005027).length < 2 ^ (prefixWord ++ tailWord_2005027).sum := by decide
  have hdescent : baseEnd_2005027 < baseStart_2005027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005044 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2005044 : Nat := 118140960795 + 2005044 * 2 ^ 59
def prefixEnd_2005044 : Nat := 4983230072969 + 3 ^ 40 * 2005044 * 2
def baseEnd_2005044 : Nat := 1029551305413558489828977

theorem tailTrace_2005044 : CollatzResearch.WordTrace tailWord_2005044 prefixEnd_2005044 1029551305413558489828977 := by
  unfold tailWord_2005044
  simp only [CollatzResearch.WordTrace]
  refine ⟨36564981274037748548863093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48753308365383664731817457 36564981274037748548863093)
  ·
    refine ⟨3427966994441038926455915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36564981274037748548863093 3427966994441038926455915)
    ·
      refine ⟨5141950491661558389683873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427966994441038926455915 5141950491661558389683873)
      ·
        refine ⟨3856462868746168792262905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5141950491661558389683873 3856462868746168792262905)
        ·
          refine ⟨2892347151559626594197179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856462868746168792262905 2892347151559626594197179)
          ·
            refine ⟨4338520727339439891295769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892347151559626594197179 4338520727339439891295769)
            ·
              refine ⟨3253890545504579918471827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4338520727339439891295769 3253890545504579918471827)
              ·
                refine ⟨4880835818256869877707741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3253890545504579918471827 4880835818256869877707741)
                ·
                  refine ⟨1830313431846326204140403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4880835818256869877707741 1830313431846326204140403)
                  ·
                    refine ⟨2745470147769489306210605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830313431846326204140403 2745470147769489306210605)
                    ·
                      refine ⟨1029551305413558489828977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745470147769489306210605 1029551305413558489828977)
                      ·
                        rfl

theorem cell23_2005044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2005044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005044 prefixEnd_2005044 := by exact prefixLift 2005044
  have htrace : WordTrace (prefixWord ++ tailWord_2005044) baseStart_2005044 baseEnd_2005044 := by
    simpa [prefixWord, tailWord_2005044, baseEnd_2005044] using wordTrace_append hprefix tailTrace_2005044
  have hstable : (prefixWord ++ tailWord_2005044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005044).length < 2 ^ (prefixWord ++ tailWord_2005044).sum := by decide
  have hdescent : baseEnd_2005044 < baseStart_2005044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005053 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2005053 : Nat := 118140960795 + 2005053 * 2 ^ 59
def prefixEnd_2005053 : Nat := 4983230072969 + 3 ^ 40 * 2005053 * 2
def baseEnd_2005053 : Nat := 1029555926739448954616435

theorem tailTrace_2005053 : CollatzResearch.WordTrace tailWord_2005053 prefixEnd_2005053 1029555926739448954616435 := by
  unfold tailWord_2005053
  simp only [CollatzResearch.WordTrace]
  refine ⟨73130290805042891634803813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48753527203361927756535875 73130290805042891634803813)
  ·
    refine ⟨13711929525945542181525715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73130290805042891634803813 13711929525945542181525715)
    ·
      refine ⟨20567894288918313272288573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13711929525945542181525715 20567894288918313272288573)
      ·
        refine ⟨7712960358344367477108215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20567894288918313272288573 7712960358344367477108215)
        ·
          refine ⟨11569440537516551215662323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712960358344367477108215 11569440537516551215662323)
          ·
            refine ⟨17354160806274826823493485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569440537516551215662323 17354160806274826823493485)
            ·
              refine ⟨6507810302353060058810057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17354160806274826823493485 6507810302353060058810057)
              ·
                refine ⟨4880857726764795044107543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507810302353060058810057 4880857726764795044107543)
                ·
                  refine ⟨7321286590147192566161315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880857726764795044107543 7321286590147192566161315)
                  ·
                    refine ⟨10981929885220788849241973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321286590147192566161315 10981929885220788849241973)
                    ·
                      refine ⟨1029555926739448954616435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10981929885220788849241973 1029555926739448954616435)
                      ·
                        rfl

theorem cell23_2005053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2005053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005053 prefixEnd_2005053 := by exact prefixLift 2005053
  have htrace : WordTrace (prefixWord ++ tailWord_2005053) baseStart_2005053 baseEnd_2005053 := by
    simpa [prefixWord, tailWord_2005053, baseEnd_2005053] using wordTrace_append hprefix tailTrace_2005053
  have hstable : (prefixWord ++ tailWord_2005053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005053).length < 2 ^ (prefixWord ++ tailWord_2005053).sum := by decide
  have hdescent : baseEnd_2005053 < baseStart_2005053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005070 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_2005070 : Nat := 118140960795 + 2005070 * 2 ^ 59
def prefixEnd_2005070 : Nat := 4983230072969 + 3 ^ 40 * 2005070 * 2
def baseEnd_2005070 : Nat := 1029564655910575388103857

theorem tailTrace_2005070 : CollatzResearch.WordTrace tailWord_2005070 prefixEnd_2005070 1029564655910575388103857 := by
  unfold tailWord_2005070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141363855747662942271583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48753940563987535692115109 9141363855747662942271583)
  ·
    refine ⟨13712045783621494413407375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141363855747662942271583 13712045783621494413407375)
    ·
      refine ⟨20568068675432241620111063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712045783621494413407375 20568068675432241620111063)
      ·
        refine ⟨30852103013148362430166595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20568068675432241620111063 30852103013148362430166595)
        ·
          refine ⟨46278154519722543645249893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30852103013148362430166595 46278154519722543645249893)
          ·
            refine ⟨8677153972447976933484355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46278154519722543645249893 8677153972447976933484355)
            ·
              refine ⟨13015730958671965400226533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8677153972447976933484355 13015730958671965400226533)
              ·
                refine ⟨2440449554750993512542475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13015730958671965400226533 2440449554750993512542475)
                ·
                  refine ⟨3660674332126490268813713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440449554750993512542475 3660674332126490268813713)
                  ·
                    refine ⟨2745505749094867701610285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660674332126490268813713 2745505749094867701610285)
                    ·
                      refine ⟨1029564655910575388103857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745505749094867701610285 1029564655910575388103857)
                      ·
                        rfl

theorem cell23_2005070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_2005070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005070 prefixEnd_2005070 := by exact prefixLift 2005070
  have htrace : WordTrace (prefixWord ++ tailWord_2005070) baseStart_2005070 baseEnd_2005070 := by
    simpa [prefixWord, tailWord_2005070, baseEnd_2005070] using wordTrace_append hprefix tailTrace_2005070
  have hstable : (prefixWord ++ tailWord_2005070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005070).length < 2 ^ (prefixWord ++ tailWord_2005070).sum := by decide
  have hdescent : baseEnd_2005070 < baseStart_2005070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005078 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2005078 : Nat := 118140960795 + 2005078 * 2 ^ 59
def prefixEnd_2005078 : Nat := 4983230072969 + 3 ^ 40 * 2005078 * 2
def baseEnd_2005078 : Nat := 1029568763755811356803821

theorem tailTrace_2005078 : CollatzResearch.WordTrace tailWord_2005078 prefixEnd_2005078 1029568763755811356803821 := by
  unfold tailWord_2005078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570700164372020056528993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48754135086634880602975925 4570700164372020056528993)
  ·
    refine ⟨3428025123279015042396745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4570700164372020056528993 3428025123279015042396745)
    ·
      refine ⟨2571018842459261281797559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3428025123279015042396745 2571018842459261281797559)
      ·
        refine ⟨3856528263688891922696339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571018842459261281797559 3856528263688891922696339)
        ·
          refine ⟨5784792395533337884044509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856528263688891922696339 5784792395533337884044509)
          ·
            refine ⟨2169297148325001706516691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5784792395533337884044509 2169297148325001706516691)
            ·
              refine ⟨3253945722487502559775037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169297148325001706516691 3253945722487502559775037)
              ·
                refine ⟨1220229645932813459915639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3253945722487502559775037 1220229645932813459915639)
                ·
                  refine ⟨1830344468899220189873459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220229645932813459915639 1830344468899220189873459)
                  ·
                    refine ⟨2745516703348830284810189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830344468899220189873459 2745516703348830284810189)
                    ·
                      refine ⟨1029568763755811356803821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745516703348830284810189 1029568763755811356803821)
                      ·
                        rfl

theorem cell23_2005078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2005078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005078 prefixEnd_2005078 := by exact prefixLift 2005078
  have htrace : WordTrace (prefixWord ++ tailWord_2005078) baseStart_2005078 baseEnd_2005078 := by
    simpa [prefixWord, tailWord_2005078, baseEnd_2005078] using wordTrace_append hprefix tailTrace_2005078
  have hstable : (prefixWord ++ tailWord_2005078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005078).length < 2 ^ (prefixWord ++ tailWord_2005078).sum := by decide
  have hdescent : baseEnd_2005078 < baseStart_2005078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005090 : List Nat := [3, 3, 2, 2, 2, 2, 9]
def baseStart_2005090 : Nat := 118140960795 + 2005090 * 2 ^ 59
def prefixEnd_2005090 : Nat := 4983230072969 + 3 ^ 40 * 2005090 * 2
def baseEnd_2005090 : Nat := 12710801549674880368565

theorem tailTrace_2005090 : CollatzResearch.WordTrace tailWord_2005090 prefixEnd_2005090 12710801549674880368565 := by
  unfold tailWord_2005090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282910076477211738475181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48754426870605897969267149 18282910076477211738475181)
  ·
    refine ⟨6856091278678954401928193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18282910076477211738475181 6856091278678954401928193)
    ·
      refine ⟨5142068459009215801446145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6856091278678954401928193 5142068459009215801446145)
      ·
        refine ⟨3856551344256911851084609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5142068459009215801446145 3856551344256911851084609)
        ·
          refine ⟨2892413508192683888313457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856551344256911851084609 2892413508192683888313457)
          ·
            refine ⟨2169310131144512916235093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892413508192683888313457 2169310131144512916235093)
            ·
              refine ⟨12710801549674880368565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2169310131144512916235093 12710801549674880368565)
              ·
                rfl

theorem cell23_2005090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 9].length) (baseStart_2005090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005090 prefixEnd_2005090 := by exact prefixLift 2005090
  have htrace : WordTrace (prefixWord ++ tailWord_2005090) baseStart_2005090 baseEnd_2005090 := by
    simpa [prefixWord, tailWord_2005090, baseEnd_2005090] using wordTrace_append hprefix tailTrace_2005090
  have hstable : (prefixWord ++ tailWord_2005090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005090).length < 2 ^ (prefixWord ++ tailWord_2005090).sum := by decide
  have hdescent : baseEnd_2005090 < baseStart_2005090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005100 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_2005100 : Nat := 118140960795 + 2005100 * 2 ^ 59
def prefixEnd_2005100 : Nat := 4983230072969 + 3 ^ 40 * 2005100 * 2
def baseEnd_2005100 : Nat := 1029580060330210270728719

theorem tailTrace_2005100 : CollatzResearch.WordTrace tailWord_2005100 prefixEnd_2005100 1029580060330210270728719 := by
  unfold tailWord_2005100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566002517936309330882377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48754670023915079107843169 36566002517936309330882377)
  ·
    refine ⟨27424501888452231998161783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36566002517936309330882377 27424501888452231998161783)
    ·
      refine ⟨41136752832678347997242675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27424501888452231998161783 41136752832678347997242675)
      ·
        refine ⟨61705129249017521995864013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41136752832678347997242675 61705129249017521995864013)
        ·
          refine ⟨23139423468381570748449005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61705129249017521995864013 23139423468381570748449005)
          ·
            refine ⟨8677283800643089030668377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23139423468381570748449005 8677283800643089030668377)
            ·
              refine ⟨6507962850482316773001283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8677283800643089030668377 6507962850482316773001283)
              ·
                refine ⟨9761944275723475159501925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507962850482316773001283 9761944275723475159501925)
                ·
                  refine ⟨1830364551698151592406611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9761944275723475159501925 1830364551698151592406611)
                  ·
                    refine ⟨2745546827547227388609917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830364551698151592406611 2745546827547227388609917)
                    ·
                      refine ⟨1029580060330210270728719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745546827547227388609917 1029580060330210270728719)
                      ·
                        rfl

theorem cell23_2005100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_2005100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005100 prefixEnd_2005100 := by exact prefixLift 2005100
  have htrace : WordTrace (prefixWord ++ tailWord_2005100) baseStart_2005100 baseEnd_2005100 := by
    simpa [prefixWord, tailWord_2005100, baseEnd_2005100] using wordTrace_append hprefix tailTrace_2005100
  have hstable : (prefixWord ++ tailWord_2005100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005100).length < 2 ^ (prefixWord ++ tailWord_2005100).sum := by decide
  have hdescent : baseEnd_2005100 < baseStart_2005100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005101 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2005101 : Nat := 118140960795 + 2005101 * 2 ^ 59
def prefixEnd_2005101 : Nat := 4983230072969 + 3 ^ 40 * 2005101 * 2
def baseEnd_2005101 : Nat := 1029580573810864766816215

theorem tailTrace_2005101 : CollatzResearch.WordTrace tailWord_2005101 prefixEnd_2005101 1029580573810864766816215 := by
  unfold tailWord_2005101
  simp only [CollatzResearch.WordTrace]
  refine ⟨73132041508868995832551157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48754694339245997221700771 73132041508868995832551157)
  ·
    refine ⟨6856128891456468359301671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73132041508868995832551157 6856128891456468359301671)
    ·
      refine ⟨10284193337184702538952507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856128891456468359301671 10284193337184702538952507)
      ·
        refine ⟨15426290005777053808428761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284193337184702538952507 15426290005777053808428761)
        ·
          refine ⟨11569717504332790356321571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15426290005777053808428761 11569717504332790356321571)
          ·
            refine ⟨17354576256499185534482357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569717504332790356321571 17354576256499185534482357)
            ·
              refine ⟨1626991524046798643857721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17354576256499185534482357 1626991524046798643857721)
              ·
                refine ⟨1220243643035098982893291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626991524046798643857721 1220243643035098982893291)
                ·
                  refine ⟨1830365464552648474339937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220243643035098982893291 1830365464552648474339937)
                  ·
                    refine ⟨1372774098414486355754953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830365464552648474339937 1372774098414486355754953)
                    ·
                      refine ⟨1029580573810864766816215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372774098414486355754953 1029580573810864766816215)
                      ·
                        rfl

theorem cell23_2005101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2005101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005101 prefixEnd_2005101 := by exact prefixLift 2005101
  have htrace : WordTrace (prefixWord ++ tailWord_2005101) baseStart_2005101 baseEnd_2005101 := by
    simpa [prefixWord, tailWord_2005101, baseEnd_2005101] using wordTrace_append hprefix tailTrace_2005101
  have hstable : (prefixWord ++ tailWord_2005101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005101).length < 2 ^ (prefixWord ++ tailWord_2005101).sum := by decide
  have hdescent : baseEnd_2005101 < baseStart_2005101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005117 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_2005117 : Nat := 118140960795 + 2005117 * 2 ^ 59
def prefixEnd_2005117 : Nat := 4983230072969 + 3 ^ 40 * 2005117 * 2
def baseEnd_2005117 : Nat := 1029588789501336704216141

theorem tailTrace_2005117 : CollatzResearch.WordTrace tailWord_2005117 prefixEnd_2005117 1029588789501336704216141 := by
  unfold tailWord_2005117
  simp only [CollatzResearch.WordTrace]
  refine ⟨73132625076811030565133605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48755083384540687043422403 73132625076811030565133605)
  ·
    refine ⟨13712367201902068230962551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73132625076811030565133605 13712367201902068230962551)
    ·
      refine ⟨20568550802853102346443827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712367201902068230962551 20568550802853102346443827)
      ·
        refine ⟨30852826204279653519665741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20568550802853102346443827 30852826204279653519665741)
        ·
          refine ⟨11569809826604870069874653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30852826204279653519665741 11569809826604870069874653)
          ·
            refine ⟨4338678684976826276202995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11569809826604870069874653 4338678684976826276202995)
            ·
              refine ⟨6508018027465239414304493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338678684976826276202995 6508018027465239414304493)
              ·
                refine ⟨2440506760299464780364185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6508018027465239414304493 2440506760299464780364185)
                ·
                  refine ⟨1830380070224598585273139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440506760299464780364185 1830380070224598585273139)
                  ·
                    refine ⟨2745570105336897877909709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830380070224598585273139 2745570105336897877909709)
                    ·
                      refine ⟨1029588789501336704216141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745570105336897877909709 1029588789501336704216141)
                      ·
                        rfl

theorem cell23_2005117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_2005117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005117 prefixEnd_2005117 := by exact prefixLift 2005117
  have htrace : WordTrace (prefixWord ++ tailWord_2005117) baseStart_2005117 baseEnd_2005117 := by
    simpa [prefixWord, tailWord_2005117, baseEnd_2005117] using wordTrace_append hprefix tailTrace_2005117
  have hstable : (prefixWord ++ tailWord_2005117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005117).length < 2 ^ (prefixWord ++ tailWord_2005117).sum := by decide
  have hdescent : baseEnd_2005117 < baseStart_2005117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005127 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_2005127 : Nat := 118140960795 + 2005127 * 2 ^ 59
def prefixEnd_2005127 : Nat := 4983230072969 + 3 ^ 40 * 2005127 * 2
def baseEnd_2005127 : Nat := 1029593924307881665091095

theorem tailTrace_2005127 : CollatzResearch.WordTrace tailWord_2005127 prefixEnd_2005127 1029593924307881665091095 := by
  unfold tailWord_2005127
  simp only [CollatzResearch.WordTrace]
  refine ⟨73132989806774802272997635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48755326537849868181998423 73132989806774802272997635)
  ·
    refine ⟨109699484710162203409496453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73132989806774802272997635 109699484710162203409496453)
    ·
      refine ⟨20568653383155413139280585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109699484710162203409496453 20568653383155413139280585)
      ·
        refine ⟨15426490037366559854460439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20568653383155413139280585 15426490037366559854460439)
        ·
          refine ⟨23139735056049839781690659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15426490037366559854460439 23139735056049839781690659)
          ·
            refine ⟨34709602584074759672535989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23139735056049839781690659 34709602584074759672535989)
            ·
              refine ⟨3254025242257008719300249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34709602584074759672535989 3254025242257008719300249)
              ·
                refine ⟨2440518931692756539475187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254025242257008719300249 2440518931692756539475187)
                ·
                  refine ⟨3660778397539134809212781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440518931692756539475187 3660778397539134809212781)
                  ·
                    refine ⟨1372791899077175553454793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3660778397539134809212781 1372791899077175553454793)
                    ·
                      refine ⟨1029593924307881665091095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372791899077175553454793 1029593924307881665091095)
                      ·
                        rfl

theorem cell23_2005127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_2005127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005127 prefixEnd_2005127 := by exact prefixLift 2005127
  have htrace : WordTrace (prefixWord ++ tailWord_2005127) baseStart_2005127 baseEnd_2005127 := by
    simpa [prefixWord, tailWord_2005127, baseEnd_2005127] using wordTrace_append hprefix tailTrace_2005127
  have hstable : (prefixWord ++ tailWord_2005127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005127).length < 2 ^ (prefixWord ++ tailWord_2005127).sum := by decide
  have hdescent : baseEnd_2005127 < baseStart_2005127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005180 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 7]
def baseStart_2005180 : Nat := 118140960795 + 2005180 * 2 ^ 59
def prefixEnd_2005180 : Nat := 4983230072969 + 3 ^ 40 * 2005180 * 2
def baseEnd_2005180 : Nat := 114402348753618884192039

theorem tailTrace_2005180 : CollatzResearch.WordTrace tailWord_2005180 prefixEnd_2005180 114402348753618884192039 := by
  unfold tailWord_2005180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36567461437791396162338497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48756615250388528216451329 36567461437791396162338497)
  ·
    refine ⟨27425596078343547121753873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36567461437791396162338497 27425596078343547121753873)
    ·
      refine ⟨20569197058757660341315405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27425596078343547121753873 20569197058757660341315405)
      ·
        refine ⟨7713448897034122627993277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20569197058757660341315405 7713448897034122627993277)
        ·
          refine ⟨2892543336387795985497479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7713448897034122627993277 2892543336387795985497479)
          ·
            refine ⟨4338815004581693978246219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892543336387795985497479 4338815004581693978246219)
            ·
              refine ⟨6508222506872540967369329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338815004581693978246219 6508222506872540967369329)
              ·
                refine ⟨4881166880154405725526997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6508222506872540967369329 4881166880154405725526997)
                ·
                  refine ⟨114402348753618884192039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4881166880154405725526997 114402348753618884192039)
                  ·
                    rfl

theorem cell23_2005180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_2005180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005180 prefixEnd_2005180 := by exact prefixLift 2005180
  have htrace : WordTrace (prefixWord ++ tailWord_2005180) baseStart_2005180 baseEnd_2005180 := by
    simpa [prefixWord, tailWord_2005180, baseEnd_2005180] using wordTrace_append hprefix tailTrace_2005180
  have hstable : (prefixWord ++ tailWord_2005180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005180).length < 2 ^ (prefixWord ++ tailWord_2005180).sum := by decide
  have hdescent : baseEnd_2005180 < baseStart_2005180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005193 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_2005193 : Nat := 118140960795 + 2005193 * 2 ^ 59
def prefixEnd_2005193 : Nat := 4983230072969 + 3 ^ 40 * 2005193 * 2
def baseEnd_2005193 : Nat := 343209271343692802288597

theorem tailTrace_2005193 : CollatzResearch.WordTrace tailWord_2005193 prefixEnd_2005193 343209271343692802288597 := by
  unfold tailWord_2005193
  simp only [CollatzResearch.WordTrace]
  refine ⟨73135397024535695544900233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48756931349690463696600155 73135397024535695544900233)
  ·
    refine ⟨54851547768401771658675175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73135397024535695544900233 54851547768401771658675175)
    ·
      refine ⟨82277321652602657488012763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54851547768401771658675175 82277321652602657488012763)
      ·
        refine ⟨123415982478903986232019145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82277321652602657488012763 123415982478903986232019145)
        ·
          refine ⟨92561986859177989674014359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123415982478903986232019145 92561986859177989674014359)
          ·
            refine ⟨138842980288766984511021539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92561986859177989674014359 138842980288766984511021539)
            ·
              refine ⟨208264470433150476766532309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138842980288766984511021539 208264470433150476766532309)
              ·
                refine ⟨4881198525776964299215601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208264470433150476766532309 4881198525776964299215601)
                ·
                  refine ⟨3660898894332723224411701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881198525776964299215601 3660898894332723224411701)
                  ·
                    refine ⟨343209271343692802288597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3660898894332723224411701 343209271343692802288597)
                    ·
                      rfl

theorem cell23_2005193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_2005193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005193 prefixEnd_2005193 := by exact prefixLift 2005193
  have htrace : WordTrace (prefixWord ++ tailWord_2005193) baseStart_2005193 baseEnd_2005193 := by
    simpa [prefixWord, tailWord_2005193, baseEnd_2005193] using wordTrace_append hprefix tailTrace_2005193
  have hstable : (prefixWord ++ tailWord_2005193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005193).length < 2 ^ (prefixWord ++ tailWord_2005193).sum := by decide
  have hdescent : baseEnd_2005193 < baseStart_2005193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005274 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_2005274 : Nat := 118140960795 + 2005274 * 2 ^ 59
def prefixEnd_2005274 : Nat := 4983230072969 + 3 ^ 40 * 2005274 * 2
def baseEnd_2005274 : Nat := 343223135321364196650973

theorem tailTrace_2005274 : CollatzResearch.WordTrace tailWord_2005274 prefixEnd_2005274 343223135321364196650973 := by
  unfold tailWord_2005274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284587834310561594649719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48758900891494830919065917 18284587834310561594649719)
  ·
    refine ⟨27426881751465842391974579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18284587834310561594649719 27426881751465842391974579)
    ·
      refine ⟨41140322627198763587961869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27426881751465842391974579 41140322627198763587961869)
      ·
        refine ⟨15427620985199536345485701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41140322627198763587961869 15427620985199536345485701)
        ·
          refine ⟨2892678934724913064778569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15427620985199536345485701 2892678934724913064778569)
          ·
            refine ⟨2169509201043684798583927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892678934724913064778569 2169509201043684798583927)
            ·
              refine ⟨3254263801565527197875891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169509201043684798583927 3254263801565527197875891)
              ·
                refine ⟨4881395702348290796813837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254263801565527197875891 4881395702348290796813837)
                ·
                  refine ⟨1830523388380609048805189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4881395702348290796813837 1830523388380609048805189)
                  ·
                    refine ⟨343223135321364196650973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830523388380609048805189 343223135321364196650973)
                    ·
                      rfl

theorem cell23_2005274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_2005274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005274 prefixEnd_2005274 := by exact prefixLift 2005274
  have htrace : WordTrace (prefixWord ++ tailWord_2005274) baseStart_2005274 baseEnd_2005274 := by
    simpa [prefixWord, tailWord_2005274, baseEnd_2005274] using wordTrace_append hprefix tailTrace_2005274
  have hstable : (prefixWord ++ tailWord_2005274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005274).length < 2 ^ (prefixWord ++ tailWord_2005274).sum := by decide
  have hdescent : baseEnd_2005274 < baseStart_2005274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005347 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 2, 4]
def baseStart_2005347 : Nat := 118140960795 + 2005347 * 2 ^ 59
def prefixEnd_2005347 : Nat := 4983230072969 + 3 ^ 40 * 2005347 * 2
def baseEnd_2005347 : Nat := 343235630017290268113361

theorem tailTrace_2005347 : CollatzResearch.WordTrace tailWord_2005347 prefixEnd_2005347 343235630017290268113361 := by
  unfold tailWord_2005347
  simp only [CollatzResearch.WordTrace]
  refine ⟨73141013865977779846006295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48760675910651853230670863 73141013865977779846006295)
  ·
    refine ⟨109711520798966669769009443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73141013865977779846006295 109711520798966669769009443)
    ·
      refine ⟨164567281198450004653514165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109711520798966669769009443 164567281198450004653514165)
      ·
        refine ⟨15428182612354687936266953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164567281198450004653514165 15428182612354687936266953)
        ·
          refine ⟨11571136959266015952200215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15428182612354687936266953 11571136959266015952200215)
          ·
            refine ⟨17356705438899023928300323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11571136959266015952200215 17356705438899023928300323)
            ·
              refine ⟨26035058158348535892450485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17356705438899023928300323 26035058158348535892450485)
              ·
                refine ⟨2440786702345175239917233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26035058158348535892450485 2440786702345175239917233)
                ·
                  refine ⟨1830590026758881429937925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440786702345175239917233 1830590026758881429937925)
                  ·
                    refine ⟨343235630017290268113361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830590026758881429937925 343235630017290268113361)
                    ·
                      rfl

theorem cell23_2005347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 4].length) (baseStart_2005347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005347 prefixEnd_2005347 := by exact prefixLift 2005347
  have htrace : WordTrace (prefixWord ++ tailWord_2005347) baseStart_2005347 baseEnd_2005347 := by
    simpa [prefixWord, tailWord_2005347, baseEnd_2005347] using wordTrace_append hprefix tailTrace_2005347
  have hstable : (prefixWord ++ tailWord_2005347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005347).length < 2 ^ (prefixWord ++ tailWord_2005347).sum := by decide
  have hdescent : baseEnd_2005347 < baseStart_2005347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005357 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2005357 : Nat := 118140960795 + 2005357 * 2 ^ 59
def prefixEnd_2005357 : Nat := 4983230072969 + 3 ^ 40 * 2005357 * 2
def baseEnd_2005357 : Nat := 1029712024858415765215037

theorem tailTrace_2005357 : CollatzResearch.WordTrace tailWord_2005357 prefixEnd_2005357 1029712024858415765215037 := by
  unfold tailWord_2005357
  simp only [CollatzResearch.WordTrace]
  refine ⟨73141378595941551553870325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48760919063961034369246883 73141378595941551553870325)
  ·
    refine ⟨6857004243369520458175343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73141378595941551553870325 6857004243369520458175343)
    ·
      refine ⟨10285506365054280687263015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857004243369520458175343 10285506365054280687263015)
      ·
        refine ⟨15428259547581421030894523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285506365054280687263015 15428259547581421030894523)
        ·
          refine ⟨23142389321372131546341785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15428259547581421030894523 23142389321372131546341785)
          ·
            refine ⟨17356791991029098659756339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23142389321372131546341785 17356791991029098659756339)
            ·
              refine ⟨26035187986543647989634509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17356791991029098659756339 26035187986543647989634509)
              ·
                refine ⟨9763195494953867996112941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26035187986543647989634509 9763195494953867996112941)
                ·
                  refine ⟨3661198310607700498542353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9763195494953867996112941 3661198310607700498542353)
                  ·
                    refine ⟨2745898732955775373906765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661198310607700498542353 2745898732955775373906765)
                    ·
                      refine ⟨1029712024858415765215037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745898732955775373906765 1029712024858415765215037)
                      ·
                        rfl

theorem cell23_2005357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2005357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005357 prefixEnd_2005357 := by exact prefixLift 2005357
  have htrace : WordTrace (prefixWord ++ tailWord_2005357) baseStart_2005357 baseEnd_2005357 := by
    simpa [prefixWord, tailWord_2005357, baseEnd_2005357] using wordTrace_append hprefix tailTrace_2005357
  have hstable : (prefixWord ++ tailWord_2005357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005357).length < 2 ^ (prefixWord ++ tailWord_2005357).sum := by decide
  have hdescent : baseEnd_2005357 < baseStart_2005357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005371 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 1, 2, 2]
def baseStart_2005371 : Nat := 118140960795 + 2005371 * 2 ^ 59
def prefixEnd_2005371 : Nat := 4983230072969 + 3 ^ 40 * 2005371 * 2
def baseEnd_2005371 : Nat := 1029719213587578710439973

theorem tailTrace_2005371 : CollatzResearch.WordTrace tailWord_2005371 prefixEnd_2005371 1029719213587578710439973 := by
  unfold tailWord_2005371
  simp only [CollatzResearch.WordTrace]
  refine ⟨73141889217890831944879967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48761259478593887963253311 73141889217890831944879967)
  ·
    refine ⟨109712833826836247917319951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73141889217890831944879967 109712833826836247917319951)
    ·
      refine ⟨164569250740254371875979927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109712833826836247917319951 164569250740254371875979927)
      ·
        refine ⟨246853876110381557813969891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164569250740254371875979927 246853876110381557813969891)
        ·
          refine ⟨370280814165572336720954837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246853876110381557813969891 370280814165572336720954837)
          ·
            refine ⟨8678456582005601641897379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 370280814165572336720954837 8678456582005601641897379)
            ·
              refine ⟨13017684873008402462846069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678456582005601641897379 13017684873008402462846069)
              ·
                refine ⟨1220407956844537730891819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13017684873008402462846069 1220407956844537730891819)
                ·
                  refine ⟨1830611935266806596337729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220407956844537730891819 1830611935266806596337729)
                  ·
                    refine ⟨1372958951450104947253297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830611935266806596337729 1372958951450104947253297)
                    ·
                      refine ⟨1029719213587578710439973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372958951450104947253297 1029719213587578710439973)
                      ·
                        rfl

theorem cell23_2005371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 1, 2, 2].length) (baseStart_2005371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005371 prefixEnd_2005371 := by exact prefixLift 2005371
  have htrace : WordTrace (prefixWord ++ tailWord_2005371) baseStart_2005371 baseEnd_2005371 := by
    simpa [prefixWord, tailWord_2005371, baseEnd_2005371] using wordTrace_append hprefix tailTrace_2005371
  have hstable : (prefixWord ++ tailWord_2005371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005371).length < 2 ^ (prefixWord ++ tailWord_2005371).sum := by decide
  have hdescent : baseEnd_2005371 < baseStart_2005371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005494 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2005494 : Nat := 118140960795 + 2005494 * 2 ^ 59
def prefixEnd_2005494 : Nat := 4983230072969 + 3 ^ 40 * 2005494 * 2
def baseEnd_2005494 : Nat := 1029782371708081729201907

theorem tailTrace_2005494 : CollatzResearch.WordTrace tailWord_2005494 prefixEnd_2005494 1029782371708081729201907 := by
  unfold tailWord_2005494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571648462277826496975471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48764250264296815967738357 4571648462277826496975471)
  ·
    refine ⟨6857472693416739745463207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571648462277826496975471 6857472693416739745463207)
    ·
      refine ⟨10286209040125109618194811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857472693416739745463207 10286209040125109618194811)
      ·
        refine ⟨15429313560187664427292217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10286209040125109618194811 15429313560187664427292217)
        ·
          refine ⟨11571985170140748320469163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15429313560187664427292217 11571985170140748320469163)
          ·
            refine ⟨17357977755211122480703745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11571985170140748320469163 17357977755211122480703745)
            ·
              refine ⟨13018483316408341860527809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17357977755211122480703745 13018483316408341860527809)
              ·
                refine ⟨9763862487306256395395857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13018483316408341860527809 9763862487306256395395857)
                ·
                  refine ⟨7322896865479692296546893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9763862487306256395395857 7322896865479692296546893)
                  ·
                    refine ⟨2746086324554884611205085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7322896865479692296546893 2746086324554884611205085)
                    ·
                      refine ⟨1029782371708081729201907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746086324554884611205085 1029782371708081729201907)
                      ·
                        rfl

theorem cell23_2005494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2005494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005494 prefixEnd_2005494 := by exact prefixLift 2005494
  have htrace : WordTrace (prefixWord ++ tailWord_2005494) baseStart_2005494 baseEnd_2005494 := by
    simpa [prefixWord, tailWord_2005494, baseEnd_2005494] using wordTrace_append hprefix tailTrace_2005494
  have hstable : (prefixWord ++ tailWord_2005494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005494).length < 2 ^ (prefixWord ++ tailWord_2005494).sum := by decide
  have hdescent : baseEnd_2005494 < baseStart_2005494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005497 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_2005497 : Nat := 118140960795 + 2005497 * 2 ^ 59
def prefixEnd_2005497 : Nat := 4983230072969 + 3 ^ 40 * 2005497 * 2
def baseEnd_2005497 : Nat := 343261304050015072488131

theorem tailTrace_2005497 : CollatzResearch.WordTrace tailWord_2005497 prefixEnd_2005497 343261304050015072488131 := by
  unfold tailWord_2005497
  simp only [CollatzResearch.WordTrace]
  refine ⟨73146484815434355463966745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48764323210289570309311163 73146484815434355463966745)
  ·
    refine ⟨54859863611575766597975059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73146484815434355463966745 54859863611575766597975059)
    ·
      refine ⟨82289795417363649896962589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54859863611575766597975059 82289795417363649896962589)
      ·
        refine ⟨30858673281511368711360971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82289795417363649896962589 30858673281511368711360971)
        ·
          refine ⟨46288009922267053067041457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30858673281511368711360971 46288009922267053067041457)
          ·
            refine ⟨34716007441700289800281093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46288009922267053067041457 34716007441700289800281093)
            ·
              refine ⟨6509251395318804337552705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34716007441700289800281093 6509251395318804337552705)
              ·
                refine ⟨4881938546489103253164529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6509251395318804337552705 4881938546489103253164529)
                ·
                  refine ⟨3661453909866827439873397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881938546489103253164529 3661453909866827439873397)
                  ·
                    refine ⟨343261304050015072488131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3661453909866827439873397 343261304050015072488131)
                    ·
                      rfl

theorem cell23_2005497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_2005497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005497 prefixEnd_2005497 := by exact prefixLift 2005497
  have htrace : WordTrace (prefixWord ++ tailWord_2005497) baseStart_2005497 baseEnd_2005497 := by
    simpa [prefixWord, tailWord_2005497, baseEnd_2005497] using wordTrace_append hprefix tailTrace_2005497
  have hstable : (prefixWord ++ tailWord_2005497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005497).length < 2 ^ (prefixWord ++ tailWord_2005497).sum := by decide
  have hdescent : baseEnd_2005497 < baseStart_2005497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005554 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2005554 : Nat := 118140960795 + 2005554 * 2 ^ 59
def prefixEnd_2005554 : Nat := 4983230072969 + 3 ^ 40 * 2005554 * 2
def baseEnd_2005554 : Nat := 1029813180547351494451631

theorem tailTrace_2005554 : CollatzResearch.WordTrace tailWord_2005554 prefixEnd_2005554 1029813180547351494451631 := by
  unfold tailWord_2005554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18287140944056963549697929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48765709184151902799194477 18287140944056963549697929)
  ·
    refine ⟨13715355708042722662273447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18287140944056963549697929 13715355708042722662273447)
    ·
      refine ⟨20573033562064083993410171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13715355708042722662273447 20573033562064083993410171)
      ·
        refine ⟨30859550343096125990115257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20573033562064083993410171 30859550343096125990115257)
        ·
          refine ⟨23144662757322094492586443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30859550343096125990115257 23144662757322094492586443)
          ·
            refine ⟨34716994135983141738879665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23144662757322094492586443 34716994135983141738879665)
            ·
              refine ⟨26037745601987356304159749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34716994135983141738879665 26037745601987356304159749)
              ·
                refine ⟨4882077300372629307029953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26037745601987356304159749 4882077300372629307029953)
                ·
                  refine ⟨3661557975279471980272465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882077300372629307029953 3661557975279471980272465)
                  ·
                    refine ⟨2746168481459603985204349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661557975279471980272465 2746168481459603985204349)
                    ·
                      refine ⟨1029813180547351494451631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746168481459603985204349 1029813180547351494451631)
                      ·
                        rfl

theorem cell23_2005554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2005554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005554 prefixEnd_2005554 := by exact prefixLift 2005554
  have htrace : WordTrace (prefixWord ++ tailWord_2005554) baseStart_2005554 baseEnd_2005554 := by
    simpa [prefixWord, tailWord_2005554, baseEnd_2005554] using wordTrace_append hprefix tailTrace_2005554
  have hstable : (prefixWord ++ tailWord_2005554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005554).length < 2 ^ (prefixWord ++ tailWord_2005554).sum := by decide
  have hdescent : baseEnd_2005554 < baseStart_2005554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005557 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 8]
def baseStart_2005557 : Nat := 118140960795 + 2005557 * 2 ^ 59
def prefixEnd_2005557 : Nat := 4983230072969 + 3 ^ 40 * 2005557 * 2
def baseEnd_2005557 : Nat := 114423857887701664746013

theorem tailTrace_2005557 : CollatzResearch.WordTrace tailWord_2005557 prefixEnd_2005557 114423857887701664746013 := by
  unfold tailWord_2005557
  simp only [CollatzResearch.WordTrace]
  refine ⟨73148673195216985711150925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48765782130144657140767283 73148673195216985711150925)
  ·
    refine ⟨27430752448206369641681597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73148673195216985711150925 27430752448206369641681597)
    ·
      refine ⟨10286532168077388615630599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27430752448206369641681597 10286532168077388615630599)
      ·
        refine ⟨15429798252116082923445899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10286532168077388615630599 15429798252116082923445899)
        ·
          refine ⟨23144697378174124385168849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429798252116082923445899 23144697378174124385168849)
          ·
            refine ⟨17358523033630593288876637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23144697378174124385168849 17358523033630593288876637)
            ·
              refine ⟨6509446137611472483328739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17358523033630593288876637 6509446137611472483328739)
              ·
                refine ⟨9764169206417208724993109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6509446137611472483328739 9764169206417208724993109)
                ·
                  refine ⟨114423857887701664746013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9764169206417208724993109 114423857887701664746013)
                  ·
                    rfl

theorem cell23_2005557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_2005557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005557 prefixEnd_2005557 := by exact prefixLift 2005557
  have htrace : WordTrace (prefixWord ++ tailWord_2005557) baseStart_2005557 baseEnd_2005557 := by
    simpa [prefixWord, tailWord_2005557, baseEnd_2005557] using wordTrace_append hprefix tailTrace_2005557
  have hstable : (prefixWord ++ tailWord_2005557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005557).length < 2 ^ (prefixWord ++ tailWord_2005557).sum := by decide
  have hdescent : baseEnd_2005557 < baseStart_2005557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005561 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 1, 4]
def baseStart_2005561 : Nat := 118140960795 + 2005561 * 2 ^ 59
def prefixEnd_2005561 : Nat := 4983230072969 + 3 ^ 40 * 2005561 * 2
def baseEnd_2005561 : Nat := 343272258303977655688033

theorem tailTrace_2005561 : CollatzResearch.WordTrace tailWord_2005561 prefixEnd_2005561 343272258303977655688033 := by
  unfold tailWord_2005561
  simp only [CollatzResearch.WordTrace]
  refine ⟨73148819087202494394296537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48765879391468329596197691 73148819087202494394296537)
  ·
    refine ⟨54861614315401870795722403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73148819087202494394296537 54861614315401870795722403)
    ·
      refine ⟨82292421473102806193583605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54861614315401870795722403 82292421473102806193583605)
      ·
        refine ⟨7714914513103388080648463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82292421473102806193583605 7714914513103388080648463)
        ·
          refine ⟨11572371769655082120972695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7714914513103388080648463 11572371769655082120972695)
          ·
            refine ⟨17358557654482623181459043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11572371769655082120972695 17358557654482623181459043)
            ·
              refine ⟨26037836481723934772188565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17358557654482623181459043 26037836481723934772188565)
              ·
                refine ⟨1220523585080809442446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26037836481723934772188565 1220523585080809442446339)
                ·
                  refine ⟨1830785377621214163669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220523585080809442446339 1830785377621214163669509)
                  ·
                    refine ⟨343272258303977655688033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830785377621214163669509 343272258303977655688033)
                    ·
                      rfl

theorem cell23_2005561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 4].length) (baseStart_2005561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005561 prefixEnd_2005561 := by exact prefixLift 2005561
  have htrace : WordTrace (prefixWord ++ tailWord_2005561) baseStart_2005561 baseEnd_2005561 := by
    simpa [prefixWord, tailWord_2005561, baseEnd_2005561] using wordTrace_append hprefix tailTrace_2005561
  have hstable : (prefixWord ++ tailWord_2005561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005561).length < 2 ^ (prefixWord ++ tailWord_2005561).sum := by decide
  have hdescent : baseEnd_2005561 < baseStart_2005561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005584 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3]
def baseStart_2005584 : Nat := 118140960795 + 2005584 * 2 ^ 59
def prefixEnd_2005584 : Nat := 4983230072969 + 3 ^ 40 * 2005584 * 2
def baseEnd_2005584 : Nat := 1029828584966986377076493

theorem tailTrace_2005584 : CollatzResearch.WordTrace tailWord_2005584 prefixEnd_2005584 1029828584966986377076493 := by
  unfold tailWord_2005584
  simp only [CollatzResearch.WordTrace]
  refine ⟨36574828983059584661191903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48766438644079446214922537 36574828983059584661191903)
  ·
    refine ⟨54862243474589376991787855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36574828983059584661191903 54862243474589376991787855)
    ·
      refine ⟨82293365211884065487681783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54862243474589376991787855 82293365211884065487681783)
      ·
        refine ⟨123440047817826098231522675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82293365211884065487681783 123440047817826098231522675)
        ·
          refine ⟨185160071726739147347284013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123440047817826098231522675 185160071726739147347284013)
          ·
            refine ⟨69435026897527180255231505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185160071726739147347284013 69435026897527180255231505)
            ·
              refine ⟨52076270173145385191423629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69435026897527180255231505 52076270173145385191423629)
              ·
                refine ⟨19528601314929519446783861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52076270173145385191423629 19528601314929519446783861)
                ·
                  refine ⟨1830806373274642448135987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19528601314929519446783861 1830806373274642448135987)
                  ·
                    refine ⟨2746209559911963672203981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830806373274642448135987 2746209559911963672203981)
                    ·
                      refine ⟨1029828584966986377076493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746209559911963672203981 1029828584966986377076493)
                      ·
                        rfl

theorem cell23_2005584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_2005584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005584 prefixEnd_2005584 := by exact prefixLift 2005584
  have htrace : WordTrace (prefixWord ++ tailWord_2005584) baseStart_2005584 baseEnd_2005584 := by
    simpa [prefixWord, tailWord_2005584, baseEnd_2005584] using wordTrace_append hprefix tailTrace_2005584
  have hstable : (prefixWord ++ tailWord_2005584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005584).length < 2 ^ (prefixWord ++ tailWord_2005584).sum := by decide
  have hdescent : baseEnd_2005584 < baseStart_2005584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005604 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_2005604 : Nat := 118140960795 + 2005604 * 2 ^ 59
def prefixEnd_2005604 : Nat := 4983230072969 + 3 ^ 40 * 2005604 * 2
def baseEnd_2005604 : Nat := 343279618193358766275467

theorem tailTrace_2005604 : CollatzResearch.WordTrace tailWord_2005604 prefixEnd_2005604 343279618193358766275467 := by
  unfold tailWord_2005604
  simp only [CollatzResearch.WordTrace]
  refine ⟨36575193713023356369055933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48766924950697808492074577 36575193713023356369055933)
  ·
    refine ⟨13715697642383758638395975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36575193713023356369055933 13715697642383758638395975)
    ·
      refine ⟨20573546463575637957593963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13715697642383758638395975 20573546463575637957593963)
      ·
        refine ⟨30860319695363456936390945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20573546463575637957593963 30860319695363456936390945)
        ·
          refine ⟨23145239771522592702293209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30860319695363456936390945 23145239771522592702293209)
          ·
            refine ⟨17358929828641944526719907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23145239771522592702293209 17358929828641944526719907)
            ·
              refine ⟨26038394742962916790079861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17358929828641944526719907 26038394742962916790079861)
              ·
                refine ⟨2441099507152773449069987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26038394742962916790079861 2441099507152773449069987)
                ·
                  refine ⟨3661649260729160173604981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441099507152773449069987 3661649260729160173604981)
                  ·
                    refine ⟨343279618193358766275467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3661649260729160173604981 343279618193358766275467)
                    ·
                      rfl

theorem cell23_2005604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_2005604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005604 prefixEnd_2005604 := by exact prefixLift 2005604
  have htrace : WordTrace (prefixWord ++ tailWord_2005604) baseStart_2005604 baseEnd_2005604 := by
    simpa [prefixWord, tailWord_2005604, baseEnd_2005604] using wordTrace_append hprefix tailTrace_2005604
  have hstable : (prefixWord ++ tailWord_2005604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005604).length < 2 ^ (prefixWord ++ tailWord_2005604).sum := by decide
  have hdescent : baseEnd_2005604 < baseStart_2005604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005627 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_2005627 : Nat := 118140960795 + 2005627 * 2 ^ 59
def prefixEnd_2005627 : Nat := 4983230072969 + 3 ^ 40 * 2005627 * 2
def baseEnd_2005627 : Nat := 1029850664635129708838795

theorem tailTrace_2005627 : CollatzResearch.WordTrace tailWord_2005627 prefixEnd_2005627 1029850664635129708838795 := by
  unfold tailWord_2005627
  simp only [CollatzResearch.WordTrace]
  refine ⟨73151226304963387666199135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48767484203308925110799423 73151226304963387666199135)
  ·
    refine ⟨109726839457445081499298703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73151226304963387666199135 109726839457445081499298703)
    ·
      refine ⟨164590259186167622248948055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109726839457445081499298703 164590259186167622248948055)
      ·
        refine ⟨246885388779251433373422083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164590259186167622248948055 246885388779251433373422083)
        ·
          refine ⟨370328083168877150060133125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246885388779251433373422083 370328083168877150060133125)
          ·
            refine ⟨69436515594164465636274961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370328083168877150060133125 69436515594164465636274961)
            ·
              refine ⟨52077386695623349227206221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69436515594164465636274961 52077386695623349227206221)
              ·
                refine ⟨19529020010858755960202333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52077386695623349227206221 19529020010858755960202333)
                ·
                  refine ⟨7323382504072033485075875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19529020010858755960202333 7323382504072033485075875)
                  ·
                    refine ⟨10985073756108050227613813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323382504072033485075875 10985073756108050227613813)
                    ·
                      refine ⟨1029850664635129708838795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10985073756108050227613813 1029850664635129708838795)
                      ·
                        rfl

theorem cell23_2005627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_2005627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005627 prefixEnd_2005627 := by exact prefixLift 2005627
  have htrace : WordTrace (prefixWord ++ tailWord_2005627) baseStart_2005627 baseEnd_2005627 := by
    simpa [prefixWord, tailWord_2005627, baseEnd_2005627] using wordTrace_append hprefix tailTrace_2005627
  have hstable : (prefixWord ++ tailWord_2005627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005627).length < 2 ^ (prefixWord ++ tailWord_2005627).sum := by decide
  have hdescent : baseEnd_2005627 < baseStart_2005627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005641 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 5, 2, 2]
def baseStart_2005641 : Nat := 118140960795 + 2005641 * 2 ^ 59
def prefixEnd_2005641 : Nat := 4983230072969 + 3 ^ 40 * 2005641 * 2
def baseEnd_2005641 : Nat := 1029857853364292654063731

theorem tailTrace_2005641 : CollatzResearch.WordTrace tailWord_2005641 prefixEnd_2005641 1029857853364292654063731 := by
  unfold tailWord_2005641
  simp only [CollatzResearch.WordTrace]
  refine ⟨73151736926912668057208777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48767824617941778704805851 73151736926912668057208777)
  ·
    refine ⟨54863802695184501042906583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73151736926912668057208777 54863802695184501042906583)
    ·
      refine ⟨82295704042776751564359875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54863802695184501042906583 82295704042776751564359875)
      ·
        refine ⟨123443556064165127346539813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82295704042776751564359875 123443556064165127346539813)
        ·
          refine ⟨23145666762030961377476215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123443556064165127346539813 23145666762030961377476215)
          ·
            refine ⟨34718500143046442066214323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23145666762030961377476215 34718500143046442066214323)
            ·
              refine ⟨52077750214569663099321485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34718500143046442066214323 52077750214569663099321485)
              ·
                refine ⟨19529156330463623662245557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52077750214569663099321485 19529156330463623662245557)
                ·
                  refine ⟨1830858405980964718335521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19529156330463623662245557 1830858405980964718335521)
                  ·
                    refine ⟨1373143804485723538751641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830858405980964718335521 1373143804485723538751641)
                    ·
                      refine ⟨1029857853364292654063731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373143804485723538751641 1029857853364292654063731)
                      ·
                        rfl

theorem cell23_2005641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2, 2].length) (baseStart_2005641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005641 prefixEnd_2005641 := by exact prefixLift 2005641
  have htrace : WordTrace (prefixWord ++ tailWord_2005641) baseStart_2005641 baseEnd_2005641 := by
    simpa [prefixWord, tailWord_2005641, baseEnd_2005641] using wordTrace_append hprefix tailTrace_2005641
  have hstable : (prefixWord ++ tailWord_2005641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005641).length < 2 ^ (prefixWord ++ tailWord_2005641).sum := by decide
  have hdescent : baseEnd_2005641 < baseStart_2005641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005661 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2005661 : Nat := 118140960795 + 2005661 * 2 ^ 59
def prefixEnd_2005661 : Nat := 4983230072969 + 3 ^ 40 * 2005661 * 2
def baseEnd_2005661 : Nat := 1029868122977382575813639

theorem tailTrace_2005661 : CollatzResearch.WordTrace tailWord_2005661 prefixEnd_2005661 1029868122977382575813639 := by
  unfold tailWord_2005661
  simp only [CollatzResearch.WordTrace]
  refine ⟨73152466386840211472936837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48768310924560140981957891 73152466386840211472936837)
  ·
    refine ⟨13716087447532539651175657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73152466386840211472936837 13716087447532539651175657)
    ·
      refine ⟨10287065585649404738381743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13716087447532539651175657 10287065585649404738381743)
      ·
        refine ⟨15430598378474107107572615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10287065585649404738381743 15430598378474107107572615)
        ·
          refine ⟨23145897567711160661358923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15430598378474107107572615 23145897567711160661358923)
          ·
            refine ⟨34718846351566740992038385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23145897567711160661358923 34718846351566740992038385)
            ·
              refine ⟨26039134763675055744028789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34718846351566740992038385 26039134763675055744028789)
              ·
                refine ⟨2441168884094536476002699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26039134763675055744028789 2441168884094536476002699)
                ·
                  refine ⟨3661753326141804714004049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441168884094536476002699 3661753326141804714004049)
                  ·
                    refine ⟨2746314994606353535503037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661753326141804714004049 2746314994606353535503037)
                    ·
                      refine ⟨1029868122977382575813639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746314994606353535503037 1029868122977382575813639)
                      ·
                        rfl

theorem cell23_2005661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2005661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005661 prefixEnd_2005661 := by exact prefixLift 2005661
  have htrace : WordTrace (prefixWord ++ tailWord_2005661) baseStart_2005661 baseEnd_2005661 := by
    simpa [prefixWord, tailWord_2005661, baseEnd_2005661] using wordTrace_append hprefix tailTrace_2005661
  have hstable : (prefixWord ++ tailWord_2005661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005661).length < 2 ^ (prefixWord ++ tailWord_2005661).sum := by decide
  have hdescent : baseEnd_2005661 < baseStart_2005661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005664 : List Nat := [2, 1, 1, 4, 5, 10]
def baseStart_2005664 : Nat := 118140960795 + 2005664 * 2 ^ 59
def prefixEnd_2005664 : Nat := 4983230072969 + 3 ^ 40 * 2005664 * 2
def baseEnd_2005664 : Nat := 4238146763042576395375

theorem tailTrace_2005664 : CollatzResearch.WordTrace tailWord_2005664 prefixEnd_2005664 4238146763042576395375 := by
  unfold tailWord_2005664
  simp only [CollatzResearch.WordTrace]
  refine ⟨36576287902914671492648023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48768383870552895323530697 36576287902914671492648023)
  ·
    refine ⟨54864431854372007238972035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36576287902914671492648023 54864431854372007238972035)
    ·
      refine ⟨82296647781558010858458053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54864431854372007238972035 82296647781558010858458053)
      ·
        refine ⟨15430621459042127035960885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82296647781558010858458053 15430621459042127035960885)
        ·
          refine ⟨1446620761785199409621333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15430621459042127035960885 1446620761785199409621333)
          ·
            refine ⟨4238146763042576395375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1446620761785199409621333 4238146763042576395375)
            ·
              rfl

theorem cell23_2005664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 10].length) (baseStart_2005664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005664 prefixEnd_2005664 := by exact prefixLift 2005664
  have htrace : WordTrace (prefixWord ++ tailWord_2005664) baseStart_2005664 baseEnd_2005664 := by
    simpa [prefixWord, tailWord_2005664, baseEnd_2005664] using wordTrace_append hprefix tailTrace_2005664
  have hstable : (prefixWord ++ tailWord_2005664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005664).length < 2 ^ (prefixWord ++ tailWord_2005664).sum := by decide
  have hdescent : baseEnd_2005664 < baseStart_2005664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005667 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2005667 : Nat := 118140960795 + 2005667 * 2 ^ 59
def prefixEnd_2005667 : Nat := 4983230072969 + 3 ^ 40 * 2005667 * 2
def baseEnd_2005667 : Nat := 1029871203861309552338611

theorem tailTrace_2005667 : CollatzResearch.WordTrace tailWord_2005667 prefixEnd_2005667 1029871203861309552338611 := by
  unfold tailWord_2005667
  simp only [CollatzResearch.WordTrace]
  refine ⟨73152685224818474497655255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48768456816545649665103503 73152685224818474497655255)
  ·
    refine ⟨109729027837227711746482883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73152685224818474497655255 109729027837227711746482883)
    ·
      refine ⟨164593541755841567619724325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109729027837227711746482883 164593541755841567619724325)
      ·
        refine ⟨30861289079220293928698311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164593541755841567619724325 30861289079220293928698311)
        ·
          refine ⟨46291933618830440893047467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30861289079220293928698311 46291933618830440893047467)
          ·
            refine ⟨69437900428245661339571201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46291933618830440893047467 69437900428245661339571201)
            ·
              refine ⟨52078425321184246004678401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69437900428245661339571201 52078425321184246004678401)
              ·
                refine ⟨39058818990888184503508801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52078425321184246004678401 39058818990888184503508801)
                ·
                  refine ⟨29294114243166138377631601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39058818990888184503508801 29294114243166138377631601)
                  ·
                    refine ⟨21970585682374603783223701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29294114243166138377631601 21970585682374603783223701)
                    ·
                      refine ⟨1029871203861309552338611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21970585682374603783223701 1029871203861309552338611)
                      ·
                        rfl

theorem cell23_2005667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2005667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005667 prefixEnd_2005667 := by exact prefixLift 2005667
  have htrace : WordTrace (prefixWord ++ tailWord_2005667) baseStart_2005667 baseEnd_2005667 := by
    simpa [prefixWord, tailWord_2005667, baseEnd_2005667] using wordTrace_append hprefix tailTrace_2005667
  have hstable : (prefixWord ++ tailWord_2005667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005667).length < 2 ^ (prefixWord ++ tailWord_2005667).sum := by decide
  have hdescent : baseEnd_2005667 < baseStart_2005667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005678 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2005678 : Nat := 118140960795 + 2005678 * 2 ^ 59
def prefixEnd_2005678 : Nat := 4983230072969 + 3 ^ 40 * 2005678 * 2
def baseEnd_2005678 : Nat := 1029876852148509009301061

theorem tailTrace_2005678 : CollatzResearch.WordTrace tailWord_2005678 prefixEnd_2005678 1029876852148509009301061 := by
  unfold tailWord_2005678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144135803472327922038211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48768724285185748917537125 9144135803472327922038211)
  ·
    refine ⟨13716203705208491883057317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144135803472327922038211 13716203705208491883057317)
    ·
      refine ⟨2571788194726592228073247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13716203705208491883057317 2571788194726592228073247)
      ·
        refine ⟨3857682292089888342109871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571788194726592228073247 3857682292089888342109871)
        ·
          refine ⟨5786523438134832513164807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857682292089888342109871 5786523438134832513164807)
          ·
            refine ⟨8679785157202248769747211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786523438134832513164807 8679785157202248769747211)
            ·
              refine ⟨13019677735803373154620817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679785157202248769747211 13019677735803373154620817)
              ·
                refine ⟨9764758301852529865965613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13019677735803373154620817 9764758301852529865965613)
                ·
                  refine ⟨3661784363194698699737105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9764758301852529865965613 3661784363194698699737105)
                  ·
                    refine ⟨2746338272396024024802829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3661784363194698699737105 2746338272396024024802829)
                    ·
                      refine ⟨1029876852148509009301061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746338272396024024802829 1029876852148509009301061)
                      ·
                        rfl

theorem cell23_2005678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2005678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005678 prefixEnd_2005678 := by exact prefixLift 2005678
  have htrace : WordTrace (prefixWord ++ tailWord_2005678) baseStart_2005678 baseEnd_2005678 := by
    simpa [prefixWord, tailWord_2005678, baseEnd_2005678] using wordTrace_append hprefix tailTrace_2005678
  have hstable : (prefixWord ++ tailWord_2005678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005678).length < 2 ^ (prefixWord ++ tailWord_2005678).sum := by decide
  have hdescent : baseEnd_2005678 < baseStart_2005678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005694 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2005694 : Nat := 118140960795 + 2005694 * 2 ^ 59
def prefixEnd_2005694 : Nat := 4983230072969 + 3 ^ 40 * 2005694 * 2
def baseEnd_2005694 : Nat := 343295022612993648900329

theorem tailTrace_2005694 : CollatzResearch.WordTrace tailWord_2005694 prefixEnd_2005694 343295022612993648900329 := by
  unfold tailWord_2005694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144208749465082263611017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48769113330480438739258757 9144208749465082263611017)
  ·
    refine ⟨6858156562098811697708263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9144208749465082263611017 6858156562098811697708263)
    ·
      refine ⟨10287234843148217546562395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858156562098811697708263 10287234843148217546562395)
      ·
        refine ⟨15430852264722326319843593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10287234843148217546562395 15430852264722326319843593)
        ·
          refine ⟨11573139198541744739882695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15430852264722326319843593 11573139198541744739882695)
          ·
            refine ⟨17359708797812617109824043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11573139198541744739882695 17359708797812617109824043)
            ·
              refine ⟨26039563196718925664736065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17359708797812617109824043 26039563196718925664736065)
              ·
                refine ⟨19529672397539194248552049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26039563196718925664736065 19529672397539194248552049)
                ·
                  refine ⟨14647254298154395686414037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19529672397539194248552049 14647254298154395686414037)
                  ·
                    refine ⟨343295022612993648900329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14647254298154395686414037 343295022612993648900329)
                    ·
                      rfl

theorem cell23_2005694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2005694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005694 prefixEnd_2005694 := by exact prefixLift 2005694
  have htrace : WordTrace (prefixWord ++ tailWord_2005694) baseStart_2005694 baseEnd_2005694 := by
    simpa [prefixWord, tailWord_2005694, baseEnd_2005694] using wordTrace_append hprefix tailTrace_2005694
  have hstable : (prefixWord ++ tailWord_2005694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005694).length < 2 ^ (prefixWord ++ tailWord_2005694).sum := by decide
  have hdescent : baseEnd_2005694 < baseStart_2005694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005709 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2005709 : Nat := 118140960795 + 2005709 * 2 ^ 59
def prefixEnd_2005709 : Nat := 4983230072969 + 3 ^ 40 * 2005709 * 2
def baseEnd_2005709 : Nat := 1029892770048798388013419

theorem tailTrace_2005709 : CollatzResearch.WordTrace tailWord_2005709 prefixEnd_2005709 1029892770048798388013419 := by
  unfold tailWord_2005709
  simp only [CollatzResearch.WordTrace]
  refine ⟨73154217090666315670684181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48769478060444210447122787 73154217090666315670684181)
  ·
    refine ⟨3429103926124983547063321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73154217090666315670684181 3429103926124983547063321)
    ·
      refine ⟨2571827944593737660297491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3429103926124983547063321 2571827944593737660297491)
      ·
        refine ⟨3857741916890606490446237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571827944593737660297491 3857741916890606490446237)
        ·
          refine ⟨1446653218833977433917339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3857741916890606490446237 1446653218833977433917339)
          ·
            refine ⟨2169979828250966150876009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446653218833977433917339 2169979828250966150876009)
            ·
              refine ⟨1627484871188224613157007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169979828250966150876009 1627484871188224613157007)
              ·
                refine ⟨2441227306782336919735511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627484871188224613157007 2441227306782336919735511)
                ·
                  refine ⟨3661840960173505379603267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441227306782336919735511 3661840960173505379603267)
                  ·
                    refine ⟨5492761440260258069404901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3661840960173505379603267 5492761440260258069404901)
                    ·
                      refine ⟨1029892770048798388013419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5492761440260258069404901 1029892770048798388013419)
                      ·
                        rfl

theorem cell23_2005709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2005709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005709 prefixEnd_2005709 := by exact prefixLift 2005709
  have htrace : WordTrace (prefixWord ++ tailWord_2005709) baseStart_2005709 baseEnd_2005709 := by
    simpa [prefixWord, tailWord_2005709, baseEnd_2005709] using wordTrace_append hprefix tailTrace_2005709
  have hstable : (prefixWord ++ tailWord_2005709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005709).length < 2 ^ (prefixWord ++ tailWord_2005709).sum := by decide
  have hdescent : baseEnd_2005709 < baseStart_2005709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005744 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_2005744 : Nat := 118140960795 + 2005744 * 2 ^ 59
def prefixEnd_2005744 : Nat := 4983230072969 + 3 ^ 40 * 2005744 * 2
def baseEnd_2005744 : Nat := 1029910741871705751075757

theorem tailTrace_2005744 : CollatzResearch.WordTrace tailWord_2005744 prefixEnd_2005744 1029910741871705751075757 := by
  unfold tailWord_2005744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36577746822769758324104143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48770329097026344432138857 36577746822769758324104143)
  ·
    refine ⟨54866620234154637486156215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36577746822769758324104143 54866620234154637486156215)
    ·
      refine ⟨82299930351231956229234323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54866620234154637486156215 82299930351231956229234323)
      ·
        refine ⟨123449895526847934343851485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82299930351231956229234323 123449895526847934343851485)
        ·
          refine ⟨46293710822567975378944307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123449895526847934343851485 46293710822567975378944307)
          ·
            refine ⟨69440566233851963068416461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46293710822567975378944307 69440566233851963068416461)
            ·
              refine ⟨26040212337694486150656173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69440566233851963068416461 26040212337694486150656173)
              ·
                refine ⟨9765079626635432306496065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26040212337694486150656173 9765079626635432306496065)
                ·
                  refine ⟨7323809719976574229872049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9765079626635432306496065 7323809719976574229872049)
                  ·
                    refine ⟨5492857289982430672404037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7323809719976574229872049 5492857289982430672404037)
                    ·
                      refine ⟨1029910741871705751075757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5492857289982430672404037 1029910741871705751075757)
                      ·
                        rfl

theorem cell23_2005744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_2005744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005744 prefixEnd_2005744 := by exact prefixLift 2005744
  have htrace : WordTrace (prefixWord ++ tailWord_2005744) baseStart_2005744 baseEnd_2005744 := by
    simpa [prefixWord, tailWord_2005744, baseEnd_2005744] using wordTrace_append hprefix tailTrace_2005744
  have hstable : (prefixWord ++ tailWord_2005744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005744).length < 2 ^ (prefixWord ++ tailWord_2005744).sum := by decide
  have hdescent : baseEnd_2005744 < baseStart_2005744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005754 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_2005754 : Nat := 118140960795 + 2005754 * 2 ^ 59
def prefixEnd_2005754 : Nat := 4983230072969 + 3 ^ 40 * 2005754 * 2
def baseEnd_2005754 : Nat := 114435097408694523550079

theorem tailTrace_2005754 : CollatzResearch.WordTrace tailWord_2005754 prefixEnd_2005754 114435097408694523550079 := by
  unfold tailWord_2005754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288964593875822089018079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48770572250335525570714877 18288964593875822089018079)
  ·
    refine ⟨27433446890813733133527119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18288964593875822089018079 27433446890813733133527119)
    ·
      refine ⟨41150170336220599700290679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27433446890813733133527119 41150170336220599700290679)
      ·
        refine ⟨61725255504330899550436019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41150170336220599700290679 61725255504330899550436019)
        ·
          refine ⟨92587883256496349325654029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61725255504330899550436019 92587883256496349325654029)
          ·
            refine ⟨34720456221186130997120261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92587883256496349325654029 34720456221186130997120261)
            ·
              refine ⟨6510085541472399561960049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34720456221186130997120261 6510085541472399561960049)
              ·
                refine ⟨4882564156104299671470037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6510085541472399561960049 4882564156104299671470037)
                ·
                  refine ⟨114435097408694523550079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4882564156104299671470037 114435097408694523550079)
                  ·
                    rfl

theorem cell23_2005754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_2005754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005754 prefixEnd_2005754 := by exact prefixLift 2005754
  have htrace : WordTrace (prefixWord ++ tailWord_2005754) baseStart_2005754 baseEnd_2005754 := by
    simpa [prefixWord, tailWord_2005754, baseEnd_2005754] using wordTrace_append hprefix tailTrace_2005754
  have hstable : (prefixWord ++ tailWord_2005754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005754).length < 2 ^ (prefixWord ++ tailWord_2005754).sum := by decide
  have hdescent : baseEnd_2005754 < baseStart_2005754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005818 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_2005818 : Nat := 118140960795 + 2005818 * 2 ^ 59
def prefixEnd_2005818 : Nat := 4983230072969 + 3 ^ 40 * 2005818 * 2
def baseEnd_2005818 : Nat := 343316246480046153850139

theorem tailTrace_2005818 : CollatzResearch.WordTrace tailWord_2005818 prefixEnd_2005818 343316246480046153850139 := by
  unfold tailWord_2005818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18289548161817856821600527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48772128431514284857601405 18289548161817856821600527)
  ·
    refine ⟨27434322242726785232400791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18289548161817856821600527 27434322242726785232400791)
    ·
      refine ⟨41151483364090177848601187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27434322242726785232400791 41151483364090177848601187)
      ·
        refine ⟨61727225046135266772901781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41151483364090177848601187 61727225046135266772901781)
        ·
          refine ⟨2893463674037590629979771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61727225046135266772901781 2893463674037590629979771)
          ·
            refine ⟨4340195511056385944969657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893463674037590629979771 4340195511056385944969657)
            ·
              refine ⟨3255146633292289458727243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340195511056385944969657 3255146633292289458727243)
              ·
                refine ⟨4882719949938434188090865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255146633292289458727243 4882719949938434188090865)
                ·
                  refine ⟨3662039962453825641068149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4882719949938434188090865 3662039962453825641068149)
                  ·
                    refine ⟨343316246480046153850139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3662039962453825641068149 343316246480046153850139)
                    ·
                      rfl

theorem cell23_2005818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_2005818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005818 prefixEnd_2005818 := by exact prefixLift 2005818
  have htrace : WordTrace (prefixWord ++ tailWord_2005818) baseStart_2005818 baseEnd_2005818 := by
    simpa [prefixWord, tailWord_2005818, baseEnd_2005818] using wordTrace_append hprefix tailTrace_2005818
  have hstable : (prefixWord ++ tailWord_2005818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005818).length < 2 ^ (prefixWord ++ tailWord_2005818).sum := by decide
  have hdescent : baseEnd_2005818 < baseStart_2005818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005861 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 6]
def baseStart_2005861 : Nat := 118140960795 + 2005861 * 2 ^ 59
def prefixEnd_2005861 : Nat := 4983230072969 + 3 ^ 40 * 2005861 * 2
def baseEnd_2005861 : Nat := 114441202123142421479191

theorem tailTrace_2005861 : CollatzResearch.WordTrace tailWord_2005861 prefixEnd_2005861 114441202123142421479191 := by
  unfold tailWord_2005861
  simp only [CollatzResearch.WordTrace]
  refine ⟨73159760986115645630217437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48773173990743763753478291 73159760986115645630217437)
  ·
    refine ⟨27434910369793367111331539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73159760986115645630217437 27434910369793367111331539)
    ·
      refine ⟨41152365554690050666997309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27434910369793367111331539 41152365554690050666997309)
      ·
        refine ⟨15432137083008769000123991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41152365554690050666997309 15432137083008769000123991)
        ·
          refine ⟨23148205624513153500185987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15432137083008769000123991 23148205624513153500185987)
          ·
            refine ⟨34722308436769730250278981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23148205624513153500185987 34722308436769730250278981)
            ·
              refine ⟨6510432831894324421927309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34722308436769730250278981 6510432831894324421927309)
              ·
                refine ⟨2441412311960371658222741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6510432831894324421927309 2441412311960371658222741)
                ·
                  refine ⟨114441202123142421479191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2441412311960371658222741 114441202123142421479191)
                  ·
                    rfl

theorem cell23_2005861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_2005861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005861 prefixEnd_2005861 := by exact prefixLift 2005861
  have htrace : WordTrace (prefixWord ++ tailWord_2005861) baseStart_2005861 baseEnd_2005861 := by
    simpa [prefixWord, tailWord_2005861, baseEnd_2005861] using wordTrace_append hprefix tailTrace_2005861
  have hstable : (prefixWord ++ tailWord_2005861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005861).length < 2 ^ (prefixWord ++ tailWord_2005861).sum := by decide
  have hdescent : baseEnd_2005861 < baseStart_2005861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005956 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2005956 : Nat := 118140960795 + 2005956 * 2 ^ 59
def prefixEnd_2005956 : Nat := 4983230072969 + 3 ^ 40 * 2005956 * 2
def baseEnd_2005956 : Nat := 1030019599770458921624783

theorem tailTrace_2005956 : CollatzResearch.WordTrace tailWord_2005956 prefixEnd_2005956 1030019599770458921624783 := by
  unfold tailWord_2005956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36581612960385738427462861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48775483947180984569950481 36581612960385738427462861)
  ·
    refine ⟨13718104860144651910298573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36581612960385738427462861 13718104860144651910298573)
    ·
      refine ⟨5144289322554244466361965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13718104860144651910298573 5144289322554244466361965)
      ·
        refine ⟨1929108495957841674885737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5144289322554244466361965 1929108495957841674885737)
        ·
          refine ⟨1446831371968381256164303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929108495957841674885737 1446831371968381256164303)
          ·
            refine ⟨2170247057952571884246455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446831371968381256164303 2170247057952571884246455)
            ·
              refine ⟨3255370586928857826369683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170247057952571884246455 3255370586928857826369683)
              ·
                refine ⟨4883055880393286739554525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255370586928857826369683 4883055880393286739554525)
                ·
                  refine ⟨1831145955147482527332947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4883055880393286739554525 1831145955147482527332947)
                  ·
                    refine ⟨2746718932721223790999421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831145955147482527332947 2746718932721223790999421)
                    ·
                      refine ⟨1030019599770458921624783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746718932721223790999421 1030019599770458921624783)
                      ·
                        rfl

theorem cell23_2005956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2005956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005956 prefixEnd_2005956 := by exact prefixLift 2005956
  have htrace : WordTrace (prefixWord ++ tailWord_2005956) baseStart_2005956 baseEnd_2005956 := by
    simpa [prefixWord, tailWord_2005956, baseEnd_2005956] using wordTrace_append hprefix tailTrace_2005956
  have hstable : (prefixWord ++ tailWord_2005956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005956).length < 2 ^ (prefixWord ++ tailWord_2005956).sum := by decide
  have hdescent : baseEnd_2005956 < baseStart_2005956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005961 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_2005961 : Nat := 118140960795 + 2005961 * 2 ^ 59
def prefixEnd_2005961 : Nat := 4983230072969 + 3 ^ 40 * 2005961 * 2
def baseEnd_2005961 : Nat := 1030022167173731402062259

theorem tailTrace_2005961 : CollatzResearch.WordTrace tailWord_2005961 prefixEnd_2005961 1030022167173731402062259 := by
  unfold tailWord_2005961
  simp only [CollatzResearch.WordTrace]
  refine ⟨73163408285753362708857737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48775605523835575139238491 73163408285753362708857737)
  ·
    refine ⟨54872556214315022031643303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73163408285753362708857737 54872556214315022031643303)
    ·
      refine ⟨82308834321472533047464955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54872556214315022031643303 82308834321472533047464955)
      ·
        refine ⟨123463251482208799571197433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82308834321472533047464955 123463251482208799571197433)
        ·
          refine ⟨92597438611656599678398075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123463251482208799571197433 92597438611656599678398075)
          ·
            refine ⟨138896157917484899517597113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92597438611656599678398075 138896157917484899517597113)
            ·
              refine ⟨104172118438113674638197835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138896157917484899517597113 104172118438113674638197835)
              ·
                refine ⟨156258177657170511957296753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104172118438113674638197835 156258177657170511957296753)
                ·
                  refine ⟨117193633242877883967972565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156258177657170511957296753 117193633242877883967972565)
                  ·
                    refine ⟨2746725779129950405499357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 117193633242877883967972565 2746725779129950405499357)
                    ·
                      refine ⟨1030022167173731402062259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746725779129950405499357 1030022167173731402062259)
                      ·
                        rfl

theorem cell23_2005961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_2005961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005961 prefixEnd_2005961 := by exact prefixLift 2005961
  have htrace : WordTrace (prefixWord ++ tailWord_2005961) baseStart_2005961 baseEnd_2005961 := by
    simpa [prefixWord, tailWord_2005961, baseEnd_2005961] using wordTrace_append hprefix tailTrace_2005961
  have hstable : (prefixWord ++ tailWord_2005961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005961).length < 2 ^ (prefixWord ++ tailWord_2005961).sum := by decide
  have hdescent : baseEnd_2005961 < baseStart_2005961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2005972 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_2005972 : Nat := 118140960795 + 2005972 * 2 ^ 59
def prefixEnd_2005972 : Nat := 4983230072969 + 3 ^ 40 * 2005972 * 2
def baseEnd_2005972 : Nat := 343342605153643619674903

theorem tailTrace_2005972 : CollatzResearch.WordTrace tailWord_2005972 prefixEnd_2005972 343342605153643619674903 := by
  unfold tailWord_2005972
  simp only [CollatzResearch.WordTrace]
  refine ⟨36581904744356755793754085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48775872992475674391672113 36581904744356755793754085)
  ·
    refine ⟨6859107139566891711328891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36581904744356755793754085 6859107139566891711328891)
    ·
      refine ⟨10288660709350337566993337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6859107139566891711328891 10288660709350337566993337)
      ·
        refine ⟨7716495532012753175245003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10288660709350337566993337 7716495532012753175245003)
        ·
          refine ⟨11574743298019129762867505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716495532012753175245003 11574743298019129762867505)
          ·
            refine ⟨8681057473514347322150629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11574743298019129762867505 8681057473514347322150629)
            ·
              refine ⟨1627698276283940122903243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8681057473514347322150629 1627698276283940122903243)
              ·
                refine ⟨2441547414425910184354865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627698276283940122903243 2441547414425910184354865)
                ·
                  refine ⟨1831160560819432638266149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441547414425910184354865 1831160560819432638266149)
                  ·
                    refine ⟨343342605153643619674903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831160560819432638266149 343342605153643619674903)
                    ·
                      rfl

theorem cell23_2005972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_2005972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2005972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2005972 prefixEnd_2005972 := by exact prefixLift 2005972
  have htrace : WordTrace (prefixWord ++ tailWord_2005972) baseStart_2005972 baseEnd_2005972 := by
    simpa [prefixWord, tailWord_2005972, baseEnd_2005972] using wordTrace_append hprefix tailTrace_2005972
  have hstable : (prefixWord ++ tailWord_2005972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2005972).length < 2 ^ (prefixWord ++ tailWord_2005972).sum := by decide
  have hdescent : baseEnd_2005972 < baseStart_2005972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2005972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006011 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 2, 6]
def baseStart_2006011 : Nat := 118140960795 + 2006011 * 2 ^ 59
def prefixEnd_2006011 : Nat := 4983230072969 + 3 ^ 40 * 2006011 * 2
def baseEnd_2006011 : Nat := 343349280402152068812343

theorem tailTrace_2006011 : CollatzResearch.WordTrace tailWord_2006011 prefixEnd_2006011 343349280402152068812343 := by
  unfold tailWord_2006011
  simp only [CollatzResearch.WordTrace]
  refine ⟨73165231935572221248177887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48776821290381480832118591 73165231935572221248177887)
  ·
    refine ⟨109747847903358331872266831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73165231935572221248177887 109747847903358331872266831)
    ·
      refine ⟨164621771855037497808400247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109747847903358331872266831 164621771855037497808400247)
      ·
        refine ⟨246932657782556246712600371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164621771855037497808400247 246932657782556246712600371)
        ·
          refine ⟨370398986673834370068900557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246932657782556246712600371 370398986673834370068900557)
          ·
            refine ⟨138899620002687888775837709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370398986673834370068900557 138899620002687888775837709)
            ·
              refine ⟨52087357501007958290939141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138899620002687888775837709 52087357501007958290939141)
              ·
                refine ⟨9766379531438992179551089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52087357501007958290939141 9766379531438992179551089)
                ·
                  refine ⟨7324784648579244134663317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766379531438992179551089 7324784648579244134663317)
                  ·
                    refine ⟨343349280402152068812343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7324784648579244134663317 343349280402152068812343)
                    ·
                      rfl

theorem cell23_2006011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_2006011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006011 prefixEnd_2006011 := by exact prefixLift 2006011
  have htrace : WordTrace (prefixWord ++ tailWord_2006011) baseStart_2006011 baseEnd_2006011 := by
    simpa [prefixWord, tailWord_2006011, baseEnd_2006011] using wordTrace_append hprefix tailTrace_2006011
  have hstable : (prefixWord ++ tailWord_2006011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006011).length < 2 ^ (prefixWord ++ tailWord_2006011).sum := by decide
  have hdescent : baseEnd_2006011 < baseStart_2006011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006012 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_2006012 : Nat := 118140960795 + 2006012 * 2 ^ 59
def prefixEnd_2006012 : Nat := 4983230072969 + 3 ^ 40 * 2006012 * 2
def baseEnd_2006012 : Nat := 1030048354687110702524525

theorem tailTrace_2006012 : CollatzResearch.WordTrace tailWord_2006012 prefixEnd_2006012 1030048354687110702524525 := by
  unfold tailWord_2006012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582634204284299209482145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48776845605712398945976193 36582634204284299209482145)
  ·
    refine ⟨27436975653213224407111609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36582634204284299209482145 27436975653213224407111609)
    ·
      refine ⟨20577731739909918305333707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27436975653213224407111609 20577731739909918305333707)
      ·
        refine ⟨30866597609864877458000561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20577731739909918305333707 30866597609864877458000561)
        ·
          refine ⟨23149948207398658093500421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30866597609864877458000561 23149948207398658093500421)
          ·
            refine ⟨4340615288887248392531329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23149948207398658093500421 4340615288887248392531329)
            ·
              refine ⟨3255461466665436294398497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340615288887248392531329 3255461466665436294398497)
              ·
                refine ⟨2441596099999077220798873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255461466665436294398497 2441596099999077220798873)
                ·
                  refine ⟨1831197074999307915599155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441596099999077220798873 1831197074999307915599155)
                  ·
                    refine ⟨2746795612498961873398733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831197074999307915599155 2746795612498961873398733)
                    ·
                      refine ⟨1030048354687110702524525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2746795612498961873398733 1030048354687110702524525)
                      ·
                        rfl

theorem cell23_2006012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_2006012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006012 prefixEnd_2006012 := by exact prefixLift 2006012
  have htrace : WordTrace (prefixWord ++ tailWord_2006012) baseStart_2006012 baseEnd_2006012 := by
    simpa [prefixWord, tailWord_2006012, baseEnd_2006012] using wordTrace_append hprefix tailTrace_2006012
  have hstable : (prefixWord ++ tailWord_2006012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006012).length < 2 ^ (prefixWord ++ tailWord_2006012).sum := by decide
  have hdescent : baseEnd_2006012 < baseStart_2006012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006028 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_2006028 : Nat := 118140960795 + 2006028 * 2 ^ 59
def prefixEnd_2006028 : Nat := 4983230072969 + 3 ^ 40 * 2006028 * 2
def baseEnd_2006028 : Nat := 343352190125860879974817

theorem tailTrace_2006028 : CollatzResearch.WordTrace tailWord_2006028 prefixEnd_2006028 343352190125860879974817 := by
  unfold tailWord_2006028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582925988255316575773369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48777234651007088767697825 36582925988255316575773369)
  ·
    refine ⟨27437194491191487431830027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36582925988255316575773369 27437194491191487431830027)
    ·
      refine ⟨41155791736787231147745041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27437194491191487431830027 41155791736787231147745041)
      ·
        refine ⟨30866843802590423360808781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41155791736787231147745041 30866843802590423360808781)
        ·
          refine ⟨11575066425971408760303293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30866843802590423360808781 11575066425971408760303293)
          ·
            refine ⟨4340649909739278285113735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11575066425971408760303293 4340649909739278285113735)
            ·
              refine ⟨6510974864608917427670603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340649909739278285113735 6510974864608917427670603)
              ·
                refine ⟨9766462296913376141505905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510974864608917427670603 9766462296913376141505905)
                ·
                  refine ⟨7324846722685032106129429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766462296913376141505905 7324846722685032106129429)
                  ·
                    refine ⟨343352190125860879974817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7324846722685032106129429 343352190125860879974817)
                    ·
                      rfl

theorem cell23_2006028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_2006028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006028 prefixEnd_2006028 := by exact prefixLift 2006028
  have htrace : WordTrace (prefixWord ++ tailWord_2006028) baseStart_2006028 baseEnd_2006028 := by
    simpa [prefixWord, tailWord_2006028, baseEnd_2006028] using wordTrace_append hprefix tailTrace_2006028
  have hstable : (prefixWord ++ tailWord_2006028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006028).length < 2 ^ (prefixWord ++ tailWord_2006028).sum := by decide
  have hdescent : baseEnd_2006028 < baseStart_2006028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006035 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 6, 2, 2]
def baseStart_2006035 : Nat := 118140960795 + 2006035 * 2 ^ 59
def prefixEnd_2006035 : Nat := 4983230072969 + 3 ^ 40 * 2006035 * 2
def baseEnd_2006035 : Nat := 1030060164742164112536919

theorem tailTrace_2006035 : CollatzResearch.WordTrace tailWord_2006035 prefixEnd_2006035 1030060164742164112536919 := by
  unfold tailWord_2006035
  simp only [CollatzResearch.WordTrace]
  refine ⟨73166107287485273347051559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48777404858323515564701039 73166107287485273347051559)
  ·
    refine ⟨109749160931227910020577339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73166107287485273347051559 109749160931227910020577339)
    ·
      refine ⟨164623741396841865030866009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109749160931227910020577339 164623741396841865030866009)
      ·
        refine ⟨123467806047631398773149507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164623741396841865030866009 123467806047631398773149507)
        ·
          refine ⟨185201709071447098159724261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123467806047631398773149507 185201709071447098159724261)
          ·
            refine ⟨34725320450896330904948299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185201709071447098159724261 34725320450896330904948299)
            ·
              refine ⟨52087980676344496357422449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34725320450896330904948299 52087980676344496357422449)
              ·
                refine ⟨39065985507258372268066837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52087980676344496357422449 39065985507258372268066837)
                ·
                  refine ⟨1831218070652736200065633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39065985507258372268066837 1831218070652736200065633)
                  ·
                    refine ⟨1373413552989552150049225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1831218070652736200065633 1373413552989552150049225)
                    ·
                      refine ⟨1030060164742164112536919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373413552989552150049225 1030060164742164112536919)
                      ·
                        rfl

theorem cell23_2006035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2, 2].length) (baseStart_2006035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006035 prefixEnd_2006035 := by exact prefixLift 2006035
  have htrace : WordTrace (prefixWord ++ tailWord_2006035) baseStart_2006035 baseEnd_2006035 := by
    simpa [prefixWord, tailWord_2006035, baseEnd_2006035] using wordTrace_append hprefix tailTrace_2006035
  have hstable : (prefixWord ++ tailWord_2006035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006035).length < 2 ^ (prefixWord ++ tailWord_2006035).sum := by decide
  have hdescent : baseEnd_2006035 < baseStart_2006035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006041 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 9]
def baseStart_2006041 : Nat := 118140960795 + 2006041 * 2 ^ 59
def prefixEnd_2006041 : Nat := 4983230072969 + 3 ^ 40 * 2006041 * 2
def baseEnd_2006041 : Nat := 114451471736232343229099

theorem tailTrace_2006041 : CollatzResearch.WordTrace tailWord_2006041 prefixEnd_2006041 114451471736232343229099 := by
  unfold tailWord_2006041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73166326125463536371769977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48777550750309024247846651 73166326125463536371769977)
  ·
    refine ⟨54874744594097652278827483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73166326125463536371769977 54874744594097652278827483)
    ·
      refine ⟨82312116891146478418241225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54874744594097652278827483 82312116891146478418241225)
      ·
        refine ⟨61734087668359858813680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82312116891146478418241225 61734087668359858813680919)
        ·
          refine ⟨92601131502539788220521379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61734087668359858813680919 92601131502539788220521379)
          ·
            refine ⟨138901697253809682330782069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92601131502539788220521379 138901697253809682330782069)
            ·
              refine ⟨13022034117544657718510819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138901697253809682330782069 13022034117544657718510819)
              ·
                refine ⟨19533051176316986577766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13022034117544657718510819 19533051176316986577766229)
                ·
                  refine ⟨114451471736232343229099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19533051176316986577766229 114451471736232343229099)
                  ·
                    rfl

theorem cell23_2006041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_2006041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006041 prefixEnd_2006041 := by exact prefixLift 2006041
  have htrace : WordTrace (prefixWord ++ tailWord_2006041) baseStart_2006041 baseEnd_2006041 := by
    simpa [prefixWord, tailWord_2006041, baseEnd_2006041] using wordTrace_append hprefix tailTrace_2006041
  have hstable : (prefixWord ++ tailWord_2006041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006041).length < 2 ^ (prefixWord ++ tailWord_2006041).sum := by decide
  have hdescent : baseEnd_2006041 < baseStart_2006041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006052 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2006052 : Nat := 118140960795 + 2006052 * 2 ^ 59
def prefixEnd_2006052 : Nat := 4983230072969 + 3 ^ 40 * 2006052 * 2
def baseEnd_2006052 : Nat := 1030068893913290546024341

theorem tailTrace_2006052 : CollatzResearch.WordTrace tailWord_2006052 prefixEnd_2006052 1030068893913290546024341 := by
  unfold tailWord_2006052
  simp only [CollatzResearch.WordTrace]
  refine ⟨36583363664211842625210205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48777818218949123500280273 36583363664211842625210205)
  ·
    refine ⟨13718761374079440984453827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36583363664211842625210205 13718761374079440984453827)
    ·
      refine ⟨20578142061119161476680741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13718761374079440984453827 20578142061119161476680741)
      ·
        refine ⟨3858401636459842776877639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20578142061119161476680741 3858401636459842776877639)
        ·
          refine ⟨5787602454689764165316459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858401636459842776877639 5787602454689764165316459)
          ·
            refine ⟨8681403682034646247974689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787602454689764165316459 8681403682034646247974689)
            ·
              refine ⟨6511052761525984685981017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681403682034646247974689 6511052761525984685981017)
              ·
                refine ⟨4883289571144488514485763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6511052761525984685981017 4883289571144488514485763)
                ·
                  refine ⟨7324934356716732771728645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883289571144488514485763 7324934356716732771728645)
                  ·
                    refine ⟨1373425191884387394699121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7324934356716732771728645 1373425191884387394699121)
                    ·
                      refine ⟨1030068893913290546024341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373425191884387394699121 1030068893913290546024341)
                      ·
                        rfl

theorem cell23_2006052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2006052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006052 prefixEnd_2006052 := by exact prefixLift 2006052
  have htrace : WordTrace (prefixWord ++ tailWord_2006052) baseStart_2006052 baseEnd_2006052 := by
    simpa [prefixWord, tailWord_2006052, baseEnd_2006052] using wordTrace_append hprefix tailTrace_2006052
  have hstable : (prefixWord ++ tailWord_2006052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006052).length < 2 ^ (prefixWord ++ tailWord_2006052).sum := by decide
  have hdescent : baseEnd_2006052 < baseStart_2006052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006086 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2006086 : Nat := 118140960795 + 2006086 * 2 ^ 59
def prefixEnd_2006086 : Nat := 4983230072969 + 3 ^ 40 * 2006086 * 2
def baseEnd_2006086 : Nat := 1030086352255543412999185

theorem tailTrace_2006086 : CollatzResearch.WordTrace tailWord_2006086 prefixEnd_2006086 1030086352255543412999185 := by
  unfold tailWord_2006086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286498981571890908036191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48778644940200339371438741 2286498981571890908036191)
  ·
    refine ⟨3429748472357836362054287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2286498981571890908036191 3429748472357836362054287)
    ·
      refine ⟨5144622708536754543081431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429748472357836362054287 5144622708536754543081431)
      ·
        refine ⟨7716934062805131814622147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144622708536754543081431 7716934062805131814622147)
        ·
          refine ⟨11575401094207697721933221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7716934062805131814622147 11575401094207697721933221)
          ·
            refine ⟨2170387705163943322862479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11575401094207697721933221 2170387705163943322862479)
            ·
              refine ⟨3255581557745914984293719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170387705163943322862479 3255581557745914984293719)
              ·
                refine ⟨4883372336618872476440579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255581557745914984293719 4883372336618872476440579)
                ·
                  refine ⟨7325058504928308714660869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883372336618872476440579 7325058504928308714660869)
                  ·
                    refine ⟨1373448469674057883998913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7325058504928308714660869 1373448469674057883998913)
                    ·
                      refine ⟨1030086352255543412999185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373448469674057883998913 1030086352255543412999185)
                      ·
                        rfl

theorem cell23_2006086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2006086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006086 prefixEnd_2006086 := by exact prefixLift 2006086
  have htrace : WordTrace (prefixWord ++ tailWord_2006086) baseStart_2006086 baseEnd_2006086 := by
    simpa [prefixWord, tailWord_2006086, baseEnd_2006086] using wordTrace_append hprefix tailTrace_2006086
  have hstable : (prefixWord ++ tailWord_2006086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006086).length < 2 ^ (prefixWord ++ tailWord_2006086).sum := by decide
  have hdescent : baseEnd_2006086 < baseStart_2006086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006125 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2006125 : Nat := 118140960795 + 2006125 * 2 ^ 59
def prefixEnd_2006125 : Nat := 4983230072969 + 3 ^ 40 * 2006125 * 2
def baseEnd_2006125 : Nat := 1030106378001068760411505

theorem tailTrace_2006125 : CollatzResearch.WordTrace tailWord_2006125 prefixEnd_2006125 1030106378001068760411505 := by
  unfold tailWord_2006125
  simp only [CollatzResearch.WordTrace]
  refine ⟨73169389857159218717827829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48779593238106145811885219 73169389857159218717827829)
  ·
    refine ⟨6859630299108676754796359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73169389857159218717827829 6859630299108676754796359)
    ·
      refine ⟨10289445448663015132194539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6859630299108676754796359 10289445448663015132194539)
      ·
        refine ⟨15434168172994522698291809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10289445448663015132194539 15434168172994522698291809)
        ·
          refine ⟨11575626129745892023718857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15434168172994522698291809 11575626129745892023718857)
          ·
            refine ⟨8681719597309419017789143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575626129745892023718857 8681719597309419017789143)
            ·
              refine ⟨13022579395964128526683715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681719597309419017789143 13022579395964128526683715)
              ·
                refine ⟨19533869093946192790025573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13022579395964128526683715 19533869093946192790025573)
                ·
                  refine ⟨3662600455114911148129795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19533869093946192790025573 3662600455114911148129795)
                  ·
                    refine ⟨5493900682672366722194693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3662600455114911148129795 5493900682672366722194693)
                    ·
                      refine ⟨1030106378001068760411505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5493900682672366722194693 1030106378001068760411505)
                      ·
                        rfl

theorem cell23_2006125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2006125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006125 prefixEnd_2006125 := by exact prefixLift 2006125
  have htrace : WordTrace (prefixWord ++ tailWord_2006125) baseStart_2006125 baseEnd_2006125 := by
    simpa [prefixWord, tailWord_2006125, baseEnd_2006125] using wordTrace_append hprefix tailTrace_2006125
  have hstable : (prefixWord ++ tailWord_2006125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006125).length < 2 ^ (prefixWord ++ tailWord_2006125).sum := by decide
  have hdescent : baseEnd_2006125 < baseStart_2006125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006162 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2006162 : Nat := 118140960795 + 2006162 * 2 ^ 59
def prefixEnd_2006162 : Nat := 4983230072969 + 3 ^ 40 * 2006162 * 2
def baseEnd_2006162 : Nat := 1030125376785285115648835

theorem tailTrace_2006162 : CollatzResearch.WordTrace tailWord_2006162 prefixEnd_2006162 1030125376785285115648835 := by
  unfold tailWord_2006162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292684839506293509231185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48780492905350116024616493 18292684839506293509231185)
  ·
    refine ⟨13719513629629720131923389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18292684839506293509231185 13719513629629720131923389)
    ·
      refine ⟨5144817611111145049471271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13719513629629720131923389 5144817611111145049471271)
      ·
        refine ⟨7717226416666717574206907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144817611111145049471271 7717226416666717574206907)
        ·
          refine ⟨11575839625000076361310361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717226416666717574206907 11575839625000076361310361)
          ·
            refine ⟨8681879718750057270982771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11575839625000076361310361 8681879718750057270982771)
            ·
              refine ⟨13022819578125085906474157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8681879718750057270982771 13022819578125085906474157)
              ·
                refine ⟨4883557341796907214927809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13022819578125085906474157 4883557341796907214927809)
                ·
                  refine ⟨3662668006347680411195857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4883557341796907214927809 3662668006347680411195857)
                  ·
                    refine ⟨2747001004760760308396893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3662668006347680411195857 2747001004760760308396893)
                    ·
                      refine ⟨1030125376785285115648835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747001004760760308396893 1030125376785285115648835)
                      ·
                        rfl

theorem cell23_2006162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2006162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006162 prefixEnd_2006162 := by exact prefixLift 2006162
  have htrace : WordTrace (prefixWord ++ tailWord_2006162) baseStart_2006162 baseEnd_2006162 := by
    simpa [prefixWord, tailWord_2006162, baseEnd_2006162] using wordTrace_append hprefix tailTrace_2006162
  have hstable : (prefixWord ++ tailWord_2006162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006162).length < 2 ^ (prefixWord ++ tailWord_2006162).sum := by decide
  have hdescent : baseEnd_2006162 < baseStart_2006162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006186 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2006186 : Nat := 118140960795 + 2006186 * 2 ^ 59
def prefixEnd_2006186 : Nat := 4983230072969 + 3 ^ 40 * 2006186 * 2
def baseEnd_2006186 : Nat := 343379233440331007249575

theorem tailTrace_2006186 : CollatzResearch.WordTrace tailWord_2006186 prefixEnd_2006186 343379233440331007249575 := by
  unfold tailWord_2006186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18292903677484556533949603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48781076473292150757198941 18292903677484556533949603)
  ·
    refine ⟨27439355516226834800924405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18292903677484556533949603 27439355516226834800924405)
    ·
      refine ⟨2572439579646265762586663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27439355516226834800924405 2572439579646265762586663)
      ·
        refine ⟨3858659369469398643879995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572439579646265762586663 3858659369469398643879995)
        ·
          refine ⟨5787989054204097965819993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858659369469398643879995 5787989054204097965819993)
          ·
            refine ⟨4340991790653073474364995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787989054204097965819993 4340991790653073474364995)
            ·
              refine ⟨6511487685979610211547493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340991790653073474364995 6511487685979610211547493)
              ·
                refine ⟨1220903941121176914665155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6511487685979610211547493 1220903941121176914665155)
                ·
                  refine ⟨1831355911681765371997733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220903941121176914665155 1831355911681765371997733)
                  ·
                    refine ⟨343379233440331007249575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831355911681765371997733 343379233440331007249575)
                    ·
                      rfl

theorem cell23_2006186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2006186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006186 prefixEnd_2006186 := by exact prefixLift 2006186
  have htrace : WordTrace (prefixWord ++ tailWord_2006186) baseStart_2006186 baseEnd_2006186 := by
    simpa [prefixWord, tailWord_2006186, baseEnd_2006186] using wordTrace_append hprefix tailTrace_2006186
  have hstable : (prefixWord ++ tailWord_2006186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006186).length < 2 ^ (prefixWord ++ tailWord_2006186).sum := by decide
  have hdescent : baseEnd_2006186 < baseStart_2006186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006209 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2006209 : Nat := 118140960795 + 2006209 * 2 ^ 59
def prefixEnd_2006209 : Nat := 4983230072969 + 3 ^ 40 * 2006209 * 2
def baseEnd_2006209 : Nat := 1030149510376046431761119

theorem tailTrace_2006209 : CollatzResearch.WordTrace tailWord_2006209 prefixEnd_2006209 1030149510376046431761119 := by
  unfold tailWord_2006209
  simp only [CollatzResearch.WordTrace]
  refine ⟨73172453588854901063885681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48781635725903267375923787 73172453588854901063885681)
  ·
    refine ⟨54879340191641175797914261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73172453588854901063885681 54879340191641175797914261)
    ·
      refine ⟨2572469071483180115527231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54879340191641175797914261 2572469071483180115527231)
      ·
        refine ⟨3858703607224770173290847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572469071483180115527231 3858703607224770173290847)
        ·
          refine ⟨5788055410837155259936271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858703607224770173290847 5788055410837155259936271)
          ·
            refine ⟨8682083116255732889904407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788055410837155259936271 8682083116255732889904407)
            ·
              refine ⟨13023124674383599334856611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682083116255732889904407 13023124674383599334856611)
              ·
                refine ⟨19534687011575399002284917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13023124674383599334856611 19534687011575399002284917)
                ·
                  refine ⟨1831376907335193656464211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19534687011575399002284917 1831376907335193656464211)
                  ·
                    refine ⟨2747065361002790484696317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831376907335193656464211 2747065361002790484696317)
                    ·
                      refine ⟨1030149510376046431761119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747065361002790484696317 1030149510376046431761119)
                      ·
                        rfl

theorem cell23_2006209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2006209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006209 prefixEnd_2006209 := by exact prefixLift 2006209
  have htrace : WordTrace (prefixWord ++ tailWord_2006209) baseStart_2006209 baseEnd_2006209 := by
    simpa [prefixWord, tailWord_2006209, baseEnd_2006209] using wordTrace_append hprefix tailTrace_2006209
  have hstable : (prefixWord ++ tailWord_2006209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006209).length < 2 ^ (prefixWord ++ tailWord_2006209).sum := by decide
  have hdescent : baseEnd_2006209 < baseStart_2006209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006225 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_2006225 : Nat := 118140960795 + 2006225 * 2 ^ 59
def prefixEnd_2006225 : Nat := 4983230072969 + 3 ^ 40 * 2006225 * 2
def baseEnd_2006225 : Nat := 343385908688839456387015

theorem tailTrace_2006225 : CollatzResearch.WordTrace tailWord_2006225 prefixEnd_2006225 343385908688839456387015 := by
  unfold tailWord_2006225
  simp only [CollatzResearch.WordTrace]
  refine ⟨73173037156796935796468129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48782024771197957197645419 73173037156796935796468129)
  ·
    refine ⟨54879777867597701847351097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73173037156796935796468129 54879777867597701847351097)
    ·
      refine ⟨41159833400698276385513323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54879777867597701847351097 41159833400698276385513323)
      ·
        refine ⟨61739750101047414578269985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41159833400698276385513323 61739750101047414578269985)
        ·
          refine ⟨46304812575785560933702489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61739750101047414578269985 46304812575785560933702489)
          ·
            refine ⟨34728609431839170700276867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46304812575785560933702489 34728609431839170700276867)
            ·
              refine ⟨52092914147758756050415301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34728609431839170700276867 52092914147758756050415301)
              ·
                refine ⟨9767421402704766759452869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52092914147758756050415301 9767421402704766759452869)
                ·
                  refine ⟨1831391513007143767397413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9767421402704766759452869 1831391513007143767397413)
                  ·
                    refine ⟨343385908688839456387015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831391513007143767397413 343385908688839456387015)
                    ·
                      rfl

theorem cell23_2006225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_2006225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006225 prefixEnd_2006225 := by exact prefixLift 2006225
  have htrace : WordTrace (prefixWord ++ tailWord_2006225) baseStart_2006225 baseEnd_2006225 := by
    simpa [prefixWord, tailWord_2006225, baseEnd_2006225] using wordTrace_append hprefix tailTrace_2006225
  have hstable : (prefixWord ++ tailWord_2006225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006225).length < 2 ^ (prefixWord ++ tailWord_2006225).sum := by decide
  have hdescent : baseEnd_2006225 < baseStart_2006225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006226 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2006226 : Nat := 118140960795 + 2006226 * 2 ^ 59
def prefixEnd_2006226 : Nat := 4983230072969 + 3 ^ 40 * 2006226 * 2
def baseEnd_2006226 : Nat := 1030158239547172865248541

theorem tailTrace_2006226 : CollatzResearch.WordTrace tailWord_2006226 prefixEnd_2006226 1030158239547172865248541 := by
  unfold tailWord_2006226
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293268407448328241813633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48782049086528875311503021 18293268407448328241813633)
  ·
    refine ⟨13719951305586246181360225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18293268407448328241813633 13719951305586246181360225)
    ·
      refine ⟨10289963479189684636020169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13719951305586246181360225 10289963479189684636020169)
      ·
        refine ⟨7717472609392263477015127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10289963479189684636020169 7717472609392263477015127)
        ·
          refine ⟨11576208914088395215522691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717472609392263477015127 11576208914088395215522691)
          ·
            refine ⟨17364313371132592823284037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576208914088395215522691 17364313371132592823284037)
            ·
              refine ⟨3255808757087361154365757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17364313371132592823284037 3255808757087361154365757)
              ·
                refine ⟨1220928283907760432887159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3255808757087361154365757 1220928283907760432887159)
                ·
                  refine ⟨1831392425861640649330739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220928283907760432887159 1831392425861640649330739)
                  ·
                    refine ⟨2747088638792460973996109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831392425861640649330739 2747088638792460973996109)
                    ·
                      refine ⟨1030158239547172865248541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747088638792460973996109 1030158239547172865248541)
                      ·
                        rfl

theorem cell23_2006226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2006226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006226 prefixEnd_2006226 := by exact prefixLift 2006226
  have htrace : WordTrace (prefixWord ++ tailWord_2006226) baseStart_2006226 baseEnd_2006226 := by
    simpa [prefixWord, tailWord_2006226, baseEnd_2006226] using wordTrace_append hprefix tailTrace_2006226
  have hstable : (prefixWord ++ tailWord_2006226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006226).length < 2 ^ (prefixWord ++ tailWord_2006226).sum := by decide
  have hdescent : baseEnd_2006226 < baseStart_2006226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006229 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2006229 : Nat := 118140960795 + 2006229 * 2 ^ 59
def prefixEnd_2006229 : Nat := 4983230072969 + 3 ^ 40 * 2006229 * 2
def baseEnd_2006229 : Nat := 343386593329712117837009

theorem tailTrace_2006229 : CollatzResearch.WordTrace tailWord_2006229 prefixEnd_2006229 343386593329712117837009 := by
  unfold tailWord_2006229
  simp only [CollatzResearch.WordTrace]
  refine ⟨73173183048782444479613741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48782122032521629653075827 73173183048782444479613741)
  ·
    refine ⟨27439943643293416679855153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73173183048782444479613741 27439943643293416679855153)
    ·
      refine ⟨20579957732470062509891365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27439943643293416679855153 20579957732470062509891365)
      ·
        refine ⟨3858742074838136720604631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20579957732470062509891365 3858742074838136720604631)
        ·
          refine ⟨5788113112257205080906947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858742074838136720604631 5788113112257205080906947)
          ·
            refine ⟨8682169668385807621360421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788113112257205080906947 8682169668385807621360421)
            ·
              refine ⟨1627906812822338929005079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8682169668385807621360421 1627906812822338929005079)
              ·
                refine ⟨2441860219233508393507619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627906812822338929005079 2441860219233508393507619)
                ·
                  refine ⟨3662790328850262590261429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441860219233508393507619 3662790328850262590261429)
                  ·
                    refine ⟨343386593329712117837009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3662790328850262590261429 343386593329712117837009)
                    ·
                      rfl

theorem cell23_2006229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2006229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006229 prefixEnd_2006229 := by exact prefixLift 2006229
  have htrace : WordTrace (prefixWord ++ tailWord_2006229) baseStart_2006229 baseEnd_2006229 := by
    simpa [prefixWord, tailWord_2006229, baseEnd_2006229] using wordTrace_append hprefix tailTrace_2006229
  have hstable : (prefixWord ++ tailWord_2006229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006229).length < 2 ^ (prefixWord ++ tailWord_2006229).sum := by decide
  have hdescent : baseEnd_2006229 < baseStart_2006229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006259 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 2, 4]
def baseStart_2006259 : Nat := 118140960795 + 2006259 * 2 ^ 59
def prefixEnd_2006259 : Nat := 4983230072969 + 3 ^ 40 * 2006259 * 2
def baseEnd_2006259 : Nat := 343391728136257078711963

theorem tailTrace_2006259 : CollatzResearch.WordTrace tailWord_2006259 prefixEnd_2006259 343391728136257078711963 := by
  unfold tailWord_2006259
  simp only [CollatzResearch.WordTrace]
  refine ⟨73174277238673759603205831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48782851492449173068803887 73174277238673759603205831)
  ·
    refine ⟨109761415858010639404808747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73174277238673759603205831 109761415858010639404808747)
    ·
      refine ⟨164642123787015959107213121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109761415858010639404808747 164642123787015959107213121)
      ·
        refine ⟨123481592840261969330409841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164642123787015959107213121 123481592840261969330409841)
        ·
          refine ⟨92611194630196476997807381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123481592840261969330409841 92611194630196476997807381)
          ·
            refine ⟨4341149748290459859272221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92611194630196476997807381 4341149748290459859272221)
            ·
              refine ⟨1627931155608922447227083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4341149748290459859272221 1627931155608922447227083)
              ·
                refine ⟨2441896733413383670840625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627931155608922447227083 2441896733413383670840625)
                ·
                  refine ⟨1831422550060037753130469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441896733413383670840625 1831422550060037753130469)
                  ·
                    refine ⟨343391728136257078711963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831422550060037753130469 343391728136257078711963)
                    ·
                      rfl

theorem cell23_2006259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 4].length) (baseStart_2006259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006259 prefixEnd_2006259 := by exact prefixLift 2006259
  have htrace : WordTrace (prefixWord ++ tailWord_2006259) baseStart_2006259 baseEnd_2006259 := by
    simpa [prefixWord, tailWord_2006259, baseEnd_2006259] using wordTrace_append hprefix tailTrace_2006259
  have hstable : (prefixWord ++ tailWord_2006259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006259).length < 2 ^ (prefixWord ++ tailWord_2006259).sum := by decide
  have hdescent : baseEnd_2006259 < baseStart_2006259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006283 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 1, 2, 2]
def baseStart_2006283 : Nat := 118140960795 + 2006283 * 2 ^ 59
def prefixEnd_2006283 : Nat := 4983230072969 + 3 ^ 40 * 2006283 * 2
def baseEnd_2006283 : Nat := 1030187507944479142235779

theorem tailTrace_2006283 : CollatzResearch.WordTrace tailWord_2006283 prefixEnd_2006283 1030187507944479142235779 := by
  unfold tailWord_2006283
  simp only [CollatzResearch.WordTrace]
  refine ⟨73175152590586811702079503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48783435060391207801386335 73175152590586811702079503)
  ·
    refine ⟨109762728885880217553119255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73175152590586811702079503 109762728885880217553119255)
    ·
      refine ⟨164644093328820326329678883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109762728885880217553119255 164644093328820326329678883)
      ·
        refine ⟨246966139993230489494518325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164644093328820326329678883 246966139993230489494518325)
        ·
          refine ⟨23153075624365358390111093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246966139993230489494518325 23153075624365358390111093)
          ·
            refine ⟨2170600839784252349072915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23153075624365358390111093 2170600839784252349072915)
            ·
              refine ⟨3255901259676378523609373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170600839784252349072915 3255901259676378523609373)
              ·
                refine ⟨1220962972378641946353515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3255901259676378523609373 1220962972378641946353515)
                ·
                  refine ⟨1831444458567962919530273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220962972378641946353515 1831444458567962919530273)
                  ·
                    refine ⟨1373583343925972189647705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1831444458567962919530273 1373583343925972189647705)
                    ·
                      refine ⟨1030187507944479142235779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373583343925972189647705 1030187507944479142235779)
                      ·
                        rfl

theorem cell23_2006283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 1, 2, 2].length) (baseStart_2006283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006283 prefixEnd_2006283 := by exact prefixLift 2006283
  have htrace : WordTrace (prefixWord ++ tailWord_2006283) baseStart_2006283 baseEnd_2006283 := by
    simpa [prefixWord, tailWord_2006283, baseEnd_2006283] using wordTrace_append hprefix tailTrace_2006283
  have hstable : (prefixWord ++ tailWord_2006283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006283).length < 2 ^ (prefixWord ++ tailWord_2006283).sum := by decide
  have hdescent : baseEnd_2006283 < baseStart_2006283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006295 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2006295 : Nat := 118140960795 + 2006295 * 2 ^ 59
def prefixEnd_2006295 : Nat := 4983230072969 + 3 ^ 40 * 2006295 * 2
def baseEnd_2006295 : Nat := 1030193669712333095285723

theorem tailTrace_2006295 : CollatzResearch.WordTrace tailWord_2006295 prefixEnd_2006295 1030193669712333095285723 := by
  unfold tailWord_2006295
  simp only [CollatzResearch.WordTrace]
  refine ⟨73175590266543337751516339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48783726844362225167677559 73175590266543337751516339)
  ·
    refine ⟨109763385399815006627274509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73175590266543337751516339 109763385399815006627274509)
    ·
      refine ⟨41161269524930627485227941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109763385399815006627274509 41161269524930627485227941)
      ·
        refine ⟨7717738035924492653480239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41161269524930627485227941 7717738035924492653480239)
        ·
          refine ⟨11576607053886738980220359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7717738035924492653480239 11576607053886738980220359)
          ·
            refine ⟨17364910580830108470330539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11576607053886738980220359 17364910580830108470330539)
            ·
              refine ⟨26047365871245162705495809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17364910580830108470330539 26047365871245162705495809)
              ·
                refine ⟨19535524403433872029121857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26047365871245162705495809 19535524403433872029121857)
                ·
                  refine ⟨14651643302575404021841393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19535524403433872029121857 14651643302575404021841393)
                  ·
                    refine ⟨10988732476931553016381045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14651643302575404021841393 10988732476931553016381045)
                    ·
                      refine ⟨1030193669712333095285723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10988732476931553016381045 1030193669712333095285723)
                      ·
                        rfl

theorem cell23_2006295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2006295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006295 prefixEnd_2006295 := by exact prefixLift 2006295
  have htrace : WordTrace (prefixWord ++ tailWord_2006295) baseStart_2006295 baseEnd_2006295 := by
    simpa [prefixWord, tailWord_2006295, baseEnd_2006295] using wordTrace_append hprefix tailTrace_2006295
  have hstable : (prefixWord ++ tailWord_2006295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006295).length < 2 ^ (prefixWord ++ tailWord_2006295).sum := by decide
  have hdescent : baseEnd_2006295 < baseStart_2006295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006305 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2006305 : Nat := 118140960795 + 2006305 * 2 ^ 59
def prefixEnd_2006305 : Nat := 4983230072969 + 3 ^ 40 * 2006305 * 2
def baseEnd_2006305 : Nat := 1030198804518878056160677

theorem tailTrace_2006305 : CollatzResearch.WordTrace tailWord_2006305 prefixEnd_2006305 1030198804518878056160677 := by
  unfold tailWord_2006305
  simp only [CollatzResearch.WordTrace]
  refine ⟨73175954996507109459380369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48783969997671406306253579 73175954996507109459380369)
  ·
    refine ⟨54881966247380332094535277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73175954996507109459380369 54881966247380332094535277)
    ·
      refine ⟨20580737342767624535450729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54881966247380332094535277 20580737342767624535450729)
      ·
        refine ⟨15435553007075718401588047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20580737342767624535450729 15435553007075718401588047)
        ·
          refine ⟨23153329510613577602382071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435553007075718401588047 23153329510613577602382071)
          ·
            refine ⟨34729994265920366403573107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153329510613577602382071 34729994265920366403573107)
            ·
              refine ⟨52094991398880549605359661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34729994265920366403573107 52094991398880549605359661)
              ·
                refine ⟨19535621774580206102009873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52094991398880549605359661 19535621774580206102009873)
                ·
                  refine ⟨14651716330935154576507405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19535621774580206102009873 14651716330935154576507405)
                  ·
                    refine ⟨5494393624100682966190277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14651716330935154576507405 5494393624100682966190277)
                    ·
                      refine ⟨1030198804518878056160677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5494393624100682966190277 1030198804518878056160677)
                      ·
                        rfl

theorem cell23_2006305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2006305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006305 prefixEnd_2006305 := by exact prefixLift 2006305
  have htrace : WordTrace (prefixWord ++ tailWord_2006305) baseStart_2006305 baseEnd_2006305 := by
    simpa [prefixWord, tailWord_2006305, baseEnd_2006305] using wordTrace_append hprefix tailTrace_2006305
  have hstable : (prefixWord ++ tailWord_2006305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006305).length < 2 ^ (prefixWord ++ tailWord_2006305).sum := by decide
  have hdescent : baseEnd_2006305 < baseStart_2006305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006372 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_2006372 : Nat := 118140960795 + 2006372 * 2 ^ 59
def prefixEnd_2006372 : Nat := 4983230072969 + 3 ^ 40 * 2006372 * 2
def baseEnd_2006372 : Nat := 1030233207722729294022869

theorem tailTrace_2006372 : CollatzResearch.WordTrace tailWord_2006372 prefixEnd_2006372 1030233207722729294022869 := by
  unfold tailWord_2006372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36589199343632189951034685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48785599124842919934712913 36589199343632189951034685)
  ·
    refine ⟨13720949753862071231638007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36589199343632189951034685 13720949753862071231638007)
    ·
      refine ⟨20581424630793106847457011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13720949753862071231638007 20581424630793106847457011)
      ·
        refine ⟨30872136946189660271185517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20581424630793106847457011 30872136946189660271185517)
        ·
          refine ⟨11577051354821122601694569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30872136946189660271185517 11577051354821122601694569)
          ·
            refine ⟨8682788516115841951270927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11577051354821122601694569 8682788516115841951270927)
            ·
              refine ⟨13024182774173762926906391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8682788516115841951270927 13024182774173762926906391)
              ·
                refine ⟨19536274161260644390359587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024182774173762926906391 19536274161260644390359587)
                ·
                  refine ⟨29304411241890966585539381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19536274161260644390359587 29304411241890966585539381)
                  ·
                    refine ⟨2747288553927278117394317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29304411241890966585539381 2747288553927278117394317)
                    ·
                      refine ⟨1030233207722729294022869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747288553927278117394317 1030233207722729294022869)
                      ·
                        rfl

theorem cell23_2006372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_2006372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006372 prefixEnd_2006372 := by exact prefixLift 2006372
  have htrace : WordTrace (prefixWord ++ tailWord_2006372) baseStart_2006372 baseEnd_2006372 := by
    simpa [prefixWord, tailWord_2006372, baseEnd_2006372] using wordTrace_append hprefix tailTrace_2006372
  have hstable : (prefixWord ++ tailWord_2006372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006372).length < 2 ^ (prefixWord ++ tailWord_2006372).sum := by decide
  have hdescent : baseEnd_2006372 < baseStart_2006372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006385 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_2006385 : Nat := 118140960795 + 2006385 * 2 ^ 59
def prefixEnd_2006385 : Nat := 4983230072969 + 3 ^ 40 * 2006385 * 2
def baseEnd_2006385 : Nat := 1030239882971237743160309

theorem tailTrace_2006385 : CollatzResearch.WordTrace tailWord_2006385 prefixEnd_2006385 1030239882971237743160309 := by
  unfold tailWord_2006385
  simp only [CollatzResearch.WordTrace]
  refine ⟨73178872836217283122292609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48785915224144855414861739 73178872836217283122292609)
  ·
    refine ⟨54884154627162962341719457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73178872836217283122292609 54884154627162962341719457)
    ·
      refine ⟨41163115970372221756289593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54884154627162962341719457 41163115970372221756289593)
      ·
        refine ⟨30872336977779166317217195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41163115970372221756289593 30872336977779166317217195)
        ·
          refine ⟨46308505466668749475825793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30872336977779166317217195 46308505466668749475825793)
          ·
            refine ⟨34731379100001562106869345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46308505466668749475825793 34731379100001562106869345)
            ·
              refine ⟨26048534325001171580152009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34731379100001562106869345 26048534325001171580152009)
              ·
                refine ⟨19536400743750878685114007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26048534325001171580152009 19536400743750878685114007)
                ·
                  refine ⟨29304601115626318027671011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19536400743750878685114007 29304601115626318027671011)
                  ·
                    refine ⟨43956901673439477041506517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29304601115626318027671011 43956901673439477041506517)
                    ·
                      refine ⟨1030239882971237743160309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43956901673439477041506517 1030239882971237743160309)
                      ·
                        rfl

theorem cell23_2006385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_2006385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006385 prefixEnd_2006385 := by exact prefixLift 2006385
  have htrace : WordTrace (prefixWord ++ tailWord_2006385) baseStart_2006385 baseEnd_2006385 := by
    simpa [prefixWord, tailWord_2006385, baseEnd_2006385] using wordTrace_append hprefix tailTrace_2006385
  have hstable : (prefixWord ++ tailWord_2006385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006385).length < 2 ^ (prefixWord ++ tailWord_2006385).sum := by decide
  have hdescent : baseEnd_2006385 < baseStart_2006385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006412 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2006412 : Nat := 118140960795 + 2006412 * 2 ^ 59
def prefixEnd_2006412 : Nat := 4983230072969 + 3 ^ 40 * 2006412 * 2
def baseEnd_2006412 : Nat := 1030253746948909137522685

theorem tailTrace_2006412 : CollatzResearch.WordTrace tailWord_2006412 prefixEnd_2006412 1030253746948909137522685 := by
  unfold tailWord_2006412
  simp only [CollatzResearch.WordTrace]
  refine ⟨36589928803559733366762745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48786571738079644489016993 36589928803559733366762745)
  ·
    refine ⟨27442446602669800025072059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36589928803559733366762745 27442446602669800025072059)
    ·
      refine ⟨41163669904004700037608089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27442446602669800025072059 41163669904004700037608089)
      ·
        refine ⟨30872752428003525028206067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41163669904004700037608089 30872752428003525028206067)
        ·
          refine ⟨46309128642005287542309101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30872752428003525028206067 46309128642005287542309101)
          ·
            refine ⟨17365923240751982828365913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46309128642005287542309101 17365923240751982828365913)
            ·
              refine ⟨13024442430563987121274435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17365923240751982828365913 13024442430563987121274435)
              ·
                refine ⟨19536663645845980681911653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13024442430563987121274435 19536663645845980681911653)
                ·
                  refine ⟨3663124433596121377858435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19536663645845980681911653 3663124433596121377858435)
                  ·
                    refine ⟨5494686650394182066787653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3663124433596121377858435 5494686650394182066787653)
                    ·
                      refine ⟨1030253746948909137522685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5494686650394182066787653 1030253746948909137522685)
                      ·
                        rfl

theorem cell23_2006412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2006412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006412 prefixEnd_2006412 := by exact prefixLift 2006412
  have htrace : WordTrace (prefixWord ++ tailWord_2006412) baseStart_2006412 baseEnd_2006412 := by
    simpa [prefixWord, tailWord_2006412, baseEnd_2006412] using wordTrace_append hprefix tailTrace_2006412
  have hstable : (prefixWord ++ tailWord_2006412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006412).length < 2 ^ (prefixWord ++ tailWord_2006412).sum := by decide
  have hdescent : baseEnd_2006412 < baseStart_2006412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006432 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2006432 : Nat := 118140960795 + 2006432 * 2 ^ 59
def prefixEnd_2006432 : Nat := 4983230072969 + 3 ^ 40 * 2006432 * 2
def baseEnd_2006432 : Nat := 1030264016561999059272593

theorem tailTrace_2006432 : CollatzResearch.WordTrace tailWord_2006432 prefixEnd_2006432 1030264016561999059272593 := by
  unfold tailWord_2006432
  simp only [CollatzResearch.WordTrace]
  refine ⟨36590293533523505074626775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48787058044698006766169033 36590293533523505074626775)
  ·
    refine ⟨54885440300285257611940163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36590293533523505074626775 54885440300285257611940163)
    ·
      refine ⟨82328160450427886417910245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54885440300285257611940163 82328160450427886417910245)
      ·
        refine ⟨15436530084455228703358171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82328160450427886417910245 15436530084455228703358171)
        ·
          refine ⟨23154795126682843055037257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15436530084455228703358171 23154795126682843055037257)
          ·
            refine ⟨17366096345012132291277943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23154795126682843055037257 17366096345012132291277943)
            ·
              refine ⟨26049144517518198436916915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366096345012132291277943 26049144517518198436916915)
              ·
                refine ⟨39073716776277297655375373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26049144517518198436916915 39073716776277297655375373)
                ·
                  refine ⟨14652643791103986620765765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39073716776277297655375373 14652643791103986620765765)
                  ·
                    refine ⟨2747370710831997491393581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14652643791103986620765765 2747370710831997491393581)
                    ·
                      refine ⟨1030264016561999059272593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747370710831997491393581 1030264016561999059272593)
                      ·
                        rfl

theorem cell23_2006432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2006432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006432 prefixEnd_2006432 := by exact prefixLift 2006432
  have htrace : WordTrace (prefixWord ++ tailWord_2006432) baseStart_2006432 baseEnd_2006432 := by
    simpa [prefixWord, tailWord_2006432, baseEnd_2006432] using wordTrace_append hprefix tailTrace_2006432
  have hstable : (prefixWord ++ tailWord_2006432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006432).length < 2 ^ (prefixWord ++ tailWord_2006432).sum := by decide
  have hdescent : baseEnd_2006432 < baseStart_2006432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006439 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2006439 : Nat := 118140960795 + 2006439 * 2 ^ 59
def prefixEnd_2006439 : Nat := 4983230072969 + 3 ^ 40 * 2006439 * 2
def baseEnd_2006439 : Nat := 343422536975526843961687

theorem tailTrace_2006439 : CollatzResearch.WordTrace tailWord_2006439 prefixEnd_2006439 343422536975526843961687 := by
  unfold tailWord_2006439
  simp only [CollatzResearch.WordTrace]
  refine ⟨73180842378021650344758371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48787228252014433563172247 73180842378021650344758371)
  ·
    refine ⟨109771263567032475517137557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73180842378021650344758371 109771263567032475517137557)
    ·
      refine ⟨5145527979704647289865823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109771263567032475517137557 5145527979704647289865823)
      ·
        refine ⟨7718291969556970934798735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145527979704647289865823 7718291969556970934798735)
        ·
          refine ⟨11577437954335456402198103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718291969556970934798735 11577437954335456402198103)
          ·
            refine ⟨17366156931503184603297155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577437954335456402198103 17366156931503184603297155)
            ·
              refine ⟨26049235397254776904945733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17366156931503184603297155 26049235397254776904945733)
              ·
                refine ⟨4884231636985270669677325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26049235397254776904945733 4884231636985270669677325)
                ·
                  refine ⟨1831586863869476501128997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4884231636985270669677325 1831586863869476501128997)
                  ·
                    refine ⟨343422536975526843961687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831586863869476501128997 343422536975526843961687)
                    ·
                      rfl

theorem cell23_2006439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2006439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006439 prefixEnd_2006439 := by exact prefixLift 2006439
  have htrace : WordTrace (prefixWord ++ tailWord_2006439) baseStart_2006439 baseEnd_2006439 := by
    simpa [prefixWord, tailWord_2006439, baseEnd_2006439] using wordTrace_append hprefix tailTrace_2006439
  have hstable : (prefixWord ++ tailWord_2006439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006439).length < 2 ^ (prefixWord ++ tailWord_2006439).sum := by decide
  have hdescent : baseEnd_2006439 < baseStart_2006439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006449 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2006449 : Nat := 118140960795 + 2006449 * 2 ^ 59
def prefixEnd_2006449 : Nat := 4983230072969 + 3 ^ 40 * 2006449 * 2
def baseEnd_2006449 : Nat := 1030272745733125492760015

theorem tailTrace_2006449 : CollatzResearch.WordTrace tailWord_2006449 prefixEnd_2006449 1030272745733125492760015 := by
  unfold tailWord_2006449
  simp only [CollatzResearch.WordTrace]
  refine ⟨73181207107985422052622401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48787471405323614701748267 73181207107985422052622401)
  ·
    refine ⟨54885905330989066539466801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73181207107985422052622401 54885905330989066539466801)
    ·
      refine ⟨41164428998241799904600101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54885905330989066539466801 41164428998241799904600101)
      ·
        refine ⟨7718330437170337482112519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41164428998241799904600101 7718330437170337482112519)
        ·
          refine ⟨11577495655755506223168779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718330437170337482112519 11577495655755506223168779)
          ·
            refine ⟨17366243483633259334753169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11577495655755506223168779 17366243483633259334753169)
            ·
              refine ⟨13024682612724944501064877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17366243483633259334753169 13024682612724944501064877)
              ·
                refine ⟨4884255979771854187899329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13024682612724944501064877 4884255979771854187899329)
                ·
                  refine ⟨3663191984828890640924497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884255979771854187899329 3663191984828890640924497)
                  ·
                    refine ⟨2747393988621667980693373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3663191984828890640924497 2747393988621667980693373)
                    ·
                      refine ⟨1030272745733125492760015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747393988621667980693373 1030272745733125492760015)
                      ·
                        rfl

theorem cell23_2006449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2006449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006449 prefixEnd_2006449 := by exact prefixLift 2006449
  have htrace : WordTrace (prefixWord ++ tailWord_2006449) baseStart_2006449 baseEnd_2006449 := by
    simpa [prefixWord, tailWord_2006449, baseEnd_2006449] using wordTrace_append hprefix tailTrace_2006449
  have hstable : (prefixWord ++ tailWord_2006449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006449).length < 2 ^ (prefixWord ++ tailWord_2006449).sum := by decide
  have hdescent : baseEnd_2006449 < baseStart_2006449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006456 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 1, 4]
def baseStart_2006456 : Nat := 118140960795 + 2006456 * 2 ^ 59
def prefixEnd_2006456 : Nat := 4983230072969 + 3 ^ 40 * 2006456 * 2
def baseEnd_2006456 : Nat := 343425446699235655124161

theorem tailTrace_2006456 : CollatzResearch.WordTrace tailWord_2006456 prefixEnd_2006456 343425446699235655124161 := by
  unfold tailWord_2006456
  simp only [CollatzResearch.WordTrace]
  refine ⟨36590731209480031124063611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48787641612640041498751481 36590731209480031124063611)
  ·
    refine ⟨54886096814220046686095417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36590731209480031124063611 54886096814220046686095417)
    ·
      refine ⟨41164572610665035014571563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54886096814220046686095417 41164572610665035014571563)
      ·
        refine ⟨61746858915997552521857345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41164572610665035014571563 61746858915997552521857345)
        ·
          refine ⟨46310144186998164391393009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61746858915997552521857345 46310144186998164391393009)
          ·
            refine ⟨34732608140248623293544757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46310144186998164391393009 34732608140248623293544757)
            ·
              refine ⟨3256182013148308433769821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34732608140248623293544757 3256182013148308433769821)
              ·
                refine ⟨1221068254930615662663683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3256182013148308433769821 1221068254930615662663683)
                ·
                  refine ⟨1831602382395923493995525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221068254930615662663683 1831602382395923493995525)
                  ·
                    refine ⟨343425446699235655124161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831602382395923493995525 343425446699235655124161)
                    ·
                      rfl

theorem cell23_2006456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_2006456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006456 prefixEnd_2006456 := by exact prefixLift 2006456
  have htrace : WordTrace (prefixWord ++ tailWord_2006456) baseStart_2006456 baseEnd_2006456 := by
    simpa [prefixWord, tailWord_2006456, baseEnd_2006456] using wordTrace_append hprefix tailTrace_2006456
  have hstable : (prefixWord ++ tailWord_2006456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006456).length < 2 ^ (prefixWord ++ tailWord_2006456).sum := by decide
  have hdescent : baseEnd_2006456 < baseStart_2006456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006486 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2006486 : Nat := 118140960795 + 2006486 * 2 ^ 59
def prefixEnd_2006486 : Nat := 4983230072969 + 3 ^ 40 * 2006486 * 2
def baseEnd_2006486 : Nat := 114476860501926871999705

theorem tailTrace_2006486 : CollatzResearch.WordTrace tailWord_2006486 prefixEnd_2006486 114476860501926871999705 := by
  unfold tailWord_2006486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4573909788053211085732457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48788371072567584914479541 4573909788053211085732457)
  ·
    refine ⟨3430432341039908314299343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4573909788053211085732457 3430432341039908314299343)
    ·
      refine ⟨5145648511559862471449015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430432341039908314299343 5145648511559862471449015)
      ·
        refine ⟨7718472767339793707173523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145648511559862471449015 7718472767339793707173523)
        ·
          refine ⟨11577709151009690560760285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718472767339793707173523 11577709151009690560760285)
          ·
            refine ⟨4341640931628633960285107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11577709151009690560760285 4341640931628633960285107)
            ·
              refine ⟨6512461397442950940427661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341640931628633960285107 6512461397442950940427661)
              ·
                refine ⟨2442173024041106602660373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6512461397442950940427661 2442173024041106602660373)
                ·
                  refine ⟨114476860501926871999705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2442173024041106602660373 114476860501926871999705)
                  ·
                    rfl

theorem cell23_2006486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2006486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006486 prefixEnd_2006486 := by exact prefixLift 2006486
  have htrace : WordTrace (prefixWord ++ tailWord_2006486) baseStart_2006486 baseEnd_2006486 := by
    simpa [prefixWord, tailWord_2006486, baseEnd_2006486] using wordTrace_append hprefix tailTrace_2006486
  have hstable : (prefixWord ++ tailWord_2006486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006486).length < 2 ^ (prefixWord ++ tailWord_2006486).sum := by decide
  have hdescent : baseEnd_2006486 < baseStart_2006486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006499 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 3, 5]
def baseStart_2006499 : Nat := 118140960795 + 2006499 * 2 ^ 59
def prefixEnd_2006499 : Nat := 4983230072969 + 3 ^ 40 * 2006499 * 2
def baseEnd_2006499 : Nat := 343432806588616765711595

theorem tailTrace_2006499 : CollatzResearch.WordTrace tailWord_2006499 prefixEnd_2006499 343432806588616765711595 := by
  unfold tailWord_2006499
  simp only [CollatzResearch.WordTrace]
  refine ⟨73183030757804280591942551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48788687171869520394628367 73183030757804280591942551)
  ·
    refine ⟨109774546136706420887913827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73183030757804280591942551 109774546136706420887913827)
    ·
      refine ⟨164661819205059631331870741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109774546136706420887913827 164661819205059631331870741)
      ·
        refine ⟨7718522775237170218681441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164661819205059631331870741 7718522775237170218681441)
        ·
          refine ⟨5788892081427877664011081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7718522775237170218681441 5788892081427877664011081)
          ·
            refine ⟨4341669061070908248008311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5788892081427877664011081 4341669061070908248008311)
            ·
              refine ⟨6512503591606362372012467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341669061070908248008311 6512503591606362372012467)
              ·
                refine ⟨9768755387409543558018701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512503591606362372012467 9768755387409543558018701)
                ·
                  refine ⟨3663283270278578834257013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9768755387409543558018701 3663283270278578834257013)
                  ·
                    refine ⟨343432806588616765711595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3663283270278578834257013 343432806588616765711595)
                    ·
                      rfl

theorem cell23_2006499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 5].length) (baseStart_2006499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006499 prefixEnd_2006499 := by exact prefixLift 2006499
  have htrace : WordTrace (prefixWord ++ tailWord_2006499) baseStart_2006499 baseEnd_2006499 := by
    simpa [prefixWord, tailWord_2006499, baseEnd_2006499] using wordTrace_append hprefix tailTrace_2006499
  have hstable : (prefixWord ++ tailWord_2006499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006499).length < 2 ^ (prefixWord ++ tailWord_2006499).sum := by decide
  have hdescent : baseEnd_2006499 < baseStart_2006499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006512 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_2006512 : Nat := 118140960795 + 2006512 * 2 ^ 59
def prefixEnd_2006512 : Nat := 4983230072969 + 3 ^ 40 * 2006512 * 2
def baseEnd_2006512 : Nat := 343435031671452915424075

theorem tailTrace_2006512 : CollatzResearch.WordTrace tailWord_2006512 prefixEnd_2006512 343435031671452915424075 := by
  unfold tailWord_2006512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36591752453378591906082895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48789003271171455874777193 36591752453378591906082895)
  ·
    refine ⟨54887628680067887859124343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36591752453378591906082895 54887628680067887859124343)
    ·
      refine ⟨82331443020101831788686515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54887628680067887859124343 82331443020101831788686515)
      ·
        refine ⟨123497164530152747683029773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82331443020101831788686515 123497164530152747683029773)
        ·
          refine ⟨46311436698807280381136165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123497164530152747683029773 46311436698807280381136165)
          ·
            refine ⟨8683394381026365071463031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46311436698807280381136165 8683394381026365071463031)
            ·
              refine ⟨13025091571539547607194547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683394381026365071463031 13025091571539547607194547)
              ·
                refine ⟨19537637357309321410791821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025091571539547607194547 19537637357309321410791821)
                ·
                  refine ⟨7326614008990995529046933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19537637357309321410791821 7326614008990995529046933)
                  ·
                    refine ⟨343435031671452915424075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7326614008990995529046933 343435031671452915424075)
                    ·
                      rfl

theorem cell23_2006512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_2006512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006512 prefixEnd_2006512 := by exact prefixLift 2006512
  have htrace : WordTrace (prefixWord ++ tailWord_2006512) baseStart_2006512 baseEnd_2006512 := by
    simpa [prefixWord, tailWord_2006512, baseEnd_2006512] using wordTrace_append hprefix tailTrace_2006512
  have hstable : (prefixWord ++ tailWord_2006512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006512).length < 2 ^ (prefixWord ++ tailWord_2006512).sum := by decide
  have hdescent : baseEnd_2006512 < baseStart_2006512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006549 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2006549 : Nat := 118140960795 + 2006549 * 2 ^ 59
def prefixEnd_2006549 : Nat := 4983230072969 + 3 ^ 40 * 2006549 * 2
def baseEnd_2006549 : Nat := 1030324093798575101509555

theorem tailTrace_2006549 : CollatzResearch.WordTrace tailWord_2006549 prefixEnd_2006549 1030324093798575101509555 := by
  unfold tailWord_2006549
  simp only [CollatzResearch.WordTrace]
  refine ⟨73184854407623139131262701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48789902938415426087508467 73184854407623139131262701)
  ·
    refine ⟨27444320402858677174223513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73184854407623139131262701 27444320402858677174223513)
    ·
      refine ⟨20583240302144007880667635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27444320402858677174223513 20583240302144007880667635)
      ·
        refine ⟨30874860453216011821001453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20583240302144007880667635 30874860453216011821001453)
        ·
          refine ⟨11578072669956004432875545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30874860453216011821001453 11578072669956004432875545)
          ·
            refine ⟨8683554502467003324656659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11578072669956004432875545 8683554502467003324656659)
            ·
              refine ⟨13025331753700504986984989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683554502467003324656659 13025331753700504986984989)
              ·
                refine ⟨4884499407637689370119371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13025331753700504986984989 4884499407637689370119371)
                ·
                  refine ⟨7326749111456534055179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4884499407637689370119371 7326749111456534055179057)
                  ·
                    refine ⟨5495061833592400541384293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7326749111456534055179057 5495061833592400541384293)
                    ·
                      refine ⟨1030324093798575101509555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5495061833592400541384293 1030324093798575101509555)
                      ·
                        rfl

theorem cell23_2006549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2006549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006549 prefixEnd_2006549 := by exact prefixLift 2006549
  have htrace : WordTrace (prefixWord ++ tailWord_2006549) baseStart_2006549 baseEnd_2006549 := by
    simpa [prefixWord, tailWord_2006549, baseEnd_2006549] using wordTrace_append hprefix tailTrace_2006549
  have hstable : (prefixWord ++ tailWord_2006549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006549).length < 2 ^ (prefixWord ++ tailWord_2006549).sum := by decide
  have hdescent : baseEnd_2006549 < baseStart_2006549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006556 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2006556 : Nat := 118140960795 + 2006556 * 2 ^ 59
def prefixEnd_2006556 : Nat := 4983230072969 + 3 ^ 40 * 2006556 * 2
def baseEnd_2006556 : Nat := 1030327688163156574122023

theorem tailTrace_2006556 : CollatzResearch.WordTrace tailWord_2006556 prefixEnd_2006556 1030327688163156574122023 := by
  unfold tailWord_2006556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36592554859298889663383761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48790073145731852884511681 36592554859298889663383761)
  ·
    refine ⟨27444416144474167247537821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36592554859298889663383761 27444416144474167247537821)
    ·
      refine ⟨10291656054177812717826683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27444416144474167247537821 10291656054177812717826683)
      ·
        refine ⟨15437484081266719076740025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10291656054177812717826683 15437484081266719076740025)
        ·
          refine ⟨11578113060950039307555019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15437484081266719076740025 11578113060950039307555019)
          ·
            refine ⟨17367169591425058961332529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11578113060950039307555019 17367169591425058961332529)
            ·
              refine ⟨13025377193568794220999397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17367169591425058961332529 13025377193568794220999397)
              ·
                refine ⟨2442258223794148916437387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13025377193568794220999397 2442258223794148916437387)
                ·
                  refine ⟨3663387335691223374656081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442258223794148916437387 3663387335691223374656081)
                  ·
                    refine ⟨2747540501768417530992061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3663387335691223374656081 2747540501768417530992061)
                    ·
                      refine ⟨1030327688163156574122023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747540501768417530992061 1030327688163156574122023)
                      ·
                        rfl

theorem cell23_2006556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2006556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006556 prefixEnd_2006556 := by exact prefixLift 2006556
  have htrace : WordTrace (prefixWord ++ tailWord_2006556) baseStart_2006556 baseEnd_2006556 := by
    simpa [prefixWord, tailWord_2006556, baseEnd_2006556] using wordTrace_append hprefix tailTrace_2006556
  have hstable : (prefixWord ++ tailWord_2006556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006556).length < 2 ^ (prefixWord ++ tailWord_2006556).sum := by decide
  have hdescent : baseEnd_2006556 < baseStart_2006556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006586 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_2006586 : Nat := 118140960795 + 2006586 * 2 ^ 59
def prefixEnd_2006586 : Nat := 4983230072969 + 3 ^ 40 * 2006586 * 2
def baseEnd_2006586 : Nat := 1030343092582791456746885

theorem tailTrace_2006586 : CollatzResearch.WordTrace tailWord_2006586 prefixEnd_2006586 1030343092582791456746885 := by
  unfold tailWord_2006586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296550977122273612589903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48790802605659396300239741 18296550977122273612589903)
  ·
    refine ⟨27444826465683410418884855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18296550977122273612589903 27444826465683410418884855)
    ·
      refine ⟨41167239698525115628327283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27444826465683410418884855 41167239698525115628327283)
      ·
        refine ⟨61750859547787673442490925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41167239698525115628327283 61750859547787673442490925)
        ·
          refine ⟨23156572330420377540934097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61750859547787673442490925 23156572330420377540934097)
          ·
            refine ⟨17367429247815283155700573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23156572330420377540934097 17367429247815283155700573)
            ·
              refine ⟨6512785967930731183387715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17367429247815283155700573 6512785967930731183387715)
              ·
                refine ⟨9769178951896096775081573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512785967930731183387715 9769178951896096775081573)
                ·
                  refine ⟨1831721053480518145327795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9769178951896096775081573 1831721053480518145327795)
                  ·
                    refine ⟨2747581580220777217991693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831721053480518145327795 2747581580220777217991693)
                    ·
                      refine ⟨1030343092582791456746885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747581580220777217991693 1030343092582791456746885)
                      ·
                        rfl

theorem cell23_2006586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_2006586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006586 prefixEnd_2006586 := by exact prefixLift 2006586
  have htrace : WordTrace (prefixWord ++ tailWord_2006586) baseStart_2006586 baseEnd_2006586 := by
    simpa [prefixWord, tailWord_2006586, baseEnd_2006586] using wordTrace_append hprefix tailTrace_2006586
  have hstable : (prefixWord ++ tailWord_2006586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006586).length < 2 ^ (prefixWord ++ tailWord_2006586).sum := by decide
  have hdescent : baseEnd_2006586 < baseStart_2006586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006621 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2006621 : Nat := 118140960795 + 2006621 * 2 ^ 59
def prefixEnd_2006621 : Nat := 4983230072969 + 3 ^ 40 * 2006621 * 2
def baseEnd_2006621 : Nat := 1030361064405698819809225

theorem tailTrace_2006621 : CollatzResearch.WordTrace tailWord_2006621 prefixEnd_2006621 1030361064405698819809225 := by
  unfold tailWord_2006621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73187480463362295427883717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48791653642241530285255811 73187480463362295427883717)
  ·
    refine ⟨13722652586880430392728197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73187480463362295427883717 13722652586880430392728197)
    ·
      refine ⟨2572997360040080698636537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13722652586880430392728197 2572997360040080698636537)
      ·
        refine ⟨1929748020030060523977403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2572997360040080698636537 1929748020030060523977403)
        ·
          refine ⟨2894622030045090785966105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929748020030060523977403 2894622030045090785966105)
          ·
            refine ⟨2170966522533818089474579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894622030045090785966105 2170966522533818089474579)
            ·
              refine ⟨3256449783800727134211869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170966522533818089474579 3256449783800727134211869)
              ·
                refine ⟨1221168668925272675329451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3256449783800727134211869 1221168668925272675329451)
                ·
                  refine ⟨1831753003387909012994177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221168668925272675329451 1831753003387909012994177)
                  ·
                    refine ⟨1373814752540931759745633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1831753003387909012994177 1373814752540931759745633)
                    ·
                      refine ⟨1030361064405698819809225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373814752540931759745633 1030361064405698819809225)
                      ·
                        rfl

theorem cell23_2006621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2006621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006621 prefixEnd_2006621 := by exact prefixLift 2006621
  have htrace : WordTrace (prefixWord ++ tailWord_2006621) baseStart_2006621 baseEnd_2006621 := by
    simpa [prefixWord, tailWord_2006621, baseEnd_2006621] using wordTrace_append hprefix tailTrace_2006621
  have hstable : (prefixWord ++ tailWord_2006621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006621).length < 2 ^ (prefixWord ++ tailWord_2006621).sum := by decide
  have hdescent : baseEnd_2006621 < baseStart_2006621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006629 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2006629 : Nat := 118140960795 + 2006629 * 2 ^ 59
def prefixEnd_2006629 : Nat := 4983230072969 + 3 ^ 40 * 2006629 * 2
def baseEnd_2006629 : Nat := 1030365172250934788509187

theorem tailTrace_2006629 : CollatzResearch.WordTrace tailWord_2006629 prefixEnd_2006629 1030365172250934788509187 := by
  unfold tailWord_2006629
  simp only [CollatzResearch.WordTrace]
  refine ⟨73187772247333312794174941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48791848164888875196116627 73187772247333312794174941)
  ·
    refine ⟨27445414592749992297815603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73187772247333312794174941 27445414592749992297815603)
    ·
      refine ⟨41168121889124988446723405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27445414592749992297815603 41168121889124988446723405)
      ·
        refine ⟨15438045708421870667521277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41168121889124988446723405 15438045708421870667521277)
        ·
          refine ⟨5789267140658201500320479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15438045708421870667521277 5789267140658201500320479)
          ·
            refine ⟨8683900710987302250480719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789267140658201500320479 8683900710987302250480719)
            ·
              refine ⟨13025851066480953375721079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683900710987302250480719 13025851066480953375721079)
              ·
                refine ⟨19538776599721430063581619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025851066480953375721079 19538776599721430063581619)
                ·
                  refine ⟨29308164899582145095372429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19538776599721430063581619 29308164899582145095372429)
                  ·
                    refine ⟨10990561837343304410764661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29308164899582145095372429 10990561837343304410764661)
                    ·
                      refine ⟨1030365172250934788509187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10990561837343304410764661 1030365172250934788509187)
                      ·
                        rfl

theorem cell23_2006629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2006629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006629 prefixEnd_2006629 := by exact prefixLift 2006629
  have htrace : WordTrace (prefixWord ++ tailWord_2006629) baseStart_2006629 baseEnd_2006629 := by
    simpa [prefixWord, tailWord_2006629, baseEnd_2006629] using wordTrace_append hprefix tailTrace_2006629
  have hstable : (prefixWord ++ tailWord_2006629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006629).length < 2 ^ (prefixWord ++ tailWord_2006629).sum := by decide
  have hdescent : baseEnd_2006629 < baseStart_2006629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006659 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3]
def baseStart_2006659 : Nat := 118140960795 + 2006659 * 2 ^ 59
def prefixEnd_2006659 : Nat := 4983230072969 + 3 ^ 40 * 2006659 * 2
def baseEnd_2006659 : Nat := 1030380576670569671134049

theorem tailTrace_2006659 : CollatzResearch.WordTrace tailWord_2006659 prefixEnd_2006659 1030380576670569671134049 := by
  unfold tailWord_2006659
  simp only [CollatzResearch.WordTrace]
  refine ⟨73188866437224627917767031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48792577624816418611844687 73188866437224627917767031)
  ·
    refine ⟨109783299655836941876650547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73188866437224627917767031 109783299655836941876650547)
    ·
      refine ⟨164674949483755412814975821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109783299655836941876650547 164674949483755412814975821)
      ·
        refine ⟨61753106056408279805615933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164674949483755412814975821 61753106056408279805615933)
        ·
          refine ⟨23157414771153104927105975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61753106056408279805615933 23157414771153104927105975)
          ·
            refine ⟨34736122156729657390658963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23157414771153104927105975 34736122156729657390658963)
            ·
              refine ⟨52104183235094486085988445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34736122156729657390658963 52104183235094486085988445)
              ·
                refine ⟨19539068713160432282245667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52104183235094486085988445 19539068713160432282245667)
                ·
                  refine ⟨29308603069740648423368501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19539068713160432282245667 29308603069740648423368501)
                  ·
                    refine ⟨2747681537788185789690797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29308603069740648423368501 2747681537788185789690797)
                    ·
                      refine ⟨1030380576670569671134049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747681537788185789690797 1030380576670569671134049)
                      ·
                        rfl

theorem cell23_2006659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_2006659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006659 prefixEnd_2006659 := by exact prefixLift 2006659
  have htrace : WordTrace (prefixWord ++ tailWord_2006659) baseStart_2006659 baseEnd_2006659 := by
    simpa [prefixWord, tailWord_2006659, baseEnd_2006659] using wordTrace_append hprefix tailTrace_2006659
  have hstable : (prefixWord ++ tailWord_2006659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006659).length < 2 ^ (prefixWord ++ tailWord_2006659).sum := by decide
  have hdescent : baseEnd_2006659 < baseStart_2006659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006664 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2006664 : Nat := 118140960795 + 2006664 * 2 ^ 59
def prefixEnd_2006664 : Nat := 4983230072969 + 3 ^ 40 * 2006664 * 2
def baseEnd_2006664 : Nat := 1030383144073842151571527

theorem tailTrace_2006664 : CollatzResearch.WordTrace tailWord_2006664 prefixEnd_2006664 1030383144073842151571527 := by
  unfold tailWord_2006664
  simp only [CollatzResearch.WordTrace]
  refine ⟨36594524401103256885849523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48792699201471009181132697 36594524401103256885849523)
  ·
    refine ⟨54891786601654885328774285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36594524401103256885849523 54891786601654885328774285)
    ·
      refine ⟨20584419975620581998290357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54891786601654885328774285 20584419975620581998290357)
      ·
        refine ⟨1929789372714429562339721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20584419975620581998290357 1929789372714429562339721)
        ·
          refine ⟨1447342029535822171754791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929789372714429562339721 1447342029535822171754791)
          ·
            refine ⟨2171013044303733257632187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447342029535822171754791 2171013044303733257632187)
            ·
              refine ⟨3256519566455599886448281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171013044303733257632187 3256519566455599886448281)
              ·
                refine ⟨2442389674841699914836211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256519566455599886448281 2442389674841699914836211)
                ·
                  refine ⟨3663584512262549872254317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442389674841699914836211 3663584512262549872254317)
                  ·
                    refine ⟨1373844192098456202095369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663584512262549872254317 1373844192098456202095369)
                    ·
                      refine ⟨1030383144073842151571527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373844192098456202095369 1030383144073842151571527)
                      ·
                        rfl

theorem cell23_2006664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2006664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006664 prefixEnd_2006664 := by exact prefixLift 2006664
  have htrace : WordTrace (prefixWord ++ tailWord_2006664) baseStart_2006664 baseEnd_2006664 := by
    simpa [prefixWord, tailWord_2006664, baseEnd_2006664] using wordTrace_append hprefix tailTrace_2006664
  have hstable : (prefixWord ++ tailWord_2006664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006664).length < 2 ^ (prefixWord ++ tailWord_2006664).sum := by decide
  have hdescent : baseEnd_2006664 < baseStart_2006664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006710 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2006710 : Nat := 118140960795 + 2006710 * 2 ^ 59
def prefixEnd_2006710 : Nat := 4983230072969 + 3 ^ 40 * 2006710 * 2
def baseEnd_2006710 : Nat := 1030406764183948971596315

theorem tailTrace_2006710 : CollatzResearch.WordTrace tailWord_2006710 prefixEnd_2006710 1030406764183948971596315 := by
  unfold tailWord_2006710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574420410002491476742099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48793817706693242418582389 4574420410002491476742099)
  ·
    refine ⟨6861630615003737215113149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574420410002491476742099 6861630615003737215113149)
    ·
      refine ⟨2573111480626401455667431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6861630615003737215113149 2573111480626401455667431)
      ·
        refine ⟨3859667220939602183501147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573111480626401455667431 3859667220939602183501147)
        ·
          refine ⟨5789500831409403275251721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859667220939602183501147 5789500831409403275251721)
          ·
            refine ⟨4342125623557052456438791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5789500831409403275251721 4342125623557052456438791)
            ·
              refine ⟨6513188435335578684658187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342125623557052456438791 6513188435335578684658187)
              ·
                refine ⟨9769782653003368026987281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513188435335578684658187 9769782653003368026987281)
                ·
                  refine ⟨7327336989752526020240461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9769782653003368026987281 7327336989752526020240461)
                  ·
                    refine ⟨2747751371157197257590173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7327336989752526020240461 2747751371157197257590173)
                    ·
                      refine ⟨1030406764183948971596315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747751371157197257590173 1030406764183948971596315)
                      ·
                        rfl

theorem cell23_2006710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2006710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006710 prefixEnd_2006710 := by exact prefixLift 2006710
  have htrace : WordTrace (prefixWord ++ tailWord_2006710) baseStart_2006710 baseEnd_2006710 := by
    simpa [prefixWord, tailWord_2006710, baseEnd_2006710] using wordTrace_append hprefix tailTrace_2006710
  have hstable : (prefixWord ++ tailWord_2006710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006710).length < 2 ^ (prefixWord ++ tailWord_2006710).sum := by decide
  have hdescent : baseEnd_2006710 < baseStart_2006710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006730 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_2006730 : Nat := 118140960795 + 2006730 * 2 ^ 59
def prefixEnd_2006730 : Nat := 4983230072969 + 3 ^ 40 * 2006730 * 2
def baseEnd_2006730 : Nat := 343472344599012964448741

theorem tailTrace_2006730 : CollatzResearch.WordTrace tailWord_2006730 prefixEnd_2006730 343472344599012964448741 := by
  unfold tailWord_2006730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297864004991851760900411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48794304013311604695734429 18297864004991851760900411)
  ·
    refine ⟨27446796007487777641350617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18297864004991851760900411 27446796007487777641350617)
    ·
      refine ⟨20585097005615833231012963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27446796007487777641350617 20585097005615833231012963)
      ·
        refine ⟨30877645508423749846519445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20585097005615833231012963 30877645508423749846519445)
        ·
          refine ⟨1447389633207363274055599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30877645508423749846519445 1447389633207363274055599)
          ·
            refine ⟨2171084449811044911083399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447389633207363274055599 2171084449811044911083399)
            ·
              refine ⟨3256626674716567366625099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171084449811044911083399 3256626674716567366625099)
              ·
                refine ⟨4884940012074851049937649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256626674716567366625099 4884940012074851049937649)
                ·
                  refine ⟨3663705009056138287453237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884940012074851049937649 3663705009056138287453237)
                  ·
                    refine ⟨343472344599012964448741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3663705009056138287453237 343472344599012964448741)
                    ·
                      rfl

theorem cell23_2006730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_2006730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006730 prefixEnd_2006730 := by exact prefixLift 2006730
  have htrace : WordTrace (prefixWord ++ tailWord_2006730) baseStart_2006730 baseEnd_2006730 := by
    simpa [prefixWord, tailWord_2006730, baseEnd_2006730] using wordTrace_append hprefix tailTrace_2006730
  have hstable : (prefixWord ++ tailWord_2006730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006730).length < 2 ^ (prefixWord ++ tailWord_2006730).sum := by decide
  have hdescent : baseEnd_2006730 < baseStart_2006730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006736 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_2006736 : Nat := 118140960795 + 2006736 * 2 ^ 59
def prefixEnd_2006736 : Nat := 4983230072969 + 3 ^ 40 * 2006736 * 2
def baseEnd_2006736 : Nat := 1030420114680965869871195

theorem tailTrace_2006736 : CollatzResearch.WordTrace tailWord_2006736 prefixEnd_2006736 1030420114680965869871195 := by
  unfold tailWord_2006736
  simp only [CollatzResearch.WordTrace]
  refine ⟨36595837428972835034160031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48794449905297113378880041 36595837428972835034160031)
  ·
    refine ⟨54893756143459252551240047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36595837428972835034160031 54893756143459252551240047)
    ·
      refine ⟨82340634215188878826860071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54893756143459252551240047 82340634215188878826860071)
      ·
        refine ⟨123510951322783318240290107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82340634215188878826860071 123510951322783318240290107)
        ·
          refine ⟨185266426984174977360435161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123510951322783318240290107 185266426984174977360435161)
          ·
            refine ⟨138949820238131233020326371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185266426984174977360435161 138949820238131233020326371)
            ·
              refine ⟨208424730357196849530489557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138949820238131233020326371 208424730357196849530489557)
              ·
                refine ⟨4884954617746801160870849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208424730357196849530489557 4884954617746801160870849)
                ·
                  refine ⟨3663715963310100870653137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4884954617746801160870849 3663715963310100870653137)
                  ·
                    refine ⟨2747786972482575652989853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3663715963310100870653137 2747786972482575652989853)
                    ·
                      refine ⟨1030420114680965869871195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747786972482575652989853 1030420114680965869871195)
                      ·
                        rfl

theorem cell23_2006736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_2006736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006736 prefixEnd_2006736 := by exact prefixLift 2006736
  have htrace : WordTrace (prefixWord ++ tailWord_2006736) baseStart_2006736 baseEnd_2006736 := by
    simpa [prefixWord, tailWord_2006736, baseEnd_2006736] using wordTrace_append hprefix tailTrace_2006736
  have hstable : (prefixWord ++ tailWord_2006736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006736).length < 2 ^ (prefixWord ++ tailWord_2006736).sum := by decide
  have hdescent : baseEnd_2006736 < baseStart_2006736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006760 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 1, 4]
def baseStart_2006760 : Nat := 118140960795 + 2006760 * 2 ^ 59
def prefixEnd_2006760 : Nat := 4983230072969 + 3 ^ 40 * 2006760 * 2
def baseEnd_2006760 : Nat := 343477479405557925323695

theorem tailTrace_2006760 : CollatzResearch.WordTrace tailWord_2006760 prefixEnd_2006760 343477479405557925323695 := by
  unfold tailWord_2006760
  simp only [CollatzResearch.WordTrace]
  refine ⟨36596275104929361083596867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48795033473239148111462489 36596275104929361083596867)
  ·
    refine ⟨54894412657394041625395301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36596275104929361083596867 54894412657394041625395301)
    ·
      refine ⟨10292702373261382804761619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54894412657394041625395301 10292702373261382804761619)
      ·
        refine ⟨15439053559892074207142429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292702373261382804761619 15439053559892074207142429)
        ·
          refine ⟨5789645084959527827678411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15439053559892074207142429 5789645084959527827678411)
          ·
            refine ⟨8684467627439291741517617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789645084959527827678411 8684467627439291741517617)
            ·
              refine ⟨6513350720579468806138213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8684467627439291741517617 6513350720579468806138213)
              ·
                refine ⟨1221253260108650401150915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6513350720579468806138213 1221253260108650401150915)
                ·
                  refine ⟨1831879890162975601726373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221253260108650401150915 1831879890162975601726373)
                  ·
                    refine ⟨343477479405557925323695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831879890162975601726373 343477479405557925323695)
                    ·
                      rfl

theorem cell23_2006760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_2006760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006760 prefixEnd_2006760 := by exact prefixLift 2006760
  have htrace : WordTrace (prefixWord ++ tailWord_2006760) baseStart_2006760 baseEnd_2006760 := by
    simpa [prefixWord, tailWord_2006760, baseEnd_2006760] using wordTrace_append hprefix tailTrace_2006760
  have hstable : (prefixWord ++ tailWord_2006760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006760).length < 2 ^ (prefixWord ++ tailWord_2006760).sum := by decide
  have hdescent : baseEnd_2006760 < baseStart_2006760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006783 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 3]
def baseStart_2006783 : Nat := 118140960795 + 2006783 * 2 ^ 59
def prefixEnd_2006783 : Nat := 4983230072969 + 3 ^ 40 * 2006783 * 2
def baseEnd_2006783 : Nat := 1030444248271727185983479

theorem tailTrace_2006783 : CollatzResearch.WordTrace tailWord_2006783 prefixEnd_2006783 1030444248271727185983479 := by
  unfold tailWord_2006783
  simp only [CollatzResearch.WordTrace]
  refine ⟨73193389088775397095281003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48795592725850264730187335 73193389088775397095281003)
  ·
    refine ⟨109790083633163095642921505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73193389088775397095281003 109790083633163095642921505)
    ·
      refine ⟨82342562724872321732191129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109790083633163095642921505 82342562724872321732191129)
      ·
        refine ⟨61756922043654241299143347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82342562724872321732191129 61756922043654241299143347)
        ·
          refine ⟨92635383065481361948715021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61756922043654241299143347 92635383065481361948715021)
          ·
            refine ⟨34738268649555510730768133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92635383065481361948715021 34738268649555510730768133)
            ·
              refine ⟨6513425371791658262019025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34738268649555510730768133 6513425371791658262019025)
              ·
                refine ⟨4885069028843743696514269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513425371791658262019025 4885069028843743696514269)
                ·
                  refine ⟨1831900885816403886192851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4885069028843743696514269 1831900885816403886192851)
                  ·
                    refine ⟨2747851328724605829289277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831900885816403886192851 2747851328724605829289277)
                    ·
                      refine ⟨1030444248271727185983479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747851328724605829289277 1030444248271727185983479)
                      ·
                        rfl

theorem cell23_2006783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_2006783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006783 prefixEnd_2006783 := by exact prefixLift 2006783
  have htrace : WordTrace (prefixWord ++ tailWord_2006783) baseStart_2006783 baseEnd_2006783 := by
    simpa [prefixWord, tailWord_2006783, baseEnd_2006783] using wordTrace_append hprefix tailTrace_2006783
  have hstable : (prefixWord ++ tailWord_2006783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006783).length < 2 ^ (prefixWord ++ tailWord_2006783).sum := by decide
  have hdescent : baseEnd_2006783 < baseStart_2006783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006793 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 2, 3, 2]
def baseStart_2006793 : Nat := 118140960795 + 2006793 * 2 ^ 59
def prefixEnd_2006793 : Nat := 4983230072969 + 3 ^ 40 * 2006793 * 2
def baseEnd_2006793 : Nat := 1030449383078272146858433

theorem tailTrace_2006793 : CollatzResearch.WordTrace tailWord_2006793 prefixEnd_2006793 1030449383078272146858433 := by
  unfold tailWord_2006793
  simp only [CollatzResearch.WordTrace]
  refine ⟨73193753818739168803145033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48795835879159445868763355 73193753818739168803145033)
  ·
    refine ⟨54895315364054376602358775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73193753818739168803145033 54895315364054376602358775)
    ·
      refine ⟨82342973046081564903538163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54895315364054376602358775 82342973046081564903538163)
      ·
        refine ⟨123514459569122347355307245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82342973046081564903538163 123514459569122347355307245)
        ·
          refine ⟨46317922338420880258240217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123514459569122347355307245 46317922338420880258240217)
          ·
            refine ⟨34738441753815660193680163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46317922338420880258240217 34738441753815660193680163)
            ·
              refine ⟨52107662630723490290520245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34738441753815660193680163 52107662630723490290520245)
              ·
                refine ⟨4885093371630327214736273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52107662630723490290520245 4885093371630327214736273)
                ·
                  refine ⟨3663820028722745411052205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885093371630327214736273 3663820028722745411052205)
                  ·
                    refine ⟨1373932510771029529144577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663820028722745411052205 1373932510771029529144577)
                    ·
                      refine ⟨1030449383078272146858433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373932510771029529144577 1030449383078272146858433)
                      ·
                        rfl

theorem cell23_2006793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3, 2].length) (baseStart_2006793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006793 prefixEnd_2006793 := by exact prefixLift 2006793
  have htrace : WordTrace (prefixWord ++ tailWord_2006793) baseStart_2006793 baseEnd_2006793 := by
    simpa [prefixWord, tailWord_2006793, baseEnd_2006793] using wordTrace_append hprefix tailTrace_2006793
  have hstable : (prefixWord ++ tailWord_2006793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006793).length < 2 ^ (prefixWord ++ tailWord_2006793).sum := by decide
  have hdescent : baseEnd_2006793 < baseStart_2006793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006804 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2006804 : Nat := 118140960795 + 2006804 * 2 ^ 59
def prefixEnd_2006804 : Nat := 4983230072969 + 3 ^ 40 * 2006804 * 2
def baseEnd_2006804 : Nat := 1030455031365471603820883

theorem tailTrace_2006804 : CollatzResearch.WordTrace tailWord_2006804 prefixEnd_2006804 1030455031365471603820883 := by
  unfold tailWord_2006804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36597077510849658840897733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48796103347799545121196977 36597077510849658840897733)
  ·
    refine ⟨6861952033284311032668325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36597077510849658840897733 6861952033284311032668325)
    ·
      refine ⟨1286616006240808318625311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6861952033284311032668325 1286616006240808318625311)
      ·
        refine ⟨1929924009361212477937967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286616006240808318625311 1929924009361212477937967)
        ·
          refine ⟨2894886014041818716906951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929924009361212477937967 2894886014041818716906951)
          ·
            refine ⟨4342329021062728075360427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894886014041818716906951 4342329021062728075360427)
            ·
              refine ⟨6513493531594092113040641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342329021062728075360427 6513493531594092113040641)
              ·
                refine ⟨4885120148695569084780481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513493531594092113040641 4885120148695569084780481)
                ·
                  refine ⟨3663840111521676813585361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885120148695569084780481 3663840111521676813585361)
                  ·
                    refine ⟨2747880083641257610189021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3663840111521676813585361 2747880083641257610189021)
                    ·
                      refine ⟨1030455031365471603820883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2747880083641257610189021 1030455031365471603820883)
                      ·
                        rfl

theorem cell23_2006804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2006804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006804 prefixEnd_2006804 := by exact prefixLift 2006804
  have htrace : WordTrace (prefixWord ++ tailWord_2006804) baseStart_2006804 baseEnd_2006804 := by
    simpa [prefixWord, tailWord_2006804, baseEnd_2006804] using wordTrace_append hprefix tailTrace_2006804
  have hstable : (prefixWord ++ tailWord_2006804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006804).length < 2 ^ (prefixWord ++ tailWord_2006804).sum := by decide
  have hdescent : baseEnd_2006804 < baseStart_2006804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006810 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_2006810 : Nat := 118140960795 + 2006810 * 2 ^ 59
def prefixEnd_2006810 : Nat := 4983230072969 + 3 ^ 40 * 2006810 * 2
def baseEnd_2006810 : Nat := 1030458112249398580345855

theorem tailTrace_2006810 : CollatzResearch.WordTrace tailWord_2006810 prefixEnd_2006810 1030458112249398580345855 := by
  unfold tailWord_2006810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18298593464919395176628471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48796249239785053804342589 18298593464919395176628471)
  ·
    refine ⟨27447890197379092764942707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18298593464919395176628471 27447890197379092764942707)
    ·
      refine ⟨41171835296068639147414061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27447890197379092764942707 41171835296068639147414061)
      ·
        refine ⟨15439438236025739680280273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41171835296068639147414061 15439438236025739680280273)
        ·
          refine ⟨11579578677019304760210205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15439438236025739680280273 11579578677019304760210205)
          ·
            refine ⟨4342342003882239285078827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11579578677019304760210205 4342342003882239285078827)
            ·
              refine ⟨6513513005823358927618241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342342003882239285078827 6513513005823358927618241)
              ·
                refine ⟨4885134754367519195713681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6513513005823358927618241 4885134754367519195713681)
                ·
                  refine ⟨3663851065775639396785261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4885134754367519195713681 3663851065775639396785261)
                  ·
                    refine ⟨1373944149665864773794473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663851065775639396785261 1373944149665864773794473)
                    ·
                      refine ⟨1030458112249398580345855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373944149665864773794473 1030458112249398580345855)
                      ·
                        rfl

theorem cell23_2006810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_2006810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006810 prefixEnd_2006810 := by exact prefixLift 2006810
  have htrace : WordTrace (prefixWord ++ tailWord_2006810) baseStart_2006810 baseEnd_2006810 := by
    simpa [prefixWord, tailWord_2006810, baseEnd_2006810] using wordTrace_append hprefix tailTrace_2006810
  have hstable : (prefixWord ++ tailWord_2006810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006810).length < 2 ^ (prefixWord ++ tailWord_2006810).sum := by decide
  have hdescent : baseEnd_2006810 < baseStart_2006810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006837 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2006837 : Nat := 118140960795 + 2006837 * 2 ^ 59
def prefixEnd_2006837 : Nat := 4983230072969 + 3 ^ 40 * 2006837 * 2
def baseEnd_2006837 : Nat := 343490658742356658236077

theorem tailTrace_2006837 : CollatzResearch.WordTrace tailWord_2006837 prefixEnd_2006837 343490658742356658236077 := by
  unfold tailWord_2006837
  simp only [CollatzResearch.WordTrace]
  refine ⟨73195358630579764317746765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48796905753719842878497843 73195358630579764317746765)
  ·
    refine ⟨27448259486467411619155037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73195358630579764317746765 27448259486467411619155037)
    ·
      refine ⟨10293097307425279357183139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27448259486467411619155037 10293097307425279357183139)
      ·
        refine ⟨15439645961137919035774709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10293097307425279357183139 15439645961137919035774709)
        ·
          refine ⟨1447466808856679909603879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15439645961137919035774709 1447466808856679909603879)
          ·
            refine ⟨2171200213285019864405819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447466808856679909603879 2171200213285019864405819)
            ·
              refine ⟨3256800319927529796608729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171200213285019864405819 3256800319927529796608729)
              ·
                refine ⟨2442600239945647347456547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256800319927529796608729 2442600239945647347456547)
                ·
                  refine ⟨3663900359918471021184821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442600239945647347456547 3663900359918471021184821)
                  ·
                    refine ⟨343490658742356658236077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3663900359918471021184821 343490658742356658236077)
                    ·
                      rfl

theorem cell23_2006837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2006837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006837 prefixEnd_2006837 := by exact prefixLift 2006837
  have htrace : WordTrace (prefixWord ++ tailWord_2006837) baseStart_2006837 baseEnd_2006837 := by
    simpa [prefixWord, tailWord_2006837, baseEnd_2006837] using wordTrace_append hprefix tailTrace_2006837
  have hstable : (prefixWord ++ tailWord_2006837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006837).length < 2 ^ (prefixWord ++ tailWord_2006837).sum := by decide
  have hdescent : baseEnd_2006837 < baseStart_2006837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006840 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_2006840 : Nat := 118140960795 + 2006840 * 2 ^ 59
def prefixEnd_2006840 : Nat := 4983230072969 + 3 ^ 40 * 2006840 * 2
def baseEnd_2006840 : Nat := 1030473516669033462970717

theorem tailTrace_2006840 : CollatzResearch.WordTrace tailWord_2006840 prefixEnd_2006840 1030473516669033462970717 := by
  unfold tailWord_2006840
  simp only [CollatzResearch.WordTrace]
  refine ⟨36597734024784447915052987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48796978699712597220070649 36597734024784447915052987)
  ·
    refine ⟨54896601037176671872579481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36597734024784447915052987 54896601037176671872579481)
    ·
      refine ⟨41172450777882503904434611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54896601037176671872579481 41172450777882503904434611)
      ·
        refine ⟨61758676166823755856651917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41172450777882503904434611 61758676166823755856651917)
        ·
          refine ⟨23159503562558908446244469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61758676166823755856651917 23159503562558908446244469)
          ·
            refine ⟨2171203458989897666835419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23159503562558908446244469 2171203458989897666835419)
            ·
              refine ⟨3256805188484846500253129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171203458989897666835419 3256805188484846500253129)
              ·
                refine ⟨2442603891363634875189847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256805188484846500253129 2442603891363634875189847)
                ·
                  refine ⟨3663905837045452312784771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442603891363634875189847 3663905837045452312784771)
                  ·
                    refine ⟨5495858755568178469177157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3663905837045452312784771 5495858755568178469177157)
                    ·
                      refine ⟨1030473516669033462970717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5495858755568178469177157 1030473516669033462970717)
                      ·
                        rfl

theorem cell23_2006840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_2006840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006840 prefixEnd_2006840 := by exact prefixLift 2006840
  have htrace : WordTrace (prefixWord ++ tailWord_2006840) baseStart_2006840 baseEnd_2006840 := by
    simpa [prefixWord, tailWord_2006840, baseEnd_2006840] using wordTrace_append hprefix tailTrace_2006840
  have hstable : (prefixWord ++ tailWord_2006840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006840).length < 2 ^ (prefixWord ++ tailWord_2006840).sum := by decide
  have hdescent : baseEnd_2006840 < baseStart_2006840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006854 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2006854 : Nat := 118140960795 + 2006854 * 2 ^ 59
def prefixEnd_2006854 : Nat := 4983230072969 + 3 ^ 40 * 2006854 * 2
def baseEnd_2006854 : Nat := 343493568466065469398551

theorem tailTrace_2006854 : CollatzResearch.WordTrace tailWord_2006854 prefixEnd_2006854 343493568466065469398551 := by
  unfold tailWord_2006854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287374333484943006909863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48797319114345450814077077 2287374333484943006909863)
  ·
    refine ⟨3431061500227414510364795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287374333484943006909863 3431061500227414510364795)
    ·
      refine ⟨5146592250341121765547193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431061500227414510364795 5146592250341121765547193)
      ·
        refine ⟨3859944187755841324160395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5146592250341121765547193 3859944187755841324160395)
        ·
          refine ⟨5789916281633761986240593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859944187755841324160395 5789916281633761986240593)
          ·
            refine ⟨4342437211225321489680445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5789916281633761986240593 4342437211225321489680445)
            ·
              refine ⟨1628413954209495558630167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4342437211225321489680445 1628413954209495558630167)
              ·
                refine ⟨2442620931314243337945251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628413954209495558630167 2442620931314243337945251)
                ·
                  refine ⟨3663931396971365006917877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442620931314243337945251 3663931396971365006917877)
                  ·
                    refine ⟨343493568466065469398551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3663931396971365006917877 343493568466065469398551)
                    ·
                      rfl

theorem cell23_2006854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2006854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006854 prefixEnd_2006854 := by exact prefixLift 2006854
  have htrace : WordTrace (prefixWord ++ tailWord_2006854) baseStart_2006854 baseEnd_2006854 := by
    simpa [prefixWord, tailWord_2006854, baseEnd_2006854] using wordTrace_append hprefix tailTrace_2006854
  have hstable : (prefixWord ++ tailWord_2006854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006854).length < 2 ^ (prefixWord ++ tailWord_2006854).sum := by decide
  have hdescent : baseEnd_2006854 < baseStart_2006854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006857 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 1, 2, 2]
def baseStart_2006857 : Nat := 118140960795 + 2006857 * 2 ^ 59
def prefixEnd_2006857 : Nat := 4983230072969 + 3 ^ 40 * 2006857 * 2
def baseEnd_2006857 : Nat := 1030482245840159896458139

theorem tailTrace_2006857 : CollatzResearch.WordTrace tailWord_2006857 prefixEnd_2006857 1030482245840159896458139 := by
  unfold tailWord_2006857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73196088090507307733474825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48797392060338205155649883 73196088090507307733474825)
  ·
    refine ⟨54897066067880480800106119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73196088090507307733474825 54897066067880480800106119)
    ·
      refine ⟨82345599101820721200159179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54897066067880480800106119 82345599101820721200159179)
      ·
        refine ⟨123518398652731081800238769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82345599101820721200159179 123518398652731081800238769)
        ·
          refine ⟨92638798989548311350179077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123518398652731081800238769 92638798989548311350179077)
          ·
            refine ⟨17369774810540308378158577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92638798989548311350179077 17369774810540308378158577)
            ·
              refine ⟨13027331107905231283618933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17369774810540308378158577 13027331107905231283618933)
              ·
                refine ⟨1221312291366115432839275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13027331107905231283618933 1221312291366115432839275)
                ·
                  refine ⟨1831968437049173149258913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221312291366115432839275 1831968437049173149258913)
                  ·
                    refine ⟨1373976327786879861944185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1831968437049173149258913 1373976327786879861944185)
                    ·
                      refine ⟨1030482245840159896458139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1373976327786879861944185 1030482245840159896458139)
                      ·
                        rfl

theorem cell23_2006857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 2, 2].length) (baseStart_2006857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006857 prefixEnd_2006857 := by exact prefixLift 2006857
  have htrace : WordTrace (prefixWord ++ tailWord_2006857) baseStart_2006857 baseEnd_2006857 := by
    simpa [prefixWord, tailWord_2006857, baseEnd_2006857] using wordTrace_append hprefix tailTrace_2006857
  have hstable : (prefixWord ++ tailWord_2006857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006857).length < 2 ^ (prefixWord ++ tailWord_2006857).sum := by decide
  have hdescent : baseEnd_2006857 < baseStart_2006857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006860 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2006860 : Nat := 118140960795 + 2006860 * 2 ^ 59
def prefixEnd_2006860 : Nat := 4983230072969 + 3 ^ 40 * 2006860 * 2
def baseEnd_2006860 : Nat := 1030483786282123384720625

theorem tailTrace_2006860 : CollatzResearch.WordTrace tailWord_2006860 prefixEnd_2006860 1030483786282123384720625 := by
  unfold tailWord_2006860
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598098754748219622917017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48797465006330959497222689 36598098754748219622917017)
  ·
    refine ⟨27448574066061164717187763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36598098754748219622917017 27448574066061164717187763)
    ·
      refine ⟨41172861099091747075781645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27448574066061164717187763 41172861099091747075781645)
      ·
        refine ⟨15439822912159405153418117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41172861099091747075781645 15439822912159405153418117)
        ·
          refine ⟨2894966796029888466265897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15439822912159405153418117 2894966796029888466265897)
          ·
            refine ⟨2171225097022416349699423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894966796029888466265897 2171225097022416349699423)
            ·
              refine ⟨3256837645533624524549135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171225097022416349699423 3256837645533624524549135)
              ·
                refine ⟨4885256468300436786823703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256837645533624524549135 4885256468300436786823703)
                ·
                  refine ⟨7327884702450655180235555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885256468300436786823703 7327884702450655180235555)
                  ·
                    refine ⟨10991827053675982770353333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7327884702450655180235555 10991827053675982770353333)
                    ·
                      refine ⟨1030483786282123384720625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10991827053675982770353333 1030483786282123384720625)
                      ·
                        rfl

theorem cell23_2006860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2006860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006860 prefixEnd_2006860 := by exact prefixLift 2006860
  have htrace : WordTrace (prefixWord ++ tailWord_2006860) baseStart_2006860 baseEnd_2006860 := by
    simpa [prefixWord, tailWord_2006860, baseEnd_2006860] using wordTrace_append hprefix tailTrace_2006860
  have hstable : (prefixWord ++ tailWord_2006860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006860).length < 2 ^ (prefixWord ++ tailWord_2006860).sum := by decide
  have hdescent : baseEnd_2006860 < baseStart_2006860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006896 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_2006896 : Nat := 118140960795 + 2006896 * 2 ^ 59
def prefixEnd_2006896 : Nat := 4983230072969 + 3 ^ 40 * 2006896 * 2
def baseEnd_2006896 : Nat := 1030502271585685243870459

theorem tailTrace_2006896 : CollatzResearch.WordTrace tailWord_2006896 prefixEnd_2006896 1030502271585685243870459 := by
  unfold tailWord_2006896
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598755268683008697072271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48798340358244011596096361 36598755268683008697072271)
  ·
    refine ⟨54898132903024513045608407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36598755268683008697072271 54898132903024513045608407)
    ·
      refine ⟨82347199354536769568412611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54898132903024513045608407 82347199354536769568412611)
      ·
        refine ⟨123520799031805154352618917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82347199354536769568412611 123520799031805154352618917)
        ·
          refine ⟨23160149818463466441116047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123520799031805154352618917 23160149818463466441116047)
          ·
            refine ⟨34740224727695199661674071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23160149818463466441116047 34740224727695199661674071)
            ·
              refine ⟨52110337091542799492511107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34740224727695199661674071 52110337091542799492511107)
              ·
                refine ⟨78165505637314199238766661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52110337091542799492511107 78165505637314199238766661)
                ·
                  refine ⟨14656032306996412357268749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78165505637314199238766661 14656032306996412357268749)
                  ·
                    refine ⟨5496012115123654633975781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14656032306996412357268749 5496012115123654633975781)
                    ·
                      refine ⟨1030502271585685243870459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5496012115123654633975781 1030502271585685243870459)
                      ·
                        rfl

theorem cell23_2006896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_2006896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006896 prefixEnd_2006896 := by exact prefixLift 2006896
  have htrace : WordTrace (prefixWord ++ tailWord_2006896) baseStart_2006896 baseEnd_2006896 := by
    simpa [prefixWord, tailWord_2006896, baseEnd_2006896] using wordTrace_append hprefix tailTrace_2006896
  have hstable : (prefixWord ++ tailWord_2006896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006896).length < 2 ^ (prefixWord ++ tailWord_2006896).sum := by decide
  have hdescent : baseEnd_2006896 < baseStart_2006896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2006990 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_2006990 : Nat := 118140960795 + 2006990 * 2 ^ 59
def prefixEnd_2006990 : Nat := 4983230072969 + 3 ^ 40 * 2006990 * 2
def baseEnd_2006990 : Nat := 1030550538767207876095027

theorem tailTrace_2006990 : CollatzResearch.WordTrace tailWord_2006990 prefixEnd_2006990 1030550538767207876095027 := by
  unfold tailWord_2006990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9150117374878183931008303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48800625999350314298710949 9150117374878183931008303)
  ·
    refine ⟨13725176062317275896512455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9150117374878183931008303 13725176062317275896512455)
    ·
      refine ⟨20587764093475913844768683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13725176062317275896512455 20587764093475913844768683)
      ·
        refine ⟨30881646140213870767153025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20587764093475913844768683 30881646140213870767153025)
        ·
          refine ⟨23161234605160403075364769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30881646140213870767153025 23161234605160403075364769)
          ·
            refine ⟨17370925953870302306523577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23161234605160403075364769 17370925953870302306523577)
            ·
              refine ⟨13028194465402726729892683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17370925953870302306523577 13028194465402726729892683)
              ·
                refine ⟨19542291698104090094839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13028194465402726729892683 19542291698104090094839025)
                ·
                  refine ⟨14656718773578067571129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19542291698104090094839025 14656718773578067571129269)
                  ·
                    refine ⟨1374067385022943834793369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14656718773578067571129269 1374067385022943834793369)
                    ·
                      refine ⟨1030550538767207876095027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374067385022943834793369 1030550538767207876095027)
                      ·
                        rfl

theorem cell23_2006990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_2006990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2006990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2006990 prefixEnd_2006990 := by exact prefixLift 2006990
  have htrace : WordTrace (prefixWord ++ tailWord_2006990) baseStart_2006990 baseEnd_2006990 := by
    simpa [prefixWord, tailWord_2006990, baseEnd_2006990] using wordTrace_append hprefix tailTrace_2006990
  have hstable : (prefixWord ++ tailWord_2006990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2006990).length < 2 ^ (prefixWord ++ tailWord_2006990).sum := by decide
  have hdescent : baseEnd_2006990 < baseStart_2006990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2006990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007103 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 3, 6]
def baseStart_2007103 : Nat := 118140960795 + 2007103 * 2 ^ 59
def prefixEnd_2007103 : Nat := 4983230072969 + 3 ^ 40 * 2007103 * 2
def baseEnd_2007103 : Nat := 343536187360388644660669

theorem tailTrace_2007103 : CollatzResearch.WordTrace tailWord_2007103 prefixEnd_2007103 343536187360388644660669 := by
  unfold tailWord_2007103
  simp only [CollatzResearch.WordTrace]
  refine ⟨73205060447616091746929963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48803373631744061164619975 73205060447616091746929963)
  ·
    refine ⟨109807590671424137620394945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73205060447616091746929963 109807590671424137620394945)
    ·
      refine ⟨82355693003568103215296209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109807590671424137620394945 82355693003568103215296209)
      ·
        refine ⟨61766769752676077411472157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82355693003568103215296209 61766769752676077411472157)
        ·
          refine ⟨23162538657253529029302059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61766769752676077411472157 23162538657253529029302059)
          ·
            refine ⟨34743807985880293543953089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162538657253529029302059 34743807985880293543953089)
            ·
              refine ⟨26057855989410220157964817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34743807985880293543953089 26057855989410220157964817)
              ·
                refine ⟨19543391992057665118473613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26057855989410220157964817 19543391992057665118473613)
                ·
                  refine ⟨7328771997021624419427605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19543391992057665118473613 7328771997021624419427605)
                  ·
                    refine ⟨343536187360388644660669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7328771997021624419427605 343536187360388644660669)
                    ·
                      rfl

theorem cell23_2007103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_2007103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007103 prefixEnd_2007103 := by exact prefixLift 2007103
  have htrace : WordTrace (prefixWord ++ tailWord_2007103) baseStart_2007103 baseEnd_2007103 := by
    simpa [prefixWord, tailWord_2007103, baseEnd_2007103] using wordTrace_append hprefix tailTrace_2007103
  have hstable : (prefixWord ++ tailWord_2007103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007103).length < 2 ^ (prefixWord ++ tailWord_2007103).sum := by decide
  have hdescent : baseEnd_2007103 < baseStart_2007103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007104 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 1, 1, 3]
def baseStart_2007104 : Nat := 118140960795 + 2007104 * 2 ^ 59
def prefixEnd_2007104 : Nat := 4983230072969 + 3 ^ 40 * 2007104 * 2
def baseEnd_2007104 : Nat := 1030609075561820430069503

theorem tailTrace_2007104 : CollatzResearch.WordTrace tailWord_2007104 prefixEnd_2007104 1030609075561820430069503 := by
  unfold tailWord_2007104
  simp only [CollatzResearch.WordTrace]
  refine ⟨36602548460306234458858183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48803397947074979278477577 36602548460306234458858183)
  ·
    refine ⟨54903822690459351688287275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36602548460306234458858183 54903822690459351688287275)
    ·
      refine ⟨82355734035689027532430913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54903822690459351688287275 82355734035689027532430913)
      ·
        refine ⟨61766800526766770649323185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82355734035689027532430913 61766800526766770649323185)
        ·
          refine ⟨46325100395075077986992389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61766800526766770649323185 46325100395075077986992389)
          ·
            refine ⟨8685956324076577122561073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46325100395075077986992389 8685956324076577122561073)
            ·
              refine ⟨6514467243057432841920805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685956324076577122561073 6514467243057432841920805)
              ·
                refine ⟨1221462608073268657860151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6514467243057432841920805 1221462608073268657860151)
                ·
                  refine ⟨1832193912109902986790227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221462608073268657860151 1832193912109902986790227)
                  ·
                    refine ⟨2748290868164854480185341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832193912109902986790227 2748290868164854480185341)
                    ·
                      refine ⟨1030609075561820430069503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748290868164854480185341 1030609075561820430069503)
                      ·
                        rfl

theorem cell23_2007104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_2007104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007104 prefixEnd_2007104 := by exact prefixLift 2007104
  have htrace : WordTrace (prefixWord ++ tailWord_2007104) baseStart_2007104 baseEnd_2007104 := by
    simpa [prefixWord, tailWord_2007104, baseEnd_2007104] using wordTrace_append hprefix tailTrace_2007104
  have hstable : (prefixWord ++ tailWord_2007104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007104).length < 2 ^ (prefixWord ++ tailWord_2007104).sum := by decide
  have hdescent : baseEnd_2007104 < baseStart_2007104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007140 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_2007140 : Nat := 118140960795 + 2007140 * 2 ^ 59
def prefixEnd_2007140 : Nat := 4983230072969 + 3 ^ 40 * 2007140 * 2
def baseEnd_2007140 : Nat := 1030627560865382289219337

theorem tailTrace_2007140 : CollatzResearch.WordTrace tailWord_2007140 prefixEnd_2007140 1030627560865382289219337 := by
  unfold tailWord_2007140
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603204974241023533013437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48804273298988031377351249 36603204974241023533013437)
  ·
    refine ⟨13726201865340383824880039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36603204974241023533013437 13726201865340383824880039)
    ·
      refine ⟨20589302798010575737320059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13726201865340383824880039 20589302798010575737320059)
      ·
        refine ⟨30883954197015863605980089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20589302798010575737320059 30883954197015863605980089)
        ·
          refine ⟨23162965647761897704485067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30883954197015863605980089 23162965647761897704485067)
          ·
            refine ⟨34744448471642846556727601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162965647761897704485067 34744448471642846556727601)
            ·
              refine ⟨26058336353732134917545701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34744448471642846556727601 26058336353732134917545701)
              ·
                refine ⟨4885938066324775297039819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26058336353732134917545701 4885938066324775297039819)
                ·
                  refine ⟨7328907099487162945559729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4885938066324775297039819 7328907099487162945559729)
                  ·
                    refine ⟨5496680324615372209169797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7328907099487162945559729 5496680324615372209169797)
                    ·
                      refine ⟨1030627560865382289219337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5496680324615372209169797 1030627560865382289219337)
                      ·
                        rfl

theorem cell23_2007140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_2007140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007140 prefixEnd_2007140 := by exact prefixLift 2007140
  have htrace : WordTrace (prefixWord ++ tailWord_2007140) baseStart_2007140 baseEnd_2007140 := by
    simpa [prefixWord, tailWord_2007140, baseEnd_2007140] using wordTrace_append hprefix tailTrace_2007140
  have hstable : (prefixWord ++ tailWord_2007140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007140).length < 2 ^ (prefixWord ++ tailWord_2007140).sum := by decide
  have hdescent : baseEnd_2007140 < baseStart_2007140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007161 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 3, 2, 2]
def baseStart_2007161 : Nat := 118140960795 + 2007161 * 2 ^ 59
def prefixEnd_2007161 : Nat := 4983230072969 + 3 ^ 40 * 2007161 * 2
def baseEnd_2007161 : Nat := 1030638343959126707056741

theorem tailTrace_2007161 : CollatzResearch.WordTrace tailWord_2007161 prefixEnd_2007161 1030638343959126707056741 := by
  unfold tailWord_2007161
  simp only [CollatzResearch.WordTrace]
  refine ⟨73207175881405967652541337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48804783920937311768360891 73207175881405967652541337)
  ·
    refine ⟨54905381911054475739406003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73207175881405967652541337 54905381911054475739406003)
    ·
      refine ⟨82358072866581713609109005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54905381911054475739406003 82358072866581713609109005)
      ·
        refine ⟨30884277324968142603415877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82358072866581713609109005 30884277324968142603415877)
        ·
          refine ⟨5790801998431526738140477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30884277324968142603415877 5790801998431526738140477)
          ·
            refine ⟨2171550749411822526802679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5790801998431526738140477 2171550749411822526802679)
            ·
              refine ⟨3257326124117733790204019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171550749411822526802679 3257326124117733790204019)
              ·
                refine ⟨4885989186176600685306029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257326124117733790204019 4885989186176600685306029)
                ·
                  refine ⟨1832245944816225256989761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4885989186176600685306029 1832245944816225256989761)
                  ·
                    refine ⟨1374184458612168942742321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832245944816225256989761 1374184458612168942742321)
                    ·
                      refine ⟨1030638343959126707056741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374184458612168942742321 1030638343959126707056741)
                      ·
                        rfl

theorem cell23_2007161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_2007161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007161 prefixEnd_2007161 := by exact prefixLift 2007161
  have htrace : WordTrace (prefixWord ++ tailWord_2007161) baseStart_2007161 baseEnd_2007161 := by
    simpa [prefixWord, tailWord_2007161, baseEnd_2007161] using wordTrace_append hprefix tailTrace_2007161
  have hstable : (prefixWord ++ tailWord_2007161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007161).length < 2 ^ (prefixWord ++ tailWord_2007161).sum := by decide
  have hdescent : baseEnd_2007161 < baseStart_2007161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007194 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2007194 : Nat := 118140960795 + 2007194 * 2 ^ 59
def prefixEnd_2007194 : Nat := 4983230072969 + 3 ^ 40 * 2007194 * 2
def baseEnd_2007194 : Nat := 1030655288820725077944089

theorem tailTrace_2007194 : CollatzResearch.WordTrace tailWord_2007194 prefixEnd_2007194 1030655288820725077944089 := by
  unfold tailWord_2007194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302094872571603572123159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48805586326857609525661757 18302094872571603572123159)
  ·
    refine ⟨27453142308857405358184739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18302094872571603572123159 27453142308857405358184739)
    ·
      refine ⟨41179713463286108037277109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27453142308857405358184739 41179713463286108037277109)
      ·
        refine ⟨3860598137183072628494729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41179713463286108037277109 3860598137183072628494729)
        ·
          refine ⟨2895448602887304471371047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860598137183072628494729 2895448602887304471371047)
          ·
            refine ⟨4343172904330956707056571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895448602887304471371047 4343172904330956707056571)
            ·
              refine ⟨6514759356496435060584857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343172904330956707056571 6514759356496435060584857)
              ·
                refine ⟨4886069517372326295438643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6514759356496435060584857 4886069517372326295438643)
                ·
                  refine ⟨7329104276058489443157965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886069517372326295438643 7329104276058489443157965)
                  ·
                    refine ⟨2748414103521933541184237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7329104276058489443157965 2748414103521933541184237)
                    ·
                      refine ⟨1030655288820725077944089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748414103521933541184237 1030655288820725077944089)
                      ·
                        rfl

theorem cell23_2007194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2007194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007194 prefixEnd_2007194 := by exact prefixLift 2007194
  have htrace : WordTrace (prefixWord ++ tailWord_2007194) baseStart_2007194 baseEnd_2007194 := by
    simpa [prefixWord, tailWord_2007194, baseEnd_2007194] using wordTrace_append hprefix tailTrace_2007194
  have hstable : (prefixWord ++ tailWord_2007194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007194).length < 2 ^ (prefixWord ++ tailWord_2007194).sum := by decide
  have hdescent : baseEnd_2007194 < baseStart_2007194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007198 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_2007198 : Nat := 118140960795 + 2007198 * 2 ^ 59
def prefixEnd_2007198 : Nat := 4983230072969 + 3 ^ 40 * 2007198 * 2
def baseEnd_2007198 : Nat := 1030657342743343062294071

theorem tailTrace_2007198 : CollatzResearch.WordTrace tailWord_2007198 prefixEnd_2007198 1030657342743343062294071 := by
  unfold tailWord_2007198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151065672783990371454781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48805683588181281981092165 9151065672783990371454781)
  ·
    refine ⟨3431649627293996389295543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9151065672783990371454781 3431649627293996389295543)
    ·
      refine ⟨5147474440940994583943315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431649627293996389295543 5147474440940994583943315)
      ·
        refine ⟨7721211661411491875914973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147474440940994583943315 7721211661411491875914973)
        ·
          refine ⟨2895454373029309453468115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7721211661411491875914973 2895454373029309453468115)
          ·
            refine ⟨4343181559543964180202173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895454373029309453468115 4343181559543964180202173)
            ·
              refine ⟨1628693084828986567575815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4343181559543964180202173 1628693084828986567575815)
              ·
                refine ⟨2443039627243479851363723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628693084828986567575815 2443039627243479851363723)
                ·
                  refine ⟨3664559440865219777045585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443039627243479851363723 3664559440865219777045585)
                  ·
                    refine ⟨2748419580648914832784189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3664559440865219777045585 2748419580648914832784189)
                    ·
                      refine ⟨1030657342743343062294071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748419580648914832784189 1030657342743343062294071)
                      ·
                        rfl

theorem cell23_2007198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_2007198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007198 prefixEnd_2007198 := by exact prefixLift 2007198
  have htrace : WordTrace (prefixWord ++ tailWord_2007198) baseStart_2007198 baseEnd_2007198 := by
    simpa [prefixWord, tailWord_2007198, baseEnd_2007198] using wordTrace_append hprefix tailTrace_2007198
  have hstable : (prefixWord ++ tailWord_2007198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007198).length < 2 ^ (prefixWord ++ tailWord_2007198).sum := by decide
  have hdescent : baseEnd_2007198 < baseStart_2007198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007257 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 5]
def baseStart_2007257 : Nat := 118140960795 + 2007257 * 2 ^ 59
def prefixEnd_2007257 : Nat := 4983230072969 + 3 ^ 40 * 2007257 * 2
def baseEnd_2007257 : Nat := 114520848677995370161811

theorem tailTrace_2007257 : CollatzResearch.WordTrace tailWord_2007257 prefixEnd_2007257 114520848677995370161811 := by
  unfold tailWord_2007257
  simp only [CollatzResearch.WordTrace]
  refine ⟨73210677289058176048036025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48807118192705450698690683 73210677289058176048036025)
  ·
    refine ⟨54908007966793632036027019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73210677289058176048036025 54908007966793632036027019)
    ·
      refine ⟨82362011950190448054040529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54908007966793632036027019 82362011950190448054040529)
      ·
        refine ⟨61771508962642836040530397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82362011950190448054040529 61771508962642836040530397)
        ·
          refine ⟨23164315860991063515198899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61771508962642836040530397 23164315860991063515198899)
          ·
            refine ⟨34746473791486595272798349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23164315860991063515198899 34746473791486595272798349)
            ·
              refine ⟨13029927671807473227299381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34746473791486595272798349 13029927671807473227299381)
              ·
                refine ⟨1221555719231950615059317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13029927671807473227299381 1221555719231950615059317)
                ·
                  refine ⟨114520848677995370161811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1221555719231950615059317 114520848677995370161811)
                  ·
                    rfl

theorem cell23_2007257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 5].length) (baseStart_2007257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007257 prefixEnd_2007257 := by exact prefixLift 2007257
  have htrace : WordTrace (prefixWord ++ tailWord_2007257) baseStart_2007257 baseEnd_2007257 := by
    simpa [prefixWord, tailWord_2007257, baseEnd_2007257] using wordTrace_append hprefix tailTrace_2007257
  have hstable : (prefixWord ++ tailWord_2007257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007257).length < 2 ^ (prefixWord ++ tailWord_2007257).sum := by decide
  have hdescent : baseEnd_2007257 < baseStart_2007257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007280 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_2007280 : Nat := 118140960795 + 2007280 * 2 ^ 59
def prefixEnd_2007280 : Nat := 4983230072969 + 3 ^ 40 * 2007280 * 2
def baseEnd_2007280 : Nat := 1030699448157011741468693

theorem tailTrace_2007280 : CollatzResearch.WordTrace tailWord_2007280 prefixEnd_2007280 1030699448157011741468693 := by
  unfold tailWord_2007280
  simp only [CollatzResearch.WordTrace]
  refine ⟨36605758083987425488061647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48807677445316567317415529 36605758083987425488061647)
  ·
    refine ⟨54908637125981138232092471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36605758083987425488061647 54908637125981138232092471)
    ·
      refine ⟨82362955688971707348138707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54908637125981138232092471 82362955688971707348138707)
      ·
        refine ⟨123544433533457561022208061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82362955688971707348138707 123544433533457561022208061)
        ·
          refine ⟨46329162575046585383328023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123544433533457561022208061 46329162575046585383328023)
          ·
            refine ⟨69493743862569878074992035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46329162575046585383328023 69493743862569878074992035)
            ·
              refine ⟨104240615793854817112488053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69493743862569878074992035 104240615793854817112488053)
              ·
                refine ⟨9772557730673889104295755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104240615793854817112488053 9772557730673889104295755)
                ·
                  refine ⟨14658836596010833656443633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772557730673889104295755 14658836596010833656443633)
                  ·
                    refine ⟨10994127447008125242332725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14658836596010833656443633 10994127447008125242332725)
                    ·
                      refine ⟨1030699448157011741468693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10994127447008125242332725 1030699448157011741468693)
                      ·
                        rfl

theorem cell23_2007280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_2007280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007280 prefixEnd_2007280 := by exact prefixLift 2007280
  have htrace : WordTrace (prefixWord ++ tailWord_2007280) baseStart_2007280 baseEnd_2007280 := by
    simpa [prefixWord, tailWord_2007280, baseEnd_2007280] using wordTrace_append hprefix tailTrace_2007280
  have hstable : (prefixWord ++ tailWord_2007280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007280).length < 2 ^ (prefixWord ++ tailWord_2007280).sum := by decide
  have hdescent : baseEnd_2007280 < baseStart_2007280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007307 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4]
def baseStart_2007307 : Nat := 118140960795 + 2007307 * 2 ^ 59
def prefixEnd_2007307 : Nat := 4983230072969 + 3 ^ 40 * 2007307 * 2
def baseEnd_2007307 : Nat := 1030713312134683135831069

theorem tailTrace_2007307 : CollatzResearch.WordTrace tailWord_2007307 prefixEnd_2007307 1030713312134683135831069 := by
  unfold tailWord_2007307
  simp only [CollatzResearch.WordTrace]
  refine ⟨73212500938877034587356175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48808333959251356391570783 73212500938877034587356175)
  ·
    refine ⟨109818751408315551881034263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73212500938877034587356175 109818751408315551881034263)
    ·
      refine ⟨164728127112473327821551395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109818751408315551881034263 164728127112473327821551395)
      ·
        refine ⟨247092190668709991732327093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164728127112473327821551395 247092190668709991732327093)
        ·
          refine ⟨23164892875191561724905665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247092190668709991732327093 23164892875191561724905665)
          ·
            refine ⟨17373669656393671293679249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23164892875191561724905665 17373669656393671293679249)
            ·
              refine ⟨13030252242295253470259437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17373669656393671293679249 13030252242295253470259437)
              ·
                refine ⟨4886344590860720051347289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13030252242295253470259437 4886344590860720051347289)
                ·
                  refine ⟨3664758443145540038510467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4886344590860720051347289 3664758443145540038510467)
                  ·
                    refine ⟨5497137664718310057765701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3664758443145540038510467 5497137664718310057765701)
                    ·
                      refine ⟨1030713312134683135831069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5497137664718310057765701 1030713312134683135831069)
                      ·
                        rfl

theorem cell23_2007307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4].length) (baseStart_2007307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007307 prefixEnd_2007307 := by exact prefixLift 2007307
  have htrace : WordTrace (prefixWord ++ tailWord_2007307) baseStart_2007307 baseEnd_2007307 := by
    simpa [prefixWord, tailWord_2007307, baseEnd_2007307] using wordTrace_append hprefix tailTrace_2007307
  have hstable : (prefixWord ++ tailWord_2007307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007307).length < 2 ^ (prefixWord ++ tailWord_2007307).sum := by decide
  have hdescent : baseEnd_2007307 < baseStart_2007307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007317 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2007317 : Nat := 118140960795 + 2007317 * 2 ^ 59
def prefixEnd_2007317 : Nat := 4983230072969 + 3 ^ 40 * 2007317 * 2
def baseEnd_2007317 : Nat := 343572815647076032235341

theorem tailTrace_2007317 : CollatzResearch.WordTrace tailWord_2007317 prefixEnd_2007317 343572815647076032235341 := by
  unfold tailWord_2007317
  simp only [CollatzResearch.WordTrace]
  refine ⟨73212865668840806295220205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48808577112560537530146803 73212865668840806295220205)
  ·
    refine ⟨27454824625815302360707577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73212865668840806295220205 27454824625815302360707577)
    ·
      refine ⟨20591118469361476770530683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27454824625815302360707577 20591118469361476770530683)
      ·
        refine ⟨30886677704042215155796025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591118469361476770530683 30886677704042215155796025)
        ·
          refine ⟨23165008278031661366847019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30886677704042215155796025 23165008278031661366847019)
          ·
            refine ⟨34747512417047492050270529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23165008278031661366847019 34747512417047492050270529)
            ·
              refine ⟨26060634312785619037702897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34747512417047492050270529 26060634312785619037702897)
              ·
                refine ⟨19545475734589214278277173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26060634312785619037702897 19545475734589214278277173)
                ·
                  refine ⟨1832388350117738838588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19545475734589214278277173 1832388350117738838588485)
                  ·
                    refine ⟨343572815647076032235341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832388350117738838588485 343572815647076032235341)
                    ·
                      rfl

theorem cell23_2007317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2007317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007317 prefixEnd_2007317 := by exact prefixLift 2007317
  have htrace : WordTrace (prefixWord ++ tailWord_2007317) baseStart_2007317 baseEnd_2007317 := by
    simpa [prefixWord, tailWord_2007317, baseEnd_2007317] using wordTrace_append hprefix tailTrace_2007317
  have hstable : (prefixWord ++ tailWord_2007317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007317).length < 2 ^ (prefixWord ++ tailWord_2007317).sum := by decide
  have hdescent : baseEnd_2007317 < baseStart_2007317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007347 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 6]
def baseStart_2007347 : Nat := 118140960795 + 2007347 * 2 ^ 59
def prefixEnd_2007347 : Nat := 4983230072969 + 3 ^ 40 * 2007347 * 2
def baseEnd_2007347 : Nat := 114525983484540331036765

theorem tailTrace_2007347 : CollatzResearch.WordTrace tailWord_2007347 prefixEnd_2007347 114525983484540331036765 := by
  unfold tailWord_2007347
  simp only [CollatzResearch.WordTrace]
  refine ⟨73213959858732121418812295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48809306572488080945874863 73213959858732121418812295)
  ·
    refine ⟨109820939788098182128218443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73213959858732121418812295 109820939788098182128218443)
    ·
      refine ⟨164731409682147273192327665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109820939788098182128218443 164731409682147273192327665)
      ·
        refine ⟨123548557261610454894245749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164731409682147273192327665 123548557261610454894245749)
        ·
          refine ⟨11582677243275980146335539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123548557261610454894245749 11582677243275980146335539)
          ·
            refine ⟨17374015864913970219503309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11582677243275980146335539 17374015864913970219503309)
            ·
              refine ⟨6515255949342738832313741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17374015864913970219503309 6515255949342738832313741)
              ·
                refine ⟨2443220981003527062117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6515255949342738832313741 2443220981003527062117653)
                ·
                  refine ⟨114525983484540331036765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2443220981003527062117653 114525983484540331036765)
                  ·
                    rfl

theorem cell23_2007347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 6].length) (baseStart_2007347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007347 prefixEnd_2007347 := by exact prefixLift 2007347
  have htrace : WordTrace (prefixWord ++ tailWord_2007347) baseStart_2007347 baseEnd_2007347 := by
    simpa [prefixWord, tailWord_2007347, baseEnd_2007347] using wordTrace_append hprefix tailTrace_2007347
  have hstable : (prefixWord ++ tailWord_2007347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007347).length < 2 ^ (prefixWord ++ tailWord_2007347).sum := by decide
  have hdescent : baseEnd_2007347 < baseStart_2007347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007374 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_2007374 : Nat := 118140960795 + 2007374 * 2 ^ 59
def prefixEnd_2007374 : Nat := 4983230072969 + 3 ^ 40 * 2007374 * 2
def baseEnd_2007374 : Nat := 1030747715338534373693261

theorem tailTrace_2007374 : CollatzResearch.WordTrace tailWord_2007374 prefixEnd_2007374 1030747715338534373693261 := by
  unfold tailWord_2007374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151868078704288128755647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48809963086422870020030117 9151868078704288128755647)
  ·
    refine ⟨13727802118056432193133471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9151868078704288128755647 13727802118056432193133471)
    ·
      refine ⟨20591703177084648289700207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727802118056432193133471 20591703177084648289700207)
      ·
        refine ⟨30887554765626972434550311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20591703177084648289700207 30887554765626972434550311)
        ·
          refine ⟨46331332148440458651825467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887554765626972434550311 46331332148440458651825467)
          ·
            refine ⟨69496998222660687977738201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46331332148440458651825467 69496998222660687977738201)
            ·
              refine ⟨52122748666995515983303651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69496998222660687977738201 52122748666995515983303651)
              ·
                refine ⟨78184123000493273974955477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52122748666995515983303651 78184123000493273974955477)
                ·
                  refine ⟨1832440382824061108788019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78184123000493273974955477 1832440382824061108788019)
                  ·
                    refine ⟨2748660574236091663182029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832440382824061108788019 2748660574236091663182029)
                    ·
                      refine ⟨1030747715338534373693261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748660574236091663182029 1030747715338534373693261)
                      ·
                        rfl

theorem cell23_2007374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_2007374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007374 prefixEnd_2007374 := by exact prefixLift 2007374
  have htrace : WordTrace (prefixWord ++ tailWord_2007374) baseStart_2007374 baseEnd_2007374 := by
    simpa [prefixWord, tailWord_2007374, baseEnd_2007374] using wordTrace_append hprefix tailTrace_2007374
  have hstable : (prefixWord ++ tailWord_2007374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007374).length < 2 ^ (prefixWord ++ tailWord_2007374).sum := by decide
  have hdescent : baseEnd_2007374 < baseStart_2007374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007384 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_2007384 : Nat := 118140960795 + 2007384 * 2 ^ 59
def prefixEnd_2007384 : Nat := 4983230072969 + 3 ^ 40 * 2007384 * 2
def baseEnd_2007384 : Nat := 1030752850145079334568215

theorem tailTrace_2007384 : CollatzResearch.WordTrace tailWord_2007384 prefixEnd_2007384 1030752850145079334568215 := by
  unfold tailWord_2007384
  simp only [CollatzResearch.WordTrace]
  refine ⟨36607654679799038368954603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48810206239732051158606137 36607654679799038368954603)
  ·
    refine ⟨54911482019698557553431905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36607654679799038368954603 54911482019698557553431905)
    ·
      refine ⟨41183611514773918165073929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54911482019698557553431905 41183611514773918165073929)
      ·
        refine ⟨30887708636080438623805447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41183611514773918165073929 30887708636080438623805447)
        ·
          refine ⟨46331562954120657935708171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30887708636080438623805447 46331562954120657935708171)
          ·
            refine ⟨69497344431180986903562257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46331562954120657935708171 69497344431180986903562257)
            ·
              refine ⟨52123008323385740177671693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69497344431180986903562257 52123008323385740177671693)
              ·
                refine ⟨19546128121269652566626885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52123008323385740177671693 19546128121269652566626885)
                ·
                  refine ⟨3664899022738059856242541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19546128121269652566626885 3664899022738059856242541)
                  ·
                    refine ⟨1374337133526772446090953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3664899022738059856242541 1374337133526772446090953)
                    ·
                      refine ⟨1030752850145079334568215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374337133526772446090953 1030752850145079334568215)
                      ·
                        rfl

theorem cell23_2007384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_2007384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007384 prefixEnd_2007384 := by exact prefixLift 2007384
  have htrace : WordTrace (prefixWord ++ tailWord_2007384) baseStart_2007384 baseEnd_2007384 := by
    simpa [prefixWord, tailWord_2007384, baseEnd_2007384] using wordTrace_append hprefix tailTrace_2007384
  have hstable : (prefixWord ++ tailWord_2007384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007384).length < 2 ^ (prefixWord ++ tailWord_2007384).sum := by decide
  have hdescent : baseEnd_2007384 < baseStart_2007384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007394 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2007394 : Nat := 118140960795 + 2007394 * 2 ^ 59
def prefixEnd_2007394 : Nat := 4983230072969 + 3 ^ 40 * 2007394 * 2
def baseEnd_2007394 : Nat := 343585994983874765147723

theorem tailTrace_2007394 : CollatzResearch.WordTrace tailWord_2007394 prefixEnd_2007394 343585994983874765147723 := by
  unfold tailWord_2007394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303918522390462111443309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48810449393041232297182157 18303918522390462111443309)
  ·
    refine ⟨6863969445896423291791241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18303918522390462111443309 6863969445896423291791241)
    ·
      refine ⟨5147977084422317468843431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6863969445896423291791241 5147977084422317468843431)
      ·
        refine ⟨7721965626633476203265147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147977084422317468843431 7721965626633476203265147)
        ·
          refine ⟨11582948439950214304897721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721965626633476203265147 11582948439950214304897721)
          ·
            refine ⟨8687211329962660728673291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11582948439950214304897721 8687211329962660728673291)
            ·
              refine ⟨13030816994943991093009937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687211329962660728673291 13030816994943991093009937)
              ·
                refine ⟨9773112746207993319757453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13030816994943991093009937 9773112746207993319757453)
                ·
                  refine ⟨3664917279827997494909045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9773112746207993319757453 3664917279827997494909045)
                  ·
                    refine ⟨343585994983874765147723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3664917279827997494909045 343585994983874765147723)
                    ·
                      rfl

theorem cell23_2007394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2007394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007394 prefixEnd_2007394 := by exact prefixLift 2007394
  have htrace : WordTrace (prefixWord ++ tailWord_2007394) baseStart_2007394 baseEnd_2007394 := by
    simpa [prefixWord, tailWord_2007394, baseEnd_2007394] using wordTrace_append hprefix tailTrace_2007394
  have hstable : (prefixWord ++ tailWord_2007394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007394).length < 2 ^ (prefixWord ++ tailWord_2007394).sum := by decide
  have hdescent : baseEnd_2007394 < baseStart_2007394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007425 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2007425 : Nat := 118140960795 + 2007425 * 2 ^ 59
def prefixEnd_2007425 : Nat := 4983230072969 + 3 ^ 40 * 2007425 * 2
def baseEnd_2007425 : Nat := 1030773902851913674155527

theorem tailTrace_2007425 : CollatzResearch.WordTrace tailWord_2007425 prefixEnd_2007425 1030773902851913674155527 := by
  unfold tailWord_2007425
  simp only [CollatzResearch.WordTrace]
  refine ⟨73216804752449540740151729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48811203168299693826767819 73216804752449540740151729)
  ·
    refine ⟨54912603564337155555113797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73216804752449540740151729 54912603564337155555113797)
    ·
      refine ⟨10296113168313216666583837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54912603564337155555113797 10296113168313216666583837)
      ·
        refine ⟨3861042438117456249968939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10296113168313216666583837 3861042438117456249968939)
        ·
          refine ⟨5791563657176184374953409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861042438117456249968939 5791563657176184374953409)
          ·
            refine ⟨4343672742882138281215057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5791563657176184374953409 4343672742882138281215057)
            ·
              refine ⟨3257754557161603710911293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4343672742882138281215057 3257754557161603710911293)
              ·
                refine ⟨1221657958935601391591735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3257754557161603710911293 1221657958935601391591735)
                ·
                  refine ⟨1832486938403402087387603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221657958935601391591735 1832486938403402087387603)
                  ·
                    refine ⟨2748730407605103131081405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832486938403402087387603 2748730407605103131081405)
                    ·
                      refine ⟨1030773902851913674155527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748730407605103131081405 1030773902851913674155527)
                      ·
                        rfl

theorem cell23_2007425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2007425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007425 prefixEnd_2007425 := by exact prefixLift 2007425
  have htrace : WordTrace (prefixWord ++ tailWord_2007425) baseStart_2007425 baseEnd_2007425 := by
    simpa [prefixWord, tailWord_2007425, baseEnd_2007425] using wordTrace_append hprefix tailTrace_2007425
  have hstable : (prefixWord ++ tailWord_2007425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007425).length < 2 ^ (prefixWord ++ tailWord_2007425).sum := by decide
  have hdescent : baseEnd_2007425 < baseStart_2007425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007431 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_2007431 : Nat := 118140960795 + 2007431 * 2 ^ 59
def prefixEnd_2007431 : Nat := 4983230072969 + 3 ^ 40 * 2007431 * 2
def baseEnd_2007431 : Nat := 1030776983735840650680499

theorem tailTrace_2007431 : CollatzResearch.WordTrace tailWord_2007431 prefixEnd_2007431 1030776983735840650680499 := by
  unfold tailWord_2007431
  simp only [CollatzResearch.WordTrace]
  refine ⟨73217023590427803764870147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48811349060285202509913431 73217023590427803764870147)
  ·
    refine ⟨109825535385641705647305221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73217023590427803764870147 109825535385641705647305221)
    ·
      refine ⟨20592287884807819808869729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109825535385641705647305221 20592287884807819808869729)
      ·
        refine ⟨15444215913605864856652297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20592287884807819808869729 15444215913605864856652297)
        ·
          refine ⟨11583161935204398642489223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15444215913605864856652297 11583161935204398642489223)
          ·
            refine ⟨17374742902806597963733835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583161935204398642489223 17374742902806597963733835)
            ·
              refine ⟨26062114354209896945600753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17374742902806597963733835 26062114354209896945600753)
              ·
                refine ⟨19546585765657422709200565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26062114354209896945600753 19546585765657422709200565)
                ·
                  refine ⟨1832492415530383378987553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19546585765657422709200565 1832492415530383378987553)
                  ·
                    refine ⟨1374369311647787534240665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832492415530383378987553 1374369311647787534240665)
                    ·
                      refine ⟨1030776983735840650680499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374369311647787534240665 1030776983735840650680499)
                      ·
                        rfl

theorem cell23_2007431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_2007431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007431 prefixEnd_2007431 := by exact prefixLift 2007431
  have htrace : WordTrace (prefixWord ++ tailWord_2007431) baseStart_2007431 baseEnd_2007431 := by
    simpa [prefixWord, tailWord_2007431, baseEnd_2007431] using wordTrace_append hprefix tailTrace_2007431
  have hstable : (prefixWord ++ tailWord_2007431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007431).length < 2 ^ (prefixWord ++ tailWord_2007431).sum := by decide
  have hdescent : baseEnd_2007431 < baseStart_2007431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007448 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2007448 : Nat := 118140960795 + 2007448 * 2 ^ 59
def prefixEnd_2007448 : Nat := 4983230072969 + 3 ^ 40 * 2007448 * 2
def baseEnd_2007448 : Nat := 1030785712906967084167921

theorem tailTrace_2007448 : CollatzResearch.WordTrace tailWord_2007448 prefixEnd_2007448 1030785712906967084167921 := by
  unfold tailWord_2007448
  simp only [CollatzResearch.WordTrace]
  refine ⟨36608821815683107834119499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48811762420910810445492665 36608821815683107834119499)
  ·
    refine ⟨54913232723524661751179249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36608821815683107834119499 54913232723524661751179249)
    ·
      refine ⟨41184924542643496313384437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54913232723524661751179249 41184924542643496313384437)
      ·
        refine ⟨3861086675872827779379791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41184924542643496313384437 3861086675872827779379791)
        ·
          refine ⟨5791630013809241669069687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861086675872827779379791 5791630013809241669069687)
          ·
            refine ⟨8687445020713862503604531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791630013809241669069687 8687445020713862503604531)
            ·
              refine ⟨13031167531070793755406797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687445020713862503604531 13031167531070793755406797)
              ·
                refine ⟨4886687824151547658277549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13031167531070793755406797 4886687824151547658277549)
                ·
                  refine ⟨1832507934056830371854081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4886687824151547658277549 1832507934056830371854081)
                  ·
                    refine ⟨1374380950542622778890561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832507934056830371854081 1374380950542622778890561)
                    ·
                      refine ⟨1030785712906967084167921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374380950542622778890561 1030785712906967084167921)
                      ·
                        rfl

theorem cell23_2007448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2007448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007448 prefixEnd_2007448 := by exact prefixLift 2007448
  have htrace : WordTrace (prefixWord ++ tailWord_2007448) baseStart_2007448 baseEnd_2007448 := by
    simpa [prefixWord, tailWord_2007448, baseEnd_2007448] using wordTrace_append hprefix tailTrace_2007448
  have hstable : (prefixWord ++ tailWord_2007448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007448).length < 2 ^ (prefixWord ++ tailWord_2007448).sum := by decide
  have hdescent : baseEnd_2007448 < baseStart_2007448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007458 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2007458 : Nat := 118140960795 + 2007458 * 2 ^ 59
def prefixEnd_2007458 : Nat := 4983230072969 + 3 ^ 40 * 2007458 * 2
def baseEnd_2007458 : Nat := 343596949237837348347625

theorem tailTrace_2007458 : CollatzResearch.WordTrace tailWord_2007458 prefixEnd_2007458 343596949237837348347625 := by
  unfold tailWord_2007458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304502090332496844025757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48812005574219991584068685 18304502090332496844025757)
  ·
    refine ⟨6864188283874686316509659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18304502090332496844025757 6864188283874686316509659)
    ·
      refine ⟨10296282425812029474764489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864188283874686316509659 10296282425812029474764489)
      ·
        refine ⟨7722211819359022106073367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10296282425812029474764489 7722211819359022106073367)
        ·
          refine ⟨11583317729038533159110051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7722211819359022106073367 11583317729038533159110051)
          ·
            refine ⟨17374976593557799738665077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11583317729038533159110051 17374976593557799738665077)
            ·
              refine ⟨1628904055646043725499851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17374976593557799738665077 1628904055646043725499851)
              ·
                refine ⟨2443356083469065588249777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628904055646043725499851 2443356083469065588249777)
                ·
                  refine ⟨1832517062601799191187333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443356083469065588249777 1832517062601799191187333)
                  ·
                    refine ⟨343596949237837348347625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832517062601799191187333 343596949237837348347625)
                    ·
                      rfl

theorem cell23_2007458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2007458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007458 prefixEnd_2007458 := by exact prefixLift 2007458
  have htrace : WordTrace (prefixWord ++ tailWord_2007458) baseStart_2007458 baseEnd_2007458 := by
    simpa [prefixWord, tailWord_2007458, baseEnd_2007458] using wordTrace_append hprefix tailTrace_2007458
  have hstable : (prefixWord ++ tailWord_2007458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007458).length < 2 ^ (prefixWord ++ tailWord_2007458).sum := by decide
  have hdescent : baseEnd_2007458 < baseStart_2007458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007476 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2007476 : Nat := 118140960795 + 2007476 * 2 ^ 59
def prefixEnd_2007476 : Nat := 4983230072969 + 3 ^ 40 * 2007476 * 2
def baseEnd_2007476 : Nat := 1030800090365292974617793

theorem tailTrace_2007476 : CollatzResearch.WordTrace tailWord_2007476 prefixEnd_2007476 1030800090365292974617793 := by
  unfold tailWord_2007476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36609332437632388225129141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48812443250176517633505521 36609332437632388225129141)
  ·
    refine ⟨3432124916028036396105857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36609332437632388225129141 3432124916028036396105857)
    ·
      refine ⟨2574093687021027297079393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3432124916028036396105857 2574093687021027297079393)
      ·
        refine ⟨1930570265265770472809545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2574093687021027297079393 1930570265265770472809545)
        ·
          refine ⟨1447927698949327854607159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930570265265770472809545 1447927698949327854607159)
          ·
            refine ⟨2171891548423991781910739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447927698949327854607159 2171891548423991781910739)
            ·
              refine ⟨3257837322635987672866109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171891548423991781910739 3257837322635987672866109)
              ·
                refine ⟨1221688995988495377324791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3257837322635987672866109 1221688995988495377324791)
                ·
                  refine ⟨1832533493982743065987187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221688995988495377324791 1832533493982743065987187)
                  ·
                    refine ⟨2748800240974114598980781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832533493982743065987187 2748800240974114598980781)
                    ·
                      refine ⟨1030800090365292974617793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748800240974114598980781 1030800090365292974617793)
                      ·
                        rfl

theorem cell23_2007476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2007476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007476 prefixEnd_2007476 := by exact prefixLift 2007476
  have htrace : WordTrace (prefixWord ++ tailWord_2007476) baseStart_2007476 baseEnd_2007476 := by
    simpa [prefixWord, tailWord_2007476, baseEnd_2007476] using wordTrace_append hprefix tailTrace_2007476
  have hstable : (prefixWord ++ tailWord_2007476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007476).length < 2 ^ (prefixWord ++ tailWord_2007476).sum := by decide
  have hdescent : baseEnd_2007476 < baseStart_2007476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007481 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2007481 : Nat := 118140960795 + 2007481 * 2 ^ 59
def prefixEnd_2007481 : Nat := 4983230072969 + 3 ^ 40 * 2007481 * 2
def baseEnd_2007481 : Nat := 1030802657768565455055269

theorem tailTrace_2007481 : CollatzResearch.WordTrace tailWord_2007481 prefixEnd_2007481 1030802657768565455055269 := by
  unfold tailWord_2007481
  simp only [CollatzResearch.WordTrace]
  refine ⟨73218847240246662304190297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48812564826831108202793531 73218847240246662304190297)
  ·
    refine ⟨54914135430184996728142723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73218847240246662304190297 54914135430184996728142723)
    ·
      refine ⟨82371203145277495092214085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54914135430184996728142723 82371203145277495092214085)
      ·
        refine ⟨15444600589739530329790141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82371203145277495092214085 15444600589739530329790141)
        ·
          refine ⟨5791725221152323873671303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15444600589739530329790141 5791725221152323873671303)
          ·
            refine ⟨8687587831728485810506955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791725221152323873671303 8687587831728485810506955)
            ·
              refine ⟨13031381747592728715760433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8687587831728485810506955 13031381747592728715760433)
              ·
                refine ⟨9773536310694546536820325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13031381747592728715760433 9773536310694546536820325)
                ·
                  refine ⟨1832538058255227475653811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9773536310694546536820325 1832538058255227475653811)
                  ·
                    refine ⟨2748807087382841213480717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832538058255227475653811 2748807087382841213480717)
                    ·
                      refine ⟨1030802657768565455055269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2748807087382841213480717 1030802657768565455055269)
                      ·
                        rfl

theorem cell23_2007481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2007481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007481 prefixEnd_2007481 := by exact prefixLift 2007481
  have htrace : WordTrace (prefixWord ++ tailWord_2007481) baseStart_2007481 baseEnd_2007481 := by
    simpa [prefixWord, tailWord_2007481, baseEnd_2007481] using wordTrace_append hprefix tailTrace_2007481
  have hstable : (prefixWord ++ tailWord_2007481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007481).length < 2 ^ (prefixWord ++ tailWord_2007481).sum := by decide
  have hdescent : baseEnd_2007481 < baseStart_2007481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007487 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_2007487 : Nat := 118140960795 + 2007487 * 2 ^ 59
def prefixEnd_2007487 : Nat := 4983230072969 + 3 ^ 40 * 2007487 * 2
def baseEnd_2007487 : Nat := 1030805738652492431580241

theorem tailTrace_2007487 : CollatzResearch.WordTrace tailWord_2007487 prefixEnd_2007487 1030805738652492431580241 := by
  unfold tailWord_2007487
  simp only [CollatzResearch.WordTrace]
  refine ⟨73219066078224925328908715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48812710718816616885939143 73219066078224925328908715)
  ·
    refine ⟨109828599117337387993363073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73219066078224925328908715 109828599117337387993363073)
    ·
      refine ⟨82371449338003040995022305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109828599117337387993363073 82371449338003040995022305)
      ·
        refine ⟨61778587003502280746266729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82371449338003040995022305 61778587003502280746266729)
        ·
          refine ⟨46333940252626710559700047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61778587003502280746266729 46333940252626710559700047)
          ·
            refine ⟨69500910378940065839550071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46333940252626710559700047 69500910378940065839550071)
            ·
              refine ⟨104251365568410098759325107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69500910378940065839550071 104251365568410098759325107)
              ·
                refine ⟨156377048352615148138987661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104251365568410098759325107 156377048352615148138987661)
                ·
                  refine ⟨58641393132230680552120373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156377048352615148138987661 58641393132230680552120373)
                  ·
                    refine ⟨5497630606146626301761285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58641393132230680552120373 5497630606146626301761285)
                    ·
                      refine ⟨1030805738652492431580241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5497630606146626301761285 1030805738652492431580241)
                      ·
                        rfl

theorem cell23_2007487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_2007487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007487 prefixEnd_2007487 := by exact prefixLift 2007487
  have htrace : WordTrace (prefixWord ++ tailWord_2007487) baseStart_2007487 baseEnd_2007487 := by
    simpa [prefixWord, tailWord_2007487, baseEnd_2007487] using wordTrace_append hprefix tailTrace_2007487
  have hstable : (prefixWord ++ tailWord_2007487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007487).length < 2 ^ (prefixWord ++ tailWord_2007487).sum := by decide
  have hdescent : baseEnd_2007487 < baseStart_2007487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007497 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_2007497 : Nat := 118140960795 + 2007497 * 2 ^ 59
def prefixEnd_2007497 : Nat := 4983230072969 + 3 ^ 40 * 2007497 * 2
def baseEnd_2007497 : Nat := 343603624486345797485065

theorem tailTrace_2007497 : CollatzResearch.WordTrace tailWord_2007497 prefixEnd_2007497 343603624486345797485065 := by
  unfold tailWord_2007497
  simp only [CollatzResearch.WordTrace]
  refine ⟨73219430808188697036772745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48812953872125798024515163 73219430808188697036772745)
  ·
    refine ⟨54914573106141522777579559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73219430808188697036772745 54914573106141522777579559)
    ·
      refine ⟨82371859659212284166369339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54914573106141522777579559 82371859659212284166369339)
      ·
        refine ⟨123557789488818426249554009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82371859659212284166369339 123557789488818426249554009)
        ·
          refine ⟨92668342116613819687165507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123557789488818426249554009 92668342116613819687165507)
          ·
            refine ⟨139002513174920729530748261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92668342116613819687165507 139002513174920729530748261)
            ·
              refine ⟨26062971220297636787015299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139002513174920729530748261 26062971220297636787015299)
              ·
                refine ⟨39094456830446455180522949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26062971220297636787015299 39094456830446455180522949)
                ·
                  refine ⟨7330210655708710346348053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39094456830446455180522949 7330210655708710346348053)
                  ·
                    refine ⟨343603624486345797485065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7330210655708710346348053 343603624486345797485065)
                    ·
                      rfl

theorem cell23_2007497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_2007497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007497 prefixEnd_2007497 := by exact prefixLift 2007497
  have htrace : WordTrace (prefixWord ++ tailWord_2007497) baseStart_2007497 baseEnd_2007497 := by
    simpa [prefixWord, tailWord_2007497, baseEnd_2007497] using wordTrace_append hprefix tailTrace_2007497
  have hstable : (prefixWord ++ tailWord_2007497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007497).length < 2 ^ (prefixWord ++ tailWord_2007497).sum := by decide
  have hdescent : baseEnd_2007497 < baseStart_2007497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007504 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2]
def baseStart_2007504 : Nat := 118140960795 + 2007504 * 2 ^ 59
def prefixEnd_2007504 : Nat := 4983230072969 + 3 ^ 40 * 2007504 * 2
def baseEnd_2007504 : Nat := 1030814467823618865067663

theorem tailTrace_2007504 : CollatzResearch.WordTrace tailWord_2007504 prefixEnd_2007504 1030814467823618865067663 := by
  unfold tailWord_2007504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36609843059581668616138783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48813124079442224821518377 36609843059581668616138783)
  ·
    refine ⟨54914764589372502924208175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36609843059581668616138783 54914764589372502924208175)
    ·
      refine ⟨82372146884058754386312263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54914764589372502924208175 82372146884058754386312263)
      ·
        refine ⟨123558220326088131579468395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82372146884058754386312263 123558220326088131579468395)
        ·
          refine ⟨185337330489132197369202593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123558220326088131579468395 185337330489132197369202593)
          ·
            refine ⟨139002997866849148026901945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185337330489132197369202593 139002997866849148026901945)
            ·
              refine ⟨104252248400136861020176459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139002997866849148026901945 104252248400136861020176459)
              ·
                refine ⟨156378372600205291530264689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104252248400136861020176459 156378372600205291530264689)
                ·
                  refine ⟨117283779450153968647698517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156378372600205291530264689 117283779450153968647698517)
                  ·
                    refine ⟨1374419290431491820090217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117283779450153968647698517 1374419290431491820090217)
                    ·
                      refine ⟨1030814467823618865067663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374419290431491820090217 1030814467823618865067663)
                      ·
                        rfl

theorem cell23_2007504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 8, 2].length) (baseStart_2007504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007504 prefixEnd_2007504 := by exact prefixLift 2007504
  have htrace : WordTrace (prefixWord ++ tailWord_2007504) baseStart_2007504 baseEnd_2007504 := by
    simpa [prefixWord, tailWord_2007504, baseEnd_2007504] using wordTrace_append hprefix tailTrace_2007504
  have hstable : (prefixWord ++ tailWord_2007504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007504).length < 2 ^ (prefixWord ++ tailWord_2007504).sum := by decide
  have hdescent : baseEnd_2007504 < baseStart_2007504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007521 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_2007521 : Nat := 118140960795 + 2007521 * 2 ^ 59
def prefixEnd_2007521 : Nat := 4983230072969 + 3 ^ 40 * 2007521 * 2
def baseEnd_2007521 : Nat := 1030823196994745298555085

theorem tailTrace_2007521 : CollatzResearch.WordTrace tailWord_2007521 prefixEnd_2007521 1030823196994745298555085 := by
  unfold tailWord_2007521
  simp only [CollatzResearch.WordTrace]
  refine ⟨73220306160101749135646417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48813537440067832757097611 73220306160101749135646417)
  ·
    refine ⟨54915229620076311851734813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73220306160101749135646417 54915229620076311851734813)
    ·
      refine ⟨20593211107528616944400555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54915229620076311851734813 20593211107528616944400555)
      ·
        refine ⟨30889816661292925416600833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20593211107528616944400555 30889816661292925416600833)
        ·
          refine ⟨23167362495969694062450625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30889816661292925416600833 23167362495969694062450625)
          ·
            refine ⟨17375521871977270546837969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23167362495969694062450625 17375521871977270546837969)
            ·
              refine ⟨13031641403982952910128477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17375521871977270546837969 13031641403982952910128477)
              ·
                refine ⟨4886865526493607341298179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13031641403982952910128477 4886865526493607341298179)
                ·
                  refine ⟨7330298289740411011947269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4886865526493607341298179 7330298289740411011947269)
                  ·
                    refine ⟨1374430929326327064740113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7330298289740411011947269 1374430929326327064740113)
                    ·
                      refine ⟨1030823196994745298555085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374430929326327064740113 1030823196994745298555085)
                      ·
                        rfl

theorem cell23_2007521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_2007521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007521 prefixEnd_2007521 := by exact prefixLift 2007521
  have htrace : WordTrace (prefixWord ++ tailWord_2007521) baseStart_2007521 baseEnd_2007521 := by
    simpa [prefixWord, tailWord_2007521, baseEnd_2007521] using wordTrace_append hprefix tailTrace_2007521
  have hstable : (prefixWord ++ tailWord_2007521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007521).length < 2 ^ (prefixWord ++ tailWord_2007521).sum := by decide
  have hdescent : baseEnd_2007521 < baseStart_2007521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007547 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_2007547 : Nat := 118140960795 + 2007547 * 2 ^ 59
def prefixEnd_2007547 : Nat := 4983230072969 + 3 ^ 40 * 2007547 * 2
def baseEnd_2007547 : Nat := 1030836547491762196829965

theorem tailTrace_2007547 : CollatzResearch.WordTrace tailWord_2007547 prefixEnd_2007547 1030836547491762196829965 := by
  unfold tailWord_2007547
  simp only [CollatzResearch.WordTrace]
  refine ⟨73221254458007555576092895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48814169638671703717395263 73221254458007555576092895)
  ·
    refine ⟨109831881687011333364139343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73221254458007555576092895 109831881687011333364139343)
    ·
      refine ⟨164747822530517000046209015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109831881687011333364139343 164747822530517000046209015)
      ·
        refine ⟨247121733795775500069313523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164747822530517000046209015 247121733795775500069313523)
        ·
          refine ⟨370682600693663250103970285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247121733795775500069313523 370682600693663250103970285)
          ·
            refine ⟨139005975260123718788988857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370682600693663250103970285 139005975260123718788988857)
            ·
              refine ⟨104254481445092789091741643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139005975260123718788988857 104254481445092789091741643)
              ·
                refine ⟨156381722167639183637612465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104254481445092789091741643 156381722167639183637612465)
                ·
                  refine ⟨117286291625729387728209349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156381722167639183637612465 117286291625729387728209349)
                  ·
                    refine ⟨21991179679824260199039253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117286291625729387728209349 21991179679824260199039253)
                    ·
                      refine ⟨1030836547491762196829965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21991179679824260199039253 1030836547491762196829965)
                      ·
                        rfl

theorem cell23_2007547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_2007547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007547 prefixEnd_2007547 := by exact prefixLift 2007547
  have htrace : WordTrace (prefixWord ++ tailWord_2007547) baseStart_2007547 baseEnd_2007547 := by
    simpa [prefixWord, tailWord_2007547, baseEnd_2007547] using wordTrace_append hprefix tailTrace_2007547
  have hstable : (prefixWord ++ tailWord_2007547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007547).length < 2 ^ (prefixWord ++ tailWord_2007547).sum := by decide
  have hdescent : baseEnd_2007547 < baseStart_2007547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007572 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2007572 : Nat := 118140960795 + 2007572 * 2 ^ 59
def prefixEnd_2007572 : Nat := 4983230072969 + 3 ^ 40 * 2007572 * 2
def baseEnd_2007572 : Nat := 1030849384508124599017351

theorem tailTrace_2007572 : CollatzResearch.WordTrace tailWord_2007572 prefixEnd_2007572 1030849384508124599017351 := by
  unfold tailWord_2007572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611083141458492422876485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48814777521944656563835313 36611083141458492422876485)
  ·
    refine ⟨6864578089023467329289341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36611083141458492422876485 6864578089023467329289341)
    ·
      refine ⟨2574216783383800248483503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6864578089023467329289341 2574216783383800248483503)
      ·
        refine ⟨3861325175075700372725255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574216783383800248483503 3861325175075700372725255)
        ·
          refine ⟨5791987762613550559087883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861325175075700372725255 5791987762613550559087883)
          ·
            refine ⟨8687981643920325838631825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791987762613550559087883 8687981643920325838631825)
            ·
              refine ⟨6515986232940244378973869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8687981643920325838631825 6515986232940244378973869)
              ·
                refine ⟨2443494837352591642115201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6515986232940244378973869 2443494837352591642115201)
                ·
                  refine ⟨1832621128014443731586401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443494837352591642115201 1832621128014443731586401)
                  ·
                    refine ⟨1374465846010832798689801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832621128014443731586401 1374465846010832798689801)
                    ·
                      refine ⟨1030849384508124599017351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374465846010832798689801 1030849384508124599017351)
                      ·
                        rfl

theorem cell23_2007572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2007572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007572 prefixEnd_2007572 := by exact prefixLift 2007572
  have htrace : WordTrace (prefixWord ++ tailWord_2007572) baseStart_2007572 baseEnd_2007572 := by
    simpa [prefixWord, tailWord_2007572, baseEnd_2007572] using wordTrace_append hprefix tailTrace_2007572
  have hstable : (prefixWord ++ tailWord_2007572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007572).length < 2 ^ (prefixWord ++ tailWord_2007572).sum := by decide
  have hdescent : baseEnd_2007572 < baseStart_2007572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007621 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_2007621 : Nat := 118140960795 + 2007621 * 2 ^ 59
def prefixEnd_2007621 : Nat := 4983230072969 + 3 ^ 40 * 2007621 * 2
def baseEnd_2007621 : Nat := 343624848353398302434875

theorem tailTrace_2007621 : CollatzResearch.WordTrace tailWord_2007621 prefixEnd_2007621 343624848353398302434875 := by
  unfold tailWord_2007621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73223953459739466214286717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48815968973159644142857811 73223953459739466214286717)
  ·
    refine ⟨27458982547402299830357519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73223953459739466214286717 27458982547402299830357519)
    ·
      refine ⟨41188473821103449745536279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27458982547402299830357519 41188473821103449745536279)
      ·
        refine ⟨61782710731655174618304419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41188473821103449745536279 61782710731655174618304419)
        ·
          refine ⟨92674066097482761927456629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61782710731655174618304419 92674066097482761927456629)
          ·
            refine ⟨8688193696639008930699059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92674066097482761927456629 8688193696639008930699059)
            ·
              refine ⟨13032290544958513396048589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688193696639008930699059 13032290544958513396048589)
              ·
                refine ⟨4887108954359442523518221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032290544958513396048589 4887108954359442523518221)
                ·
                  refine ⟨1832665857884790946319333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4887108954359442523518221 1832665857884790946319333)
                  ·
                    refine ⟨343624848353398302434875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832665857884790946319333 343624848353398302434875)
                    ·
                      rfl

theorem cell23_2007621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_2007621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007621 prefixEnd_2007621 := by exact prefixLift 2007621
  have htrace : WordTrace (prefixWord ++ tailWord_2007621) baseStart_2007621 baseEnd_2007621 := by
    simpa [prefixWord, tailWord_2007621, baseEnd_2007621] using wordTrace_append hprefix tailTrace_2007621
  have hstable : (prefixWord ++ tailWord_2007621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007621).length < 2 ^ (prefixWord ++ tailWord_2007621).sum := by decide
  have hdescent : baseEnd_2007621 < baseStart_2007621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007646 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2007646 : Nat := 118140960795 + 2007646 * 2 ^ 59
def prefixEnd_2007646 : Nat := 4983230072969 + 3 ^ 40 * 2007646 * 2
def baseEnd_2007646 : Nat := 114543042452950812165779

theorem tailTrace_2007646 : CollatzResearch.WordTrace tailWord_2007646 prefixEnd_2007646 114543042452950812165779 := by
  unfold tailWord_2007646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153108160581111935493349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48816576856432596989297861 9153108160581111935493349)
  ·
    refine ⟨1716207780108958487905003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9153108160581111935493349 1716207780108958487905003)
    ·
      refine ⟨2574311670163437731857505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716207780108958487905003 2574311670163437731857505)
      ·
        refine ⟨1930733752622578298893129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2574311670163437731857505 1930733752622578298893129)
        ·
          refine ⟨1448050314466933724169847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930733752622578298893129 1448050314466933724169847)
          ·
            refine ⟨2172075471700400586254771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448050314466933724169847 2172075471700400586254771)
            ·
              refine ⟨3258113207550600879382157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172075471700400586254771 3258113207550600879382157)
              ·
                refine ⟨1221792452831475329768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3258113207550600879382157 1221792452831475329768309)
                ·
                  refine ⟨114543042452950812165779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1221792452831475329768309 114543042452950812165779)
                  ·
                    rfl

theorem cell23_2007646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2007646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007646 prefixEnd_2007646 := by exact prefixLift 2007646
  have htrace : WordTrace (prefixWord ++ tailWord_2007646) baseStart_2007646 baseEnd_2007646 := by
    simpa [prefixWord, tailWord_2007646, baseEnd_2007646] using wordTrace_append hprefix tailTrace_2007646
  have hstable : (prefixWord ++ tailWord_2007646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007646).length < 2 ^ (prefixWord ++ tailWord_2007646).sum := by decide
  have hdescent : baseEnd_2007646 < baseStart_2007646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007681 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2007681 : Nat := 118140960795 + 2007681 * 2 ^ 59
def prefixEnd_2007681 : Nat := 4983230072969 + 3 ^ 40 * 2007681 * 2
def baseEnd_2007681 : Nat := 343635117966488224184783

theorem tailTrace_2007681 : CollatzResearch.WordTrace tailWord_2007681 prefixEnd_2007681 343635117966488224184783 := by
  unfold tailWord_2007681
  simp only [CollatzResearch.WordTrace]
  refine ⟨73226141839522096461470897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48817427893014730974313931 73226141839522096461470897)
  ·
    refine ⟨54919606379641572346103173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73226141839522096461470897 54919606379641572346103173)
    ·
      refine ⟨10297426196182794814894345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54919606379641572346103173 10297426196182794814894345)
      ·
        refine ⟨7723069647137096111170759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10297426196182794814894345 7723069647137096111170759)
        ·
          refine ⟨11584604470705644166756139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723069647137096111170759 11584604470705644166756139)
          ·
            refine ⟨17376906706058466250134209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584604470705644166756139 17376906706058466250134209)
            ·
              refine ⟨13032680029543849687600657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17376906706058466250134209 13032680029543849687600657)
              ·
                refine ⟨9774510022157887265700493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13032680029543849687600657 9774510022157887265700493)
                ·
                  refine ⟨3665441258309207724637685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9774510022157887265700493 3665441258309207724637685)
                  ·
                    refine ⟨343635117966488224184783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3665441258309207724637685 343635117966488224184783)
                    ·
                      rfl

theorem cell23_2007681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2007681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007681 prefixEnd_2007681 := by exact prefixLift 2007681
  have htrace : WordTrace (prefixWord ++ tailWord_2007681) baseStart_2007681 baseEnd_2007681 := by
    simpa [prefixWord, tailWord_2007681, baseEnd_2007681] using wordTrace_append hprefix tailTrace_2007681
  have hstable : (prefixWord ++ tailWord_2007681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007681).length < 2 ^ (prefixWord ++ tailWord_2007681).sum := by decide
  have hdescent : baseEnd_2007681 < baseStart_2007681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007698 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2007698 : Nat := 118140960795 + 2007698 * 2 ^ 59
def prefixEnd_2007698 : Nat := 4983230072969 + 3 ^ 40 * 2007698 * 2
def baseEnd_2007698 : Nat := 343638027690197035347257

theorem tailTrace_2007698 : CollatzResearch.WordTrace tailWord_2007698 prefixEnd_2007698 343638027690197035347257 := by
  unfold tailWord_2007698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306690470115127091209937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48817841253640338909893165 18306690470115127091209937)
  ·
    refine ⟨13730017852586345318407453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18306690470115127091209937 13730017852586345318407453)
    ·
      refine ⟨5148756694719879494402795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13730017852586345318407453 5148756694719879494402795)
      ·
        refine ⟨7723135042079819241604193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148756694719879494402795 7723135042079819241604193)
        ·
          refine ⟨5792351281559864431203145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7723135042079819241604193 5792351281559864431203145)
          ·
            refine ⟨4344263461169898323402359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792351281559864431203145 4344263461169898323402359)
            ·
              refine ⟨6516395191754847485103539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344263461169898323402359 6516395191754847485103539)
              ·
                refine ⟨9774592787632271227655309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516395191754847485103539 9774592787632271227655309)
                ·
                  refine ⟨3665472295362101710370741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9774592787632271227655309 3665472295362101710370741)
                  ·
                    refine ⟨343638027690197035347257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3665472295362101710370741 343638027690197035347257)
                    ·
                      rfl

theorem cell23_2007698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2007698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007698 prefixEnd_2007698 := by exact prefixLift 2007698
  have htrace : WordTrace (prefixWord ++ tailWord_2007698) baseStart_2007698 baseEnd_2007698 := by
    simpa [prefixWord, tailWord_2007698, baseEnd_2007698] using wordTrace_append hprefix tailTrace_2007698
  have hstable : (prefixWord ++ tailWord_2007698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007698).length < 2 ^ (prefixWord ++ tailWord_2007698).sum := by decide
  have hdescent : baseEnd_2007698 < baseStart_2007698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007721 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_2007721 : Nat := 118140960795 + 2007721 * 2 ^ 59
def prefixEnd_2007721 : Nat := 4983230072969 + 3 ^ 40 * 2007721 * 2
def baseEnd_2007721 : Nat := 1030925893125644516054165

theorem tailTrace_2007721 : CollatzResearch.WordTrace tailWord_2007721 prefixEnd_2007721 1030925893125644516054165 := by
  unfold tailWord_2007721
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227600759377183292927017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48818400506251455528618011 73227600759377183292927017)
  ·
    refine ⟨54920700569532887469695263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73227600759377183292927017 54920700569532887469695263)
    ·
      refine ⟨82381050854299331204542895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54920700569532887469695263 82381050854299331204542895)
      ·
        refine ⟨123571576281448996806814343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82381050854299331204542895 123571576281448996806814343)
        ·
          refine ⟨185357364422173495210221515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123571576281448996806814343 185357364422173495210221515)
          ·
            refine ⟨278036046633260242815332273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185357364422173495210221515 278036046633260242815332273)
            ·
              refine ⟨208527034974945182111499205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278036046633260242815332273 208527034974945182111499205)
              ·
                refine ⟨39098819057802221645906101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208527034974945182111499205 39098819057802221645906101)
                ·
                  refine ⟨3665514286668958279303697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39098819057802221645906101 3665514286668958279303697)
                  ·
                    refine ⟨2749135715001718709477773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665514286668958279303697 2749135715001718709477773)
                    ·
                      refine ⟨1030925893125644516054165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749135715001718709477773 1030925893125644516054165)
                      ·
                        rfl

theorem cell23_2007721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_2007721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007721 prefixEnd_2007721 := by exact prefixLift 2007721
  have htrace : WordTrace (prefixWord ++ tailWord_2007721) baseStart_2007721 baseEnd_2007721 := by
    simpa [prefixWord, tailWord_2007721, baseEnd_2007721] using wordTrace_append hprefix tailTrace_2007721
  have hstable : (prefixWord ++ tailWord_2007721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007721).length < 2 ^ (prefixWord ++ tailWord_2007721).sum := by decide
  have hdescent : baseEnd_2007721 < baseStart_2007721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007729 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2007729 : Nat := 118140960795 + 2007729 * 2 ^ 59
def prefixEnd_2007729 : Nat := 4983230072969 + 3 ^ 40 * 2007729 * 2
def baseEnd_2007729 : Nat := 1030930000970880484754129

theorem tailTrace_2007729 : CollatzResearch.WordTrace tailWord_2007729 prefixEnd_2007729 1030930000970880484754129 := by
  unfold tailWord_2007729
  simp only [CollatzResearch.WordTrace]
  refine ⟨73227892543348200659218241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48818595028898800439478827 73227892543348200659218241)
  ·
    refine ⟨54920919407511150494413681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73227892543348200659218241 54920919407511150494413681)
    ·
      refine ⟨41190689555633362870810261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54920919407511150494413681 41190689555633362870810261)
      ·
        refine ⟨1930813572920313884569231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41190689555633362870810261 1930813572920313884569231)
        ·
          refine ⟨2896220359380470826853847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930813572920313884569231 2896220359380470826853847)
          ·
            refine ⟨4344330539070706240280771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896220359380470826853847 4344330539070706240280771)
            ·
              refine ⟨6516495808606059360421157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344330539070706240280771 6516495808606059360421157)
              ·
                refine ⟨1221842964113636130078967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6516495808606059360421157 1221842964113636130078967)
                ·
                  refine ⟨1832764446170454195118451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221842964113636130078967 1832764446170454195118451)
                  ·
                    refine ⟨2749146669255681292677677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832764446170454195118451 2749146669255681292677677)
                    ·
                      refine ⟨1030930000970880484754129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749146669255681292677677 1030930000970880484754129)
                      ·
                        rfl

theorem cell23_2007729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2007729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007729 prefixEnd_2007729 := by exact prefixLift 2007729
  have htrace : WordTrace (prefixWord ++ tailWord_2007729) baseStart_2007729 baseEnd_2007729 := by
    simpa [prefixWord, tailWord_2007729, baseEnd_2007729] using wordTrace_append hprefix tailTrace_2007729
  have hstable : (prefixWord ++ tailWord_2007729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007729).length < 2 ^ (prefixWord ++ tailWord_2007729).sum := by decide
  have hdescent : baseEnd_2007729 < baseStart_2007729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007741 : List Nat := [1, 4, 1, 2, 1, 3, 3, 8]
def baseStart_2007741 : Nat := 118140960795 + 2007741 * 2 ^ 59
def prefixEnd_2007741 : Nat := 4983230072969 + 3 ^ 40 * 2007741 * 2
def baseEnd_2007741 : Nat := 38182820842175349548299

theorem tailTrace_2007741 : CollatzResearch.WordTrace tailWord_2007741 prefixEnd_2007741 38182820842175349548299 := by
  unfold tailWord_2007741
  simp only [CollatzResearch.WordTrace]
  refine ⟨73228330219304726708655077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48818886812869817805770051 73228330219304726708655077)
  ·
    refine ⟨13730311916119636257872827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73228330219304726708655077 13730311916119636257872827)
    ·
      refine ⟨20595467874179454386809241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13730311916119636257872827 20595467874179454386809241)
      ·
        refine ⟨15446600905634590790106931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20595467874179454386809241 15446600905634590790106931)
        ·
          refine ⟨23169901358451886185160397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446600905634590790106931 23169901358451886185160397)
          ·
            refine ⟨8688713009419457319435149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23169901358451886185160397 8688713009419457319435149)
            ·
              refine ⟨3258267378532296494788181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8688713009419457319435149 3258267378532296494788181)
              ·
                refine ⟨38182820842175349548299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3258267378532296494788181 38182820842175349548299)
                ·
                  rfl

theorem cell23_2007741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 8].length) (baseStart_2007741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007741 prefixEnd_2007741 := by exact prefixLift 2007741
  have htrace : WordTrace (prefixWord ++ tailWord_2007741) baseStart_2007741 baseEnd_2007741 := by
    simpa [prefixWord, tailWord_2007741, baseEnd_2007741] using wordTrace_append hprefix tailTrace_2007741
  have hstable : (prefixWord ++ tailWord_2007741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007741).length < 2 ^ (prefixWord ++ tailWord_2007741).sum := by decide
  have hdescent : baseEnd_2007741 < baseStart_2007741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007748 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2007748 : Nat := 118140960795 + 2007748 * 2 ^ 59
def prefixEnd_2007748 : Nat := 4983230072969 + 3 ^ 40 * 2007748 * 2
def baseEnd_2007748 : Nat := 1030939757103315910416541

theorem tailTrace_2007748 : CollatzResearch.WordTrace tailWord_2007748 prefixEnd_2007748 1030939757103315910416541 := by
  unfold tailWord_2007748
  simp only [CollatzResearch.WordTrace]
  refine ⟨36614292765139683452079949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48819057020186244602773265 36614292765139683452079949)
  ·
    refine ⟨13730359786927381294529981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36614292765139683452079949 13730359786927381294529981)
    ·
      refine ⟨5148884920097767985448743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13730359786927381294529981 5148884920097767985448743)
      ·
        refine ⟨7723327380146651978173115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148884920097767985448743 7723327380146651978173115)
        ·
          refine ⟨11584991070219977967259673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723327380146651978173115 11584991070219977967259673)
          ·
            refine ⟨8688743302664983475444755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584991070219977967259673 8688743302664983475444755)
            ·
              refine ⟨13033114953997475213167133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8688743302664983475444755 13033114953997475213167133)
              ·
                refine ⟨4887418107749053204937675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13033114953997475213167133 4887418107749053204937675)
                ·
                  refine ⟨7331127161623579807406513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887418107749053204937675 7331127161623579807406513)
                  ·
                    refine ⟨5498345371217684855554885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7331127161623579807406513 5498345371217684855554885)
                    ·
                      refine ⟨1030939757103315910416541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5498345371217684855554885 1030939757103315910416541)
                      ·
                        rfl

theorem cell23_2007748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2007748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007748 prefixEnd_2007748 := by exact prefixLift 2007748
  have htrace : WordTrace (prefixWord ++ tailWord_2007748) baseStart_2007748 baseEnd_2007748 := by
    simpa [prefixWord, tailWord_2007748, baseEnd_2007748] using wordTrace_append hprefix tailTrace_2007748
  have hstable : (prefixWord ++ tailWord_2007748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007748).length < 2 ^ (prefixWord ++ tailWord_2007748).sum := by decide
  have hdescent : baseEnd_2007748 < baseStart_2007748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007758 : List Nat := [4, 1, 1, 1, 3, 3, 3, 7]
def baseStart_2007758 : Nat := 118140960795 + 2007758 * 2 ^ 59
def prefixEnd_2007758 : Nat := 4983230072969 + 3 ^ 40 * 2007758 * 2
def baseEnd_2007758 : Nat := 38183144144809661899685

theorem tailTrace_2007758 : CollatzResearch.WordTrace tailWord_2007758 prefixEnd_2007758 38183144144809661899685 := by
  unfold tailWord_2007758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153618782530392326502991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48819300173495425741349285 9153618782530392326502991)
  ·
    refine ⟨13730428173795588489754487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9153618782530392326502991 13730428173795588489754487)
    ·
      refine ⟨20595642260693382734631731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13730428173795588489754487 20595642260693382734631731)
      ·
        refine ⟨30893463391040074101947597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20595642260693382734631731 30893463391040074101947597)
        ·
          refine ⟨11585048771640027788230349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30893463391040074101947597 11585048771640027788230349)
          ·
            refine ⟨4344393289365010420586381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11585048771640027788230349 4344393289365010420586381)
            ·
              refine ⟨1629147483511878907719893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4344393289365010420586381 1629147483511878907719893)
              ·
                refine ⟨38183144144809661899685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1629147483511878907719893 38183144144809661899685)
                ·
                  rfl

theorem cell23_2007758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_2007758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007758 prefixEnd_2007758 := by exact prefixLift 2007758
  have htrace : WordTrace (prefixWord ++ tailWord_2007758) baseStart_2007758 baseEnd_2007758 := by
    simpa [prefixWord, tailWord_2007758, baseEnd_2007758] using wordTrace_append hprefix tailTrace_2007758
  have hstable : (prefixWord ++ tailWord_2007758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007758).length < 2 ^ (prefixWord ++ tailWord_2007758).sum := by decide
  have hdescent : baseEnd_2007758 < baseStart_2007758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007768 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2007768 : Nat := 118140960795 + 2007768 * 2 ^ 59
def prefixEnd_2007768 : Nat := 4983230072969 + 3 ^ 40 * 2007768 * 2
def baseEnd_2007768 : Nat := 1030950026716405832166449

theorem tailTrace_2007768 : CollatzResearch.WordTrace tailWord_2007768 prefixEnd_2007768 1030950026716405832166449 := by
  unfold tailWord_2007768
  simp only [CollatzResearch.WordTrace]
  refine ⟨36614657495103455159943979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48819543326804606879925305 36614657495103455159943979)
  ·
    refine ⟨54921986242655182739915969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36614657495103455159943979 54921986242655182739915969)
    ·
      refine ⟨41191489681991387054936977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54921986242655182739915969 41191489681991387054936977)
      ·
        refine ⟨30893617261493540291202733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41191489681991387054936977 30893617261493540291202733)
        ·
          refine ⟨11585106473060077609201025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30893617261493540291202733 11585106473060077609201025)
          ·
            refine ⟨8688829854795058206900769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11585106473060077609201025 8688829854795058206900769)
            ·
              refine ⟨6516622391096293655175577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688829854795058206900769 6516622391096293655175577)
              ·
                refine ⟨4887466793322220241381683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516622391096293655175577 4887466793322220241381683)
                ·
                  refine ⟨7331200189983330362072525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887466793322220241381683 7331200189983330362072525)
                  ·
                    refine ⟨2749200071243748885777197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7331200189983330362072525 2749200071243748885777197)
                    ·
                      refine ⟨1030950026716405832166449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749200071243748885777197 1030950026716405832166449)
                      ·
                        rfl

theorem cell23_2007768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2007768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007768 prefixEnd_2007768 := by exact prefixLift 2007768
  have htrace : WordTrace (prefixWord ++ tailWord_2007768) baseStart_2007768 baseEnd_2007768 := by
    simpa [prefixWord, tailWord_2007768, baseEnd_2007768] using wordTrace_append hprefix tailTrace_2007768
  have hstable : (prefixWord ++ tailWord_2007768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007768).length < 2 ^ (prefixWord ++ tailWord_2007768).sum := by decide
  have hdescent : baseEnd_2007768 < baseStart_2007768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007772 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2007772 : Nat := 118140960795 + 2007772 * 2 ^ 59
def prefixEnd_2007772 : Nat := 4983230072969 + 3 ^ 40 * 2007772 * 2
def baseEnd_2007772 : Nat := 1030952080639023816516431

theorem tailTrace_2007772 : CollatzResearch.WordTrace tailWord_2007772 prefixEnd_2007772 1030952080639023816516431 := by
  unfold tailWord_2007772
  simp only [CollatzResearch.WordTrace]
  refine ⟨36614730441096209501516785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48819640588128279335355713 36614730441096209501516785)
  ·
    refine ⟨27461047830822157126137589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36614730441096209501516785 27461047830822157126137589)
    ·
      refine ⟨2574473234139577230575399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27461047830822157126137589 2574473234139577230575399)
      ·
        refine ⟨3861709851209365845863099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574473234139577230575399 3861709851209365845863099)
        ·
          refine ⟨5792564776814048768794649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861709851209365845863099 5792564776814048768794649)
          ·
            refine ⟨4344423582610536576595987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792564776814048768794649 4344423582610536576595987)
            ·
              refine ⟨6516635373915804864893981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344423582610536576595987 6516635373915804864893981)
              ·
                refine ⟨2443738265218426824335243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6516635373915804864893981 2443738265218426824335243)
                ·
                  refine ⟨3665607397827640236502865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443738265218426824335243 3665607397827640236502865)
                  ·
                    refine ⟨2749205548370730177377149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665607397827640236502865 2749205548370730177377149)
                    ·
                      refine ⟨1030952080639023816516431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749205548370730177377149 1030952080639023816516431)
                      ·
                        rfl

theorem cell23_2007772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2007772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007772 prefixEnd_2007772 := by exact prefixLift 2007772
  have htrace : WordTrace (prefixWord ++ tailWord_2007772) baseStart_2007772 baseEnd_2007772 := by
    simpa [prefixWord, tailWord_2007772, baseEnd_2007772] using wordTrace_append hprefix tailTrace_2007772
  have hstable : (prefixWord ++ tailWord_2007772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007772).length < 2 ^ (prefixWord ++ tailWord_2007772).sum := by decide
  have hdescent : baseEnd_2007772 < baseStart_2007772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007785 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 3]
def baseStart_2007785 : Nat := 118140960795 + 2007785 * 2 ^ 59
def prefixEnd_2007785 : Nat := 4983230072969 + 3 ^ 40 * 2007785 * 2
def baseEnd_2007785 : Nat := 1030958755887532265653871

theorem tailTrace_2007785 : CollatzResearch.WordTrace tailWord_2007785 prefixEnd_2007785 1030958755887532265653871 := by
  unfold tailWord_2007785
  simp only [CollatzResearch.WordTrace]
  refine ⟨73229935031145322223256809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48819956687430214815504539 73229935031145322223256809)
  ·
    refine ⟨54922451273358991667442607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73229935031145322223256809 54922451273358991667442607)
    ·
      refine ⟨82383676910038487501163911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54922451273358991667442607 82383676910038487501163911)
      ·
        refine ⟨123575515365057731251745867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82383676910038487501163911 123575515365057731251745867)
        ·
          refine ⟨185363273047586596877618801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123575515365057731251745867 185363273047586596877618801)
          ·
            refine ⟨139022454785689947658214101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185363273047586596877618801 139022454785689947658214101)
            ·
              refine ⟨3258338784039608148239393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139022454785689947658214101 3258338784039608148239393)
              ·
                refine ⟨2443754088029706111179545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258338784039608148239393 2443754088029706111179545)
                ·
                  refine ⟨1832815566022279583384659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443754088029706111179545 1832815566022279583384659)
                  ·
                    refine ⟨2749223349033419375076989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832815566022279583384659 2749223349033419375076989)
                    ·
                      refine ⟨1030958755887532265653871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749223349033419375076989 1030958755887532265653871)
                      ·
                        rfl

theorem cell23_2007785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_2007785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007785 prefixEnd_2007785 := by exact prefixLift 2007785
  have htrace : WordTrace (prefixWord ++ tailWord_2007785) baseStart_2007785 baseEnd_2007785 := by
    simpa [prefixWord, tailWord_2007785, baseEnd_2007785] using wordTrace_append hprefix tailTrace_2007785
  have hstable : (prefixWord ++ tailWord_2007785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007785).length < 2 ^ (prefixWord ++ tailWord_2007785).sum := by decide
  have hdescent : baseEnd_2007785 < baseStart_2007785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007796 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2007796 : Nat := 118140960795 + 2007796 * 2 ^ 59
def prefixEnd_2007796 : Nat := 4983230072969 + 3 ^ 40 * 2007796 * 2
def baseEnd_2007796 : Nat := 343654801391577240872107

theorem tailTrace_2007796 : CollatzResearch.WordTrace tailWord_2007796 prefixEnd_2007796 343654801391577240872107 := by
  unfold tailWord_2007796
  simp only [CollatzResearch.WordTrace]
  refine ⟨36615168117052735550953621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48820224156070314067938161 36615168117052735550953621)
  ·
    refine ⟨1716336005486846978950951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36615168117052735550953621 1716336005486846978950951)
    ·
      refine ⟨2574504008230270468426427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716336005486846978950951 2574504008230270468426427)
      ·
        refine ⟨3861756012345405702639641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574504008230270468426427 3861756012345405702639641)
        ·
          refine ⟨2896317009259054276979731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3861756012345405702639641 2896317009259054276979731)
          ·
            refine ⟨4344475513888581415469597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896317009259054276979731 4344475513888581415469597)
            ·
              refine ⟨1629178317708218030801099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4344475513888581415469597 1629178317708218030801099)
              ·
                refine ⟨2443767476562327046201649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629178317708218030801099 2443767476562327046201649)
                ·
                  refine ⟨1832825607421745284651237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443767476562327046201649 1832825607421745284651237)
                  ·
                    refine ⟨343654801391577240872107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832825607421745284651237 343654801391577240872107)
                    ·
                      rfl

theorem cell23_2007796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2007796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007796 prefixEnd_2007796 := by exact prefixLift 2007796
  have htrace : WordTrace (prefixWord ++ tailWord_2007796) baseStart_2007796 baseEnd_2007796 := by
    simpa [prefixWord, tailWord_2007796, baseEnd_2007796] using wordTrace_append hprefix tailTrace_2007796
  have hstable : (prefixWord ++ tailWord_2007796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007796).length < 2 ^ (prefixWord ++ tailWord_2007796).sum := by decide
  have hdescent : baseEnd_2007796 < baseStart_2007796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007811 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_2007811 : Nat := 118140960795 + 2007811 * 2 ^ 59
def prefixEnd_2007811 : Nat := 4983230072969 + 3 ^ 40 * 2007811 * 2
def baseEnd_2007811 : Nat := 1030972106384549163928751

theorem tailTrace_2007811 : CollatzResearch.WordTrace tailWord_2007811 prefixEnd_2007811 1030972106384549163928751 := by
  unfold tailWord_2007811
  simp only [CollatzResearch.WordTrace]
  refine ⟨73230883329051128663703287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48820588886034085775802191 73230883329051128663703287)
  ·
    refine ⟨109846324993576692995554931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73230883329051128663703287 109846324993576692995554931)
    ·
      refine ⟨164769487490365039493332397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109846324993576692995554931 164769487490365039493332397)
      ·
        refine ⟨61788557808886889809999649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164769487490365039493332397 61788557808886889809999649)
        ·
          refine ⟨46341418356665167357499737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61788557808886889809999649 46341418356665167357499737)
          ·
            refine ⟨34756063767498875518124803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46341418356665167357499737 34756063767498875518124803)
            ·
              refine ⟨52134095651248313277187205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34756063767498875518124803 52134095651248313277187205)
              ·
                refine ⟨9775142934609058739472601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52134095651248313277187205 9775142934609058739472601)
                ·
                  refine ⟨7331357200956794054604451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775142934609058739472601 7331357200956794054604451)
                  ·
                    refine ⟨10997035801435191081906677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331357200956794054604451 10997035801435191081906677)
                    ·
                      refine ⟨1030972106384549163928751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10997035801435191081906677 1030972106384549163928751)
                      ·
                        rfl

theorem cell23_2007811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_2007811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007811 prefixEnd_2007811 := by exact prefixLift 2007811
  have htrace : WordTrace (prefixWord ++ tailWord_2007811) baseStart_2007811 baseEnd_2007811 := by
    simpa [prefixWord, tailWord_2007811, baseEnd_2007811] using wordTrace_append hprefix tailTrace_2007811
  have hstable : (prefixWord ++ tailWord_2007811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007811).length < 2 ^ (prefixWord ++ tailWord_2007811).sum := by decide
  have hdescent : baseEnd_2007811 < baseStart_2007811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007812 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2007812 : Nat := 118140960795 + 2007812 * 2 ^ 59
def prefixEnd_2007812 : Nat := 4983230072969 + 3 ^ 40 * 2007812 * 2
def baseEnd_2007812 : Nat := 1030972619865203660016247

theorem tailTrace_2007812 : CollatzResearch.WordTrace tailWord_2007812 prefixEnd_2007812 1030972619865203660016247 := by
  unfold tailWord_2007812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36615459901023752917244845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48820613201365003889659793 36615459901023752917244845)
  ·
    refine ⟨13730797462883907343966817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36615459901023752917244845 13730797462883907343966817)
    ·
      refine ⟨10298098097162930507975113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13730797462883907343966817 10298098097162930507975113)
      ·
        refine ⟨7723573572872197880981335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10298098097162930507975113 7723573572872197880981335)
        ·
          refine ⟨11585360359308296821472003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723573572872197880981335 11585360359308296821472003)
          ·
            refine ⟨17378040538962445232208005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585360359308296821472003 17378040538962445232208005)
            ·
              refine ⟨3258382601055458481039001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17378040538962445232208005 3258382601055458481039001)
              ·
                refine ⟨2443786950791593860779251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258382601055458481039001 2443786950791593860779251)
                ·
                  refine ⟨3665680426187390791168877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443786950791593860779251 3665680426187390791168877)
                  ·
                    refine ⟨1374630159820271546688329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3665680426187390791168877 1374630159820271546688329)
                    ·
                      refine ⟨1030972619865203660016247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374630159820271546688329 1030972619865203660016247)
                      ·
                        rfl

theorem cell23_2007812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2007812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007812 prefixEnd_2007812 := by exact prefixLift 2007812
  have htrace : WordTrace (prefixWord ++ tailWord_2007812) baseStart_2007812 baseEnd_2007812 := by
    simpa [prefixWord, tailWord_2007812, baseEnd_2007812] using wordTrace_append hprefix tailTrace_2007812
  have hstable : (prefixWord ++ tailWord_2007812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007812).length < 2 ^ (prefixWord ++ tailWord_2007812).sum := by decide
  have hdescent : baseEnd_2007812 < baseStart_2007812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007825 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_2007825 : Nat := 118140960795 + 2007825 * 2 ^ 59
def prefixEnd_2007825 : Nat := 4983230072969 + 3 ^ 40 * 2007825 * 2
def baseEnd_2007825 : Nat := 1030979295113712109153687

theorem tailTrace_2007825 : CollatzResearch.WordTrace tailWord_2007825 prefixEnd_2007825 1030979295113712109153687 := by
  unfold tailWord_2007825
  simp only [CollatzResearch.WordTrace]
  refine ⟨73231393951000409054712929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48820929300666939369808619 73231393951000409054712929)
  ·
    refine ⟨54923545463250306791034697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73231393951000409054712929 54923545463250306791034697)
    ·
      refine ⟨41192659097437730093276023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54923545463250306791034697 41192659097437730093276023)
      ·
        refine ⟨61788988646156595139914035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41192659097437730093276023 61788988646156595139914035)
        ·
          refine ⟨92683482969234892709871053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61788988646156595139914035 92683482969234892709871053)
          ·
            refine ⟨34756306113463084766201645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92683482969234892709871053 34756306113463084766201645)
            ·
              refine ⟨13033614792548656787325617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34756306113463084766201645 13033614792548656787325617)
              ·
                refine ⟨9775211094411492590494213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13033614792548656787325617 9775211094411492590494213)
                ·
                  refine ⟨1832852080202154860717665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9775211094411492590494213 1832852080202154860717665)
                  ·
                    refine ⟨1374639060151616145538249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832852080202154860717665 1374639060151616145538249)
                    ·
                      refine ⟨1030979295113712109153687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374639060151616145538249 1030979295113712109153687)
                      ·
                        rfl

theorem cell23_2007825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_2007825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007825 prefixEnd_2007825 := by exact prefixLift 2007825
  have htrace : WordTrace (prefixWord ++ tailWord_2007825) baseStart_2007825 baseEnd_2007825 := by
    simpa [prefixWord, tailWord_2007825, baseEnd_2007825] using wordTrace_append hprefix tailTrace_2007825
  have hstable : (prefixWord ++ tailWord_2007825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007825).length < 2 ^ (prefixWord ++ tailWord_2007825).sum := by decide
  have hdescent : baseEnd_2007825 < baseStart_2007825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007841 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2007841 : Nat := 118140960795 + 2007841 * 2 ^ 59
def prefixEnd_2007841 : Nat := 4983230072969 + 3 ^ 40 * 2007841 * 2
def baseEnd_2007841 : Nat := 1030987510804184046553613

theorem tailTrace_2007841 : CollatzResearch.WordTrace tailWord_2007841 prefixEnd_2007841 1030987510804184046553613 := by
  unfold tailWord_2007841
  simp only [CollatzResearch.WordTrace]
  refine ⟨73231977518942443787295377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48821318345961629191530251 73231977518942443787295377)
  ·
    refine ⟨54923983139206832840471533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73231977518942443787295377 54923983139206832840471533)
    ·
      refine ⟨20596493677202562315176825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54923983139206832840471533 20596493677202562315176825)
      ·
        refine ⟨15447370257901921736382619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20596493677202562315176825 15447370257901921736382619)
        ·
          refine ⟨23171055386852882604573929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447370257901921736382619 23171055386852882604573929)
          ·
            refine ⟨17378291540139661953430447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23171055386852882604573929 17378291540139661953430447)
            ·
              refine ⟨26067437310209492930145671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17378291540139661953430447 26067437310209492930145671)
              ·
                refine ⟨39101155965314239395218507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26067437310209492930145671 39101155965314239395218507)
                ·
                  refine ⟨58651733947971359092827761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39101155965314239395218507 58651733947971359092827761)
                  ·
                    refine ⟨43988800460978519319620821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58651733947971359092827761 43988800460978519319620821)
                    ·
                      refine ⟨1030987510804184046553613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43988800460978519319620821 1030987510804184046553613)
                      ·
                        rfl

theorem cell23_2007841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2007841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007841 prefixEnd_2007841 := by exact prefixLift 2007841
  have htrace : WordTrace (prefixWord ++ tailWord_2007841) baseStart_2007841 baseEnd_2007841 := by
    simpa [prefixWord, tailWord_2007841, baseEnd_2007841] using wordTrace_append hprefix tailTrace_2007841
  have hstable : (prefixWord ++ tailWord_2007841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007841).length < 2 ^ (prefixWord ++ tailWord_2007841).sum := by decide
  have hdescent : baseEnd_2007841 < baseStart_2007841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007842 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_2007842 : Nat := 118140960795 + 2007842 * 2 ^ 59
def prefixEnd_2007842 : Nat := 4983230072969 + 3 ^ 40 * 2007842 * 2
def baseEnd_2007842 : Nat := 1030988024284838542641109

theorem tailTrace_2007842 : CollatzResearch.WordTrace tailWord_2007842 prefixEnd_2007842 1030988024284838542641109 := by
  unfold tailWord_2007842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308003497984705239520445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48821342661292547305387853 18308003497984705239520445)
  ·
    refine ⟨6865501311744264464820167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18308003497984705239520445 6865501311744264464820167)
    ·
      refine ⟨10298251967616396697230251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865501311744264464820167 10298251967616396697230251)
      ·
        refine ⟨15447377951424595045845377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298251967616396697230251 15447377951424595045845377)
        ·
          refine ⟨11585533463568446284384033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15447377951424595045845377 11585533463568446284384033)
          ·
            refine ⟨8689150097676334713288025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11585533463568446284384033 8689150097676334713288025)
            ·
              refine ⟨6516862573257251034966019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689150097676334713288025 6516862573257251034966019)
              ·
                refine ⟨9775293859885876552449029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516862573257251034966019 9775293859885876552449029)
                ·
                  refine ⟨1832867598728601853584193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9775293859885876552449029 1832867598728601853584193)
                  ·
                    refine ⟨1374650699046451390188145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832867598728601853584193 1374650699046451390188145)
                    ·
                      refine ⟨1030988024284838542641109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374650699046451390188145 1030988024284838542641109)
                      ·
                        rfl

theorem cell23_2007842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_2007842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007842 prefixEnd_2007842 := by exact prefixLift 2007842
  have htrace : WordTrace (prefixWord ++ tailWord_2007842) baseStart_2007842 baseEnd_2007842 := by
    simpa [prefixWord, tailWord_2007842, baseEnd_2007842] using wordTrace_append hprefix tailTrace_2007842
  have hstable : (prefixWord ++ tailWord_2007842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007842).length < 2 ^ (prefixWord ++ tailWord_2007842).sum := by decide
  have hdescent : baseEnd_2007842 < baseStart_2007842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007853 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2007853 : Nat := 118140960795 + 2007853 * 2 ^ 59
def prefixEnd_2007853 : Nat := 4983230072969 + 3 ^ 40 * 2007853 * 2
def baseEnd_2007853 : Nat := 1030993672572037999603559

theorem tailTrace_2007853 : CollatzResearch.WordTrace tailWord_2007853 prefixEnd_2007853 1030993672572037999603559 := by
  unfold tailWord_2007853
  simp only [CollatzResearch.WordTrace]
  refine ⟨73232415194898969836732213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48821610129932646557821475 73232415194898969836732213)
  ·
    refine ⟨6865538924521778422193645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73232415194898969836732213 6865538924521778422193645)
    ·
      refine ⟨2574577096695666908322617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6865538924521778422193645 2574577096695666908322617)
      ·
        refine ⟨1930932822521750181241963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2574577096695666908322617 1930932822521750181241963)
        ·
          refine ⟨2896399233782625271862945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930932822521750181241963 2896399233782625271862945)
          ·
            refine ⟨2172299425336968953897209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2896399233782625271862945 2172299425336968953897209)
            ·
              refine ⟨1629224569002726715422907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172299425336968953897209 1629224569002726715422907)
              ·
                refine ⟨2443836853504090073134361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629224569002726715422907 2443836853504090073134361)
                ·
                  refine ⟨1832877640128067554850771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443836853504090073134361 1832877640128067554850771)
                  ·
                    refine ⟨2749316460192101332276157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1832877640128067554850771 2749316460192101332276157)
                    ·
                      refine ⟨1030993672572037999603559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749316460192101332276157 1030993672572037999603559)
                      ·
                        rfl

theorem cell23_2007853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2007853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007853 prefixEnd_2007853 := by exact prefixLift 2007853
  have htrace : WordTrace (prefixWord ++ tailWord_2007853) baseStart_2007853 baseEnd_2007853 := by
    simpa [prefixWord, tailWord_2007853, baseEnd_2007853] using wordTrace_append hprefix tailTrace_2007853
  have hstable : (prefixWord ++ tailWord_2007853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007853).length < 2 ^ (prefixWord ++ tailWord_2007853).sum := by decide
  have hdescent : baseEnd_2007853 < baseStart_2007853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007858 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2007858 : Nat := 118140960795 + 2007858 * 2 ^ 59
def prefixEnd_2007858 : Nat := 4983230072969 + 3 ^ 40 * 2007858 * 2
def baseEnd_2007858 : Nat := 1030996239975310480041035

theorem tailTrace_2007858 : CollatzResearch.WordTrace tailWord_2007858 prefixEnd_2007858 1030996239975310480041035 := by
  unfold tailWord_2007858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308149389970213922666057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48821731706587237127109485 18308149389970213922666057)
  ·
    refine ⟨13731112042477660441999543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18308149389970213922666057 13731112042477660441999543)
    ·
      refine ⟨20596668063716490662999315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13731112042477660441999543 20596668063716490662999315)
      ·
        refine ⟨30895002095574735994498973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20596668063716490662999315 30895002095574735994498973)
        ·
          refine ⟨11585625785840525997937115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30895002095574735994498973 11585625785840525997937115)
          ·
            refine ⟨17378438678760788996905673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11585625785840525997937115 17378438678760788996905673)
            ·
              refine ⟨13033829009070591747679255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17378438678760788996905673 13033829009070591747679255)
              ·
                refine ⟨19550743513605887621518883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13033829009070591747679255 19550743513605887621518883)
                ·
                  refine ⟨29326115270408831432278325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19550743513605887621518883 29326115270408831432278325)
                  ·
                    refine ⟨2749323306600827946776093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29326115270408831432278325 2749323306600827946776093)
                    ·
                      refine ⟨1030996239975310480041035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749323306600827946776093 1030996239975310480041035)
                      ·
                        rfl

theorem cell23_2007858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2007858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007858 prefixEnd_2007858 := by exact prefixLift 2007858
  have htrace : WordTrace (prefixWord ++ tailWord_2007858) baseStart_2007858 baseEnd_2007858 := by
    simpa [prefixWord, tailWord_2007858, baseEnd_2007858] using wordTrace_append hprefix tailTrace_2007858
  have hstable : (prefixWord ++ tailWord_2007858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007858).length < 2 ^ (prefixWord ++ tailWord_2007858).sum := by decide
  have hdescent : baseEnd_2007858 < baseStart_2007858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007859 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 2, 2, 2]
def baseStart_2007859 : Nat := 118140960795 + 2007859 * 2 ^ 59
def prefixEnd_2007859 : Nat := 4983230072969 + 3 ^ 40 * 2007859 * 2
def baseEnd_2007859 : Nat := 1030996753455964976128531

theorem tailTrace_2007859 : CollatzResearch.WordTrace tailWord_2007859 prefixEnd_2007859 1030996753455964976128531 := by
  unfold tailWord_2007859
  simp only [CollatzResearch.WordTrace]
  refine ⟨73232634032877232861450631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48821756021918155240967087 73232634032877232861450631)
  ·
    refine ⟨109848951049315849292175947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73232634032877232861450631 109848951049315849292175947)
    ·
      refine ⟨164773426573973773938263921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109848951049315849292175947 164773426573973773938263921)
      ·
        refine ⟨123580069930480330453697941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164773426573973773938263921 123580069930480330453697941)
        ·
          refine ⟨5792815777991265490017091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123580069930480330453697941 5792815777991265490017091)
          ·
            refine ⟨8689223666986898235025637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792815777991265490017091 8689223666986898235025637)
            ·
              refine ⟨1629229437560043419067307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8689223666986898235025637 1629229437560043419067307)
              ·
                refine ⟨2443844156340065128600961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629229437560043419067307 2443844156340065128600961)
                ·
                  refine ⟨1832883117255048846450721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2443844156340065128600961 1832883117255048846450721)
                  ·
                    refine ⟨1374662337941286634838041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832883117255048846450721 1374662337941286634838041)
                    ·
                      refine ⟨1030996753455964976128531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374662337941286634838041 1030996753455964976128531)
                      ·
                        rfl

theorem cell23_2007859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 2, 2, 2].length) (baseStart_2007859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007859 prefixEnd_2007859 := by exact prefixLift 2007859
  have htrace : WordTrace (prefixWord ++ tailWord_2007859) baseStart_2007859 baseEnd_2007859 := by
    simpa [prefixWord, tailWord_2007859, baseEnd_2007859] using wordTrace_append hprefix tailTrace_2007859
  have hstable : (prefixWord ++ tailWord_2007859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007859).length < 2 ^ (prefixWord ++ tailWord_2007859).sum := by decide
  have hdescent : baseEnd_2007859 < baseStart_2007859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007925 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2007925 : Nat := 118140960795 + 2007925 * 2 ^ 59
def prefixEnd_2007925 : Nat := 4983230072969 + 3 ^ 40 * 2007925 * 2
def baseEnd_2007925 : Nat := 343676881059720572634409

theorem tailTrace_2007925 : CollatzResearch.WordTrace tailWord_2007925 prefixEnd_2007925 343676881059720572634409 := by
  unfold tailWord_2007925
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235041250638126133353229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48823360833758750755568819 73235041250638126133353229)
  ·
    refine ⟨27463140468989297300007461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73235041250638126133353229 27463140468989297300007461)
    ·
      refine ⟨5149338837935493243751399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27463140468989297300007461 5149338837935493243751399)
      ·
        refine ⟨7724008256903239865627099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5149338837935493243751399 7724008256903239865627099)
        ·
          refine ⟨11586012385354859798440649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724008256903239865627099 11586012385354859798440649)
          ·
            refine ⟨8689509289016144848830487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11586012385354859798440649 8689509289016144848830487)
            ·
              refine ⟨13034263933524217273245731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689509289016144848830487 13034263933524217273245731)
              ·
                refine ⟨19551395900286325909868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13034263933524217273245731 19551395900286325909868597)
                ·
                  refine ⟨1832943365651843054050181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19551395900286325909868597 1832943365651843054050181)
                  ·
                    refine ⟨343676881059720572634409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1832943365651843054050181 343676881059720572634409)
                    ·
                      rfl

theorem cell23_2007925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2007925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007925 prefixEnd_2007925 := by exact prefixLift 2007925
  have htrace : WordTrace (prefixWord ++ tailWord_2007925) baseStart_2007925 baseEnd_2007925 := by
    simpa [prefixWord, tailWord_2007925, baseEnd_2007925] using wordTrace_append hprefix tailTrace_2007925
  have hstable : (prefixWord ++ tailWord_2007925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007925).length < 2 ^ (prefixWord ++ tailWord_2007925).sum := by decide
  have hdescent : baseEnd_2007925 < baseStart_2007925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007935 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_2007935 : Nat := 118140960795 + 2007935 * 2 ^ 59
def prefixEnd_2007935 : Nat := 4983230072969 + 3 ^ 40 * 2007935 * 2
def baseEnd_2007935 : Nat := 1031035777985706678778181

theorem tailTrace_2007935 : CollatzResearch.WordTrace tailWord_2007935 prefixEnd_2007935 1031035777985706678778181 := by
  unfold tailWord_2007935
  simp only [CollatzResearch.WordTrace]
  refine ⟨73235405980601897841217259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48823603987067931894144839 73235405980601897841217259)
  ·
    refine ⟨109853108970902846761825889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73235405980601897841217259 109853108970902846761825889)
    ·
      refine ⟨82389831728177135071369417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109853108970902846761825889 82389831728177135071369417)
      ·
        refine ⟨61792373796132851303527063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82389831728177135071369417 61792373796132851303527063)
        ·
          refine ⟨92688560694199276955290595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61792373796132851303527063 92688560694199276955290595)
          ·
            refine ⟨139032841041298915432935893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92688560694199276955290595 139032841041298915432935893)
            ·
              refine ⟨3258582211905443330459435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139032841041298915432935893 3258582211905443330459435)
              ·
                refine ⟨4887873317858164995689153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258582211905443330459435 4887873317858164995689153)
                ·
                  refine ⟨3665904988393623746766865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887873317858164995689153 3665904988393623746766865)
                  ·
                    refine ⟨2749428741295217810075149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3665904988393623746766865 2749428741295217810075149)
                    ·
                      refine ⟨1031035777985706678778181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749428741295217810075149 1031035777985706678778181)
                      ·
                        rfl

theorem cell23_2007935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_2007935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007935 prefixEnd_2007935 := by exact prefixLift 2007935
  have htrace : WordTrace (prefixWord ++ tailWord_2007935) baseStart_2007935 baseEnd_2007935 := by
    simpa [prefixWord, tailWord_2007935, baseEnd_2007935] using wordTrace_append hprefix tailTrace_2007935
  have hstable : (prefixWord ++ tailWord_2007935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007935).length < 2 ^ (prefixWord ++ tailWord_2007935).sum := by decide
  have hdescent : baseEnd_2007935 < baseStart_2007935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2007968 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_2007968 : Nat := 118140960795 + 2007968 * 2 ^ 59
def prefixEnd_2007968 : Nat := 4983230072969 + 3 ^ 40 * 2007968 * 2
def baseEnd_2007968 : Nat := 343684240949101683221843

theorem tailTrace_2007968 : CollatzResearch.WordTrace tailWord_2007968 prefixEnd_2007968 343684240949101683221843 := by
  unfold tailWord_2007968
  simp only [CollatzResearch.WordTrace]
  refine ⟨36618304794741172238584279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48824406392988229651445705 36618304794741172238584279)
  ·
    refine ⟨54927457192111758357876419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36618304794741172238584279 54927457192111758357876419)
    ·
      refine ⟨82391185788167637536814629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54927457192111758357876419 82391185788167637536814629)
      ·
        refine ⟨15448347335281432038152743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82391185788167637536814629 15448347335281432038152743)
        ·
          refine ⟨23172521002922148057229115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15448347335281432038152743 23172521002922148057229115)
          ·
            refine ⟨34758781504383222085843673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23172521002922148057229115 34758781504383222085843673)
            ·
              refine ⟨26069086128287416564382755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34758781504383222085843673 26069086128287416564382755)
              ·
                refine ⟨39103629192431124846574133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26069086128287416564382755 39103629192431124846574133)
                ·
                  refine ⟨3665965236790417954366325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39103629192431124846574133 3665965236790417954366325)
                  ·
                    refine ⟨343684240949101683221843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3665965236790417954366325 343684240949101683221843)
                    ·
                      rfl

theorem cell23_2007968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_2007968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2007968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2007968 prefixEnd_2007968 := by exact prefixLift 2007968
  have htrace : WordTrace (prefixWord ++ tailWord_2007968) baseStart_2007968 baseEnd_2007968 := by
    simpa [prefixWord, tailWord_2007968, baseEnd_2007968] using wordTrace_append hprefix tailTrace_2007968
  have hstable : (prefixWord ++ tailWord_2007968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2007968).length < 2 ^ (prefixWord ++ tailWord_2007968).sum := by decide
  have hdescent : baseEnd_2007968 < baseStart_2007968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2007968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008015 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 4, 4]
def baseStart_2008015 : Nat := 118140960795 + 2008015 * 2 ^ 59
def prefixEnd_2008015 : Nat := 4983230072969 + 3 ^ 40 * 2008015 * 2
def baseEnd_2008015 : Nat := 343692285479355455259271

theorem tailTrace_2008015 : CollatzResearch.WordTrace tailWord_2008015 prefixEnd_2008015 343692285479355455259271 := by
  unfold tailWord_2008015
  simp only [CollatzResearch.WordTrace]
  refine ⟨73238323820312071504129499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48825549213541381002752999 73238323820312071504129499)
  ·
    refine ⟨109857485730468107256194249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73238323820312071504129499 109857485730468107256194249)
    ·
      refine ⟨82393114297851080442145687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109857485730468107256194249 82393114297851080442145687)
      ·
        refine ⟨123589671446776620663218531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82393114297851080442145687 123589671446776620663218531)
        ·
          refine ⟨185384507170164930994827797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123589671446776620663218531 185384507170164930994827797)
          ·
            refine ⟨8689898773601481140382553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185384507170164930994827797 8689898773601481140382553)
            ·
              refine ⟨6517424080201110855286915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689898773601481140382553 6517424080201110855286915)
              ·
                refine ⟨9776136120301666282930373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517424080201110855286915 9776136120301666282930373)
                ·
                  refine ⟨1833025522556562428049445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9776136120301666282930373 1833025522556562428049445)
                  ·
                    refine ⟨343692285479355455259271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833025522556562428049445 343692285479355455259271)
                    ·
                      rfl

theorem cell23_2008015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_2008015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008015 prefixEnd_2008015 := by exact prefixLift 2008015
  have htrace : WordTrace (prefixWord ++ tailWord_2008015) baseStart_2008015 baseEnd_2008015 := by
    simpa [prefixWord, tailWord_2008015, baseEnd_2008015] using wordTrace_append hprefix tailTrace_2008015
  have hstable : (prefixWord ++ tailWord_2008015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008015).length < 2 ^ (prefixWord ++ tailWord_2008015).sum := by decide
  have hdescent : baseEnd_2008015 < baseStart_2008015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008025 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_2008025 : Nat := 118140960795 + 2008025 * 2 ^ 59
def prefixEnd_2008025 : Nat := 4983230072969 + 3 ^ 40 * 2008025 * 2
def baseEnd_2008025 : Nat := 1031081991244611326652767

theorem tailTrace_2008025 : CollatzResearch.WordTrace tailWord_2008025 prefixEnd_2008025 1031081991244611326652767 := by
  unfold tailWord_2008025
  simp only [CollatzResearch.WordTrace]
  refine ⟨73238688550275843211993529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48825792366850562141329019 73238688550275843211993529)
  ·
    refine ⟨54929016412706882408995147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73238688550275843211993529 54929016412706882408995147)
    ·
      refine ⟨82393524619060323613492721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54929016412706882408995147 82393524619060323613492721)
      ·
        refine ⟨61795143464295242710119541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82393524619060323613492721 61795143464295242710119541)
        ·
          refine ⟨5793294699777679004073707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61795143464295242710119541 5793294699777679004073707)
          ·
            refine ⟨8689942049666518506110561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793294699777679004073707 8689942049666518506110561)
            ·
              refine ⟨6517456537249888879582921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689942049666518506110561 6517456537249888879582921)
              ·
                refine ⟨4888092402937416659687191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517456537249888879582921 4888092402937416659687191)
                ·
                  refine ⟨7332138604406124989530787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888092402937416659687191 7332138604406124989530787)
                  ·
                    refine ⟨10998207906609187484296181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7332138604406124989530787 10998207906609187484296181)
                    ·
                      refine ⟨1031081991244611326652767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10998207906609187484296181 1031081991244611326652767)
                      ·
                        rfl

theorem cell23_2008025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_2008025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008025 prefixEnd_2008025 := by exact prefixLift 2008025
  have htrace : WordTrace (prefixWord ++ tailWord_2008025) baseStart_2008025 baseEnd_2008025 := by
    simpa [prefixWord, tailWord_2008025, baseEnd_2008025] using wordTrace_append hprefix tailTrace_2008025
  have hstable : (prefixWord ++ tailWord_2008025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008025).length < 2 ^ (prefixWord ++ tailWord_2008025).sum := by decide
  have hdescent : baseEnd_2008025 < baseStart_2008025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008035 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2008035 : Nat := 118140960795 + 2008035 * 2 ^ 59
def prefixEnd_2008035 : Nat := 4983230072969 + 3 ^ 40 * 2008035 * 2
def baseEnd_2008035 : Nat := 1031087126051156287527721

theorem tailTrace_2008035 : CollatzResearch.WordTrace tailWord_2008035 prefixEnd_2008035 1031087126051156287527721 := by
  unfold tailWord_2008035
  simp only [CollatzResearch.WordTrace]
  refine ⟨73239053280239614919857559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48826035520159743279905039 73239053280239614919857559)
  ·
    refine ⟨109858579920359422379786339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73239053280239614919857559 109858579920359422379786339)
    ·
      refine ⟨164787869880539133569679509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109858579920359422379786339 164787869880539133569679509)
      ·
        refine ⟨7724431400650271886078727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164787869880539133569679509 7724431400650271886078727)
        ·
          refine ⟨11586647100975407829118091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724431400650271886078727 11586647100975407829118091)
          ·
            refine ⟨17379970651463111743677137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586647100975407829118091 17379970651463111743677137)
            ·
              refine ⟨13034977988597333807757853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17379970651463111743677137 13034977988597333807757853)
              ·
                refine ⟨4888116745724000177909195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13034977988597333807757853 4888116745724000177909195)
                ·
                  refine ⟨7332175118586000266863793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888116745724000177909195 7332175118586000266863793)
                  ·
                    refine ⟨5499131338939500200147845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7332175118586000266863793 5499131338939500200147845)
                    ·
                      refine ⟨1031087126051156287527721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5499131338939500200147845 1031087126051156287527721)
                      ·
                        rfl

theorem cell23_2008035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2008035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008035 prefixEnd_2008035 := by exact prefixLift 2008035
  have htrace : WordTrace (prefixWord ++ tailWord_2008035) baseStart_2008035 baseEnd_2008035 := by
    simpa [prefixWord, tailWord_2008035, baseEnd_2008035] using wordTrace_append hprefix tailTrace_2008035
  have hstable : (prefixWord ++ tailWord_2008035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008035).length < 2 ^ (prefixWord ++ tailWord_2008035).sum := by decide
  have hdescent : baseEnd_2008035 < baseStart_2008035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008039 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2008039 : Nat := 118140960795 + 2008039 * 2 ^ 59
def prefixEnd_2008039 : Nat := 4983230072969 + 3 ^ 40 * 2008039 * 2
def baseEnd_2008039 : Nat := 1031089179973774271877703

theorem tailTrace_2008039 : CollatzResearch.WordTrace tailWord_2008039 prefixEnd_2008039 1031089179973774271877703 := by
  unfold tailWord_2008039
  simp only [CollatzResearch.WordTrace]
  refine ⟨73239199172225123603003171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48826132781483415735335447 73239199172225123603003171)
  ·
    refine ⟨109858798758337685404504757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73239199172225123603003171 109858798758337685404504757)
    ·
      refine ⟨10299262383594158006672321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109858798758337685404504757 10299262383594158006672321)
      ·
        refine ⟨7724446787695618505004241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10299262383594158006672321 7724446787695618505004241)
        ·
          refine ⟨5793335090771713878753181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7724446787695618505004241 5793335090771713878753181)
          ·
            refine ⟨2172500659039392704532443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5793335090771713878753181 2172500659039392704532443)
            ·
              refine ⟨3258750988559089056798665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172500659039392704532443 3258750988559089056798665)
              ·
                refine ⟨2444063241419316792598999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258750988559089056798665 2444063241419316792598999)
                ·
                  refine ⟨3666094862128975188898499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444063241419316792598999 3666094862128975188898499)
                  ·
                    refine ⟨5499142293193462783347749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666094862128975188898499 5499142293193462783347749)
                    ·
                      refine ⟨1031089179973774271877703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5499142293193462783347749 1031089179973774271877703)
                      ·
                        rfl

theorem cell23_2008039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2008039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008039 prefixEnd_2008039 := by exact prefixLift 2008039
  have htrace : WordTrace (prefixWord ++ tailWord_2008039) baseStart_2008039 baseEnd_2008039 := by
    simpa [prefixWord, tailWord_2008039, baseEnd_2008039] using wordTrace_append hprefix tailTrace_2008039
  have hstable : (prefixWord ++ tailWord_2008039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008039).length < 2 ^ (prefixWord ++ tailWord_2008039).sum := by decide
  have hdescent : baseEnd_2008039 < baseStart_2008039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008042 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2008042 : Nat := 118140960795 + 2008042 * 2 ^ 59
def prefixEnd_2008042 : Nat := 4983230072969 + 3 ^ 40 * 2008042 * 2
def baseEnd_2008042 : Nat := 1031090720415737760140189

theorem tailTrace_2008042 : CollatzResearch.WordTrace tailWord_2008042 prefixEnd_2008042 1031090720415737760140189 := by
  unfold tailWord_2008042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309827147803563778840595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48826205727476170076908253 18309827147803563778840595)
  ·
    refine ⟨27464740721705345668260893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309827147803563778840595 27464740721705345668260893)
    ·
      refine ⟨10299277770639504625597835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27464740721705345668260893 10299277770639504625597835)
      ·
        refine ⟨15448916655959256938396753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299277770639504625597835 15448916655959256938396753)
        ·
          refine ⟨11586687491969442703797565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15448916655959256938396753 11586687491969442703797565)
          ·
            refine ⟨4345007809488541013924087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11586687491969442703797565 4345007809488541013924087)
            ·
              refine ⟨6517511714232811520886131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345007809488541013924087 6517511714232811520886131)
              ·
                refine ⟨9776267571349217281329197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517511714232811520886131 9776267571349217281329197)
                ·
                  refine ⟨3666100339255956480498449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9776267571349217281329197 3666100339255956480498449)
                  ·
                    refine ⟨2749575254441967360373837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666100339255956480498449 2749575254441967360373837)
                    ·
                      refine ⟨1031090720415737760140189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749575254441967360373837 1031090720415737760140189)
                      ·
                        rfl

theorem cell23_2008042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2008042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008042 prefixEnd_2008042 := by exact prefixLift 2008042
  have htrace : WordTrace (prefixWord ++ tailWord_2008042) baseStart_2008042 baseEnd_2008042 := by
    simpa [prefixWord, tailWord_2008042, baseEnd_2008042] using wordTrace_append hprefix tailTrace_2008042
  have hstable : (prefixWord ++ tailWord_2008042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008042).length < 2 ^ (prefixWord ++ tailWord_2008042).sum := by decide
  have hdescent : baseEnd_2008042 < baseStart_2008042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008058 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_2008058 : Nat := 118140960795 + 2008058 * 2 ^ 59
def prefixEnd_2008058 : Nat := 4983230072969 + 3 ^ 40 * 2008058 * 2
def baseEnd_2008058 : Nat := 343699645368736565846705

theorem tailTrace_2008058 : CollatzResearch.WordTrace tailWord_2008058 prefixEnd_2008058 343699645368736565846705 := by
  unfold tailWord_2008058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309973039789072461986207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48826594772770859898629885 18309973039789072461986207)
  ·
    refine ⟨27464959559683608692979311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309973039789072461986207 27464959559683608692979311)
    ·
      refine ⟨41197439339525413039468967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27464959559683608692979311 41197439339525413039468967)
      ·
        refine ⟨61796159009288119559203451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41197439339525413039468967 61796159009288119559203451)
        ·
          refine ⟨92694238513932179338805177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61796159009288119559203451 92694238513932179338805177)
          ·
            refine ⟨69520678885449134504103883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92694238513932179338805177 69520678885449134504103883)
            ·
              refine ⟨104281018328173701756155825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69520678885449134504103883 104281018328173701756155825)
              ·
                refine ⟨78210763746130276317116869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104281018328173701756155825 78210763746130276317116869)
                ·
                  refine ⟨14664518202399426809459413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78210763746130276317116869 14664518202399426809459413)
                  ·
                    refine ⟨343699645368736565846705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14664518202399426809459413 343699645368736565846705)
                    ·
                      rfl

theorem cell23_2008058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_2008058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008058 prefixEnd_2008058 := by exact prefixLift 2008058
  have htrace : WordTrace (prefixWord ++ tailWord_2008058) baseStart_2008058 baseEnd_2008058 := by
    simpa [prefixWord, tailWord_2008058, baseEnd_2008058] using wordTrace_append hprefix tailTrace_2008058
  have hstable : (prefixWord ++ tailWord_2008058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008058).length < 2 ^ (prefixWord ++ tailWord_2008058).sum := by decide
  have hdescent : baseEnd_2008058 < baseStart_2008058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008062 : List Nat := [4, 2, 2, 2, 3, 10]
def baseStart_2008062 : Nat := 118140960795 + 2008062 * 2 ^ 59
def prefixEnd_2008062 : Nat := 4983230072969 + 3 ^ 40 * 2008062 * 2
def baseEnd_2008062 : Nat := 4243213950735916386379

theorem tailTrace_2008062 : CollatzResearch.WordTrace tailWord_2008062 prefixEnd_2008062 4243213950735916386379 := by
  unfold tailWord_2008062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155004756392724816386305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48826692034094532354060293 9155004756392724816386305)
  ·
    refine ⟨6866253567294543612289729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9155004756392724816386305 6866253567294543612289729)
    ·
      refine ⟨5149690175470907709217297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6866253567294543612289729 5149690175470907709217297)
      ·
        refine ⟨3862267631603180781912973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5149690175470907709217297 3862267631603180781912973)
        ·
          refine ⟨1448350361851192793217365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3862267631603180781912973 1448350361851192793217365)
          ·
            refine ⟨4243213950735916386379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1448350361851192793217365 4243213950735916386379)
            ·
              rfl

theorem cell23_2008062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 10].length) (baseStart_2008062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008062 prefixEnd_2008062 := by exact prefixLift 2008062
  have htrace : WordTrace (prefixWord ++ tailWord_2008062) baseStart_2008062 baseEnd_2008062 := by
    simpa [prefixWord, tailWord_2008062, baseEnd_2008062] using wordTrace_append hprefix tailTrace_2008062
  have hstable : (prefixWord ++ tailWord_2008062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008062).length < 2 ^ (prefixWord ++ tailWord_2008062).sum := by decide
  have hdescent : baseEnd_2008062 < baseStart_2008062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008112 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2]
def baseStart_2008112 : Nat := 118140960795 + 2008112 * 2 ^ 59
def prefixEnd_2008112 : Nat := 4983230072969 + 3 ^ 40 * 2008112 * 2
def baseEnd_2008112 : Nat := 1031126664061552486264867

theorem tailTrace_2008112 : CollatzResearch.WordTrace tailWord_2008112 prefixEnd_2008112 1031126664061552486264867 := by
  unfold tailWord_2008112
  simp only [CollatzResearch.WordTrace]
  refine ⟨36620930850480328535205295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48827907800640438046940393 36620930850480328535205295)
  ·
    refine ⟨54931396275720492802807943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36620930850480328535205295 54931396275720492802807943)
    ·
      refine ⟨82397094413580739204211915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54931396275720492802807943 82397094413580739204211915)
      ·
        refine ⟨123595641620371108806317873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82397094413580739204211915 123595641620371108806317873)
        ·
          refine ⟨92696731215278331604738405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123595641620371108806317873 92696731215278331604738405)
          ·
            refine ⟨17380637102864687175888451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92696731215278331604738405 17380637102864687175888451)
            ·
              refine ⟨26070955654297030763832677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17380637102864687175888451 26070955654297030763832677)
              ·
                refine ⟨4888304185180693268218627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26070955654297030763832677 4888304185180693268218627)
                ·
                  refine ⟨7332456277771039902327941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888304185180693268218627 7332456277771039902327941)
                  ·
                    refine ⟨1374835552082069981686489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332456277771039902327941 1374835552082069981686489)
                    ·
                      refine ⟨1031126664061552486264867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374835552082069981686489 1031126664061552486264867)
                      ·
                        rfl

theorem cell23_2008112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2].length) (baseStart_2008112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008112 prefixEnd_2008112 := by exact prefixLift 2008112
  have htrace : WordTrace (prefixWord ++ tailWord_2008112) baseStart_2008112 baseEnd_2008112 := by
    simpa [prefixWord, tailWord_2008112, baseEnd_2008112] using wordTrace_append hprefix tailTrace_2008112
  have hstable : (prefixWord ++ tailWord_2008112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008112).length < 2 ^ (prefixWord ++ tailWord_2008112).sum := by decide
  have hdescent : baseEnd_2008112 < baseStart_2008112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008135 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 7]
def baseStart_2008135 : Nat := 118140960795 + 2008135 * 2 ^ 59
def prefixEnd_2008135 : Nat := 4983230072969 + 3 ^ 40 * 2008135 * 2
def baseEnd_2008135 : Nat := 114570941568511766253029

theorem tailTrace_2008135 : CollatzResearch.WordTrace tailWord_2008135 prefixEnd_2008135 114570941568511766253029 := by
  unfold tailWord_2008135
  simp only [CollatzResearch.WordTrace]
  refine ⟨73242700579877331998497859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48828467053251554665665239 73242700579877331998497859)
  ·
    refine ⟨109864050869815997997746789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73242700579877331998497859 109864050869815997997746789)
    ·
      refine ⟨20599509538090499624577523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109864050869815997997746789 20599509538090499624577523)
      ·
        refine ⟨30899264307135749436866285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20599509538090499624577523 30899264307135749436866285)
        ·
          refine ⟨11587224115175906038824857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30899264307135749436866285 11587224115175906038824857)
          ·
            refine ⟨8690418086381929529118643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11587224115175906038824857 8690418086381929529118643)
            ·
              refine ⟨13035627129572894293677965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690418086381929529118643 13035627129572894293677965)
              ·
                refine ⟨4888360173589835360129237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13035627129572894293677965 4888360173589835360129237)
                ·
                  refine ⟨114570941568511766253029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4888360173589835360129237 114570941568511766253029)
                  ·
                    rfl

theorem cell23_2008135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 7].length) (baseStart_2008135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008135 prefixEnd_2008135 := by exact prefixLift 2008135
  have htrace : WordTrace (prefixWord ++ tailWord_2008135) baseStart_2008135 baseEnd_2008135 := by
    simpa [prefixWord, tailWord_2008135, baseEnd_2008135] using wordTrace_append hprefix tailTrace_2008135
  have hstable : (prefixWord ++ tailWord_2008135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008135).length < 2 ^ (prefixWord ++ tailWord_2008135).sum := by decide
  have hdescent : baseEnd_2008135 < baseStart_2008135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008146 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_2008146 : Nat := 118140960795 + 2008146 * 2 ^ 59
def prefixEnd_2008146 : Nat := 4983230072969 + 3 ^ 40 * 2008146 * 2
def baseEnd_2008146 : Nat := 1031144122403805353239711

theorem tailTrace_2008146 : CollatzResearch.WordTrace tailWord_2008146 prefixEnd_2008146 1031144122403805353239711 := by
  unfold tailWord_2008146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18310775445709370219287073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48828734521891653918098861 18310775445709370219287073)
  ·
    refine ⟨13733081584282027664465305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18310775445709370219287073 13733081584282027664465305)
    ·
      refine ⟨10299811188211520748348979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13733081584282027664465305 10299811188211520748348979)
      ·
        refine ⟨15449716782317281122523469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299811188211520748348979 15449716782317281122523469)
        ·
          refine ⟨5793643793368980420946301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15449716782317281122523469 5793643793368980420946301)
          ·
            refine ⟨2172616422513367657854863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5793643793368980420946301 2172616422513367657854863)
            ·
              refine ⟨3258924633770051486782295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172616422513367657854863 3258924633770051486782295)
              ·
                refine ⟨4888386950655077230173443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258924633770051486782295 4888386950655077230173443)
                ·
                  refine ⟨7332580425982615845260165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888386950655077230173443 7332580425982615845260165)
                  ·
                    refine ⟨1374858829871740470986281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7332580425982615845260165 1374858829871740470986281)
                    ·
                      refine ⟨1031144122403805353239711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374858829871740470986281 1031144122403805353239711)
                      ·
                        rfl

theorem cell23_2008146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_2008146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008146 prefixEnd_2008146 := by exact prefixLift 2008146
  have htrace : WordTrace (prefixWord ++ tailWord_2008146) baseStart_2008146 baseEnd_2008146 := by
    simpa [prefixWord, tailWord_2008146, baseEnd_2008146] using wordTrace_append hprefix tailTrace_2008146
  have hstable : (prefixWord ++ tailWord_2008146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008146).length < 2 ^ (prefixWord ++ tailWord_2008146).sum := by decide
  have hdescent : baseEnd_2008146 < baseStart_2008146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008150 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2008150 : Nat := 118140960795 + 2008150 * 2 ^ 59
def prefixEnd_2008150 : Nat := 4983230072969 + 3 ^ 40 * 2008150 * 2
def baseEnd_2008150 : Nat := 1031146176326423337589693

theorem tailTrace_2008150 : CollatzResearch.WordTrace tailWord_2008150 prefixEnd_2008150 1031146176326423337589693 := by
  unfold tailWord_2008150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577702979676436847518369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48828831783215326373529269 4577702979676436847518369)
  ·
    refine ⟨3433277234757327635638777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4577702979676436847518369 3433277234757327635638777)
    ·
      refine ⟨2574957926067995726729083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3433277234757327635638777 2574957926067995726729083)
      ·
        refine ⟨3862436889101993590093625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574957926067995726729083 3862436889101993590093625)
        ·
          refine ⟨2896827666826495192570219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862436889101993590093625 2896827666826495192570219)
          ·
            refine ⟨4345241500239742788855329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896827666826495192570219 4345241500239742788855329)
            ·
              refine ⟨3258931125179807091641497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345241500239742788855329 3258931125179807091641497)
              ·
                refine ⟨2444198343884855318731123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3258931125179807091641497 2444198343884855318731123)
                ·
                  refine ⟨3666297515827282978096685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444198343884855318731123 3666297515827282978096685)
                  ·
                    refine ⟨1374861568435231116786257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666297515827282978096685 1374861568435231116786257)
                    ·
                      refine ⟨1031146176326423337589693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1374861568435231116786257 1031146176326423337589693)
                      ·
                        rfl

theorem cell23_2008150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2008150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008150 prefixEnd_2008150 := by exact prefixLift 2008150
  have htrace : WordTrace (prefixWord ++ tailWord_2008150) baseStart_2008150 baseEnd_2008150 := by
    simpa [prefixWord, tailWord_2008150, baseEnd_2008150] using wordTrace_append hprefix tailTrace_2008150
  have hstable : (prefixWord ++ tailWord_2008150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008150).length < 2 ^ (prefixWord ++ tailWord_2008150).sum := by decide
  have hdescent : baseEnd_2008150 < baseStart_2008150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008165 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_2008165 : Nat := 118140960795 + 2008165 * 2 ^ 59
def prefixEnd_2008165 : Nat := 4983230072969 + 3 ^ 40 * 2008165 * 2
def baseEnd_2008165 : Nat := 343717959512080259634041

theorem tailTrace_2008165 : CollatzResearch.WordTrace tailWord_2008165 prefixEnd_2008165 343717959512080259634041 := by
  unfold tailWord_2008165
  simp only [CollatzResearch.WordTrace]
  refine ⟨73243794769768647122089949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48829196513179098081393299 73243794769768647122089949)
  ·
    refine ⟨27466423038663242670783731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73243794769768647122089949 27466423038663242670783731)
    ·
      refine ⟨41199634557994864006175597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27466423038663242670783731 41199634557994864006175597)
      ·
        refine ⟨15449862959248074002315849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41199634557994864006175597 15449862959248074002315849)
        ·
          refine ⟨11587397219436055501736887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15449862959248074002315849 11587397219436055501736887)
          ·
            refine ⟨17381095829154083252605331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11587397219436055501736887 17381095829154083252605331)
            ·
              refine ⟨26071643743731124878907997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17381095829154083252605331 26071643743731124878907997)
              ·
                refine ⟨9776866403899171829590499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26071643743731124878907997 9776866403899171829590499)
                ·
                  refine ⟨14665299605848757744385749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776866403899171829590499 14665299605848757744385749)
                  ·
                    refine ⟨343717959512080259634041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14665299605848757744385749 343717959512080259634041)
                    ·
                      rfl

theorem cell23_2008165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_2008165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008165 prefixEnd_2008165 := by exact prefixLift 2008165
  have htrace : WordTrace (prefixWord ++ tailWord_2008165) baseStart_2008165 baseEnd_2008165 := by
    simpa [prefixWord, tailWord_2008165, baseEnd_2008165] using wordTrace_append hprefix tailTrace_2008165
  have hstable : (prefixWord ++ tailWord_2008165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008165).length < 2 ^ (prefixWord ++ tailWord_2008165).sum := by decide
  have hdescent : baseEnd_2008165 < baseStart_2008165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008169 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 5]
def baseStart_2008169 : Nat := 118140960795 + 2008169 * 2 ^ 59
def prefixEnd_2008169 : Nat := 4983230072969 + 3 ^ 40 * 2008169 * 2
def baseEnd_2008169 : Nat := 114572881384317640361345

theorem tailTrace_2008169 : CollatzResearch.WordTrace tailWord_2008169 prefixEnd_2008169 114572881384317640361345 := by
  unfold tailWord_2008169
  simp only [CollatzResearch.WordTrace]
  refine ⟨73243940661754155805235561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48829293774502770536823707 73243940661754155805235561)
  ·
    refine ⟨54932955496315616853926671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73243940661754155805235561 54932955496315616853926671)
    ·
      refine ⟨82399433244473425280890007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54932955496315616853926671 82399433244473425280890007)
      ·
        refine ⟨123599149866710137921335011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82399433244473425280890007 123599149866710137921335011)
        ·
          refine ⟨185398724800065206882002517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123599149866710137921335011 185398724800065206882002517)
          ·
            refine ⟨2172641306250764143148467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 185398724800065206882002517 2172641306250764143148467)
            ·
              refine ⟨3258961959376146214722701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172641306250764143148467 3258961959376146214722701)
              ·
                refine ⟨1222110734766054830521013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3258961959376146214722701 1222110734766054830521013)
                ·
                  refine ⟨114572881384317640361345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222110734766054830521013 114572881384317640361345)
                  ·
                    rfl

theorem cell23_2008169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 5].length) (baseStart_2008169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008169 prefixEnd_2008169 := by exact prefixLift 2008169
  have htrace : WordTrace (prefixWord ++ tailWord_2008169) baseStart_2008169 baseEnd_2008169 := by
    simpa [prefixWord, tailWord_2008169, baseEnd_2008169] using wordTrace_append hprefix tailTrace_2008169
  have hstable : (prefixWord ++ tailWord_2008169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008169).length < 2 ^ (prefixWord ++ tailWord_2008169).sum := by decide
  have hdescent : baseEnd_2008169 < baseStart_2008169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008175 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_2008175 : Nat := 118140960795 + 2008175 * 2 ^ 59
def prefixEnd_2008175 : Nat := 4983230072969 + 3 ^ 40 * 2008175 * 2
def baseEnd_2008175 : Nat := 1031159013342785739777077

theorem tailTrace_2008175 : CollatzResearch.WordTrace tailWord_2008175 prefixEnd_2008175 1031159013342785739777077 := by
  unfold tailWord_2008175
  simp only [CollatzResearch.WordTrace]
  refine ⟨73244159499732418829953979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48829439666488279219969319 73244159499732418829953979)
  ·
    refine ⟨109866239249598628244930969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73244159499732418829953979 109866239249598628244930969)
    ·
      refine ⟨82399679437198971183698227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109866239249598628244930969 82399679437198971183698227)
      ·
        refine ⟨123599519155798456775547341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82399679437198971183698227 123599519155798456775547341)
        ·
          refine ⟨46349819683424421290830253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123599519155798456775547341 46349819683424421290830253)
          ·
            refine ⟨17381182381284157984061345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46349819683424421290830253 17381182381284157984061345)
            ·
              refine ⟨13035886785963118488046009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17381182381284157984061345 13035886785963118488046009)
              ·
                refine ⟨9776915089472338866034507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13035886785963118488046009 9776915089472338866034507)
                ·
                  refine ⟨14665372634208508299051761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9776915089472338866034507 14665372634208508299051761)
                  ·
                    refine ⟨10999029475656381224288821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14665372634208508299051761 10999029475656381224288821)
                    ·
                      refine ⟨1031159013342785739777077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10999029475656381224288821 1031159013342785739777077)
                      ·
                        rfl

theorem cell23_2008175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_2008175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008175 prefixEnd_2008175 := by exact prefixLift 2008175
  have htrace : WordTrace (prefixWord ++ tailWord_2008175) baseStart_2008175 baseEnd_2008175 := by
    simpa [prefixWord, tailWord_2008175, baseEnd_2008175] using wordTrace_append hprefix tailTrace_2008175
  have hstable : (prefixWord ++ tailWord_2008175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008175).length < 2 ^ (prefixWord ++ tailWord_2008175).sum := by decide
  have hdescent : baseEnd_2008175 < baseStart_2008175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008202 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2008202 : Nat := 118140960795 + 2008202 * 2 ^ 59
def prefixEnd_2008202 : Nat := 4983230072969 + 3 ^ 40 * 2008202 * 2
def baseEnd_2008202 : Nat := 1031172877320457134139453

theorem tailTrace_2008202 : CollatzResearch.WordTrace tailWord_2008202 prefixEnd_2008202 1031172877320457134139453 := by
  unfold tailWord_2008202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311286067658650610296715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48830096180423068294124573 18311286067658650610296715)
  ·
    refine ⟨27466929101487975915445073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18311286067658650610296715 27466929101487975915445073)
    ·
      refine ⟨20600196826115981936583805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27466929101487975915445073 20600196826115981936583805)
      ·
        refine ⟨7725073809793493226218927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20600196826115981936583805 7725073809793493226218927)
        ·
          refine ⟨11587610714690239839328391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7725073809793493226218927 11587610714690239839328391)
          ·
            refine ⟨17381416072035359758992587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11587610714690239839328391 17381416072035359758992587)
            ·
              refine ⟨26072124108053039638488881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17381416072035359758992587 26072124108053039638488881)
              ·
                refine ⟨19554093081039779728866661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26072124108053039638488881 19554093081039779728866661)
                ·
                  refine ⟨3666392452694958699162499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19554093081039779728866661 3666392452694958699162499)
                  ·
                    refine ⟨5499588679042438048743749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3666392452694958699162499 5499588679042438048743749)
                    ·
                      refine ⟨1031172877320457134139453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5499588679042438048743749 1031172877320457134139453)
                      ·
                        rfl

theorem cell23_2008202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2008202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008202 prefixEnd_2008202 := by exact prefixLift 2008202
  have htrace : WordTrace (prefixWord ++ tailWord_2008202) baseStart_2008202 baseEnd_2008202 := by
    simpa [prefixWord, tailWord_2008202, baseEnd_2008202] using wordTrace_append hprefix tailTrace_2008202
  have hstable : (prefixWord ++ tailWord_2008202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008202).length < 2 ^ (prefixWord ++ tailWord_2008202).sum := by decide
  have hdescent : baseEnd_2008202 < baseStart_2008202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008242 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_2008242 : Nat := 118140960795 + 2008242 * 2 ^ 59
def prefixEnd_2008242 : Nat := 4983230072969 + 3 ^ 40 * 2008242 * 2
def baseEnd_2008242 : Nat := 114577046282959664182141

theorem tailTrace_2008242 : CollatzResearch.WordTrace tailWord_2008242 prefixEnd_2008242 114577046282959664182141 := by
  unfold tailWord_2008242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311650797622422318160745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48831068793659792848428653 18311650797622422318160745)
  ·
    refine ⟨13733738098216816738620559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18311650797622422318160745 13733738098216816738620559)
    ·
      refine ⟨20600607147325225107930839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13733738098216816738620559 20600607147325225107930839)
      ·
        refine ⟨30900910720987837661896259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20600607147325225107930839 30900910720987837661896259)
        ·
          refine ⟨46351366081481756492844389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30900910720987837661896259 46351366081481756492844389)
          ·
            refine ⟨8690881140277829342408323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46351366081481756492844389 8690881140277829342408323)
            ·
              refine ⟨13036321710416744013612485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8690881140277829342408323 13036321710416744013612485)
              ·
                refine ⟨2444310320703139502552341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13036321710416744013612485 2444310320703139502552341)
                ·
                  refine ⟨114577046282959664182141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2444310320703139502552341 114577046282959664182141)
                  ·
                    rfl

theorem cell23_2008242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_2008242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008242 prefixEnd_2008242 := by exact prefixLift 2008242
  have htrace : WordTrace (prefixWord ++ tailWord_2008242) baseStart_2008242 baseEnd_2008242 := by
    simpa [prefixWord, tailWord_2008242, baseEnd_2008242] using wordTrace_append hprefix tailTrace_2008242
  have hstable : (prefixWord ++ tailWord_2008242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008242).length < 2 ^ (prefixWord ++ tailWord_2008242).sum := by decide
  have hdescent : baseEnd_2008242 < baseStart_2008242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008265 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_2008265 : Nat := 118140960795 + 2008265 * 2 ^ 59
def prefixEnd_2008265 : Nat := 4983230072969 + 3 ^ 40 * 2008265 * 2
def baseEnd_2008265 : Nat := 1031205226601690387651663

theorem tailTrace_2008265 : CollatzResearch.WordTrace tailWord_2008265 prefixEnd_2008265 1031205226601690387651663 := by
  unfold tailWord_2008265
  simp only [CollatzResearch.WordTrace]
  refine ⟨73247442069406364200730249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48831628046270909467153499 73247442069406364200730249)
  ·
    refine ⟨54935581552054773150547687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73247442069406364200730249 54935581552054773150547687)
    ·
      refine ⟨82403372328082159725821531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54935581552054773150547687 82403372328082159725821531)
      ·
        refine ⟨123605058492123239588732297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82403372328082159725821531 123605058492123239588732297)
        ·
          refine ⟨92703793869092429691549223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123605058492123239588732297 92703793869092429691549223)
          ·
            refine ⟨139055690803638644537323835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92703793869092429691549223 139055690803638644537323835)
            ·
              refine ⟨208583536205457966805985753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139055690803638644537323835 208583536205457966805985753)
              ·
                refine ⟨156437652154093475104489315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208583536205457966805985753 156437652154093475104489315)
                ·
                  refine ⟨234656478231140212656733973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156437652154093475104489315 234656478231140212656733973)
                  ·
                    refine ⟨10999522417084697468284405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 234656478231140212656733973 10999522417084697468284405)
                    ·
                      refine ⟨1031205226601690387651663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10999522417084697468284405 1031205226601690387651663)
                      ·
                        rfl

theorem cell23_2008265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_2008265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008265 prefixEnd_2008265 := by exact prefixLift 2008265
  have htrace : WordTrace (prefixWord ++ tailWord_2008265) baseStart_2008265 baseEnd_2008265 := by
    simpa [prefixWord, tailWord_2008265, baseEnd_2008265] using wordTrace_append hprefix tailTrace_2008265
  have hstable : (prefixWord ++ tailWord_2008265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008265).length < 2 ^ (prefixWord ++ tailWord_2008265).sum := by decide
  have hdescent : baseEnd_2008265 < baseStart_2008265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008289 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2008289 : Nat := 118140960795 + 2008289 * 2 ^ 59
def prefixEnd_2008289 : Nat := 4983230072969 + 3 ^ 40 * 2008289 * 2
def baseEnd_2008289 : Nat := 343739183379132764583851

theorem tailTrace_2008289 : CollatzResearch.WordTrace tailWord_2008289 prefixEnd_2008289 343739183379132764583851 := by
  unfold tailWord_2008289
  simp only [CollatzResearch.WordTrace]
  refine ⟨73248317421319416299603921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48832211614212944199735947 73248317421319416299603921)
  ·
    refine ⟨54936238065989562224702941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73248317421319416299603921 54936238065989562224702941)
    ·
      refine ⟨20601089274746085834263603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54936238065989562224702941 20601089274746085834263603)
      ·
        refine ⟨30901633912119128751395405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20601089274746085834263603 30901633912119128751395405)
        ·
          refine ⟨11588112717044673281773277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30901633912119128751395405 11588112717044673281773277)
          ·
            refine ⟨4345542268891752480664979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11588112717044673281773277 4345542268891752480664979)
            ·
              refine ⟨6518313403337628720997469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345542268891752480664979 6518313403337628720997469)
              ·
                refine ⟨2444367526251610770374051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6518313403337628720997469 2444367526251610770374051)
                ·
                  refine ⟨3666551289377416155561077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444367526251610770374051 3666551289377416155561077)
                  ·
                    refine ⟨343739183379132764583851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3666551289377416155561077 343739183379132764583851)
                    ·
                      rfl

theorem cell23_2008289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2008289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008289 prefixEnd_2008289 := by exact prefixLift 2008289
  have htrace : WordTrace (prefixWord ++ tailWord_2008289) baseStart_2008289 baseEnd_2008289 := by
    simpa [prefixWord, tailWord_2008289, baseEnd_2008289] using wordTrace_append hprefix tailTrace_2008289
  have hstable : (prefixWord ++ tailWord_2008289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008289).length < 2 ^ (prefixWord ++ tailWord_2008289).sum := by decide
  have hdescent : baseEnd_2008289 < baseStart_2008289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008302 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2008302 : Nat := 118140960795 + 2008302 * 2 ^ 59
def prefixEnd_2008302 : Nat := 4983230072969 + 3 ^ 40 * 2008302 * 2
def baseEnd_2008302 : Nat := 343741408461968914296331

theorem tailTrace_2008302 : CollatzResearch.WordTrace tailWord_2008302 prefixEnd_2008302 343741408461968914296331 := by
  unfold tailWord_2008302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156098946284039939978395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48832527713514879679884773 9156098946284039939978395)
  ·
    refine ⟨13734148419426059909967593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156098946284039939978395 13734148419426059909967593)
    ·
      refine ⟨10300611314569544932475695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13734148419426059909967593 10300611314569544932475695)
      ·
        refine ⟨15450916971854317398713543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300611314569544932475695 15450916971854317398713543)
        ·
          refine ⟨23176375457781476098070315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15450916971854317398713543 23176375457781476098070315)
          ·
            refine ⟨34764563186672214147105473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23176375457781476098070315 34764563186672214147105473)
            ·
              refine ⟨26073422390004160610329105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34764563186672214147105473 26073422390004160610329105)
              ·
                refine ⟨19555066792503120457746829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26073422390004160610329105 19555066792503120457746829)
                ·
                  refine ⟨7333150047188670171655061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19555066792503120457746829 7333150047188670171655061)
                  ·
                    refine ⟨343741408461968914296331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7333150047188670171655061 343741408461968914296331)
                    ·
                      rfl

theorem cell23_2008302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2008302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008302 prefixEnd_2008302 := by exact prefixLift 2008302
  have htrace : WordTrace (prefixWord ++ tailWord_2008302) baseStart_2008302 baseEnd_2008302 := by
    simpa [prefixWord, tailWord_2008302, baseEnd_2008302] using wordTrace_append hprefix tailTrace_2008302
  have hstable : (prefixWord ++ tailWord_2008302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008302).length < 2 ^ (prefixWord ++ tailWord_2008302).sum := by decide
  have hdescent : baseEnd_2008302 < baseStart_2008302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008319 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 1, 6]
def baseStart_2008319 : Nat := 118140960795 + 2008319 * 2 ^ 59
def prefixEnd_2008319 : Nat := 4983230072969 + 3 ^ 40 * 2008319 * 2
def baseEnd_2008319 : Nat := 343744318185677725458805

theorem tailTrace_2008319 : CollatzResearch.WordTrace tailWord_2008319 prefixEnd_2008319 343744318185677725458805 := by
  unfold tailWord_2008319
  simp only [CollatzResearch.WordTrace]
  refine ⟨73249411611210731423196011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48832941074140487615464007 73249411611210731423196011)
  ·
    refine ⟨109874117416816097134794017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73249411611210731423196011 109874117416816097134794017)
    ·
      refine ⟨82405588062612072851095513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109874117416816097134794017 82405588062612072851095513)
      ·
        refine ⟨61804191046959054638321635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82405588062612072851095513 61804191046959054638321635)
        ·
          refine ⟨92706286570438581957482453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61804191046959054638321635 92706286570438581957482453)
          ·
            refine ⟨2172803591494654264628495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92706286570438581957482453 2172803591494654264628495)
            ·
              refine ⟨3259205387241981396942743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172803591494654264628495 3259205387241981396942743)
              ·
                refine ⟨4888808080862972095414115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259205387241981396942743 4888808080862972095414115)
                ·
                  refine ⟨7333212121294458143121173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888808080862972095414115 7333212121294458143121173)
                  ·
                    refine ⟨343744318185677725458805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7333212121294458143121173 343744318185677725458805)
                    ·
                      rfl

theorem cell23_2008319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_2008319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008319 prefixEnd_2008319 := by exact prefixLift 2008319
  have htrace : WordTrace (prefixWord ++ tailWord_2008319) baseStart_2008319 baseEnd_2008319 := by
    simpa [prefixWord, tailWord_2008319, baseEnd_2008319] using wordTrace_append hprefix tailTrace_2008319
  have hstable : (prefixWord ++ tailWord_2008319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008319).length < 2 ^ (prefixWord ++ tailWord_2008319).sum := by decide
  have hdescent : baseEnd_2008319 < baseStart_2008319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008332 : List Nat := [2, 2, 1, 2, 2, 4, 1, 9]
def baseStart_2008332 : Nat := 118140960795 + 2008332 * 2 ^ 59
def prefixEnd_2008332 : Nat := 4983230072969 + 3 ^ 40 * 2008332 * 2
def baseEnd_2008332 : Nat := 38194060363168208352365

theorem tailTrace_2008332 : CollatzResearch.WordTrace tailWord_2008332 prefixEnd_2008332 38194060363168208352365 := by
  unfold tailWord_2008332
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624942880081817321709625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48833257173442423095612833 36624942880081817321709625)
  ·
    refine ⟨27468707160061362991282219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36624942880081817321709625 27468707160061362991282219)
    ·
      refine ⟨41203060740092044486923329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27468707160061362991282219 41203060740092044486923329)
      ·
        refine ⟨30902295555069033365192497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41203060740092044486923329 30902295555069033365192497)
        ·
          refine ⟨23176721666301775023894373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30902295555069033365192497 23176721666301775023894373)
          ·
            refine ⟨4345635312431582816980195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23176721666301775023894373 4345635312431582816980195)
            ·
              refine ⟨6518452968647374225470293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345635312431582816980195 6518452968647374225470293)
              ·
                refine ⟨38194060363168208352365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6518452968647374225470293 38194060363168208352365)
                ·
                  rfl

theorem cell23_2008332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 9].length) (baseStart_2008332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008332 prefixEnd_2008332 := by exact prefixLift 2008332
  have htrace : WordTrace (prefixWord ++ tailWord_2008332) baseStart_2008332 baseEnd_2008332 := by
    simpa [prefixWord, tailWord_2008332, baseEnd_2008332] using wordTrace_append hprefix tailTrace_2008332
  have hstable : (prefixWord ++ tailWord_2008332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008332).length < 2 ^ (prefixWord ++ tailWord_2008332).sum := by decide
  have hdescent : baseEnd_2008332 < baseStart_2008332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008346 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_2008346 : Nat := 118140960795 + 2008346 * 2 ^ 59
def prefixEnd_2008346 : Nat := 4983230072969 + 3 ^ 40 * 2008346 * 2
def baseEnd_2008346 : Nat := 1031246818534704570738791

theorem tailTrace_2008346 : CollatzResearch.WordTrace tailWord_2008346 prefixEnd_2008346 1031246818534704570738791 := by
  unfold tailWord_2008346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312599095528228758607223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48833597588075276689619261 18312599095528228758607223)
  ·
    refine ⟨27468898643292343137910835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18312599095528228758607223 27468898643292343137910835)
    ·
      refine ⟨41203347964938514706866253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27468898643292343137910835 41203347964938514706866253)
      ·
        refine ⟨15451255486851943015074845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41203347964938514706866253 15451255486851943015074845)
        ·
          refine ⟨5794220807569478630653067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15451255486851943015074845 5794220807569478630653067)
          ·
            refine ⟨8691331211354217945979601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794220807569478630653067 8691331211354217945979601)
            ·
              refine ⟨6518498408515663459484701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691331211354217945979601 6518498408515663459484701)
              ·
                refine ⟨2444436903193373797306763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6518498408515663459484701 2444436903193373797306763)
                ·
                  refine ⟨3666655354790060695960145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444436903193373797306763 3666655354790060695960145)
                  ·
                    refine ⟨2749991516092545521970109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666655354790060695960145 2749991516092545521970109)
                    ·
                      refine ⟨1031246818534704570738791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2749991516092545521970109 1031246818534704570738791)
                      ·
                        rfl

theorem cell23_2008346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_2008346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008346 prefixEnd_2008346 := by exact prefixLift 2008346
  have htrace : WordTrace (prefixWord ++ tailWord_2008346) baseStart_2008346 baseEnd_2008346 := by
    simpa [prefixWord, tailWord_2008346, baseEnd_2008346] using wordTrace_append hprefix tailTrace_2008346
  have hstable : (prefixWord ++ tailWord_2008346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008346).length < 2 ^ (prefixWord ++ tailWord_2008346).sum := by decide
  have hdescent : baseEnd_2008346 < baseStart_2008346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008349 : List Nat := [1, 4, 2, 3, 1, 3, 9]
def baseStart_2008349 : Nat := 118140960795 + 2008349 * 2 ^ 59
def prefixEnd_2008349 : Nat := 4983230072969 + 3 ^ 40 * 2008349 * 2
def baseEnd_2008349 : Nat := 12731461221934173567917

theorem tailTrace_2008349 : CollatzResearch.WordTrace tailWord_2008349 prefixEnd_2008349 12731461221934173567917 := by
  unfold tailWord_2008349
  simp only [CollatzResearch.WordTrace]
  refine ⟨73250505801102046546788101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48833670534068031031192067 73250505801102046546788101)
  ·
    refine ⟨13734469837706633727522769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73250505801102046546788101 13734469837706633727522769)
    ·
      refine ⟨10300852378279975295642077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13734469837706633727522769 10300852378279975295642077)
      ·
        refine ⟨3862819641854990735865779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10300852378279975295642077 3862819641854990735865779)
        ·
          refine ⟨5794229462782486103798669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862819641854990735865779 5794229462782486103798669)
          ·
            refine ⟨2172836048543432288924501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5794229462782486103798669 2172836048543432288924501)
            ·
              refine ⟨12731461221934173567917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2172836048543432288924501 12731461221934173567917)
              ·
                rfl

theorem cell23_2008349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 9].length) (baseStart_2008349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008349 prefixEnd_2008349 := by exact prefixLift 2008349
  have htrace : WordTrace (prefixWord ++ tailWord_2008349) baseStart_2008349 baseEnd_2008349 := by
    simpa [prefixWord, tailWord_2008349, baseEnd_2008349] using wordTrace_append hprefix tailTrace_2008349
  have hstable : (prefixWord ++ tailWord_2008349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008349).length < 2 ^ (prefixWord ++ tailWord_2008349).sum := by decide
  have hdescent : baseEnd_2008349 < baseStart_2008349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008360 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_2008360 : Nat := 118140960795 + 2008360 * 2 ^ 59
def prefixEnd_2008360 : Nat := 4983230072969 + 3 ^ 40 * 2008360 * 2
def baseEnd_2008360 : Nat := 1031254007263867515963727

theorem tailTrace_2008360 : CollatzResearch.WordTrace tailWord_2008360 prefixEnd_2008360 1031254007263867515963727 := by
  unfold tailWord_2008360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36625453502031097712719267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48833938002708130283625689 36625453502031097712719267)
  ·
    refine ⟨54938180253046646569078901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36625453502031097712719267 54938180253046646569078901)
    ·
      refine ⟨5150454398723123115851147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54938180253046646569078901 5150454398723123115851147)
      ·
        refine ⟨7725681598084684673776721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150454398723123115851147 7725681598084684673776721)
        ·
          refine ⟨5794261198563513505332541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7725681598084684673776721 5794261198563513505332541)
          ·
            refine ⟨2172847949461317564499703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5794261198563513505332541 2172847949461317564499703)
            ·
              refine ⟨3259271924191976346749555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172847949461317564499703 3259271924191976346749555)
              ·
                refine ⟨4888907886287964520124333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259271924191976346749555 4888907886287964520124333)
                ·
                  refine ⟨1833340457357986695046625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4888907886287964520124333 1833340457357986695046625)
                  ·
                    refine ⟨1375005343018490021284969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1833340457357986695046625 1375005343018490021284969)
                    ·
                      refine ⟨1031254007263867515963727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375005343018490021284969 1031254007263867515963727)
                      ·
                        rfl

theorem cell23_2008360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_2008360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008360 prefixEnd_2008360 := by exact prefixLift 2008360
  have htrace : WordTrace (prefixWord ++ tailWord_2008360) baseStart_2008360 baseEnd_2008360 := by
    simpa [prefixWord, tailWord_2008360, baseEnd_2008360] using wordTrace_append hprefix tailTrace_2008360
  have hstable : (prefixWord ++ tailWord_2008360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008360).length < 2 ^ (prefixWord ++ tailWord_2008360).sum := by decide
  have hdescent : baseEnd_2008360 < baseStart_2008360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008390 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2008390 : Nat := 118140960795 + 2008390 * 2 ^ 59
def prefixEnd_2008390 : Nat := 4983230072969 + 3 ^ 40 * 2008390 * 2
def baseEnd_2008390 : Nat := 1031269411683502398588589

theorem tailTrace_2008390 : CollatzResearch.WordTrace tailWord_2008390 prefixEnd_2008390 1031269411683502398588589 := by
  unfold tailWord_2008390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289125037311047204657207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48834667462635673699353749 2289125037311047204657207)
  ·
    refine ⟨3433687555966570806985811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289125037311047204657207 3433687555966570806985811)
    ·
      refine ⟨5150531333949856210478717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3433687555966570806985811 5150531333949856210478717)
      ·
        refine ⟨1931449250231196078929519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5150531333949856210478717 1931449250231196078929519)
        ·
          refine ⟨2897173875346794118394279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931449250231196078929519 2897173875346794118394279)
          ·
            refine ⟨4345760813020191177591419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897173875346794118394279 4345760813020191177591419)
            ·
              refine ⟨6518641219530286766387129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345760813020191177591419 6518641219530286766387129)
              ·
                refine ⟨4888980914647715074790347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518641219530286766387129 4888980914647715074790347)
                ·
                  refine ⟨7333471371971572612185521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888980914647715074790347 7333471371971572612185521)
                  ·
                    refine ⟨5500103528978679459139141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7333471371971572612185521 5500103528978679459139141)
                    ·
                      refine ⟨1031269411683502398588589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5500103528978679459139141 1031269411683502398588589)
                      ·
                        rfl

theorem cell23_2008390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2008390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008390 prefixEnd_2008390 := by exact prefixLift 2008390
  have htrace : WordTrace (prefixWord ++ tailWord_2008390) baseStart_2008390 baseEnd_2008390 := by
    simpa [prefixWord, tailWord_2008390, baseEnd_2008390] using wordTrace_append hprefix tailTrace_2008390
  have hstable : (prefixWord ++ tailWord_2008390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008390).length < 2 ^ (prefixWord ++ tailWord_2008390).sum := by decide
  have hdescent : baseEnd_2008390 < baseStart_2008390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008392 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_2008392 : Nat := 118140960795 + 2008392 * 2 ^ 59
def prefixEnd_2008392 : Nat := 4983230072969 + 3 ^ 40 * 2008392 * 2
def baseEnd_2008392 : Nat := 343756812881603796921193

theorem tailTrace_2008392 : CollatzResearch.WordTrace tailWord_2008392 prefixEnd_2008392 343756812881603796921193 := by
  unfold tailWord_2008392
  simp only [CollatzResearch.WordTrace]
  refine ⟨36626037069973132445301715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48834716093297509927068953 36626037069973132445301715)
  ·
    refine ⟨54939055604959698667952573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36626037069973132445301715 54939055604959698667952573)
    ·
      refine ⟨20602145851859887000482215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54939055604959698667952573 20602145851859887000482215)
      ·
        refine ⟨30903218777789830500723323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20602145851859887000482215 30903218777789830500723323)
        ·
          refine ⟨46354828166684745751084985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30903218777789830500723323 46354828166684745751084985)
          ·
            refine ⟨34766121125013559313313739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46354828166684745751084985 34766121125013559313313739)
            ·
              refine ⟨52149181687520338969970609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34766121125013559313313739 52149181687520338969970609)
              ·
                refine ⟨39111886265640254227477957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52149181687520338969970609 39111886265640254227477957)
                ·
                  refine ⟨7333478674807547667652117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39111886265640254227477957 7333478674807547667652117)
                  ·
                    refine ⟨343756812881603796921193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7333478674807547667652117 343756812881603796921193)
                    ·
                      rfl

theorem cell23_2008392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_2008392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008392 prefixEnd_2008392 := by exact prefixLift 2008392
  have htrace : WordTrace (prefixWord ++ tailWord_2008392) baseStart_2008392 baseEnd_2008392 := by
    simpa [prefixWord, tailWord_2008392, baseEnd_2008392] using wordTrace_append hprefix tailTrace_2008392
  have hstable : (prefixWord ++ tailWord_2008392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008392).length < 2 ^ (prefixWord ++ tailWord_2008392).sum := by decide
  have hdescent : baseEnd_2008392 < baseStart_2008392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008397 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2008397 : Nat := 118140960795 + 2008397 * 2 ^ 59
def prefixEnd_2008397 : Nat := 4983230072969 + 3 ^ 40 * 2008397 * 2
def baseEnd_2008397 : Nat := 1031273006048083871201057

theorem tailTrace_2008397 : CollatzResearch.WordTrace tailWord_2008397 prefixEnd_2008397 1031273006048083871201057 := by
  unfold tailWord_2008397
  simp only [CollatzResearch.WordTrace]
  refine ⟨73252256504928150744535445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48834837669952100496356963 73252256504928150744535445)
  ·
    refine ⟨3433699523668507066150099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73252256504928150744535445 3433699523668507066150099)
    ·
      refine ⟨5150549285502760599225149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3433699523668507066150099 5150549285502760599225149)
      ·
        refine ⟨1931455982063535224709431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5150549285502760599225149 1931455982063535224709431)
        ·
          refine ⟨2897183973095302837064147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931455982063535224709431 2897183973095302837064147)
          ·
            refine ⟨4345775959642954255596221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897183973095302837064147 4345775959642954255596221)
            ·
              refine ⟨1629665984866107845848583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4345775959642954255596221 1629665984866107845848583)
              ·
                refine ⟨2444498977299161768772875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629665984866107845848583 2444498977299161768772875)
                ·
                  refine ⟨3666748465948742653159313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444498977299161768772875 3666748465948742653159313)
                  ·
                    refine ⟨2750061349461556989869485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666748465948742653159313 2750061349461556989869485)
                    ·
                      refine ⟨1031273006048083871201057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750061349461556989869485 1031273006048083871201057)
                      ·
                        rfl

theorem cell23_2008397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2008397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008397 prefixEnd_2008397 := by exact prefixLift 2008397
  have htrace : WordTrace (prefixWord ++ tailWord_2008397) baseStart_2008397 baseEnd_2008397 := by
    simpa [prefixWord, tailWord_2008397, baseEnd_2008397] using wordTrace_append hprefix tailTrace_2008397
  have hstable : (prefixWord ++ tailWord_2008397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008397).length < 2 ^ (prefixWord ++ tailWord_2008397).sum := by decide
  have hdescent : baseEnd_2008397 < baseStart_2008397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008403 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 1, 3, 2]
def baseStart_2008403 : Nat := 118140960795 + 2008403 * 2 ^ 59
def prefixEnd_2008403 : Nat := 4983230072969 + 3 ^ 40 * 2008403 * 2
def baseEnd_2008403 : Nat := 1031276086932010847726029

theorem tailTrace_2008403 : CollatzResearch.WordTrace tailWord_2008403 prefixEnd_2008403 1031276086932010847726029 := by
  unfold tailWord_2008403
  simp only [CollatzResearch.WordTrace]
  refine ⟨73252475342906413769253863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48834983561937609179502575 73252475342906413769253863)
  ·
    refine ⟨109878713014359620653880795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73252475342906413769253863 109878713014359620653880795)
    ·
      refine ⟨164818069521539430980821193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109878713014359620653880795 164818069521539430980821193)
      ·
        refine ⟨123613552141154573235615895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164818069521539430980821193 123613552141154573235615895)
        ·
          refine ⟨185420328211731859853423843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123613552141154573235615895 185420328211731859853423843)
          ·
            refine ⟨278130492317597789780135765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185420328211731859853423843 278130492317597789780135765)
            ·
              refine ⟨1629670853423424549492983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 278130492317597789780135765 1629670853423424549492983)
              ·
                refine ⟨2444506280135136824239475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629670853423424549492983 2444506280135136824239475)
                ·
                  refine ⟨3666759420202705236359213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444506280135136824239475 3666759420202705236359213)
                  ·
                    refine ⟨1375034782576014463634705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3666759420202705236359213 1375034782576014463634705)
                    ·
                      refine ⟨1031276086932010847726029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375034782576014463634705 1031276086932010847726029)
                      ·
                        rfl

theorem cell23_2008403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 3, 2].length) (baseStart_2008403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008403 prefixEnd_2008403 := by exact prefixLift 2008403
  have htrace : WordTrace (prefixWord ++ tailWord_2008403) baseStart_2008403 baseEnd_2008403 := by
    simpa [prefixWord, tailWord_2008403, baseEnd_2008403] using wordTrace_append hprefix tailTrace_2008403
  have hstable : (prefixWord ++ tailWord_2008403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008403).length < 2 ^ (prefixWord ++ tailWord_2008403).sum := by decide
  have hdescent : baseEnd_2008403 < baseStart_2008403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008419 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2008419 : Nat := 118140960795 + 2008419 * 2 ^ 59
def prefixEnd_2008419 : Nat := 4983230072969 + 3 ^ 40 * 2008419 * 2
def baseEnd_2008419 : Nat := 1031284302622482785125955

theorem tailTrace_2008419 : CollatzResearch.WordTrace tailWord_2008419 prefixEnd_2008419 1031284302622482785125955 := by
  unfold tailWord_2008419
  simp only [CollatzResearch.WordTrace]
  refine ⟨73253058910848448501836311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48835372607232299001224207 73253058910848448501836311)
  ·
    refine ⟨109879588366272672752754467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73253058910848448501836311 109879588366272672752754467)
    ·
      refine ⟨164819382549409009129131701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109879588366272672752754467 164819382549409009129131701)
      ·
        refine ⟨15451817114007094605856097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164819382549409009129131701 15451817114007094605856097)
        ·
          refine ⟨11588862835505320954392073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15451817114007094605856097 11588862835505320954392073)
          ·
            refine ⟨8691647126628990715794055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588862835505320954392073 8691647126628990715794055)
            ·
              refine ⟨13037470689943486073691083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691647126628990715794055 13037470689943486073691083)
              ·
                refine ⟨19556206034915229110536625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13037470689943486073691083 19556206034915229110536625)
                ·
                  refine ⟨14667154526186421832902469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19556206034915229110536625 14667154526186421832902469)
                  ·
                    refine ⟨2750091473659954093669213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14667154526186421832902469 2750091473659954093669213)
                    ·
                      refine ⟨1031284302622482785125955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750091473659954093669213 1031284302622482785125955)
                      ·
                        rfl

theorem cell23_2008419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2008419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008419 prefixEnd_2008419 := by exact prefixLift 2008419
  have htrace : WordTrace (prefixWord ++ tailWord_2008419) baseStart_2008419 baseEnd_2008419 := by
    simpa [prefixWord, tailWord_2008419, baseEnd_2008419] using wordTrace_append hprefix tailTrace_2008419
  have hstable : (prefixWord ++ tailWord_2008419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008419).length < 2 ^ (prefixWord ++ tailWord_2008419).sum := by decide
  have hdescent : baseEnd_2008419 < baseStart_2008419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008426 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2008426 : Nat := 118140960795 + 2008426 * 2 ^ 59
def prefixEnd_2008426 : Nat := 4983230072969 + 3 ^ 40 * 2008426 * 2
def baseEnd_2008426 : Nat := 343762632329021419246141

theorem tailTrace_2008426 : CollatzResearch.WordTrace tailWord_2008426 prefixEnd_2008426 343762632329021419246141 := by
  unfold tailWord_2008426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313328555455772174335283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48835542814548725798227421 18313328555455772174335283)
  ·
    refine ⟨27469992833183658261502925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18313328555455772174335283 27469992833183658261502925)
    ·
      refine ⟨10301247312443871848063597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27469992833183658261502925 10301247312443871848063597)
      ·
        refine ⟨3862967742166451943023849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10301247312443871848063597 3862967742166451943023849)
        ·
          refine ⟨2897225806624838957267887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862967742166451943023849 2897225806624838957267887)
          ·
            refine ⟨4345838709937258435901831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897225806624838957267887 4345838709937258435901831)
            ·
              refine ⟨6518758064905887653852747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345838709937258435901831 6518758064905887653852747)
              ·
                refine ⟨9778137097358831480779121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518758064905887653852747 9778137097358831480779121)
                ·
                  refine ⟨7333602823019123610584341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9778137097358831480779121 7333602823019123610584341)
                  ·
                    refine ⟨343762632329021419246141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7333602823019123610584341 343762632329021419246141)
                    ·
                      rfl

theorem cell23_2008426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2008426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008426 prefixEnd_2008426 := by exact prefixLift 2008426
  have htrace : WordTrace (prefixWord ++ tailWord_2008426) baseStart_2008426 baseEnd_2008426 := by
    simpa [prefixWord, tailWord_2008426, baseEnd_2008426] using wordTrace_append hprefix tailTrace_2008426
  have hstable : (prefixWord ++ tailWord_2008426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008426).length < 2 ^ (prefixWord ++ tailWord_2008426).sum := by decide
  have hdescent : baseEnd_2008426 < baseStart_2008426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008429 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2008429 : Nat := 118140960795 + 2008429 * 2 ^ 59
def prefixEnd_2008429 : Nat := 4983230072969 + 3 ^ 40 * 2008429 * 2
def baseEnd_2008429 : Nat := 1031289437429027746000909

theorem tailTrace_2008429 : CollatzResearch.WordTrace tailWord_2008429 prefixEnd_2008429 1031289437429027746000909 := by
  unfold tailWord_2008429
  simp only [CollatzResearch.WordTrace]
  refine ⟨73253423640812220209700341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48835615760541480139800227 73253423640812220209700341)
  ·
    refine ⟨6867508466326145644659407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73253423640812220209700341 6867508466326145644659407)
    ·
      refine ⟨10301262699489218466989111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867508466326145644659407 10301262699489218466989111)
      ·
        refine ⟨15451894049233827700483667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301262699489218466989111 15451894049233827700483667)
        ·
          refine ⟨23177841073850741550725501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15451894049233827700483667 23177841073850741550725501)
          ·
            refine ⟨8691690402694028081522063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23177841073850741550725501 8691690402694028081522063)
            ·
              refine ⟨13037535604041042122283095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691690402694028081522063 13037535604041042122283095)
              ·
                refine ⟨19556303406061563183424643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13037535604041042122283095 19556303406061563183424643)
                ·
                  refine ⟨29334455109092344775136965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19556303406061563183424643 29334455109092344775136965)
                  ·
                    refine ⟨5500210332954814645338181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29334455109092344775136965 5500210332954814645338181)
                    ·
                      refine ⟨1031289437429027746000909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5500210332954814645338181 1031289437429027746000909)
                      ·
                        rfl

theorem cell23_2008429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2008429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008429 prefixEnd_2008429 := by exact prefixLift 2008429
  have htrace : WordTrace (prefixWord ++ tailWord_2008429) baseStart_2008429 baseEnd_2008429 := by
    simpa [prefixWord, tailWord_2008429, baseEnd_2008429] using wordTrace_append hprefix tailTrace_2008429
  have hstable : (prefixWord ++ tailWord_2008429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008429).length < 2 ^ (prefixWord ++ tailWord_2008429).sum := by decide
  have hdescent : baseEnd_2008429 < baseStart_2008429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008433 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_2008433 : Nat := 118140960795 + 2008433 * 2 ^ 59
def prefixEnd_2008433 : Nat := 4983230072969 + 3 ^ 40 * 2008433 * 2
def baseEnd_2008433 : Nat := 1031291491351645730350891

theorem tailTrace_2008433 : CollatzResearch.WordTrace tailWord_2008433 prefixEnd_2008433 1031291491351645730350891 := by
  unfold tailWord_2008433
  simp only [CollatzResearch.WordTrace]
  refine ⟨73253569532797728892845953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48835713021865152595230635 73253569532797728892845953)
  ·
    refine ⟨54940177149598296669634465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73253569532797728892845953 54940177149598296669634465)
    ·
      refine ⟨41205132862198722502225849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54940177149598296669634465 41205132862198722502225849)
      ·
        refine ⟨30903849646649041876669387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41205132862198722502225849 30903849646649041876669387)
        ·
          refine ⟨46355774469973562815004081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30903849646649041876669387 46355774469973562815004081)
          ·
            refine ⟨34766830852480172111253061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46355774469973562815004081 34766830852480172111253061)
            ·
              refine ⟨6518780784840032270859949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34766830852480172111253061 6518780784840032270859949)
              ·
                refine ⟨2444542794315012101572481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6518780784840032270859949 2444542794315012101572481)
                ·
                  refine ⟨1833407095736259076179361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444542794315012101572481 1833407095736259076179361)
                  ·
                    refine ⟨1375055321802194307134521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1833407095736259076179361 1375055321802194307134521)
                    ·
                      refine ⟨1031291491351645730350891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375055321802194307134521 1031291491351645730350891)
                      ·
                        rfl

theorem cell23_2008433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_2008433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008433 prefixEnd_2008433 := by exact prefixLift 2008433
  have htrace : WordTrace (prefixWord ++ tailWord_2008433) baseStart_2008433 baseEnd_2008433 := by
    simpa [prefixWord, tailWord_2008433, baseEnd_2008433] using wordTrace_append hprefix tailTrace_2008433
  have hstable : (prefixWord ++ tailWord_2008433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008433).length < 2 ^ (prefixWord ++ tailWord_2008433).sum := by decide
  have hdescent : baseEnd_2008433 < baseStart_2008433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008442 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_2008442 : Nat := 118140960795 + 2008442 * 2 ^ 59
def prefixEnd_2008442 : Nat := 4983230072969 + 3 ^ 40 * 2008442 * 2
def baseEnd_2008442 : Nat := 1031296112677536195138349

theorem tailTrace_2008442 : CollatzResearch.WordTrace tailWord_2008442 prefixEnd_2008442 1031296112677536195138349 := by
  unfold tailWord_2008442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313474447441280857480895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48835931859843415619949053 18313474447441280857480895)
  ·
    refine ⟨27470211671161921286221343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18313474447441280857480895 27470211671161921286221343)
    ·
      refine ⟨41205317506742881929332015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27470211671161921286221343 41205317506742881929332015)
      ·
        refine ⟨61807976260114322893998023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41205317506742881929332015 61807976260114322893998023)
        ·
          refine ⟨92711964390171484340997035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61807976260114322893998023 92711964390171484340997035)
          ·
            refine ⟨139067946585257226511495553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92711964390171484340997035 139067946585257226511495553)
            ·
              refine ⟨104300959938942919883621665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139067946585257226511495553 104300959938942919883621665)
              ·
                refine ⟨78225719954207189912716249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104300959938942919883621665 78225719954207189912716249)
                ·
                  refine ⟨58669289965655392434537187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78225719954207189912716249 58669289965655392434537187)
                  ·
                    refine ⟨88003934948483088651805781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58669289965655392434537187 88003934948483088651805781)
                    ·
                      refine ⟨1031296112677536195138349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88003934948483088651805781 1031296112677536195138349)
                      ·
                        rfl

theorem cell23_2008442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_2008442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008442 prefixEnd_2008442 := by exact prefixLift 2008442
  have htrace : WordTrace (prefixWord ++ tailWord_2008442) baseStart_2008442 baseEnd_2008442 := by
    simpa [prefixWord, tailWord_2008442, baseEnd_2008442] using wordTrace_append hprefix tailTrace_2008442
  have hstable : (prefixWord ++ tailWord_2008442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008442).length < 2 ^ (prefixWord ++ tailWord_2008442).sum := by decide
  have hdescent : baseEnd_2008442 < baseStart_2008442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008450 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2008450 : Nat := 118140960795 + 2008450 * 2 ^ 59
def prefixEnd_2008450 : Nat := 4983230072969 + 3 ^ 40 * 2008450 * 2
def baseEnd_2008450 : Nat := 1031300220522772163838313

theorem tailTrace_2008450 : CollatzResearch.WordTrace tailWord_2008450 prefixEnd_2008450 1031300220522772163838313 := by
  unfold tailWord_2008450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18313547393434035199053701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48836126382490760530809869 18313547393434035199053701)
  ·
    refine ⟨3433790136268881599822569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18313547393434035199053701 3433790136268881599822569)
    ·
      refine ⟨2575342602201661199866927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3433790136268881599822569 2575342602201661199866927)
      ·
        refine ⟨3863013903302491799800391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575342602201661199866927 3863013903302491799800391)
        ·
          refine ⟨5794520854953737699700587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863013903302491799800391 5794520854953737699700587)
          ·
            refine ⟨8691781282430606549550881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794520854953737699700587 8691781282430606549550881)
            ·
              refine ⟨6518835961822954912163161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8691781282430606549550881 6518835961822954912163161)
              ·
                refine ⟨4889126971367216184122371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6518835961822954912163161 4889126971367216184122371)
                ·
                  refine ⟨7333690457050824276183557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889126971367216184122371 7333690457050824276183557)
                  ·
                    refine ⟨1375066960697029551784417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7333690457050824276183557 1375066960697029551784417)
                    ·
                      refine ⟨1031300220522772163838313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375066960697029551784417 1031300220522772163838313)
                      ·
                        rfl

theorem cell23_2008450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2008450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008450 prefixEnd_2008450 := by exact prefixLift 2008450
  have htrace : WordTrace (prefixWord ++ tailWord_2008450) baseStart_2008450 baseEnd_2008450 := by
    simpa [prefixWord, tailWord_2008450, baseEnd_2008450] using wordTrace_append hprefix tailTrace_2008450
  have hstable : (prefixWord ++ tailWord_2008450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008450).length < 2 ^ (prefixWord ++ tailWord_2008450).sum := by decide
  have hdescent : baseEnd_2008450 < baseStart_2008450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008456 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 5]
def baseStart_2008456 : Nat := 118140960795 + 2008456 * 2 ^ 59
def prefixEnd_2008456 : Nat := 4983230072969 + 3 ^ 40 * 2008456 * 2
def baseEnd_2008456 : Nat := 114589255711855460040365

theorem tailTrace_2008456 : CollatzResearch.WordTrace tailWord_2008456 prefixEnd_2008456 114589255711855460040365 := by
  unfold tailWord_2008456
  simp only [CollatzResearch.WordTrace]
  refine ⟨36627204205857201910466611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48836272274476269213955481 36627204205857201910466611)
  ·
    refine ⟨54940806308785802865699917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36627204205857201910466611 54940806308785802865699917)
    ·
      refine ⟨20602802365794676074637469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54940806308785802865699917 20602802365794676074637469)
      ·
        refine ⟨7726050887173003527989051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20602802365794676074637469 7726050887173003527989051)
        ·
          refine ⟨11589076330759505291983577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726050887173003527989051 11589076330759505291983577)
          ·
            refine ⟨8691807248069628968987683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11589076330759505291983577 8691807248069628968987683)
            ·
              refine ⟨13037710872104443453481525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8691807248069628968987683 13037710872104443453481525)
              ·
                refine ⟨1222285394259791573763893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13037710872104443453481525 1222285394259791573763893)
                ·
                  refine ⟨114589255711855460040365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222285394259791573763893 114589255711855460040365)
                  ·
                    rfl

theorem cell23_2008456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 5].length) (baseStart_2008456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008456 prefixEnd_2008456 := by exact prefixLift 2008456
  have htrace : WordTrace (prefixWord ++ tailWord_2008456) baseStart_2008456 baseEnd_2008456 := by
    simpa [prefixWord, tailWord_2008456, baseEnd_2008456] using wordTrace_append hprefix tailTrace_2008456
  have hstable : (prefixWord ++ tailWord_2008456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008456).length < 2 ^ (prefixWord ++ tailWord_2008456).sum := by decide
  have hdescent : baseEnd_2008456 < baseStart_2008456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008469 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2008469 : Nat := 118140960795 + 2008469 * 2 ^ 59
def prefixEnd_2008469 : Nat := 4983230072969 + 3 ^ 40 * 2008469 * 2
def baseEnd_2008469 : Nat := 343769992218402529833575

theorem tailTrace_2008469 : CollatzResearch.WordTrace tailWord_2008469 prefixEnd_2008469 343769992218402529833575 := by
  unfold tailWord_2008469
  simp only [CollatzResearch.WordTrace]
  refine ⟨73254882560667307041156461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48836588373778204694104307 73254882560667307041156461)
  ·
    refine ⟨27470580960250240140433673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73254882560667307041156461 27470580960250240140433673)
    ·
      refine ⟨20602935720187680105325255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27470580960250240140433673 20602935720187680105325255)
      ·
        refine ⟨30904403580281520157987883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20602935720187680105325255 30904403580281520157987883)
        ·
          refine ⟨46356605370422280236981825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30904403580281520157987883 46356605370422280236981825)
          ·
            refine ⟨34767454027816710177736369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46356605370422280236981825 34767454027816710177736369)
            ·
              refine ⟨26075590520862532633302277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34767454027816710177736369 26075590520862532633302277)
              ·
                refine ⟨4889173222661724868744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26075590520862532633302277 4889173222661724868744177)
                ·
                  refine ⟨3666879916996293651558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4889173222661724868744177 3666879916996293651558133)
                  ·
                    refine ⟨343769992218402529833575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3666879916996293651558133 343769992218402529833575)
                    ·
                      rfl

theorem cell23_2008469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2008469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008469 prefixEnd_2008469 := by exact prefixLift 2008469
  have htrace : WordTrace (prefixWord ++ tailWord_2008469) baseStart_2008469 baseEnd_2008469 := by
    simpa [prefixWord, tailWord_2008469, baseEnd_2008469] using wordTrace_append hprefix tailTrace_2008469
  have hstable : (prefixWord ++ tailWord_2008469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008469).length < 2 ^ (prefixWord ++ tailWord_2008469).sum := by decide
  have hdescent : baseEnd_2008469 < baseStart_2008469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008526 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_2008526 : Nat := 118140960795 + 2008526 * 2 ^ 59
def prefixEnd_2008526 : Nat := 4983230072969 + 3 ^ 40 * 2008526 * 2
def baseEnd_2008526 : Nat := 1031339245052513866487963

theorem tailTrace_2008526 : CollatzResearch.WordTrace tailWord_2008526 prefixEnd_2008526 1031339245052513866487963 := by
  unfold tailWord_2008526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9157120190182600721997679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48837974347640537183987621 9157120190182600721997679)
  ·
    refine ⟨13735680285273901082996519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9157120190182600721997679 13735680285273901082996519)
    ·
      refine ⟨20603520427910851624494779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735680285273901082996519 20603520427910851624494779)
      ·
        refine ⟨30905280641866277436742169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20603520427910851624494779 30905280641866277436742169)
        ·
          refine ⟨23178960481399708077556627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30905280641866277436742169 23178960481399708077556627)
          ·
            refine ⟨34768440722099562116334941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23178960481399708077556627 34768440722099562116334941)
            ·
              refine ⟨13038165270787335793625603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34768440722099562116334941 13038165270787335793625603)
              ·
                refine ⟨19557247906181003690438405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13038165270787335793625603 19557247906181003690438405)
                ·
                  refine ⟨3666983982408938191957201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19557247906181003690438405 3666983982408938191957201)
                  ·
                    refine ⟨2750237986806703643967901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666983982408938191957201 2750237986806703643967901)
                    ·
                      refine ⟨1031339245052513866487963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750237986806703643967901 1031339245052513866487963)
                      ·
                        rfl

theorem cell23_2008526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_2008526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008526 prefixEnd_2008526 := by exact prefixLift 2008526
  have htrace : WordTrace (prefixWord ++ tailWord_2008526) baseStart_2008526 baseEnd_2008526 := by
    simpa [prefixWord, tailWord_2008526, baseEnd_2008526] using wordTrace_append hprefix tailTrace_2008526
  have hstable : (prefixWord ++ tailWord_2008526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008526).length < 2 ^ (prefixWord ++ tailWord_2008526).sum := by decide
  have hdescent : baseEnd_2008526 < baseStart_2008526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008636 : List Nat := [2, 2, 2, 2, 4, 1, 10]
def baseStart_2008636 : Nat := 118140960795 + 2008636 * 2 ^ 59
def prefixEnd_2008636 : Nat := 4983230072969 + 3 ^ 40 * 2008636 * 2
def baseEnd_2008636 : Nat := 12733280591660597976697

theorem tailTrace_2008636 : CollatzResearch.WordTrace tailWord_2008636 prefixEnd_2008636 12733280591660597976697 := by
  unfold tailWord_2008636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630486775531147281242881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48840649034041529708323841 36630486775531147281242881)
  ·
    refine ⟨27472865081648360460932161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36630486775531147281242881 27472865081648360460932161)
    ·
      refine ⟨20604648811236270345699121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27472865081648360460932161 20604648811236270345699121)
      ·
        refine ⟨15453486608427202759274341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20604648811236270345699121 15453486608427202759274341)
        ·
          refine ⟨2897528739080100517363939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15453486608427202759274341 2897528739080100517363939)
          ·
            refine ⟨4346293108620150776045909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897528739080100517363939 4346293108620150776045909)
            ·
              refine ⟨12733280591660597976697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4346293108620150776045909 12733280591660597976697)
              ·
                rfl

theorem cell23_2008636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 10].length) (baseStart_2008636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008636 prefixEnd_2008636 := by exact prefixLift 2008636
  have htrace : WordTrace (prefixWord ++ tailWord_2008636) baseStart_2008636 baseEnd_2008636 := by
    simpa [prefixWord, tailWord_2008636, baseEnd_2008636] using wordTrace_append hprefix tailTrace_2008636
  have hstable : (prefixWord ++ tailWord_2008636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008636).length < 2 ^ (prefixWord ++ tailWord_2008636).sum := by decide
  have hdescent : baseEnd_2008636 < baseStart_2008636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008647 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_2008647 : Nat := 118140960795 + 2008647 * 2 ^ 59
def prefixEnd_2008647 : Nat := 4983230072969 + 3 ^ 40 * 2008647 * 2
def baseEnd_2008647 : Nat := 1031401376211707893074907

theorem tailTrace_2008647 : CollatzResearch.WordTrace tailWord_2008647 prefixEnd_2008647 1031401376211707893074907 := by
  unfold tailWord_2008647
  simp only [CollatzResearch.WordTrace]
  refine ⟨73261374754022443441136195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48840916502681628960757463 73261374754022443441136195)
  ·
    refine ⟨109892062131033665161704293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73261374754022443441136195 109892062131033665161704293)
    ·
      refine ⟨20604761649568812217819555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109892062131033665161704293 20604761649568812217819555)
      ·
        refine ⟨30907142474353218326729333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20604761649568812217819555 30907142474353218326729333)
        ·
          refine ⟨2897544606970614218130875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30907142474353218326729333 2897544606970614218130875)
          ·
            refine ⟨4346316910455921327196313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897544606970614218130875 4346316910455921327196313)
            ·
              refine ⟨3259737682841940995397235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4346316910455921327196313 3259737682841940995397235)
              ·
                refine ⟨4889606524262911493095853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259737682841940995397235 4889606524262911493095853)
                ·
                  refine ⟨1833602446598591809910945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4889606524262911493095853 1833602446598591809910945)
                  ·
                    refine ⟨1375201834948943857433209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1833602446598591809910945 1375201834948943857433209)
                    ·
                      refine ⟨1031401376211707893074907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375201834948943857433209 1031401376211707893074907)
                      ·
                        rfl

theorem cell23_2008647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_2008647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008647 prefixEnd_2008647 := by exact prefixLift 2008647
  have htrace : WordTrace (prefixWord ++ tailWord_2008647) baseStart_2008647 baseEnd_2008647 := by
    simpa [prefixWord, tailWord_2008647, baseEnd_2008647] using wordTrace_append hprefix tailTrace_2008647
  have hstable : (prefixWord ++ tailWord_2008647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008647).length < 2 ^ (prefixWord ++ tailWord_2008647).sum := by decide
  have hdescent : baseEnd_2008647 < baseStart_2008647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008649 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_2008649 : Nat := 118140960795 + 2008649 * 2 ^ 59
def prefixEnd_2008649 : Nat := 4983230072969 + 3 ^ 40 * 2008649 * 2
def baseEnd_2008649 : Nat := 343800801057672295083299

theorem tailTrace_2008649 : CollatzResearch.WordTrace tailWord_2008649 prefixEnd_2008649 343800801057672295083299 := by
  unfold tailWord_2008649
  simp only [CollatzResearch.WordTrace]
  refine ⟨73261447700015197782709001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48840965133343465188472667 73261447700015197782709001)
  ·
    refine ⟨54946085775011398337031751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73261447700015197782709001 54946085775011398337031751)
    ·
      refine ⟨82419128662517097505547627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54946085775011398337031751 82419128662517097505547627)
      ·
        refine ⟨123628692993775646258321441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82419128662517097505547627 123628692993775646258321441)
        ·
          refine ⟨92721519745331734693741081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123628692993775646258321441 92721519745331734693741081)
          ·
            refine ⟨69541139808998801020305811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92721519745331734693741081 69541139808998801020305811)
            ·
              refine ⟨104311709713498201530458717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69541139808998801020305811 104311709713498201530458717)
              ·
                refine ⟨39116891142561825573922019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104311709713498201530458717 39116891142561825573922019)
                ·
                  refine ⟨58675336713842738360883029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39116891142561825573922019 58675336713842738360883029)
                  ·
                    refine ⟨343800801057672295083299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 58675336713842738360883029 343800801057672295083299)
                    ·
                      rfl

theorem cell23_2008649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_2008649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008649 prefixEnd_2008649 := by exact prefixLift 2008649
  have htrace : WordTrace (prefixWord ++ tailWord_2008649) baseStart_2008649 baseEnd_2008649 := by
    simpa [prefixWord, tailWord_2008649, baseEnd_2008649] using wordTrace_append hprefix tailTrace_2008649
  have hstable : (prefixWord ++ tailWord_2008649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008649).length < 2 ^ (prefixWord ++ tailWord_2008649).sum := by decide
  have hdescent : baseEnd_2008649 < baseStart_2008649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008663 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_2008663 : Nat := 118140960795 + 2008663 * 2 ^ 59
def prefixEnd_2008663 : Nat := 4983230072969 + 3 ^ 40 * 2008663 * 2
def baseEnd_2008663 : Nat := 1031409591902179830474833

theorem tailTrace_2008663 : CollatzResearch.WordTrace tailWord_2008663 prefixEnd_2008663 1031409591902179830474833 := by
  unfold tailWord_2008663
  simp only [CollatzResearch.WordTrace]
  refine ⟨73261958321964478173718643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48841305547976318782479095 73261958321964478173718643)
  ·
    refine ⟨109892937482946717260577965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73261958321964478173718643 109892937482946717260577965)
    ·
      refine ⟨41209851556105018972716737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109892937482946717260577965 41209851556105018972716737)
      ·
        refine ⟨30907388667078764229537553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41209851556105018972716737 30907388667078764229537553)
        ·
          refine ⟨23180541500309073172153165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30907388667078764229537553 23180541500309073172153165)
          ·
            refine ⟨8692703062615902439557437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23180541500309073172153165 8692703062615902439557437)
            ·
              refine ⟨3259763648480963414834039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8692703062615902439557437 3259763648480963414834039)
              ·
                refine ⟨4889645472721445122251059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259763648480963414834039 4889645472721445122251059)
                ·
                  refine ⟨7334468209082167683376589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4889645472721445122251059 7334468209082167683376589)
                  ·
                    refine ⟨2750425578405812881266221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7334468209082167683376589 2750425578405812881266221)
                    ·
                      refine ⟨1031409591902179830474833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750425578405812881266221 1031409591902179830474833)
                      ·
                        rfl

theorem cell23_2008663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_2008663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008663 prefixEnd_2008663 := by exact prefixLift 2008663
  have htrace : WordTrace (prefixWord ++ tailWord_2008663) baseStart_2008663 baseEnd_2008663 := by
    simpa [prefixWord, tailWord_2008663, baseEnd_2008663] using wordTrace_append hprefix tailTrace_2008663
  have hstable : (prefixWord ++ tailWord_2008663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008663).length < 2 ^ (prefixWord ++ tailWord_2008663).sum := by decide
  have hdescent : baseEnd_2008663 < baseStart_2008663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008676 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_2008676 : Nat := 118140960795 + 2008676 * 2 ^ 59
def prefixEnd_2008676 : Nat := 4983230072969 + 3 ^ 40 * 2008676 * 2
def baseEnd_2008676 : Nat := 1031416267150688279612273

theorem tailTrace_2008676 : CollatzResearch.WordTrace tailWord_2008676 prefixEnd_2008676 1031416267150688279612273 := by
  unfold tailWord_2008676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631216235458690696970941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48841621647278254262627921 36631216235458690696970941)
  ·
    refine ⟨13736706088297009011364103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36631216235458690696970941 13736706088297009011364103)
    ·
      refine ⟨20605059132445513517046155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13736706088297009011364103 20605059132445513517046155)
      ·
        refine ⟨30907588698668270275569233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20605059132445513517046155 30907588698668270275569233)
        ·
          refine ⟨23180691524001202706676925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30907588698668270275569233 23180691524001202706676925)
          ·
            refine ⟨8692759321500451015003847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23180691524001202706676925 8692759321500451015003847)
            ·
              refine ⟨13039138982250676522505771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692759321500451015003847 13039138982250676522505771)
              ·
                refine ⟨19558708473376014783758657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039138982250676522505771 19558708473376014783758657)
                ·
                  refine ⟨14669031355032011087818993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19558708473376014783758657 14669031355032011087818993)
                  ·
                    refine ⟨11001773516274008315864245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14669031355032011087818993 11001773516274008315864245)
                    ·
                      refine ⟨1031416267150688279612273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11001773516274008315864245 1031416267150688279612273)
                      ·
                        rfl

theorem cell23_2008676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_2008676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008676 prefixEnd_2008676 := by exact prefixLift 2008676
  have htrace : WordTrace (prefixWord ++ tailWord_2008676) baseStart_2008676 baseEnd_2008676 := by
    simpa [prefixWord, tailWord_2008676, baseEnd_2008676] using wordTrace_append hprefix tailTrace_2008676
  have hstable : (prefixWord ++ tailWord_2008676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008676).length < 2 ^ (prefixWord ++ tailWord_2008676).sum := by decide
  have hdescent : baseEnd_2008676 < baseStart_2008676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008680 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2008680 : Nat := 118140960795 + 2008680 * 2 ^ 59
def prefixEnd_2008680 : Nat := 4983230072969 + 3 ^ 40 * 2008680 * 2
def baseEnd_2008680 : Nat := 1031418321073306263962255

theorem tailTrace_2008680 : CollatzResearch.WordTrace tailWord_2008680 prefixEnd_2008680 1031418321073306263962255 := by
  unfold tailWord_2008680
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631289181451445038543747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48841718908601926718058329 36631289181451445038543747)
  ·
    refine ⟨54946933772177167557815621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36631289181451445038543747 54946933772177167557815621)
    ·
      refine ⟨10302550082283218917090429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54946933772177167557815621 10302550082283218917090429)
      ·
        refine ⟨3863456280856207093908911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10302550082283218917090429 3863456280856207093908911)
        ·
          refine ⟨5795184421284310640863367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863456280856207093908911 5795184421284310640863367)
          ·
            refine ⟨8692776631926465961295051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795184421284310640863367 8692776631926465961295051)
            ·
              refine ⟨13039164947889698941942577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692776631926465961295051 13039164947889698941942577)
              ·
                refine ⟨9779373710917274206456933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13039164947889698941942577 9779373710917274206456933)
                ·
                  refine ⟨1833632570796988913710675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9779373710917274206456933 1833632570796988913710675)
                  ·
                    refine ⟨2750448856195483370566013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1833632570796988913710675 2750448856195483370566013)
                    ·
                      refine ⟨1031418321073306263962255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750448856195483370566013 1031418321073306263962255)
                      ·
                        rfl

theorem cell23_2008680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2008680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008680 prefixEnd_2008680 := by exact prefixLift 2008680
  have htrace : WordTrace (prefixWord ++ tailWord_2008680) baseStart_2008680 baseEnd_2008680 := by
    simpa [prefixWord, tailWord_2008680, baseEnd_2008680] using wordTrace_append hprefix tailTrace_2008680
  have hstable : (prefixWord ++ tailWord_2008680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008680).length < 2 ^ (prefixWord ++ tailWord_2008680).sum := by decide
  have hdescent : baseEnd_2008680 < baseStart_2008680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008714 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2008714 : Nat := 118140960795 + 2008714 * 2 ^ 59
def prefixEnd_2008714 : Nat := 4983230072969 + 3 ^ 40 * 2008714 * 2
def baseEnd_2008714 : Nat := 1031435779415559130937099

theorem tailTrace_2008714 : CollatzResearch.WordTrace tailWord_2008714 prefixEnd_2008714 1031435779415559130937099 := by
  unfold tailWord_2008714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315954611194928470956299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48842545629853142589216797 18315954611194928470956299)
  ·
    refine ⟨27473931916792392706434449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18315954611194928470956299 27473931916792392706434449)
    ·
      refine ⟨20605448937594294529825837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27473931916792392706434449 20605448937594294529825837)
      ·
        refine ⟨7727043351597860448684689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20605448937594294529825837 7727043351597860448684689)
        ·
          refine ⟨5795282513698395336513517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7727043351597860448684689 5795282513698395336513517)
          ·
            refine ⟨2173230942636898251192569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5795282513698395336513517 2173230942636898251192569)
            ·
              refine ⟨1629923206977673688394427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2173230942636898251192569 1629923206977673688394427)
              ·
                refine ⟨2444884810466510532591641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629923206977673688394427 2444884810466510532591641)
                ·
                  refine ⟨1833663607849882899443731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444884810466510532591641 1833663607849882899443731)
                  ·
                    refine ⟨2750495411774824349165597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1833663607849882899443731 2750495411774824349165597)
                    ·
                      refine ⟨1031435779415559130937099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750495411774824349165597 1031435779415559130937099)
                      ·
                        rfl

theorem cell23_2008714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2008714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008714 prefixEnd_2008714 := by exact prefixLift 2008714
  have htrace : WordTrace (prefixWord ++ tailWord_2008714) baseStart_2008714 baseEnd_2008714 := by
    simpa [prefixWord, tailWord_2008714, baseEnd_2008714] using wordTrace_append hprefix tailTrace_2008714
  have hstable : (prefixWord ++ tailWord_2008714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008714).length < 2 ^ (prefixWord ++ tailWord_2008714).sum := by decide
  have hdescent : baseEnd_2008714 < baseStart_2008714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008716 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2008716 : Nat := 118140960795 + 2008716 * 2 ^ 59
def prefixEnd_2008716 : Nat := 4983230072969 + 3 ^ 40 * 2008716 * 2
def baseEnd_2008716 : Nat := 1031436806376868123112089

theorem tailTrace_2008716 : CollatzResearch.WordTrace tailWord_2008716 prefixEnd_2008716 1031436806376868123112089 := by
  unfold tailWord_2008716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631945695386234112699001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48842594260514978816932001 36631945695386234112699001)
  ·
    refine ⟨27473959271539675584524251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36631945695386234112699001 27473959271539675584524251)
    ·
      refine ⟨41210938907309513376786377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27473959271539675584524251 41210938907309513376786377)
      ·
        refine ⟨30908204180482135032589783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41210938907309513376786377 30908204180482135032589783)
        ·
          refine ⟨46362306270723202548884675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30908204180482135032589783 46362306270723202548884675)
          ·
            refine ⟨69543459406084803823327013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46362306270723202548884675 69543459406084803823327013)
            ·
              refine ⟨13039398638640900716873815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69543459406084803823327013 13039398638640900716873815)
              ·
                refine ⟨19559097957961351075310723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13039398638640900716873815 19559097957961351075310723)
                ·
                  refine ⟨29338646936942026612966085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19559097957961351075310723 29338646936942026612966085)
                  ·
                    refine ⟨5500996300676629989931141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29338646936942026612966085 5500996300676629989931141)
                    ·
                      refine ⟨1031436806376868123112089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5500996300676629989931141 1031436806376868123112089)
                      ·
                        rfl

theorem cell23_2008716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2008716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008716 prefixEnd_2008716 := by exact prefixLift 2008716
  have htrace : WordTrace (prefixWord ++ tailWord_2008716) baseStart_2008716 baseEnd_2008716 := by
    simpa [prefixWord, tailWord_2008716, baseEnd_2008716] using wordTrace_append hprefix tailTrace_2008716
  have hstable : (prefixWord ++ tailWord_2008716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008716).length < 2 ^ (prefixWord ++ tailWord_2008716).sum := by decide
  have hdescent : baseEnd_2008716 < baseStart_2008716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008793 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_2008793 : Nat := 118140960795 + 2008793 * 2 ^ 59
def prefixEnd_2008793 : Nat := 4983230072969 + 3 ^ 40 * 2008793 * 2
def baseEnd_2008793 : Nat := 1031476344387264321849235

theorem tailTrace_2008793 : CollatzResearch.WordTrace tailWord_2008793 prefixEnd_2008793 1031476344387264321849235 := by
  unfold tailWord_2008793
  simp only [CollatzResearch.WordTrace]
  refine ⟨73266699811493510375951033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48844466540995673583967355 73266699811493510375951033)
  ·
    refine ⟨54950024858620132781963275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73266699811493510375951033 54950024858620132781963275)
    ·
      refine ⟨82425037287930199172944913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54950024858620132781963275 82425037287930199172944913)
      ·
        refine ⟨61818777965947649379708685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82425037287930199172944913 61818777965947649379708685)
        ·
          refine ⟨23182041737230368517390757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61818777965947649379708685 23182041737230368517390757)
          ·
            refine ⟨4346632825730694097010767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23182041737230368517390757 4346632825730694097010767)
            ·
              refine ⟨6519949238596041145516151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4346632825730694097010767 6519949238596041145516151)
              ·
                refine ⟨9779923857894061718274227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6519949238596041145516151 9779923857894061718274227)
                ·
                  refine ⟨14669885786841092577411341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9779923857894061718274227 14669885786841092577411341)
                  ·
                    refine ⟨5501207170065409716529253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14669885786841092577411341 5501207170065409716529253)
                    ·
                      refine ⟨1031476344387264321849235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5501207170065409716529253 1031476344387264321849235)
                      ·
                        rfl

theorem cell23_2008793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_2008793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008793 prefixEnd_2008793 := by exact prefixLift 2008793
  have htrace : WordTrace (prefixWord ++ tailWord_2008793) baseStart_2008793 baseEnd_2008793 := by
    simpa [prefixWord, tailWord_2008793, baseEnd_2008793] using wordTrace_append hprefix tailTrace_2008793
  have hstable : (prefixWord ++ tailWord_2008793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008793).length < 2 ^ (prefixWord ++ tailWord_2008793).sum := by decide
  have hdescent : baseEnd_2008793 < baseStart_2008793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008810 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_2008810 : Nat := 118140960795 + 2008810 * 2 ^ 59
def prefixEnd_2008810 : Nat := 4983230072969 + 3 ^ 40 * 2008810 * 2
def baseEnd_2008810 : Nat := 1031485073558390755336657

theorem tailTrace_2008810 : CollatzResearch.WordTrace tailWord_2008810 prefixEnd_2008810 1031485073558390755336657 := by
  unfold tailWord_2008810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18316829963107980569829971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48844879901621281519546589 18316829963107980569829971)
  ·
    refine ⟨27475244944661970854744957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18316829963107980569829971 27475244944661970854744957)
    ·
      refine ⟨10303216854248239070529359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27475244944661970854744957 10303216854248239070529359)
      ·
        refine ⟨15454825281372358605794039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303216854248239070529359 15454825281372358605794039)
        ·
          refine ⟨23182237922058537908691059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454825281372358605794039 23182237922058537908691059)
          ·
            refine ⟨34773356883087806863036589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23182237922058537908691059 34773356883087806863036589)
            ·
              refine ⟨13040008831157927573638721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34773356883087806863036589 13040008831157927573638721)
              ·
                refine ⟨9780006623368445680229041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13040008831157927573638721 9780006623368445680229041)
                ·
                  refine ⟨7335004967526334260171781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9780006623368445680229041 7335004967526334260171781)
                  ·
                    refine ⟨1375313431411187673782209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7335004967526334260171781 1375313431411187673782209)
                    ·
                      refine ⟨1031485073558390755336657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375313431411187673782209 1031485073558390755336657)
                      ·
                        rfl

theorem cell23_2008810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_2008810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008810 prefixEnd_2008810 := by exact prefixLift 2008810
  have htrace : WordTrace (prefixWord ++ tailWord_2008810) baseStart_2008810 baseEnd_2008810 := by
    simpa [prefixWord, tailWord_2008810, baseEnd_2008810] using wordTrace_append hprefix tailTrace_2008810
  have hstable : (prefixWord ++ tailWord_2008810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008810).length < 2 ^ (prefixWord ++ tailWord_2008810).sum := by decide
  have hdescent : baseEnd_2008810 < baseStart_2008810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008833 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 6]
def baseStart_2008833 : Nat := 118140960795 + 2008833 * 2 ^ 59
def prefixEnd_2008833 : Nat := 4983230072969 + 3 ^ 40 * 2008833 * 2
def baseEnd_2008833 : Nat := 114610764845938240594339

theorem tailTrace_2008833 : CollatzResearch.WordTrace tailWord_2008833 prefixEnd_2008833 114610764845938240594339 := by
  unfold tailWord_2008833
  simp only [CollatzResearch.WordTrace]
  refine ⟨73268158731348597207407153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48845439154232398138271435 73268158731348597207407153)
  ·
    refine ⟨54951119048511447905555365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73268158731348597207407153 54951119048511447905555365)
    ·
      refine ⟨10303334821595896482291631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54951119048511447905555365 10303334821595896482291631)
      ·
        refine ⟨15455002232393844723437447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303334821595896482291631 15455002232393844723437447)
        ·
          refine ⟨23182503348590767085156171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15455002232393844723437447 23182503348590767085156171)
          ·
            refine ⟨34773755022886150627734257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23182503348590767085156171 34773755022886150627734257)
            ·
              refine ⟨26080316267164612970800693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34773755022886150627734257 26080316267164612970800693)
              ·
                refine ⟨2445029650046682466012565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26080316267164612970800693 2445029650046682466012565)
                ·
                  refine ⟨114610764845938240594339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2445029650046682466012565 114610764845938240594339)
                  ·
                    rfl

theorem cell23_2008833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_2008833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008833 prefixEnd_2008833 := by exact prefixLift 2008833
  have htrace : WordTrace (prefixWord ++ tailWord_2008833) baseStart_2008833 baseEnd_2008833 := by
    simpa [prefixWord, tailWord_2008833, baseEnd_2008833] using wordTrace_append hprefix tailTrace_2008833
  have hstable : (prefixWord ++ tailWord_2008833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008833).length < 2 ^ (prefixWord ++ tailWord_2008833).sum := by decide
  have hdescent : baseEnd_2008833 < baseStart_2008833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008845 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2008845 : Nat := 118140960795 + 2008845 * 2 ^ 59
def prefixEnd_2008845 : Nat := 4983230072969 + 3 ^ 40 * 2008845 * 2
def baseEnd_2008845 : Nat := 114611449486810902044333

theorem tailTrace_2008845 : CollatzResearch.WordTrace tailWord_2008845 prefixEnd_2008845 114611449486810902044333 := by
  unfold tailWord_2008845
  simp only [CollatzResearch.WordTrace]
  refine ⟨73268596407305123256843989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48845730938203415504562659 73268596407305123256843989)
  ·
    refine ⟨1717232728296213826332281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 73268596407305123256843989 1717232728296213826332281)
    ·
      refine ⟨1287924546222160369749211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1717232728296213826332281 1287924546222160369749211)
      ·
        refine ⟨1931886819333240554623817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287924546222160369749211 1931886819333240554623817)
        ·
          refine ⟨1448915114499930415967863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931886819333240554623817 1448915114499930415967863)
          ·
            refine ⟨2173372671749895623951795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448915114499930415967863 2173372671749895623951795)
            ·
              refine ⟨3260059007624843435927693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173372671749895623951795 3260059007624843435927693)
              ·
                refine ⟨1222522127859316288472885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3260059007624843435927693 1222522127859316288472885)
                ·
                  refine ⟨114611449486810902044333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222522127859316288472885 114611449486810902044333)
                  ·
                    rfl

theorem cell23_2008845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2008845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008845 prefixEnd_2008845 := by exact prefixLift 2008845
  have htrace : WordTrace (prefixWord ++ tailWord_2008845) baseStart_2008845 baseEnd_2008845 := by
    simpa [prefixWord, tailWord_2008845, baseEnd_2008845] using wordTrace_append hprefix tailTrace_2008845
  have hstable : (prefixWord ++ tailWord_2008845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008845).length < 2 ^ (prefixWord ++ tailWord_2008845).sum := by decide
  have hdescent : baseEnd_2008845 < baseStart_2008845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008850 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_2008850 : Nat := 118140960795 + 2008850 * 2 ^ 59
def prefixEnd_2008850 : Nat := 4983230072969 + 3 ^ 40 * 2008850 * 2
def baseEnd_2008850 : Nat := 114611734753841177648497

theorem tailTrace_2008850 : CollatzResearch.WordTrace tailWord_2008850 prefixEnd_2008850 114611734753841177648497 := by
  unfold tailWord_2008850
  simp only [CollatzResearch.WordTrace]
  refine ⟨18317194693071752277694001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48845852514858006073850669 18317194693071752277694001)
  ·
    refine ⟨13737896019803814208270501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18317194693071752277694001 13737896019803814208270501)
    ·
      refine ⟨2575855503713215164050719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13737896019803814208270501 2575855503713215164050719)
      ·
        refine ⟨3863783255569822746076079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575855503713215164050719 3863783255569822746076079)
        ·
          refine ⟨5795674883354734119114119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863783255569822746076079 5795674883354734119114119)
          ·
            refine ⟨8693512325032101178671179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795674883354734119114119 8693512325032101178671179)
            ·
              refine ⟨13040268487548151768006769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693512325032101178671179 13040268487548151768006769)
              ·
                refine ⟨9780201365661113826005077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13040268487548151768006769 9780201365661113826005077)
                ·
                  refine ⟨114611734753841177648497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9780201365661113826005077 114611734753841177648497)
                  ·
                    rfl

theorem cell23_2008850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_2008850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008850 prefixEnd_2008850 := by exact prefixLift 2008850
  have htrace : WordTrace (prefixWord ++ tailWord_2008850) baseStart_2008850 baseEnd_2008850 := by
    simpa [prefixWord, tailWord_2008850, baseEnd_2008850] using wordTrace_append hprefix tailTrace_2008850
  have hstable : (prefixWord ++ tailWord_2008850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008850).length < 2 ^ (prefixWord ++ tailWord_2008850).sum := by decide
  have hdescent : baseEnd_2008850 < baseStart_2008850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008884 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2008884 : Nat := 118140960795 + 2008884 * 2 ^ 59
def prefixEnd_2008884 : Nat := 4983230072969 + 3 ^ 40 * 2008884 * 2
def baseEnd_2008884 : Nat := 114613674569647051756813

theorem tailTrace_2008884 : CollatzResearch.WordTrace tailWord_2008884 prefixEnd_2008884 114613674569647051756813 := by
  unfold tailWord_2008884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36635009427081916458756853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48846679236109221945009137 36635009427081916458756853)
  ·
    refine ⟨3434532133788929668008455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36635009427081916458756853 3434532133788929668008455)
    ·
      refine ⟨5151798200683394502012683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434532133788929668008455 5151798200683394502012683)
      ·
        refine ⟨7727697301025091753019025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151798200683394502012683 7727697301025091753019025)
        ·
          refine ⟨5795772975768818814764269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7727697301025091753019025 5795772975768818814764269)
          ·
            refine ⟨2173414865913307055536601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5795772975768818814764269 2173414865913307055536601)
            ·
              refine ⟨1630061149434980291652451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2173414865913307055536601 1630061149434980291652451)
              ·
                refine ⟨2445091724152470437478677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630061149434980291652451 2445091724152470437478677)
                ·
                  refine ⟨114613674569647051756813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2445091724152470437478677 114613674569647051756813)
                  ·
                    rfl

theorem cell23_2008884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2008884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008884 prefixEnd_2008884 := by exact prefixLift 2008884
  have htrace : WordTrace (prefixWord ++ tailWord_2008884) baseStart_2008884 baseEnd_2008884 := by
    simpa [prefixWord, tailWord_2008884, baseEnd_2008884] using wordTrace_append hprefix tailTrace_2008884
  have hstable : (prefixWord ++ tailWord_2008884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008884).length < 2 ^ (prefixWord ++ tailWord_2008884).sum := by decide
  have hdescent : baseEnd_2008884 < baseStart_2008884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008903 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2008903 : Nat := 118140960795 + 2008903 * 2 ^ 59
def prefixEnd_2008903 : Nat := 4983230072969 + 3 ^ 40 * 2008903 * 2
def baseEnd_2008903 : Nat := 1031532827259258891473729

theorem tailTrace_2008903 : CollatzResearch.WordTrace tailWord_2008903 prefixEnd_2008903 1031532827259258891473729 := by
  unfold tailWord_2008903
  simp only [CollatzResearch.WordTrace]
  refine ⟨73270711841094999162455363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48847141227396666108303575 73270711841094999162455363)
  ·
    refine ⟨109906067761642498743683045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73270711841094999162455363 109906067761642498743683045)
    ·
      refine ⟨20607387705307968514440571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109906067761642498743683045 20607387705307968514440571)
      ·
        refine ⟨30911081557961952771660857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20607387705307968514440571 30911081557961952771660857)
        ·
          refine ⟨23183311168471464578745643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30911081557961952771660857 23183311168471464578745643)
          ·
            refine ⟨34774966752707196868118465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23183311168471464578745643 34774966752707196868118465)
            ·
              refine ⟨26081225064530397651088849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34774966752707196868118465 26081225064530397651088849)
              ·
                refine ⟨19560918798397798238316637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26081225064530397651088849 19560918798397798238316637)
                ·
                  refine ⟨7335344549399174339368739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19560918798397798238316637 7335344549399174339368739)
                  ·
                    refine ⟨11003016824098761509053109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7335344549399174339368739 11003016824098761509053109)
                    ·
                      refine ⟨1031532827259258891473729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11003016824098761509053109 1031532827259258891473729)
                      ·
                        rfl

theorem cell23_2008903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2008903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008903 prefixEnd_2008903 := by exact prefixLift 2008903
  have htrace : WordTrace (prefixWord ++ tailWord_2008903) baseStart_2008903 baseEnd_2008903 := by
    simpa [prefixWord, tailWord_2008903, baseEnd_2008903] using wordTrace_append hprefix tailTrace_2008903
  have hstable : (prefixWord ++ tailWord_2008903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008903).length < 2 ^ (prefixWord ++ tailWord_2008903).sum := by decide
  have hdescent : baseEnd_2008903 < baseStart_2008903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008927 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 2, 4]
def baseStart_2008927 : Nat := 118140960795 + 2008927 * 2 ^ 59
def prefixEnd_2008927 : Nat := 4983230072969 + 3 ^ 40 * 2008927 * 2
def baseEnd_2008927 : Nat := 343848383598322265857873

theorem tailTrace_2008927 : CollatzResearch.WordTrace tailWord_2008927 prefixEnd_2008927 343848383598322265857873 := by
  unfold tailWord_2008927
  simp only [CollatzResearch.WordTrace]
  refine ⟨73271587193008051261329035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48847724795338700840886023 73271587193008051261329035)
  ·
    refine ⟨109907380789512076891993553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73271587193008051261329035 109907380789512076891993553)
    ·
      refine ⟨82430535592134057668995165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109907380789512076891993553 82430535592134057668995165)
      ·
        refine ⟨30911450847050271625873187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82430535592134057668995165 30911450847050271625873187)
        ·
          refine ⟨46367176270575407438809781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30911450847050271625873187 46367176270575407438809781)
          ·
            refine ⟨4346922775366444447388417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46367176270575407438809781 4346922775366444447388417)
            ·
              refine ⟨3260192081524833335541313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4346922775366444447388417 3260192081524833335541313)
              ·
                refine ⟨2445144061143625001655985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260192081524833335541313 2445144061143625001655985)
                ·
                  refine ⟨1833858045857718751241989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445144061143625001655985 1833858045857718751241989)
                  ·
                    refine ⟨343848383598322265857873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833858045857718751241989 343848383598322265857873)
                    ·
                      rfl

theorem cell23_2008927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_2008927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008927 prefixEnd_2008927 := by exact prefixLift 2008927
  have htrace : WordTrace (prefixWord ++ tailWord_2008927) baseStart_2008927 baseEnd_2008927 := by
    simpa [prefixWord, tailWord_2008927, baseEnd_2008927] using wordTrace_append hprefix tailTrace_2008927
  have hstable : (prefixWord ++ tailWord_2008927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008927).length < 2 ^ (prefixWord ++ tailWord_2008927).sum := by decide
  have hdescent : baseEnd_2008927 < baseStart_2008927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008940 : List Nat := [2, 2, 1, 1, 4, 4, 1, 8]
def baseStart_2008940 : Nat := 118140960795 + 2008940 * 2 ^ 59
def prefixEnd_2008940 : Nat := 4983230072969 + 3 ^ 40 * 2008940 * 2
def baseEnd_2008940 : Nat := 38205623186795379507817

theorem tailTrace_2008940 : CollatzResearch.WordTrace tailWord_2008940 prefixEnd_2008940 38205623186795379507817 := by
  unfold tailWord_2008940
  simp only [CollatzResearch.WordTrace]
  refine ⟨36636030670980477240776137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48848040894640636321034849 36636030670980477240776137)
  ·
    refine ⟨27477023003235357930582103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36636030670980477240776137 27477023003235357930582103)
    ·
      refine ⟨41215534504853036895873155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27477023003235357930582103 41215534504853036895873155)
      ·
        refine ⟨61823301757279555343809733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41215534504853036895873155 61823301757279555343809733)
        ·
          refine ⟨11591869079489916626964325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61823301757279555343809733 11591869079489916626964325)
          ·
            refine ⟨2173475452404359367555811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11591869079489916626964325 2173475452404359367555811)
            ·
              refine ⟨3260213178606539051333717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173475452404359367555811 3260213178606539051333717)
              ·
                refine ⟨38205623186795379507817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3260213178606539051333717 38205623186795379507817)
                ·
                  rfl

theorem cell23_2008940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 8].length) (baseStart_2008940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008940 prefixEnd_2008940 := by exact prefixLift 2008940
  have htrace : WordTrace (prefixWord ++ tailWord_2008940) baseStart_2008940 baseEnd_2008940 := by
    simpa [prefixWord, tailWord_2008940, baseEnd_2008940] using wordTrace_append hprefix tailTrace_2008940
  have hstable : (prefixWord ++ tailWord_2008940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008940).length < 2 ^ (prefixWord ++ tailWord_2008940).sum := by decide
  have hdescent : baseEnd_2008940 < baseStart_2008940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008953 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_2008953 : Nat := 118140960795 + 2008953 * 2 ^ 59
def prefixEnd_2008953 : Nat := 4983230072969 + 3 ^ 40 * 2008953 * 2
def baseEnd_2008953 : Nat := 343852833763994565282833

theorem tailTrace_2008953 : CollatzResearch.WordTrace tailWord_2008953 prefixEnd_2008953 343852833763994565282833 := by
  unfold tailWord_2008953
  simp only [CollatzResearch.WordTrace]
  refine ⟨73272535490913857701775513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48848356993942571801183675 73272535490913857701775513)
  ·
    refine ⟨54954401618185393276331635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73272535490913857701775513 54954401618185393276331635)
    ·
      refine ⟨82431602427278089914497453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54954401618185393276331635 82431602427278089914497453)
      ·
        refine ⟨30911850910229283717936545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82431602427278089914497453 30911850910229283717936545)
        ·
          refine ⟨23183888182671962788452409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30911850910229283717936545 23183888182671962788452409)
          ·
            refine ⟨17387916137003972091339307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23183888182671962788452409 17387916137003972091339307)
            ·
              refine ⟨26081874205505958137008961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17387916137003972091339307 26081874205505958137008961)
              ·
                refine ⟨19561405654129468602756721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26081874205505958137008961 19561405654129468602756721)
                ·
                  refine ⟨14671054240597101452067541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19561405654129468602756721 14671054240597101452067541)
                  ·
                    refine ⟨343852833763994565282833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14671054240597101452067541 343852833763994565282833)
                    ·
                      rfl

theorem cell23_2008953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_2008953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008953 prefixEnd_2008953 := by exact prefixLift 2008953
  have htrace : WordTrace (prefixWord ++ tailWord_2008953) baseStart_2008953 baseEnd_2008953 := by
    simpa [prefixWord, tailWord_2008953, baseEnd_2008953] using wordTrace_append hprefix tailTrace_2008953
  have hstable : (prefixWord ++ tailWord_2008953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008953).length < 2 ^ (prefixWord ++ tailWord_2008953).sum := by decide
  have hdescent : baseEnd_2008953 < baseStart_2008953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2008968 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_2008968 : Nat := 118140960795 + 2008968 * 2 ^ 59
def prefixEnd_2008968 : Nat := 4983230072969 + 3 ^ 40 * 2008968 * 2
def baseEnd_2008968 : Nat := 1031566203501801137160931

theorem tailTrace_2008968 : CollatzResearch.WordTrace tailWord_2008968 prefixEnd_2008968 1031566203501801137160931 := by
  unfold tailWord_2008968
  simp only [CollatzResearch.WordTrace]
  refine ⟨36636541292929757631785779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48848721723906343509047705 36636541292929757631785779)
  ·
    refine ⟨54954811939394636447678669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36636541292929757631785779 54954811939394636447678669)
    ·
      refine ⟨20608054477272988667879501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54954811939394636447678669 20608054477272988667879501)
      ·
        refine ⟨7728020428977370750454813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20608054477272988667879501 7728020428977370750454813)
        ·
          refine ⟨2898007660866514031420555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7728020428977370750454813 2898007660866514031420555)
          ·
            refine ⟨4347011491299771047130833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898007660866514031420555 4347011491299771047130833)
            ·
              refine ⟨3260258618474828285348125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347011491299771047130833 3260258618474828285348125)
              ·
                refine ⟨1222596981928060607005547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3260258618474828285348125 1222596981928060607005547)
                ·
                  refine ⟨1833895472892090910508321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222596981928060607005547 1833895472892090910508321)
                  ·
                    refine ⟨1375421604669068182881241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1833895472892090910508321 1375421604669068182881241)
                    ·
                      refine ⟨1031566203501801137160931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375421604669068182881241 1031566203501801137160931)
                      ·
                        rfl

theorem cell23_2008968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_2008968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2008968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2008968 prefixEnd_2008968 := by exact prefixLift 2008968
  have htrace : WordTrace (prefixWord ++ tailWord_2008968) baseStart_2008968 baseEnd_2008968 := by
    simpa [prefixWord, tailWord_2008968, baseEnd_2008968] using wordTrace_append hprefix tailTrace_2008968
  have hstable : (prefixWord ++ tailWord_2008968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2008968).length < 2 ^ (prefixWord ++ tailWord_2008968).sum := by decide
  have hdescent : baseEnd_2008968 < baseStart_2008968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2008968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009010 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2009010 : Nat := 118140960795 + 2009010 * 2 ^ 59
def prefixEnd_2009010 : Nat := 4983230072969 + 3 ^ 40 * 2009010 * 2
def baseEnd_2009010 : Nat := 1031587769689289972835737

theorem tailTrace_2009010 : CollatzResearch.WordTrace tailWord_2009010 prefixEnd_2009010 1031587769689289972835737 := by
  unfold tailWord_2009010
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318653612926839109150121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48849742967804904291066989 18318653612926839109150121)
  ·
    refine ⟨13738990209695129331862591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18318653612926839109150121 13738990209695129331862591)
    ·
      refine ⟨20608485314542693997793887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13738990209695129331862591 20608485314542693997793887)
      ·
        refine ⟨30912727971814040996690831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20608485314542693997793887 30912727971814040996690831)
        ·
          refine ⟨46369091957721061495036247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30912727971814040996690831 46369091957721061495036247)
          ·
            refine ⟨69553637936581592242554371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46369091957721061495036247 69553637936581592242554371)
            ·
              refine ⟨104330456904872388363831557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69553637936581592242554371 104330456904872388363831557)
              ·
                refine ⟨19561960669663572818218417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104330456904872388363831557 19561960669663572818218417)
                ·
                  refine ⟨14671470502247679613663813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19561960669663572818218417 14671470502247679613663813)
                  ·
                    refine ⟨2750900719171439927561965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14671470502247679613663813 2750900719171439927561965)
                    ·
                      refine ⟨1031587769689289972835737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750900719171439927561965 1031587769689289972835737)
                      ·
                        rfl

theorem cell23_2009010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2009010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009010 prefixEnd_2009010 := by exact prefixLift 2009010
  have htrace : WordTrace (prefixWord ++ tailWord_2009010) baseStart_2009010 baseEnd_2009010 := by
    simpa [prefixWord, tailWord_2009010, baseEnd_2009010] using wordTrace_append hprefix tailTrace_2009010
  have hstable : (prefixWord ++ tailWord_2009010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009010).length < 2 ^ (prefixWord ++ tailWord_2009010).sum := by decide
  have hdescent : baseEnd_2009010 < baseStart_2009010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009040 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_2009040 : Nat := 118140960795 + 2009040 * 2 ^ 59
def prefixEnd_2009040 : Nat := 4983230072969 + 3 ^ 40 * 2009040 * 2
def baseEnd_2009040 : Nat := 1031603174108924855460599

theorem tailTrace_2009040 : CollatzResearch.WordTrace tailWord_2009040 prefixEnd_2009040 1031603174108924855460599 := by
  unfold tailWord_2009040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36637854320799335780096287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48850472427732447706795049 36637854320799335780096287)
  ·
    refine ⟨54956781481199003670144431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36637854320799335780096287 54956781481199003670144431)
    ·
      refine ⟨82435172221798505505216647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54956781481199003670144431 82435172221798505505216647)
      ·
        refine ⟨123652758332697758257824971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82435172221798505505216647 123652758332697758257824971)
        ·
          refine ⟨185479137499046637386737457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123652758332697758257824971 185479137499046637386737457)
          ·
            refine ⟨139109353124284978040053093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185479137499046637386737457 139109353124284978040053093)
            ·
              refine ⟨26083003710803433382509955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139109353124284978040053093 26083003710803433382509955)
              ·
                refine ⟨39124505566205150073764933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26083003710803433382509955 39124505566205150073764933)
                ·
                  refine ⟨7335844793663465638830925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39124505566205150073764933 7335844793663465638830925)
                  ·
                    refine ⟨2750941797623799614561597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7335844793663465638830925 2750941797623799614561597)
                    ·
                      refine ⟨1031603174108924855460599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750941797623799614561597 1031603174108924855460599)
                      ·
                        rfl

theorem cell23_2009040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_2009040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009040 prefixEnd_2009040 := by exact prefixLift 2009040
  have htrace : WordTrace (prefixWord ++ tailWord_2009040) baseStart_2009040 baseEnd_2009040 := by
    simpa [prefixWord, tailWord_2009040, baseEnd_2009040] using wordTrace_append hprefix tailTrace_2009040
  have hstable : (prefixWord ++ tailWord_2009040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009040).length < 2 ^ (prefixWord ++ tailWord_2009040).sum := by decide
  have hdescent : baseEnd_2009040 < baseStart_2009040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 13]
def baseStart_2009043 : Nat := 118140960795 + 2009043 * 2 ^ 59
def prefixEnd_2009043 : Nat := 4983230072969 + 3 ^ 40 * 2009043 * 2
def baseEnd_2009043 : Nat := 343868238183629447907695

theorem tailTrace_2009043 : CollatzResearch.WordTrace tailWord_2009043 prefixEnd_2009043 343868238183629447907695 := by
  unfold tailWord_2009043
  simp only [CollatzResearch.WordTrace]
  refine ⟨73275818060587803072551783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48850545373725202048367855 73275818060587803072551783)
  ·
    refine ⟨109913727090881704608827675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73275818060587803072551783 109913727090881704608827675)
    ·
      refine ⟨164870590636322556913241513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109913727090881704608827675 164870590636322556913241513)
      ·
        refine ⟨123652942977241917684931135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164870590636322556913241513 123652942977241917684931135)
        ·
          refine ⟨185479414465862876527396703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123652942977241917684931135 185479414465862876527396703)
          ·
            refine ⟨278219121698794314791095055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185479414465862876527396703 278219121698794314791095055)
            ·
              refine ⟨417328682548191472186642583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278219121698794314791095055 417328682548191472186642583)
              ·
                refine ⟨625993023822287208279963875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417328682548191472186642583 625993023822287208279963875)
                ·
                  refine ⟨938989535733430812419945813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 625993023822287208279963875 938989535733430812419945813)
                  ·
                    refine ⟨343868238183629447907695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 938989535733430812419945813 343868238183629447907695)
                    ·
                      rfl

theorem cell23_2009043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_2009043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009043 prefixEnd_2009043 := by exact prefixLift 2009043
  have htrace : WordTrace (prefixWord ++ tailWord_2009043) baseStart_2009043 baseEnd_2009043 := by
    simpa [prefixWord, tailWord_2009043, baseEnd_2009043] using wordTrace_append hprefix tailTrace_2009043
  have hstable : (prefixWord ++ tailWord_2009043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009043).length < 2 ^ (prefixWord ++ tailWord_2009043).sum := by decide
  have hdescent : baseEnd_2009043 < baseStart_2009043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009052 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2009052 : Nat := 118140960795 + 2009052 * 2 ^ 59
def prefixEnd_2009052 : Nat := 4983230072969 + 3 ^ 40 * 2009052 * 2
def baseEnd_2009052 : Nat := 1031609335876778808510545

theorem tailTrace_2009052 : CollatzResearch.WordTrace tailWord_2009052 prefixEnd_2009052 1031609335876778808510545 := by
  unfold tailWord_2009052
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638073158777598804814705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48850764211703465073086273 36638073158777598804814705)
  ·
    refine ⟨27478554869083199103611029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36638073158777598804814705 27478554869083199103611029)
    ·
      refine ⟨1288057259488274957981767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27478554869083199103611029 1288057259488274957981767)
      ·
        refine ⟨1932085889232412436972651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288057259488274957981767 1932085889232412436972651)
        ·
          refine ⟨2898128833848618655458977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932085889232412436972651 2898128833848618655458977)
          ·
            refine ⟨2173596625386463991594233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898128833848618655458977 2173596625386463991594233)
            ·
              refine ⟨1630197469039847993695675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2173596625386463991594233 1630197469039847993695675)
              ·
                refine ⟨2445296203559771990543513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630197469039847993695675 2445296203559771990543513)
                ·
                  refine ⟨1833972152669828992907635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445296203559771990543513 1833972152669828992907635)
                  ·
                    refine ⟨2750958229004743489361453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1833972152669828992907635 2750958229004743489361453)
                    ·
                      refine ⟨1031609335876778808510545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2750958229004743489361453 1031609335876778808510545)
                      ·
                        rfl

theorem cell23_2009052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2009052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009052 prefixEnd_2009052 := by exact prefixLift 2009052
  have htrace : WordTrace (prefixWord ++ tailWord_2009052) baseStart_2009052 baseEnd_2009052 := by
    simpa [prefixWord, tailWord_2009052, baseEnd_2009052] using wordTrace_append hprefix tailTrace_2009052
  have hstable : (prefixWord ++ tailWord_2009052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009052).length < 2 ^ (prefixWord ++ tailWord_2009052).sum := by decide
  have hdescent : baseEnd_2009052 < baseStart_2009052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009060 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_2009060 : Nat := 118140960795 + 2009060 * 2 ^ 59
def prefixEnd_2009060 : Nat := 4983230072969 + 3 ^ 40 * 2009060 * 2
def baseEnd_2009060 : Nat := 343871147907338259070169

theorem tailTrace_2009060 : CollatzResearch.WordTrace tailWord_2009060 prefixEnd_2009060 343871147907338259070169 := by
  unfold tailWord_2009060
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638219050763107487960317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48850958734350809983947089 36638219050763107487960317)
  ·
    refine ⟨13739332144036165307985119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36638219050763107487960317 13739332144036165307985119)
    ·
      refine ⟨20608998216054247961977679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13739332144036165307985119 20608998216054247961977679)
      ·
        refine ⟨30913497324081371942966519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20608998216054247961977679 30913497324081371942966519)
        ·
          refine ⟨46370245986122057914449779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30913497324081371942966519 46370245986122057914449779)
          ·
            refine ⟨69555368979183086871674669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46370245986122057914449779 69555368979183086871674669)
            ·
              refine ⟨26083263367193657576878001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69555368979183086871674669 26083263367193657576878001)
              ·
                refine ⟨19562447525395243182658501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26083263367193657576878001 19562447525395243182658501)
                ·
                  refine ⟨3667958911011608096748469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19562447525395243182658501 3667958911011608096748469)
                  ·
                    refine ⟨343871147907338259070169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3667958911011608096748469 343871147907338259070169)
                    ·
                      rfl

theorem cell23_2009060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_2009060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009060 prefixEnd_2009060 := by exact prefixLift 2009060
  have htrace : WordTrace (prefixWord ++ tailWord_2009060) baseStart_2009060 baseEnd_2009060 := by
    simpa [prefixWord, tailWord_2009060, baseEnd_2009060] using wordTrace_append hprefix tailTrace_2009060
  have hstable : (prefixWord ++ tailWord_2009060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009060).length < 2 ^ (prefixWord ++ tailWord_2009060).sum := by decide
  have hdescent : baseEnd_2009060 < baseStart_2009060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009080 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_2009080 : Nat := 118140960795 + 2009080 * 2 ^ 59
def prefixEnd_2009080 : Nat := 4983230072969 + 3 ^ 40 * 2009080 * 2
def baseEnd_2009080 : Nat := 1031623713335104698960415

theorem tailTrace_2009080 : CollatzResearch.WordTrace tailWord_2009080 prefixEnd_2009080 1031623713335104698960415 := by
  unfold tailWord_2009080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638583780726879195824347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48851445040969172261099129 36638583780726879195824347)
  ·
    refine ⟨54957875671090318793736521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36638583780726879195824347 54957875671090318793736521)
    ·
      refine ⟨41218406753317739095302391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54957875671090318793736521 41218406753317739095302391)
      ·
        refine ⟨61827610129976608642953587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41218406753317739095302391 61827610129976608642953587)
        ·
          refine ⟨92741415194964912964430381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61827610129976608642953587 92741415194964912964430381)
          ·
            refine ⟨34778030698111842361661393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92741415194964912964430381 34778030698111842361661393)
            ·
              refine ⟨26083523023583881771246045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34778030698111842361661393 26083523023583881771246045)
              ·
                refine ⟨9781321133843955664217267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26083523023583881771246045 9781321133843955664217267)
                ·
                  refine ⟨14671981700765933496325901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781321133843955664217267 14671981700765933496325901)
                  ·
                    refine ⟨5501993137787225061122213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14671981700765933496325901 5501993137787225061122213)
                    ·
                      refine ⟨1031623713335104698960415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5501993137787225061122213 1031623713335104698960415)
                      ·
                        rfl

theorem cell23_2009080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_2009080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009080 prefixEnd_2009080 := by exact prefixLift 2009080
  have htrace : WordTrace (prefixWord ++ tailWord_2009080) baseStart_2009080 baseEnd_2009080 := by
    simpa [prefixWord, tailWord_2009080, baseEnd_2009080] using wordTrace_append hprefix tailTrace_2009080
  have hstable : (prefixWord ++ tailWord_2009080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009080).length < 2 ^ (prefixWord ++ tailWord_2009080).sum := by decide
  have hdescent : baseEnd_2009080 < baseStart_2009080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009098 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_2009098 : Nat := 118140960795 + 2009098 * 2 ^ 59
def prefixEnd_2009098 : Nat := 4983230072969 + 3 ^ 40 * 2009098 * 2
def baseEnd_2009098 : Nat := 114625883998542847615037

theorem tailTrace_2009098 : CollatzResearch.WordTrace tailWord_2009098 prefixEnd_2009098 114625883998542847615037 := by
  unfold tailWord_2009098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319456018847136866450987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48851882716925698310535965 18319456018847136866450987)
  ·
    refine ⟨27479184028270705299676481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18319456018847136866450987 27479184028270705299676481)
    ·
      refine ⟨20609388021203028974757361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27479184028270705299676481 20609388021203028974757361)
      ·
        refine ⟨15457041015902271731068021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20609388021203028974757361 15457041015902271731068021)
        ·
          refine ⟨1449097595240837974787627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15457041015902271731068021 1449097595240837974787627)
          ·
            refine ⟨2173646392861256962181441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449097595240837974787627 2173646392861256962181441)
            ·
              refine ⟨1630234794645942721636081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2173646392861256962181441 1630234794645942721636081)
              ·
                refine ⟨1222676095984457041227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630234794645942721636081 1222676095984457041227061)
                ·
                  refine ⟨114625883998542847615037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222676095984457041227061 114625883998542847615037)
                  ·
                    rfl

theorem cell23_2009098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_2009098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009098 prefixEnd_2009098 := by exact prefixLift 2009098
  have htrace : WordTrace (prefixWord ++ tailWord_2009098) baseStart_2009098 baseEnd_2009098 := by
    simpa [prefixWord, tailWord_2009098, baseEnd_2009098] using wordTrace_append hprefix tailTrace_2009098
  have hstable : (prefixWord ++ tailWord_2009098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009098).length < 2 ^ (prefixWord ++ tailWord_2009098).sum := by decide
  have hdescent : baseEnd_2009098 < baseStart_2009098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009100 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2009100 : Nat := 118140960795 + 2009100 * 2 ^ 59
def prefixEnd_2009100 : Nat := 4983230072969 + 3 ^ 40 * 2009100 * 2
def baseEnd_2009100 : Nat := 1031633982948194620710323

theorem tailTrace_2009100 : CollatzResearch.WordTrace tailWord_2009100 prefixEnd_2009100 1031633982948194620710323 := by
  unfold tailWord_2009100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638948510690650903688377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48851931347587534538251169 36638948510690650903688377)
  ·
    refine ⟨27479211383017988177766283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36638948510690650903688377 27479211383017988177766283)
    ·
      refine ⟨41218817074526982266649425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27479211383017988177766283 41218817074526982266649425)
      ·
        refine ⟨30914112805895236699987069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41218817074526982266649425 30914112805895236699987069)
        ·
          refine ⟨11592792302210713762495151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30914112805895236699987069 11592792302210713762495151)
          ·
            refine ⟨17389188453316070643742727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592792302210713762495151 17389188453316070643742727)
            ·
              refine ⟨26083782679974105965614091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17389188453316070643742727 26083782679974105965614091)
              ·
                refine ⟨39125674019961158948421137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26083782679974105965614091 39125674019961158948421137)
                ·
                  refine ⟨29344255514970869211315853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39125674019961158948421137 29344255514970869211315853)
                  ·
                    refine ⟨11004095818114075954243445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29344255514970869211315853 11004095818114075954243445)
                    ·
                      refine ⟨1031633982948194620710323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11004095818114075954243445 1031633982948194620710323)
                      ·
                        rfl

theorem cell23_2009100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2009100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009100 prefixEnd_2009100 := by exact prefixLift 2009100
  have htrace : WordTrace (prefixWord ++ tailWord_2009100) baseStart_2009100 baseEnd_2009100 := by
    simpa [prefixWord, tailWord_2009100, baseEnd_2009100] using wordTrace_append hprefix tailTrace_2009100
  have hstable : (prefixWord ++ tailWord_2009100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009100).length < 2 ^ (prefixWord ++ tailWord_2009100).sum := by decide
  have hdescent : baseEnd_2009100 < baseStart_2009100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009114 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_2009114 : Nat := 118140960795 + 2009114 * 2 ^ 59
def prefixEnd_2009114 : Nat := 4983230072969 + 3 ^ 40 * 2009114 * 2
def baseEnd_2009114 : Nat := 1031641171677357565935259

theorem tailTrace_2009114 : CollatzResearch.WordTrace tailWord_2009114 prefixEnd_2009114 1031641171677357565935259 := by
  unfold tailWord_2009114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319601910832645549596599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48852271762220388132257597 18319601910832645549596599)
  ·
    refine ⟨27479402866248968324394899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18319601910832645549596599 27479402866248968324394899)
    ·
      refine ⟨41219104299373452486592349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27479402866248968324394899 41219104299373452486592349)
      ·
        refine ⟨15457164112265044682472131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41219104299373452486592349 15457164112265044682472131)
        ·
          refine ⟨23185746168397567023708197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15457164112265044682472131 23185746168397567023708197)
          ·
            refine ⟨4347327406574543816945287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23185746168397567023708197 4347327406574543816945287)
            ·
              refine ⟨6520991109861815725417931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347327406574543816945287 6520991109861815725417931)
              ·
                refine ⟨9781486664792723588126897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6520991109861815725417931 9781486664792723588126897)
                ·
                  refine ⟨7336114998594542691095173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9781486664792723588126897 7336114998594542691095173)
                  ·
                    refine ⟨1375521562236476754580345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336114998594542691095173 1375521562236476754580345)
                    ·
                      refine ⟨1031641171677357565935259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375521562236476754580345 1031641171677357565935259)
                      ·
                        rfl

theorem cell23_2009114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_2009114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009114 prefixEnd_2009114 := by exact prefixLift 2009114
  have htrace : WordTrace (prefixWord ++ tailWord_2009114) baseStart_2009114 baseEnd_2009114 := by
    simpa [prefixWord, tailWord_2009114, baseEnd_2009114] using wordTrace_append hprefix tailTrace_2009114
  have hstable : (prefixWord ++ tailWord_2009114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009114).length < 2 ^ (prefixWord ++ tailWord_2009114).sum := by decide
  have hdescent : baseEnd_2009114 < baseStart_2009114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009128 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2009128 : Nat := 118140960795 + 2009128 * 2 ^ 59
def prefixEnd_2009128 : Nat := 4983230072969 + 3 ^ 40 * 2009128 * 2
def baseEnd_2009128 : Nat := 343882786802173503720065

theorem tailTrace_2009128 : CollatzResearch.WordTrace tailWord_2009128 prefixEnd_2009128 343882786802173503720065 := by
  unfold tailWord_2009128
  simp only [CollatzResearch.WordTrace]
  refine ⟨36639459132639931294698019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48852612176853241726264025 36639459132639931294698019)
  ·
    refine ⟨54959188698959896942047029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36639459132639931294698019 54959188698959896942047029)
    ·
      refine ⟨5152423940527490338316909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54959188698959896942047029 5152423940527490338316909)
      ·
        refine ⟨1932158977697808876868841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5152423940527490338316909 1932158977697808876868841)
        ·
          refine ⟨1449119233273356657651631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932158977697808876868841 1449119233273356657651631)
          ·
            refine ⟨2173678849910034986477447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449119233273356657651631 2173678849910034986477447)
            ·
              refine ⟨3260518274865052479716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173678849910034986477447 3260518274865052479716171)
              ·
                refine ⟨4890777412297578719574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260518274865052479716171 4890777412297578719574257)
                ·
                  refine ⟨3668083059223184039680693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4890777412297578719574257 3668083059223184039680693)
                  ·
                    refine ⟨343882786802173503720065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3668083059223184039680693 343882786802173503720065)
                    ·
                      rfl

theorem cell23_2009128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2009128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009128 prefixEnd_2009128 := by exact prefixLift 2009128
  have htrace : WordTrace (prefixWord ++ tailWord_2009128) baseStart_2009128 baseEnd_2009128 := by
    simpa [prefixWord, tailWord_2009128, baseEnd_2009128] using wordTrace_append hprefix tailTrace_2009128
  have hstable : (prefixWord ++ tailWord_2009128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009128).length < 2 ^ (prefixWord ++ tailWord_2009128).sum := by decide
  have hdescent : baseEnd_2009128 < baseStart_2009128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009134 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2009134 : Nat := 118140960795 + 2009134 * 2 ^ 59
def prefixEnd_2009134 : Nat := 4983230072969 + 3 ^ 40 * 2009134 * 2
def baseEnd_2009134 : Nat := 1031651441290447487685167

theorem tailTrace_2009134 : CollatzResearch.WordTrace tailWord_2009134 prefixEnd_2009134 1031651441290447487685167 := by
  unfold tailWord_2009134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9159892137907265701764307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48852758068838750409409637 9159892137907265701764307)
  ·
    refine ⟨13739838206860898552646461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9159892137907265701764307 13739838206860898552646461)
    ·
      refine ⟨5152439327572836957242423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13739838206860898552646461 5152439327572836957242423)
      ·
        refine ⟨7728658991359255435863635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152439327572836957242423 7728658991359255435863635)
        ·
          refine ⟨11592988487038883153795453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728658991359255435863635 11592988487038883153795453)
          ·
            refine ⟨4347370682639581182673295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11592988487038883153795453 4347370682639581182673295)
            ·
              refine ⟨6521056023959371774009943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347370682639581182673295 6521056023959371774009943)
              ·
                refine ⟨9781584035939057661014915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521056023959371774009943 9781584035939057661014915)
                ·
                  refine ⟨14672376053908586491522373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781584035939057661014915 14672376053908586491522373)
                  ·
                    refine ⟨2751070510107859967160445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14672376053908586491522373 2751070510107859967160445)
                    ·
                      refine ⟨1031651441290447487685167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751070510107859967160445 1031651441290447487685167)
                      ·
                        rfl

theorem cell23_2009134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2009134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009134 prefixEnd_2009134 := by exact prefixLift 2009134
  have htrace : WordTrace (prefixWord ++ tailWord_2009134) baseStart_2009134 baseEnd_2009134 := by
    simpa [prefixWord, tailWord_2009134, baseEnd_2009134] using wordTrace_append hprefix tailTrace_2009134
  have hstable : (prefixWord ++ tailWord_2009134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009134).length < 2 ^ (prefixWord ++ tailWord_2009134).sum := by decide
  have hdescent : baseEnd_2009134 < baseStart_2009134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009158 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2009158 : Nat := 118140960795 + 2009158 * 2 ^ 59
def prefixEnd_2009158 : Nat := 4983230072969 + 3 ^ 40 * 2009158 * 2
def baseEnd_2009158 : Nat := 343887921608718464595019

theorem tailTrace_2009158 : CollatzResearch.WordTrace tailWord_2009158 prefixEnd_2009158 343887921608718464595019 := by
  unfold tailWord_2009158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290000389224099303530879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48853341636780785141992085 2290000389224099303530879)
  ·
    refine ⟨3435000583836148955296319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2290000389224099303530879 3435000583836148955296319)
    ·
      refine ⟨5152500875754223432944479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3435000583836148955296319 5152500875754223432944479)
      ·
        refine ⟨7728751313631335149416719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152500875754223432944479 7728751313631335149416719)
        ·
          refine ⟨11593126970447002724125079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728751313631335149416719 11593126970447002724125079)
          ·
            refine ⟨17389690455670504086187619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593126970447002724125079 17389690455670504086187619)
            ·
              refine ⟨26084535683505756129281429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17389690455670504086187619 26084535683505756129281429)
              ·
                refine ⟨1222712610164332318560067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26084535683505756129281429 1222712610164332318560067)
                ·
                  refine ⟨1834068915246498477840101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222712610164332318560067 1834068915246498477840101)
                  ·
                    refine ⟨343887921608718464595019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834068915246498477840101 343887921608718464595019)
                    ·
                      rfl

theorem cell23_2009158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2009158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009158 prefixEnd_2009158 := by exact prefixLift 2009158
  have htrace : WordTrace (prefixWord ++ tailWord_2009158) baseStart_2009158 baseEnd_2009158 := by
    simpa [prefixWord, tailWord_2009158, baseEnd_2009158] using wordTrace_append hprefix tailTrace_2009158
  have hstable : (prefixWord ++ tailWord_2009158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009158).length < 2 ^ (prefixWord ++ tailWord_2009158).sum := by decide
  have hdescent : baseEnd_2009158 < baseStart_2009158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009160 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2009160 : Nat := 118140960795 + 2009160 * 2 ^ 59
def prefixEnd_2009160 : Nat := 4983230072969 + 3 ^ 40 * 2009160 * 2
def baseEnd_2009160 : Nat := 1031664791787464385960047

theorem tailTrace_2009160 : CollatzResearch.WordTrace tailWord_2009160 prefixEnd_2009160 1031664791787464385960047 := by
  unfold tailWord_2009160
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640042700581966027280467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48853390267442621369707289 36640042700581966027280467)
  ·
    refine ⟨54960064050872949040920701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36640042700581966027280467 54960064050872949040920701)
    ·
      refine ⟨20610024019077355890345263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54960064050872949040920701 20610024019077355890345263)
      ·
        refine ⟨30915036028616033835517895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20610024019077355890345263 30915036028616033835517895)
        ·
          refine ⟨46372554042924050753276843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30915036028616033835517895 46372554042924050753276843)
          ·
            refine ⟨69558831064386076129915265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46372554042924050753276843 69558831064386076129915265)
            ·
              refine ⟨52169123298289557097436449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69558831064386076129915265 52169123298289557097436449)
              ·
                refine ⟨39126842473717167823077337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52169123298289557097436449 39126842473717167823077337)
                ·
                  refine ⟨29345131855287875867308003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39126842473717167823077337 29345131855287875867308003)
                  ·
                    refine ⟨44017697782931813800962005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29345131855287875867308003 44017697782931813800962005)
                    ·
                      refine ⟨1031664791787464385960047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44017697782931813800962005 1031664791787464385960047)
                      ·
                        rfl

theorem cell23_2009160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2009160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009160 prefixEnd_2009160 := by exact prefixLift 2009160
  have htrace : WordTrace (prefixWord ++ tailWord_2009160) baseStart_2009160 baseEnd_2009160 := by
    simpa [prefixWord, tailWord_2009160, baseEnd_2009160] using wordTrace_append hprefix tailTrace_2009160
  have hstable : (prefixWord ++ tailWord_2009160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009160).length < 2 ^ (prefixWord ++ tailWord_2009160).sum := by decide
  have hdescent : baseEnd_2009160 < baseStart_2009160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009164 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2009164 : Nat := 118140960795 + 2009164 * 2 ^ 59
def prefixEnd_2009164 : Nat := 4983230072969 + 3 ^ 40 * 2009164 * 2
def baseEnd_2009164 : Nat := 1031666845710082370310029

theorem tailTrace_2009164 : CollatzResearch.WordTrace tailWord_2009164 prefixEnd_2009164 1031666845710082370310029 := by
  unfold tailWord_2009164
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640115646574720368853273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48853487528766293825137697 36640115646574720368853273)
  ·
    refine ⟨27480086734931040276639955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36640115646574720368853273 27480086734931040276639955)
    ·
      refine ⟨41220130102396560414959933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27480086734931040276639955 41220130102396560414959933)
      ·
        refine ⟨15457548788398710155609975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41220130102396560414959933 15457548788398710155609975)
        ·
          refine ⟨23186323182598065233414963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15457548788398710155609975 23186323182598065233414963)
          ·
            refine ⟨34779484773897097850122445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23186323182598065233414963 34779484773897097850122445)
            ·
              refine ⟨13042306790211411693795917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34779484773897097850122445 13042306790211411693795917)
              ·
                refine ⟨4890865046329279385173469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042306790211411693795917 4890865046329279385173469)
                ·
                  refine ⟨1834074392373479769440051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4890865046329279385173469 1834074392373479769440051)
                  ·
                    refine ⟨2751111588560219654160077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834074392373479769440051 2751111588560219654160077)
                    ·
                      refine ⟨1031666845710082370310029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751111588560219654160077 1031666845710082370310029)
                      ·
                        rfl

theorem cell23_2009164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2009164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009164 prefixEnd_2009164 := by exact prefixLift 2009164
  have htrace : WordTrace (prefixWord ++ tailWord_2009164) baseStart_2009164 baseEnd_2009164 := by
    simpa [prefixWord, tailWord_2009164, baseEnd_2009164] using wordTrace_append hprefix tailTrace_2009164
  have hstable : (prefixWord ++ tailWord_2009164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009164).length < 2 ^ (prefixWord ++ tailWord_2009164).sum := by decide
  have hdescent : baseEnd_2009164 < baseStart_2009164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009184 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_2009184 : Nat := 118140960795 + 2009184 * 2 ^ 59
def prefixEnd_2009184 : Nat := 4983230072969 + 3 ^ 40 * 2009184 * 2
def baseEnd_2009184 : Nat := 343892371774390764019979

theorem tailTrace_2009184 : CollatzResearch.WordTrace tailWord_2009184 prefixEnd_2009184 343892371774390764019979 := by
  unfold tailWord_2009184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640480376538492076717303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48853973835384656102289737 36640480376538492076717303)
  ·
    refine ⟨54960720564807738115075955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36640480376538492076717303 54960720564807738115075955)
    ·
      refine ⟨82441080847211607172613933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54960720564807738115075955 82441080847211607172613933)
      ·
        refine ⟨30915405317704352689730225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82441080847211607172613933 30915405317704352689730225)
        ·
          refine ⟨23186553988278264517297669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30915405317704352689730225 23186553988278264517297669)
          ·
            refine ⟨4347478872802174596993313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23186553988278264517297669 4347478872802174596993313)
            ·
              refine ⟨3260609154601630947744985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347478872802174596993313 3260609154601630947744985)
              ·
                refine ⟨2445456865951223210808739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260609154601630947744985 2445456865951223210808739)
                ·
                  refine ⟨3668185298926834816213109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445456865951223210808739 3668185298926834816213109)
                  ·
                    refine ⟨343892371774390764019979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3668185298926834816213109 343892371774390764019979)
                    ·
                      rfl

theorem cell23_2009184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_2009184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009184 prefixEnd_2009184 := by exact prefixLift 2009184
  have htrace : WordTrace (prefixWord ++ tailWord_2009184) baseStart_2009184 baseEnd_2009184 := by
    simpa [prefixWord, tailWord_2009184, baseEnd_2009184] using wordTrace_append hprefix tailTrace_2009184
  have hstable : (prefixWord ++ tailWord_2009184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009184).length < 2 ^ (prefixWord ++ tailWord_2009184).sum := by decide
  have hdescent : baseEnd_2009184 < baseStart_2009184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009187 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2009187 : Nat := 118140960795 + 2009187 * 2 ^ 59
def prefixEnd_2009187 : Nat := 4983230072969 + 3 ^ 40 * 2009187 * 2
def baseEnd_2009187 : Nat := 1031678655765135780322423

theorem tailTrace_2009187 : CollatzResearch.WordTrace tailWord_2009187 prefixEnd_2009187 1031678655765135780322423 := by
  unfold tailWord_2009187
  simp only [CollatzResearch.WordTrace]
  refine ⟨73281070172066115665793815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48854046781377410443862543 73281070172066115665793815)
  ·
    refine ⟨109921605258099173498690723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73281070172066115665793815 109921605258099173498690723)
    ·
      refine ⟨164882407887148760248036085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109921605258099173498690723 164882407887148760248036085)
      ·
        refine ⟨15457725739420196273253383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164882407887148760248036085 15457725739420196273253383)
        ·
          refine ⟨23186588609130294409880075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15457725739420196273253383 23186588609130294409880075)
          ·
            refine ⟨34779882913695441614820113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23186588609130294409880075 34779882913695441614820113)
            ·
              refine ⟨26084912185271581211115085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34779882913695441614820113 26084912185271581211115085)
              ·
                refine ⟨9781842069476842954168157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26084912185271581211115085 9781842069476842954168157)
                ·
                  refine ⟨3668190776053816107813059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9781842069476842954168157 3668190776053816107813059)
                  ·
                    refine ⟨5502286164080724161719589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668190776053816107813059 5502286164080724161719589)
                    ·
                      refine ⟨1031678655765135780322423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5502286164080724161719589 1031678655765135780322423)
                      ·
                        rfl

theorem cell23_2009187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2009187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009187 prefixEnd_2009187 := by exact prefixLift 2009187
  have htrace : WordTrace (prefixWord ++ tailWord_2009187) baseStart_2009187 baseEnd_2009187 := by
    simpa [prefixWord, tailWord_2009187, baseEnd_2009187] using wordTrace_append hprefix tailTrace_2009187
  have hstable : (prefixWord ++ tailWord_2009187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009187).length < 2 ^ (prefixWord ++ tailWord_2009187).sum := by decide
  have hdescent : baseEnd_2009187 < baseStart_2009187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009197 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_2009197 : Nat := 118140960795 + 2009197 * 2 ^ 59
def prefixEnd_2009197 : Nat := 4983230072969 + 3 ^ 40 * 2009197 * 2
def baseEnd_2009197 : Nat := 343894596857226913732459

theorem tailTrace_2009197 : CollatzResearch.WordTrace tailWord_2009197 prefixEnd_2009197 343894596857226913732459 := by
  unfold tailWord_2009197
  simp only [CollatzResearch.WordTrace]
  refine ⟨73281434902029887373657845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48854289934686591582438563 73281434902029887373657845)
  ·
    refine ⟨6870134522065301941280423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73281434902029887373657845 6870134522065301941280423)
    ·
      refine ⟨10305201783097952911920635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870134522065301941280423 10305201783097952911920635)
      ·
        refine ⟨15457802674646929367880953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305201783097952911920635 15457802674646929367880953)
        ·
          refine ⟨11593352005985197025910715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15457802674646929367880953 11593352005985197025910715)
          ·
            refine ⟨17390028008977795538866073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593352005985197025910715 17390028008977795538866073)
            ·
              refine ⟨13042521006733346654149555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17390028008977795538866073 13042521006733346654149555)
              ·
                refine ⟨19563781510100019981224333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042521006733346654149555 19563781510100019981224333)
                ·
                  refine ⟨7336418066287507492959125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19563781510100019981224333 7336418066287507492959125)
                  ·
                    refine ⟨343894596857226913732459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7336418066287507492959125 343894596857226913732459)
                    ·
                      rfl

theorem cell23_2009197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_2009197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009197 prefixEnd_2009197 := by exact prefixLift 2009197
  have htrace : WordTrace (prefixWord ++ tailWord_2009197) baseStart_2009197 baseEnd_2009197 := by
    simpa [prefixWord, tailWord_2009197, baseEnd_2009197] using wordTrace_append hprefix tailTrace_2009197
  have hstable : (prefixWord ++ tailWord_2009197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009197).length < 2 ^ (prefixWord ++ tailWord_2009197).sum := by decide
  have hdescent : baseEnd_2009197 < baseStart_2009197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009207 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_2009207 : Nat := 118140960795 + 2009207 * 2 ^ 59
def prefixEnd_2009207 : Nat := 4983230072969 + 3 ^ 40 * 2009207 * 2
def baseEnd_2009207 : Nat := 1031688925378225702072331

theorem tailTrace_2009207 : CollatzResearch.WordTrace tailWord_2009207 prefixEnd_2009207 1031688925378225702072331 := by
  unfold tailWord_2009207
  simp only [CollatzResearch.WordTrace]
  refine ⟨73281799631993659081521875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48854533087995772721014583 73281799631993659081521875)
  ·
    refine ⟨109922699447990488622282813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73281799631993659081521875 109922699447990488622282813)
    ·
      refine ⟨41221012292996433233356055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109922699447990488622282813 41221012292996433233356055)
      ·
        refine ⟨61831518439494649850034083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41221012292996433233356055 61831518439494649850034083)
        ·
          refine ⟨92747277659241974775051125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61831518439494649850034083 92747277659241974775051125)
          ·
            refine ⟨8695057280553935135161043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92747277659241974775051125 8695057280553935135161043)
            ·
              refine ⟨13042585920830902702741565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695057280553935135161043 13042585920830902702741565)
              ·
                refine ⟨4890969720311588513528087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042585920830902702741565 4890969720311588513528087)
                ·
                  refine ⟨7336454580467382770292131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890969720311588513528087 7336454580467382770292131)
                  ·
                    refine ⟨11004681870701074155438197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336454580467382770292131 11004681870701074155438197)
                    ·
                      refine ⟨1031688925378225702072331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11004681870701074155438197 1031688925378225702072331)
                      ·
                        rfl

theorem cell23_2009207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_2009207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009207 prefixEnd_2009207 := by exact prefixLift 2009207
  have htrace : WordTrace (prefixWord ++ tailWord_2009207) baseStart_2009207 baseEnd_2009207 := by
    simpa [prefixWord, tailWord_2009207, baseEnd_2009207] using wordTrace_append hprefix tailTrace_2009207
  have hstable : (prefixWord ++ tailWord_2009207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009207).length < 2 ^ (prefixWord ++ tailWord_2009207).sum := by decide
  have hdescent : baseEnd_2009207 < baseStart_2009207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009224 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2009224 : Nat := 118140960795 + 2009224 * 2 ^ 59
def prefixEnd_2009224 : Nat := 4983230072969 + 3 ^ 40 * 2009224 * 2
def baseEnd_2009224 : Nat := 1031697654549352135559753

theorem tailTrace_2009224 : CollatzResearch.WordTrace tailWord_2009224 prefixEnd_2009224 1031697654549352135559753 := by
  unfold tailWord_2009224
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641209836466035492445363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48854946448621380656593817 36641209836466035492445363)
  ·
    refine ⟨54961814754699053238668045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36641209836466035492445363 54961814754699053238668045)
    ·
      refine ⟨20610680533012144964500517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54961814754699053238668045 20610680533012144964500517)
      ·
        refine ⟨3864502599939777180843847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20610680533012144964500517 3864502599939777180843847)
        ·
          refine ⟨5796753899909665771265771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864502599939777180843847 5796753899909665771265771)
          ·
            refine ⟨8695130849864498656898657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5796753899909665771265771 8695130849864498656898657)
            ·
              refine ⟨6521348137398373992673993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8695130849864498656898657 6521348137398373992673993)
              ·
                refine ⟨4891011103048780494505495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521348137398373992673993 4891011103048780494505495)
                ·
                  refine ⟨7336516654573170741758243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891011103048780494505495 7336516654573170741758243)
                  ·
                    refine ⟨11004774981859756112637365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336516654573170741758243 11004774981859756112637365)
                    ·
                      refine ⟨1031697654549352135559753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11004774981859756112637365 1031697654549352135559753)
                      ·
                        rfl

theorem cell23_2009224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2009224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009224 prefixEnd_2009224 := by exact prefixLift 2009224
  have htrace : WordTrace (prefixWord ++ tailWord_2009224) baseStart_2009224 baseEnd_2009224 := by
    simpa [prefixWord, tailWord_2009224, baseEnd_2009224] using wordTrace_append hprefix tailTrace_2009224
  have hstable : (prefixWord ++ tailWord_2009224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009224).length < 2 ^ (prefixWord ++ tailWord_2009224).sum := by decide
  have hdescent : baseEnd_2009224 < baseStart_2009224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009234 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2009234 : Nat := 118140960795 + 2009234 * 2 ^ 59
def prefixEnd_2009234 : Nat := 4983230072969 + 3 ^ 40 * 2009234 * 2
def baseEnd_2009234 : Nat := 1031702789355897096434707

theorem tailTrace_2009234 : CollatzResearch.WordTrace tailWord_2009234 prefixEnd_2009234 1031702789355897096434707 := by
  unfold tailWord_2009234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320696100723960673188689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48855189601930561795169837 18320696100723960673188689)
  ·
    refine ⟨13740522075542970504891517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18320696100723960673188689 13740522075542970504891517)
    ·
      refine ⟨5152695778328613939334319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13740522075542970504891517 5152695778328613939334319)
      ·
        refine ⟨7729043667492920909001479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152695778328613939334319 7729043667492920909001479)
        ·
          refine ⟨11593565501239381363502219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729043667492920909001479 11593565501239381363502219)
          ·
            refine ⟨17390348251859072045253329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593565501239381363502219 17390348251859072045253329)
            ·
              refine ⟨13042761188894304033939997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17390348251859072045253329 13042761188894304033939997)
              ·
                refine ⟨4891035445835364012727499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042761188894304033939997 4891035445835364012727499)
                ·
                  refine ⟨7336553168753046019091249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891035445835364012727499 7336553168753046019091249)
                  ·
                    refine ⟨5502414876564784514318437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336553168753046019091249 5502414876564784514318437)
                    ·
                      refine ⟨1031702789355897096434707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5502414876564784514318437 1031702789355897096434707)
                      ·
                        rfl

theorem cell23_2009234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2009234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009234 prefixEnd_2009234 := by exact prefixLift 2009234
  have htrace : WordTrace (prefixWord ++ tailWord_2009234) baseStart_2009234 baseEnd_2009234 := by
    simpa [prefixWord, tailWord_2009234, baseEnd_2009234] using wordTrace_append hprefix tailTrace_2009234
  have hstable : (prefixWord ++ tailWord_2009234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009234).length < 2 ^ (prefixWord ++ tailWord_2009234).sum := by decide
  have hdescent : baseEnd_2009234 < baseStart_2009234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009258 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2009258 : Nat := 118140960795 + 2009258 * 2 ^ 59
def prefixEnd_2009258 : Nat := 4983230072969 + 3 ^ 40 * 2009258 * 2
def baseEnd_2009258 : Nat := 1031715112891605002534597

theorem tailTrace_2009258 : CollatzResearch.WordTrace tailWord_2009258 prefixEnd_2009258 1031715112891605002534597 := by
  unfold tailWord_2009258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320914938702223697907107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48855773169872596527752285 18320914938702223697907107)
  ·
    refine ⟨27481372408053335546860661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18320914938702223697907107 27481372408053335546860661)
    ·
      refine ⟨2576378663255000207518187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27481372408053335546860661 2576378663255000207518187)
      ·
        refine ⟨3864567994882500311277281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576378663255000207518187 3864567994882500311277281)
        ·
          refine ⟨2898425996161875233457961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864567994882500311277281 2898425996161875233457961)
          ·
            refine ⟨2173819497121406425093471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898425996161875233457961 2173819497121406425093471)
            ·
              refine ⟨3260729245682109637640207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173819497121406425093471 3260729245682109637640207)
              ·
                refine ⟨4891093868523164456460311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260729245682109637640207 4891093868523164456460311)
                ·
                  refine ⟨7336640802784746684690467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891093868523164456460311 7336640802784746684690467)
                  ·
                    refine ⟨11004961204177120027035701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336640802784746684690467 11004961204177120027035701)
                    ·
                      refine ⟨1031715112891605002534597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11004961204177120027035701 1031715112891605002534597)
                      ·
                        rfl

theorem cell23_2009258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2009258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009258 prefixEnd_2009258 := by exact prefixLift 2009258
  have htrace : WordTrace (prefixWord ++ tailWord_2009258) baseStart_2009258 baseEnd_2009258 := by
    simpa [prefixWord, tailWord_2009258, baseEnd_2009258] using wordTrace_append hprefix tailTrace_2009258
  have hstable : (prefixWord ++ tailWord_2009258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009258).length < 2 ^ (prefixWord ++ tailWord_2009258).sum := by decide
  have hdescent : baseEnd_2009258 < baseStart_2009258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009264 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2]
def baseStart_2009264 : Nat := 118140960795 + 2009264 * 2 ^ 59
def prefixEnd_2009264 : Nat := 4983230072969 + 3 ^ 40 * 2009264 * 2
def baseEnd_2009264 : Nat := 1031718193775531979059569

theorem tailTrace_2009264 : CollatzResearch.WordTrace tailWord_2009264 prefixEnd_2009264 1031718193775531979059569 := by
  unfold tailWord_2009264
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641939296393578908173423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48855919061858105210897897 36641939296393578908173423)
  ·
    refine ⟨54962908944590368362260135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36641939296393578908173423 54962908944590368362260135)
    ·
      refine ⟨82444363416885552543390203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54962908944590368362260135 82444363416885552543390203)
      ·
        refine ⟨123666545125328328815085305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82444363416885552543390203 123666545125328328815085305)
        ·
          refine ⟨92749908843996246611313979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123666545125328328815085305 92749908843996246611313979)
          ·
            refine ⟨139124863265994369916970969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92749908843996246611313979 139124863265994369916970969)
            ·
              refine ⟨104343647449495777437728227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139124863265994369916970969 104343647449495777437728227)
              ·
                refine ⟨156515471174243666156592341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104343647449495777437728227 156515471174243666156592341)
                ·
                  refine ⟨3668331355646335925545133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 156515471174243666156592341 3668331355646335925545133)
                  ·
                    refine ⟨1375624258367375972079425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3668331355646335925545133 1375624258367375972079425)
                    ·
                      refine ⟨1031718193775531979059569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375624258367375972079425 1031718193775531979059569)
                      ·
                        rfl

theorem cell23_2009264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 3, 2].length) (baseStart_2009264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009264 prefixEnd_2009264 := by exact prefixLift 2009264
  have htrace : WordTrace (prefixWord ++ tailWord_2009264) baseStart_2009264 baseEnd_2009264 := by
    simpa [prefixWord, tailWord_2009264, baseEnd_2009264] using wordTrace_append hprefix tailTrace_2009264
  have hstable : (prefixWord ++ tailWord_2009264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009264).length < 2 ^ (prefixWord ++ tailWord_2009264).sum := by decide
  have hdescent : baseEnd_2009264 < baseStart_2009264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009271 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_2009271 : Nat := 118140960795 + 2009271 * 2 ^ 59
def prefixEnd_2009271 : Nat := 4983230072969 + 3 ^ 40 * 2009271 * 2
def baseEnd_2009271 : Nat := 1031721788140113451672037

theorem tailTrace_2009271 : CollatzResearch.WordTrace tailWord_2009271 prefixEnd_2009271 1031721788140113451672037 := by
  unfold tailWord_2009271
  simp only [CollatzResearch.WordTrace]
  refine ⟨73284133903761798011851667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48856089269174532007901111 73284133903761798011851667)
  ·
    refine ⟨109926200855642697017777501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73284133903761798011851667 109926200855642697017777501)
    ·
      refine ⟨41222325320866011381666563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109926200855642697017777501 41222325320866011381666563)
      ·
        refine ⟨61833487981299017072499845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41222325320866011381666563 61833487981299017072499845)
        ·
          refine ⟨11593778996493565701093721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61833487981299017072499845 11593778996493565701093721)
          ·
            refine ⟨8695334247370174275820291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11593778996493565701093721 8695334247370174275820291)
            ·
              refine ⟨13043001371055261413730437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695334247370174275820291 13043001371055261413730437)
              ·
                refine ⟨2445562757072861515074457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13043001371055261413730437 2445562757072861515074457)
                ·
                  refine ⟨1834172067804646136305843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445562757072861515074457 1834172067804646136305843)
                  ·
                    refine ⟨2751258101706969204458765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834172067804646136305843 2751258101706969204458765)
                    ·
                      refine ⟨1031721788140113451672037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751258101706969204458765 1031721788140113451672037)
                      ·
                        rfl

theorem cell23_2009271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_2009271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009271 prefixEnd_2009271 := by exact prefixLift 2009271
  have htrace : WordTrace (prefixWord ++ tailWord_2009271) baseStart_2009271 baseEnd_2009271 := by
    simpa [prefixWord, tailWord_2009271, baseEnd_2009271] using wordTrace_append hprefix tailTrace_2009271
  have hstable : (prefixWord ++ tailWord_2009271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009271).length < 2 ^ (prefixWord ++ tailWord_2009271).sum := by decide
  have hdescent : baseEnd_2009271 < baseStart_2009271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009297 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_2009297 : Nat := 118140960795 + 2009297 * 2 ^ 59
def prefixEnd_2009297 : Nat := 4983230072969 + 3 ^ 40 * 2009297 * 2
def baseEnd_2009297 : Nat := 1031735138637130349946917

theorem tailTrace_2009297 : CollatzResearch.WordTrace tailWord_2009297 prefixEnd_2009297 1031735138637130349946917 := by
  unfold tailWord_2009297
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285082201667604452298145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48856721467778402968198763 73285082201667604452298145)
  ·
    refine ⟨54963811651250703339223609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73285082201667604452298145 54963811651250703339223609)
    ·
      refine ⟨41222858738438027504417707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54963811651250703339223609 41222858738438027504417707)
      ·
        refine ⟨61834288107657041256626561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41222858738438027504417707 61834288107657041256626561)
        ·
          refine ⟨46375716080742780942469921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61834288107657041256626561 46375716080742780942469921)
          ·
            refine ⟨34781787060557085706852441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46375716080742780942469921 34781787060557085706852441)
            ·
              refine ⟨26086340295417814280139331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34781787060557085706852441 26086340295417814280139331)
              ·
                refine ⟨39129510443126721420208997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26086340295417814280139331 39129510443126721420208997)
                ·
                  refine ⟨7336783208086260266289187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39129510443126721420208997 7336783208086260266289187)
                  ·
                    refine ⟨11005174812129390399433781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336783208086260266289187 11005174812129390399433781)
                    ·
                      refine ⟨1031735138637130349946917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11005174812129390399433781 1031735138637130349946917)
                      ·
                        rfl

theorem cell23_2009297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_2009297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009297 prefixEnd_2009297 := by exact prefixLift 2009297
  have htrace : WordTrace (prefixWord ++ tailWord_2009297) baseStart_2009297 baseEnd_2009297 := by
    simpa [prefixWord, tailWord_2009297, baseEnd_2009297] using wordTrace_append hprefix tailTrace_2009297
  have hstable : (prefixWord ++ tailWord_2009297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009297).length < 2 ^ (prefixWord ++ tailWord_2009297).sum := by decide
  have hdescent : baseEnd_2009297 < baseStart_2009297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_2009307 : Nat := 118140960795 + 2009307 * 2 ^ 59
def prefixEnd_2009307 : Nat := 4983230072969 + 3 ^ 40 * 2009307 * 2
def baseEnd_2009307 : Nat := 1031740273443675310821871

theorem tailTrace_2009307 : CollatzResearch.WordTrace tailWord_2009307 prefixEnd_2009307 1031740273443675310821871 := by
  unfold tailWord_2009307
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285446931631376160162175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48856964621087584106774783 73285446931631376160162175)
  ·
    refine ⟨109928170397447064240243263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73285446931631376160162175 109928170397447064240243263)
    ·
      refine ⟨164892255596170596360364895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109928170397447064240243263 164892255596170596360364895)
      ·
        refine ⟨247338383394255894540547343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164892255596170596360364895 247338383394255894540547343)
        ·
          refine ⟨371007575091383841810821015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247338383394255894540547343 371007575091383841810821015)
          ·
            refine ⟨556511362637075762716231523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371007575091383841810821015 556511362637075762716231523)
            ·
              refine ⟨834767043955613644074347285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556511362637075762716231523 834767043955613644074347285)
              ·
                refine ⟨39129705185419389565985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 834767043955613644074347285 39129705185419389565985029)
                ·
                  refine ⟨7336819722266135543622193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39129705185419389565985029 7336819722266135543622193)
                  ·
                    refine ⟨5502614791699601657716645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336819722266135543622193 5502614791699601657716645)
                    ·
                      refine ⟨1031740273443675310821871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5502614791699601657716645 1031740273443675310821871)
                      ·
                        rfl

theorem cell23_2009307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_2009307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009307 prefixEnd_2009307 := by exact prefixLift 2009307
  have htrace : WordTrace (prefixWord ++ tailWord_2009307) baseStart_2009307 baseEnd_2009307 := by
    simpa [prefixWord, tailWord_2009307, baseEnd_2009307] using wordTrace_append hprefix tailTrace_2009307
  have hstable : (prefixWord ++ tailWord_2009307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009307).length < 2 ^ (prefixWord ++ tailWord_2009307).sum := by decide
  have hdescent : baseEnd_2009307 < baseStart_2009307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009311 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 4, 2, 2]
def baseStart_2009311 : Nat := 118140960795 + 2009311 * 2 ^ 59
def prefixEnd_2009311 : Nat := 4983230072969 + 3 ^ 40 * 2009311 * 2
def baseEnd_2009311 : Nat := 1031742327366293295171853

theorem tailTrace_2009311 : CollatzResearch.WordTrace tailWord_2009311 prefixEnd_2009311 1031742327366293295171853 := by
  unfold tailWord_2009311
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285592823616884843307787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48857061882411256562205191 73285592823616884843307787)
  ·
    refine ⟨109928389235425327264961681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73285592823616884843307787 109928389235425327264961681)
    ·
      refine ⟨82446291926568995448721261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109928389235425327264961681 82446291926568995448721261)
      ·
        refine ⟨30917359472463373293270473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82446291926568995448721261 30917359472463373293270473)
        ·
          refine ⟨23188019604347529969952855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30917359472463373293270473 23188019604347529969952855)
          ·
            refine ⟨34782029406521294954929283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23188019604347529969952855 34782029406521294954929283)
            ·
              refine ⟨52173044109781942432393925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34782029406521294954929283 52173044109781942432393925)
              ·
                refine ⟨9782445770584114206073861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52173044109781942432393925 9782445770584114206073861)
                ·
                  refine ⟨1834208581984521413638849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9782445770584114206073861 1834208581984521413638849)
                  ·
                    refine ⟨1375656436488391060229137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1834208581984521413638849 1375656436488391060229137)
                    ·
                      refine ⟨1031742327366293295171853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375656436488391060229137 1031742327366293295171853)
                      ·
                        rfl

theorem cell23_2009311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_2009311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009311 prefixEnd_2009311 := by exact prefixLift 2009311
  have htrace : WordTrace (prefixWord ++ tailWord_2009311) baseStart_2009311 baseEnd_2009311 := by
    simpa [prefixWord, tailWord_2009311, baseEnd_2009311] using wordTrace_append hprefix tailTrace_2009311
  have hstable : (prefixWord ++ tailWord_2009311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009311).length < 2 ^ (prefixWord ++ tailWord_2009311).sum := by decide
  have hdescent : baseEnd_2009311 < baseStart_2009311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009315 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2009315 : Nat := 118140960795 + 2009315 * 2 ^ 59
def prefixEnd_2009315 : Nat := 4983230072969 + 3 ^ 40 * 2009315 * 2
def baseEnd_2009315 : Nat := 1031744381288911279521835

theorem tailTrace_2009315 : CollatzResearch.WordTrace tailWord_2009315 prefixEnd_2009315 1031744381288911279521835 := by
  unfold tailWord_2009315
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285738715602393526453399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48857159143734929017635599 73285738715602393526453399)
  ·
    refine ⟨109928608073403590289680099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73285738715602393526453399 109928608073403590289680099)
    ·
      refine ⟨164892912110105385434520149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109928608073403590289680099 164892912110105385434520149)
      ·
        refine ⟨1932338813790297485560783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 164892912110105385434520149 1932338813790297485560783)
        ·
          refine ⟨2898508220685446228341175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932338813790297485560783 2898508220685446228341175)
          ·
            refine ⟨4347762331028169342511763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898508220685446228341175 4347762331028169342511763)
            ·
              refine ⟨6521643496542254013767645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347762331028169342511763 6521643496542254013767645)
              ·
                refine ⟨2445616311203345255162867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6521643496542254013767645 2445616311203345255162867)
                ·
                  refine ⟨3668424466805017882744301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445616311203345255162867 3668424466805017882744301)
                  ·
                    refine ⟨1375659175051881706029113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3668424466805017882744301 1375659175051881706029113)
                    ·
                      refine ⟨1031744381288911279521835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375659175051881706029113 1031744381288911279521835)
                      ·
                        rfl

theorem cell23_2009315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2009315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009315 prefixEnd_2009315 := by exact prefixLift 2009315
  have htrace : WordTrace (prefixWord ++ tailWord_2009315) baseStart_2009315 baseEnd_2009315 := by
    simpa [prefixWord, tailWord_2009315, baseEnd_2009315] using wordTrace_append hprefix tailTrace_2009315
  have hstable : (prefixWord ++ tailWord_2009315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009315).length < 2 ^ (prefixWord ++ tailWord_2009315).sum := by decide
  have hdescent : baseEnd_2009315 < baseStart_2009315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009334 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_2009334 : Nat := 118140960795 + 2009334 * 2 ^ 59
def prefixEnd_2009334 : Nat := 4983230072969 + 3 ^ 40 * 2009334 * 2
def baseEnd_2009334 : Nat := 114639348602371856131583

theorem tailTrace_2009334 : CollatzResearch.WordTrace tailWord_2009334 prefixEnd_2009334 114639348602371856131583 := by
  unfold tailWord_2009334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580401981408347485712191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48857621135022373180930037 4580401981408347485712191)
  ·
    refine ⟨6870602972112521228568287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580401981408347485712191 6870602972112521228568287)
    ·
      refine ⟨10305904458168781842852431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870602972112521228568287 10305904458168781842852431)
      ·
        refine ⟨15458856687253172764278647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305904458168781842852431 15458856687253172764278647)
        ·
          refine ⟨23188285030879759146417971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15458856687253172764278647 23188285030879759146417971)
          ·
            refine ⟨34782427546319638719626957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23188285030879759146417971 34782427546319638719626957)
            ·
              refine ⟨13043410329869864519860109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34782427546319638719626957 13043410329869864519860109)
              ·
                refine ⟨4891278873701199194947541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13043410329869864519860109 4891278873701199194947541)
                ·
                  refine ⟨114639348602371856131583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4891278873701199194947541 114639348602371856131583)
                  ·
                    rfl

theorem cell23_2009334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_2009334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009334 prefixEnd_2009334 := by exact prefixLift 2009334
  have htrace : WordTrace (prefixWord ++ tailWord_2009334) baseStart_2009334 baseEnd_2009334 := by
    simpa [prefixWord, tailWord_2009334, baseEnd_2009334] using wordTrace_append hprefix tailTrace_2009334
  have hstable : (prefixWord ++ tailWord_2009334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009334).length < 2 ^ (prefixWord ++ tailWord_2009334).sum := by decide
  have hdescent : baseEnd_2009334 < baseStart_2009334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009344 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_2009344 : Nat := 118140960795 + 2009344 * 2 ^ 59
def prefixEnd_2009344 : Nat := 4983230072969 + 3 ^ 40 * 2009344 * 2
def baseEnd_2009344 : Nat := 1031759272227891666059201

theorem tailTrace_2009344 : CollatzResearch.WordTrace tailWord_2009344 prefixEnd_2009344 1031759272227891666059201 := by
  unfold tailWord_2009344
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643398216248665739629543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48857864288331554319506057 36643398216248665739629543)
  ·
    refine ⟨54965097324372998609444315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36643398216248665739629543 54965097324372998609444315)
    ·
      refine ⟨82447645986559497914166473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54965097324372998609444315 82447645986559497914166473)
      ·
        refine ⟨61835734489919623435624855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82447645986559497914166473 61835734489919623435624855)
        ·
          refine ⟨92753601734879435153437283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61835734489919623435624855 92753601734879435153437283)
          ·
            refine ⟨139130402602319152730155925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92753601734879435153437283 139130402602319152730155925)
            ·
              refine ⟨6521737621983710284226059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139130402602319152730155925 6521737621983710284226059)
              ·
                refine ⟨9782606432975565426339089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521737621983710284226059 9782606432975565426339089)
                ·
                  refine ⟨7336954824731674069754317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9782606432975565426339089 7336954824731674069754317)
                  ·
                    refine ⟨2751358059274377776157869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7336954824731674069754317 2751358059274377776157869)
                    ·
                      refine ⟨1031759272227891666059201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751358059274377776157869 1031759272227891666059201)
                      ·
                        rfl

theorem cell23_2009344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_2009344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009344 prefixEnd_2009344 := by exact prefixLift 2009344
  have htrace : WordTrace (prefixWord ++ tailWord_2009344) baseStart_2009344 baseEnd_2009344 := by
    simpa [prefixWord, tailWord_2009344, baseEnd_2009344] using wordTrace_append hprefix tailTrace_2009344
  have hstable : (prefixWord ++ tailWord_2009344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009344).length < 2 ^ (prefixWord ++ tailWord_2009344).sum := by decide
  have hdescent : baseEnd_2009344 < baseStart_2009344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009345 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_2009345 : Nat := 118140960795 + 2009345 * 2 ^ 59
def prefixEnd_2009345 : Nat := 4983230072969 + 3 ^ 40 * 2009345 * 2
def baseEnd_2009345 : Nat := 1031759785708546162146697

theorem tailTrace_2009345 : CollatzResearch.WordTrace tailWord_2009345 prefixEnd_2009345 1031759785708546162146697 := by
  unfold tailWord_2009345
  simp only [CollatzResearch.WordTrace]
  refine ⟨73286832905493708650045489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48857888603662472433363659 73286832905493708650045489)
  ·
    refine ⟨54965124679120281487534117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73286832905493708650045489 54965124679120281487534117)
    ·
      refine ⟨10305960877335052778912647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54965124679120281487534117 10305960877335052778912647)
      ·
        refine ⟨15458941316002579168368971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305960877335052778912647 15458941316002579168368971)
        ·
          refine ⟨23188411974003868752553457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15458941316002579168368971 23188411974003868752553457)
          ·
            refine ⟨17391308980502901564415093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23188411974003868752553457 17391308980502901564415093)
            ·
              refine ⟨1630435216922147021663915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17391308980502901564415093 1630435216922147021663915)
              ·
                refine ⟨2445652825383220532495873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630435216922147021663915 2445652825383220532495873)
                ·
                  refine ⟨1834239619037415399371905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445652825383220532495873 1834239619037415399371905)
                  ·
                    refine ⟨1375679714278061549528929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1834239619037415399371905 1375679714278061549528929)
                    ·
                      refine ⟨1031759785708546162146697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375679714278061549528929 1031759785708546162146697)
                      ·
                        rfl

theorem cell23_2009345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_2009345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009345 prefixEnd_2009345 := by exact prefixLift 2009345
  have htrace : WordTrace (prefixWord ++ tailWord_2009345) baseStart_2009345 baseEnd_2009345 := by
    simpa [prefixWord, tailWord_2009345, baseEnd_2009345] using wordTrace_append hprefix tailTrace_2009345
  have hstable : (prefixWord ++ tailWord_2009345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009345).length < 2 ^ (prefixWord ++ tailWord_2009345).sum := by decide
  have hdescent : baseEnd_2009345 < baseStart_2009345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009347 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 7]
def baseStart_2009347 : Nat := 118140960795 + 2009347 * 2 ^ 59
def prefixEnd_2009347 : Nat := 4983230072969 + 3 ^ 40 * 2009347 * 2
def baseEnd_2009347 : Nat := 343920270889951718107229

theorem tailTrace_2009347 : CollatzResearch.WordTrace tailWord_2009347 prefixEnd_2009347 343920270889951718107229 := by
  unfold tailWord_2009347
  simp only [CollatzResearch.WordTrace]
  refine ⟨73286905851486462991618295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48857937234324308661078863 73286905851486462991618295)
  ·
    refine ⟨109930358777229694487427443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73286905851486462991618295 109930358777229694487427443)
    ·
      refine ⟨164895538165844541731141165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109930358777229694487427443 164895538165844541731141165)
      ·
        refine ⟨61835826812191703149177937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164895538165844541731141165 61835826812191703149177937)
        ·
          refine ⟨46376870109143777361883453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61835826812191703149177937 46376870109143777361883453)
          ·
            refine ⟨17391326290928916510706295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46376870109143777361883453 17391326290928916510706295)
            ·
              refine ⟨26086989436393374766059443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391326290928916510706295 26086989436393374766059443)
              ·
                refine ⟨39130484154590062149089165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26086989436393374766059443 39130484154590062149089165)
                ·
                  refine ⟨14673931557971273305908437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39130484154590062149089165 14673931557971273305908437)
                  ·
                    refine ⟨343920270889951718107229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14673931557971273305908437 343920270889951718107229)
                    ·
                      rfl

theorem cell23_2009347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_2009347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009347 prefixEnd_2009347 := by exact prefixLift 2009347
  have htrace : WordTrace (prefixWord ++ tailWord_2009347) baseStart_2009347 baseEnd_2009347 := by
    simpa [prefixWord, tailWord_2009347, baseEnd_2009347] using wordTrace_append hprefix tailTrace_2009347
  have hstable : (prefixWord ++ tailWord_2009347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009347).length < 2 ^ (prefixWord ++ tailWord_2009347).sum := by decide
  have hdescent : baseEnd_2009347 < baseStart_2009347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009381 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_2009381 : Nat := 118140960795 + 2009381 * 2 ^ 59
def prefixEnd_2009381 : Nat := 4983230072969 + 3 ^ 40 * 2009381 * 2
def baseEnd_2009381 : Nat := 343926090337369340432177

theorem tailTrace_2009381 : CollatzResearch.WordTrace tailWord_2009381 prefixEnd_2009381 343926090337369340432177 := by
  unfold tailWord_2009381
  simp only [CollatzResearch.WordTrace]
  refine ⟨73288145933363286798355997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48858763955575524532237331 73288145933363286798355997)
  ·
    refine ⟨27483054725011232549383499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73288145933363286798355997 27483054725011232549383499)
    ·
      refine ⟨41224582087516848824075249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27483054725011232549383499 41224582087516848824075249)
      ·
        refine ⟨30918436565637636618056437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41224582087516848824075249 30918436565637636618056437)
        ·
          refine ⟨2898603428028528432942791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30918436565637636618056437 2898603428028528432942791)
          ·
            refine ⟨4347905142042792649414187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898603428028528432942791 4347905142042792649414187)
            ·
              refine ⟨6521857713064188974121281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347905142042792649414187 6521857713064188974121281)
              ·
                refine ⟨4891393284798141730590961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521857713064188974121281 4891393284798141730590961)
                ·
                  refine ⟨3668544963598606297943221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4891393284798141730590961 3668544963598606297943221)
                  ·
                    refine ⟨343926090337369340432177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3668544963598606297943221 343926090337369340432177)
                    ·
                      rfl

theorem cell23_2009381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_2009381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009381 prefixEnd_2009381 := by exact prefixLift 2009381
  have htrace : WordTrace (prefixWord ++ tailWord_2009381) baseStart_2009381 baseEnd_2009381 := by
    simpa [prefixWord, tailWord_2009381, baseEnd_2009381] using wordTrace_append hprefix tailTrace_2009381
  have hstable : (prefixWord ++ tailWord_2009381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009381).length < 2 ^ (prefixWord ++ tailWord_2009381).sum := by decide
  have hdescent : baseEnd_2009381 < baseStart_2009381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009444 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_2009444 : Nat := 118140960795 + 2009444 * 2 ^ 59
def prefixEnd_2009444 : Nat := 4983230072969 + 3 ^ 40 * 2009444 * 2
def baseEnd_2009444 : Nat := 1031810620293341274808741

theorem tailTrace_2009444 : CollatzResearch.WordTrace tailWord_2009444 prefixEnd_2009444 1031810620293341274808741 := by
  unfold tailWord_2009444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36645221866067524278949693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48860295821423365705266257 36645221866067524278949693)
  ·
    refine ⟨13741958199775321604606135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36645221866067524278949693 13741958199775321604606135)
    ·
      refine ⟨20612937299662982406909203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13741958199775321604606135 20612937299662982406909203)
      ·
        refine ⟨30919405949494473610363805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20612937299662982406909203 30919405949494473610363805)
        ·
          refine ⟨11594777231060427603886427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30919405949494473610363805 11594777231060427603886427)
          ·
            refine ⟨17392165846590641405829641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594777231060427603886427 17392165846590641405829641)
            ·
              refine ⟨13044124384942981054372231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17392165846590641405829641 13044124384942981054372231)
              ·
                refine ⟨19566186577414471581558347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13044124384942981054372231 19566186577414471581558347)
                ·
                  refine ⟨29349279866121707372337521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19566186577414471581558347 29349279866121707372337521)
                  ·
                    refine ⟨22011959899591280529253141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29349279866121707372337521 22011959899591280529253141)
                    ·
                      refine ⟨1031810620293341274808741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22011959899591280529253141 1031810620293341274808741)
                      ·
                        rfl

theorem cell23_2009444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_2009444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009444 prefixEnd_2009444 := by exact prefixLift 2009444
  have htrace : WordTrace (prefixWord ++ tailWord_2009444) baseStart_2009444 baseEnd_2009444 := by
    simpa [prefixWord, tailWord_2009444, baseEnd_2009444] using wordTrace_append hprefix tailTrace_2009444
  have hstable : (prefixWord ++ tailWord_2009444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009444).length < 2 ^ (prefixWord ++ tailWord_2009444).sum := by decide
  have hdescent : baseEnd_2009444 < baseStart_2009444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009445 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_2009445 : Nat := 118140960795 + 2009445 * 2 ^ 59
def prefixEnd_2009445 : Nat := 4983230072969 + 3 ^ 40 * 2009445 * 2
def baseEnd_2009445 : Nat := 343937044591331923632079

theorem tailTrace_2009445 : CollatzResearch.WordTrace tailWord_2009445 prefixEnd_2009445 343937044591331923632079 := by
  unfold tailWord_2009445
  simp only [CollatzResearch.WordTrace]
  refine ⟨73290480205131425728685789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48860320136754283819123859 73290480205131425728685789)
  ·
    refine ⟨27483930076924284648257171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73290480205131425728685789 27483930076924284648257171)
    ·
      refine ⟨41225895115386426972385757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27483930076924284648257171 41225895115386426972385757)
      ·
        refine ⟨15459710668269910114644659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41225895115386426972385757 15459710668269910114644659)
        ·
          refine ⟨23189566002404865171966989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15459710668269910114644659 23189566002404865171966989)
          ·
            refine ⟨8696087250901824439487621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23189566002404865171966989 8696087250901824439487621)
            ·
              refine ⟨1630516359544092082403929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8696087250901824439487621 1630516359544092082403929)
              ·
                refine ⟨1222887269658069061802947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630516359544092082403929 1222887269658069061802947)
                ·
                  refine ⟨1834330904487103592704421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222887269658069061802947 1834330904487103592704421)
                  ·
                    refine ⟨343937044591331923632079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834330904487103592704421 343937044591331923632079)
                    ·
                      rfl

theorem cell23_2009445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_2009445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009445 prefixEnd_2009445 := by exact prefixLift 2009445
  have htrace : WordTrace (prefixWord ++ tailWord_2009445) baseStart_2009445 baseEnd_2009445 := by
    simpa [prefixWord, tailWord_2009445, baseEnd_2009445] using wordTrace_append hprefix tailTrace_2009445
  have hstable : (prefixWord ++ tailWord_2009445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009445).length < 2 ^ (prefixWord ++ tailWord_2009445).sum := by decide
  have hdescent : baseEnd_2009445 < baseStart_2009445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009502 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2009502 : Nat := 118140960795 + 2009502 * 2 ^ 59
def prefixEnd_2009502 : Nat := 4983230072969 + 3 ^ 40 * 2009502 * 2
def baseEnd_2009502 : Nat := 1031840402171302047883475

theorem tailTrace_2009502 : CollatzResearch.WordTrace tailWord_2009502 prefixEnd_2009502 1031840402171302047883475 := by
  unfold tailWord_2009502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161569895740615557938845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48861706110616616309007173 9161569895740615557938845)
  ·
    refine ⟨3435588710902730834227067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9161569895740615557938845 3435588710902730834227067)
    ·
      refine ⟨5153383066354096251340601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3435588710902730834227067 5153383066354096251340601)
      ·
        refine ⟨3865037299765572188505451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5153383066354096251340601 3865037299765572188505451)
        ·
          refine ⟨5797555949648358282758177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865037299765572188505451 5797555949648358282758177)
          ·
            refine ⟨4348166962236268712068633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797555949648358282758177 4348166962236268712068633)
            ·
              refine ⟨3261125221677201534051475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348166962236268712068633 3261125221677201534051475)
              ·
                refine ⟨4891687832515802301077213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261125221677201534051475 4891687832515802301077213)
                ·
                  refine ⟨1834382937193425862903955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4891687832515802301077213 1834382937193425862903955)
                  ·
                    refine ⟨2751574405790138794355933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834382937193425862903955 2751574405790138794355933)
                    ·
                      refine ⟨1031840402171302047883475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751574405790138794355933 1031840402171302047883475)
                      ·
                        rfl

theorem cell23_2009502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2009502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009502 prefixEnd_2009502 := by exact prefixLift 2009502
  have htrace : WordTrace (prefixWord ++ tailWord_2009502) baseStart_2009502 baseEnd_2009502 := by
    simpa [prefixWord, tailWord_2009502, baseEnd_2009502] using wordTrace_append hprefix tailTrace_2009502
  have hstable : (prefixWord ++ tailWord_2009502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009502).length < 2 ^ (prefixWord ++ tailWord_2009502).sum := by decide
  have hdescent : baseEnd_2009502 < baseStart_2009502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009511 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2009511 : Nat := 118140960795 + 2009511 * 2 ^ 59
def prefixEnd_2009511 : Nat := 4983230072969 + 3 ^ 40 * 2009511 * 2
def baseEnd_2009511 : Nat := 1031845023497192512670933

theorem tailTrace_2009511 : CollatzResearch.WordTrace tailWord_2009511 prefixEnd_2009511 1031845023497192512670933 := by
  unfold tailWord_2009511
  simp only [CollatzResearch.WordTrace]
  refine ⟨73292887422892319000588387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48861924948594879333725591 73292887422892319000588387)
  ·
    refine ⟨109939331134338478500882581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73292887422892319000588387 109939331134338478500882581)
    ·
      refine ⟨5153406146922116179728871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109939331134338478500882581 5153406146922116179728871)
      ·
        refine ⟨7730109220383174269593307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5153406146922116179728871 7730109220383174269593307)
        ·
          refine ⟨11595163830574761404389961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730109220383174269593307 11595163830574761404389961)
          ·
            refine ⟨8696372872931071053292471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11595163830574761404389961 8696372872931071053292471)
            ·
              refine ⟨13044559309396606579938707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696372872931071053292471 13044559309396606579938707)
              ·
                refine ⟨19566838964094909869908061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13044559309396606579938707 19566838964094909869908061)
                ·
                  refine ⟨7337564611535591201215523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19566838964094909869908061 7337564611535591201215523)
                  ·
                    refine ⟨11006346917303386801823285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7337564611535591201215523 11006346917303386801823285)
                    ·
                      refine ⟨1031845023497192512670933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11006346917303386801823285 1031845023497192512670933)
                      ·
                        rfl

theorem cell23_2009511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2009511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009511 prefixEnd_2009511 := by exact prefixLift 2009511
  have htrace : WordTrace (prefixWord ++ tailWord_2009511) baseStart_2009511 baseEnd_2009511 := by
    simpa [prefixWord, tailWord_2009511, baseEnd_2009511] using wordTrace_append hprefix tailTrace_2009511
  have hstable : (prefixWord ++ tailWord_2009511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009511).length < 2 ^ (prefixWord ++ tailWord_2009511).sum := by decide
  have hdescent : baseEnd_2009511 < baseStart_2009511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009521 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2009521 : Nat := 118140960795 + 2009521 * 2 ^ 59
def prefixEnd_2009521 : Nat := 4983230072969 + 3 ^ 40 * 2009521 * 2
def baseEnd_2009521 : Nat := 1031850158303737473545887

theorem tailTrace_2009521 : CollatzResearch.WordTrace tailWord_2009521 prefixEnd_2009521 1031850158303737473545887 := by
  unfold tailWord_2009521
  simp only [CollatzResearch.WordTrace]
  refine ⟨73293252152856090708452417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48862168101904060472301611 73293252152856090708452417)
  ·
    refine ⟨54969939114642068031339313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73293252152856090708452417 54969939114642068031339313)
    ·
      refine ⟨41227454335981551023504485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54969939114642068031339313 41227454335981551023504485)
      ·
        refine ⟨7730147687996540816907091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41227454335981551023504485 7730147687996540816907091)
        ·
          refine ⟨11595221531994811225360637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730147687996540816907091 11595221531994811225360637)
          ·
            refine ⟨4348208074498054209510239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11595221531994811225360637 4348208074498054209510239)
            ·
              refine ⟨6522312111747081314265359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348208074498054209510239 6522312111747081314265359)
              ·
                refine ⟨9783468167620621971398039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522312111747081314265359 9783468167620621971398039)
                ·
                  refine ⟨14675202251430932957097059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783468167620621971398039 14675202251430932957097059)
                  ·
                    refine ⟨22012803377146399435645589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14675202251430932957097059 22012803377146399435645589)
                    ·
                      refine ⟨1031850158303737473545887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22012803377146399435645589 1031850158303737473545887)
                      ·
                        rfl

theorem cell23_2009521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2009521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009521 prefixEnd_2009521 := by exact prefixLift 2009521
  have htrace : WordTrace (prefixWord ++ tailWord_2009521) baseStart_2009521 baseEnd_2009521 := by
    simpa [prefixWord, tailWord_2009521, baseEnd_2009521] using wordTrace_append hprefix tailTrace_2009521
  have hstable : (prefixWord ++ tailWord_2009521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009521).length < 2 ^ (prefixWord ++ tailWord_2009521).sum := by decide
  have hdescent : baseEnd_2009521 < baseStart_2009521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009525 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2009525 : Nat := 118140960795 + 2009525 * 2 ^ 59
def prefixEnd_2009525 : Nat := 4983230072969 + 3 ^ 40 * 2009525 * 2
def baseEnd_2009525 : Nat := 1031852212226355457895869

theorem tailTrace_2009525 : CollatzResearch.WordTrace tailWord_2009525 prefixEnd_2009525 1031852212226355457895869 := by
  unfold tailWord_2009525
  simp only [CollatzResearch.WordTrace]
  refine ⟨73293398044841599391598029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48862265363227732927732019 73293398044841599391598029)
  ·
    refine ⟨27485024266815599771849261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73293398044841599391598029 27485024266815599771849261)
    ·
      refine ⟨10306884100055849914443473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27485024266815599771849261 10306884100055849914443473)
      ·
        refine ⟨7730163075041887435832605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10306884100055849914443473 7730163075041887435832605)
        ·
          refine ⟨2898811153140707788437227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7730163075041887435832605 2898811153140707788437227)
          ·
            refine ⟨4348216729711061682655841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898811153140707788437227 4348216729711061682655841)
            ·
              refine ⟨3261162547283296261991881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348216729711061682655841 3261162547283296261991881)
              ·
                refine ⟨2445871910462472196493911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261162547283296261991881 2445871910462472196493911)
                ·
                  refine ⟨3668807865693708294740867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445871910462472196493911 3668807865693708294740867)
                  ·
                    refine ⟨5503211798540562442111301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668807865693708294740867 5503211798540562442111301)
                    ·
                      refine ⟨1031852212226355457895869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5503211798540562442111301 1031852212226355457895869)
                      ·
                        rfl

theorem cell23_2009525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2009525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009525 prefixEnd_2009525 := by exact prefixLift 2009525
  have htrace : WordTrace (prefixWord ++ tailWord_2009525) baseStart_2009525 baseEnd_2009525 := by
    simpa [prefixWord, tailWord_2009525, baseEnd_2009525] using wordTrace_append hprefix tailTrace_2009525
  have hstable : (prefixWord ++ tailWord_2009525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009525).length < 2 ^ (prefixWord ++ tailWord_2009525).sum := by decide
  have hdescent : baseEnd_2009525 < baseStart_2009525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009548 : List Nat := [2, 2, 1, 4, 4, 1, 9]
def baseStart_2009548 : Nat := 118140960795 + 2009548 * 2 ^ 59
def prefixEnd_2009548 : Nat := 4983230072969 + 3 ^ 40 * 2009548 * 2
def baseEnd_2009548 : Nat := 12739062003474183554423

theorem tailTrace_2009548 : CollatzResearch.WordTrace tailWord_2009548 prefixEnd_2009548 12739062003474183554423 := by
  unfold tailWord_2009548
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647118461879137159842649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48862824615838849546456865 36647118461879137159842649)
  ·
    refine ⟨27485338846409352869881987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36647118461879137159842649 27485338846409352869881987)
    ·
      refine ⟨41228008269614029304822981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27485338846409352869881987 41228008269614029304822981)
      ·
        refine ⟨7730251550552630494654309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41228008269614029304822981 7730251550552630494654309)
        ·
          refine ⟨1449422165728618217747683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7730251550552630494654309 1449422165728618217747683)
          ·
            refine ⟨2174133248592927326621525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449422165728618217747683 2174133248592927326621525)
            ·
              refine ⟨12739062003474183554423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2174133248592927326621525 12739062003474183554423)
              ·
                rfl

theorem cell23_2009548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 9].length) (baseStart_2009548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009548 prefixEnd_2009548 := by exact prefixLift 2009548
  have htrace : WordTrace (prefixWord ++ tailWord_2009548) baseStart_2009548 baseEnd_2009548 := by
    simpa [prefixWord, tailWord_2009548, baseEnd_2009548] using wordTrace_append hprefix tailTrace_2009548
  have hstable : (prefixWord ++ tailWord_2009548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009548).length < 2 ^ (prefixWord ++ tailWord_2009548).sum := by decide
  have hdescent : baseEnd_2009548 < baseStart_2009548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009568 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2]
def baseStart_2009568 : Nat := 118140960795 + 2009568 * 2 ^ 59
def prefixEnd_2009568 : Nat := 4983230072969 + 3 ^ 40 * 2009568 * 2
def baseEnd_2009568 : Nat := 1031874291894498789658171

theorem tailTrace_2009568 : CollatzResearch.WordTrace tailWord_2009568 prefixEnd_2009568 1031874291894498789658171 := by
  unfold tailWord_2009568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647483191842908867706679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48863310922457211823608905 36647483191842908867706679)
  ·
    refine ⟨54971224787764363301560019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36647483191842908867706679 54971224787764363301560019)
    ·
      refine ⟨82456837181646544952340029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54971224787764363301560019 82456837181646544952340029)
      ·
        refine ⟨30921313943117454357127511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82456837181646544952340029 30921313943117454357127511)
        ·
          refine ⟨46381970914676181535691267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30921313943117454357127511 46381970914676181535691267)
          ·
            refine ⟨69572956372014272303536901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46381970914676181535691267 69572956372014272303536901)
            ·
              refine ⟨13044929319752676056913169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69572956372014272303536901 13044929319752676056913169)
              ·
                refine ⟨9783696989814507042684877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13044929319752676056913169 9783696989814507042684877)
                ·
                  refine ⟨3668886371180440141006829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9783696989814507042684877 3668886371180440141006829)
                  ·
                    refine ⟨1375832389192665052877561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3668886371180440141006829 1375832389192665052877561)
                    ·
                      refine ⟨1031874291894498789658171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375832389192665052877561 1031874291894498789658171)
                      ·
                        rfl

theorem cell23_2009568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_2009568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009568 prefixEnd_2009568 := by exact prefixLift 2009568
  have htrace : WordTrace (prefixWord ++ tailWord_2009568) baseStart_2009568 baseEnd_2009568 := by
    simpa [prefixWord, tailWord_2009568, baseEnd_2009568] using wordTrace_append hprefix tailTrace_2009568
  have hstable : (prefixWord ++ tailWord_2009568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009568).length < 2 ^ (prefixWord ++ tailWord_2009568).sum := by decide
  have hdescent : baseEnd_2009568 < baseStart_2009568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009575 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2009575 : Nat := 118140960795 + 2009575 * 2 ^ 59
def prefixEnd_2009575 : Nat := 4983230072969 + 3 ^ 40 * 2009575 * 2
def baseEnd_2009575 : Nat := 1031877886259080262270639

theorem tailTrace_2009575 : CollatzResearch.WordTrace tailWord_2009575 prefixEnd_2009575 1031877886259080262270639 := by
  unfold tailWord_2009575
  simp only [CollatzResearch.WordTrace]
  refine ⟨73295221694660457930918179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48863481129773638620612119 73295221694660457930918179)
  ·
    refine ⟨109942832541990686896377269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73295221694660457930918179 109942832541990686896377269)
    ·
      refine ⟨10307140550811626896535369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109942832541990686896377269 10307140550811626896535369)
      ·
        refine ⟨7730355413108720172401527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307140550811626896535369 7730355413108720172401527)
        ·
          refine ⟨11595533119663080258602291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730355413108720172401527 11595533119663080258602291)
          ·
            refine ⟨17393299679494620387903437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595533119663080258602291 17393299679494620387903437)
            ·
              refine ⟨6522487379810482645463789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17393299679494620387903437 6522487379810482645463789)
              ·
                refine ⟨2445932767428930992048921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6522487379810482645463789 2445932767428930992048921)
                ·
                  refine ⟨1834449575571698244036691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445932767428930992048921 1834449575571698244036691)
                  ·
                    refine ⟨2751674363357547366055037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834449575571698244036691 2751674363357547366055037)
                    ·
                      refine ⟨1031877886259080262270639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751674363357547366055037 1031877886259080262270639)
                      ·
                        rfl

theorem cell23_2009575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2009575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009575 prefixEnd_2009575 := by exact prefixLift 2009575
  have htrace : WordTrace (prefixWord ++ tailWord_2009575) baseStart_2009575 baseEnd_2009575 := by
    simpa [prefixWord, tailWord_2009575, baseEnd_2009575] using wordTrace_append hprefix tailTrace_2009575
  have hstable : (prefixWord ++ tailWord_2009575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009575).length < 2 ^ (prefixWord ++ tailWord_2009575).sum := by decide
  have hdescent : baseEnd_2009575 < baseStart_2009575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009615 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 2, 2, 2]
def baseStart_2009615 : Nat := 118140960795 + 2009615 * 2 ^ 59
def prefixEnd_2009615 : Nat := 4983230072969 + 3 ^ 40 * 2009615 * 2
def baseEnd_2009615 : Nat := 1031898425485260105770455

theorem tailTrace_2009615 : CollatzResearch.WordTrace tailWord_2009615 prefixEnd_2009615 1031898425485260105770455 := by
  unfold tailWord_2009615
  simp only [CollatzResearch.WordTrace]
  refine ⟨73296680614515544762374299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48864453743010363174916199 73296680614515544762374299)
  ·
    refine ⟨109945020921773317143561449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73296680614515544762374299 109945020921773317143561449)
    ·
      refine ⟨82458765691329987857671087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109945020921773317143561449 82458765691329987857671087)
      ·
        refine ⟨123688148536994981786506631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82458765691329987857671087 123688148536994981786506631)
        ·
          refine ⟨185532222805492472679759947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123688148536994981786506631 185532222805492472679759947)
          ·
            refine ⟨278298334208238709019639921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185532222805492472679759947 278298334208238709019639921)
            ·
              refine ⟨208723750656179031764729941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278298334208238709019639921 208723750656179031764729941)
              ·
                refine ⟨2445981453002098028492929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 208723750656179031764729941 2445981453002098028492929)
                ·
                  refine ⟨1834486089751573521369697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2445981453002098028492929 1834486089751573521369697)
                  ·
                    refine ⟨1375864567313680141027273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1834486089751573521369697 1375864567313680141027273)
                    ·
                      refine ⟨1031898425485260105770455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375864567313680141027273 1031898425485260105770455)
                      ·
                        rfl

theorem cell23_2009615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 2, 2].length) (baseStart_2009615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009615 prefixEnd_2009615 := by exact prefixLift 2009615
  have htrace : WordTrace (prefixWord ++ tailWord_2009615) baseStart_2009615 baseEnd_2009615 := by
    simpa [prefixWord, tailWord_2009615, baseEnd_2009615] using wordTrace_append hprefix tailTrace_2009615
  have hstable : (prefixWord ++ tailWord_2009615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009615).length < 2 ^ (prefixWord ++ tailWord_2009615).sum := by decide
  have hdescent : baseEnd_2009615 < baseStart_2009615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009621 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 7]
def baseStart_2009621 : Nat := 118140960795 + 2009621 * 2 ^ 59
def prefixEnd_2009621 : Nat := 4983230072969 + 3 ^ 40 * 2009621 * 2
def baseEnd_2009621 : Nat := 114655722929909675810603

theorem tailTrace_2009621 : CollatzResearch.WordTrace tailWord_2009621 prefixEnd_2009621 114655722929909675810603 := by
  unfold tailWord_2009621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73296899452493807787092717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48864599634995871858061811 73296899452493807787092717)
  ·
    refine ⟨27486337294685177920159769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73296899452493807787092717 27486337294685177920159769)
    ·
      refine ⟨20614752971013883440119827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27486337294685177920159769 20614752971013883440119827)
      ·
        refine ⟨30922129456520825160179741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20614752971013883440119827 30922129456520825160179741)
        ·
          refine ⟨11595798546195309435067403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30922129456520825160179741 11595798546195309435067403)
          ·
            refine ⟨17393697819292964152601105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595798546195309435067403 17393697819292964152601105)
            ·
              refine ⟨13045273364469723114450829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17393697819292964152601105 13045273364469723114450829)
              ·
                refine ⟨4891977511676146167919061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13045273364469723114450829 4891977511676146167919061)
                ·
                  refine ⟨114655722929909675810603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4891977511676146167919061 114655722929909675810603)
                  ·
                    rfl

theorem cell23_2009621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_2009621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009621 prefixEnd_2009621 := by exact prefixLift 2009621
  have htrace : WordTrace (prefixWord ++ tailWord_2009621) baseStart_2009621 baseEnd_2009621 := by
    simpa [prefixWord, tailWord_2009621, baseEnd_2009621] using wordTrace_append hprefix tailTrace_2009621
  have hstable : (prefixWord ++ tailWord_2009621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009621).length < 2 ^ (prefixWord ++ tailWord_2009621).sum := by decide
  have hdescent : baseEnd_2009621 < baseStart_2009621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009628 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2009628 : Nat := 118140960795 + 2009628 * 2 ^ 59
def prefixEnd_2009628 : Nat := 4983230072969 + 3 ^ 40 * 2009628 * 2
def baseEnd_2009628 : Nat := 1031905100733768554907895

theorem tailTrace_2009628 : CollatzResearch.WordTrace tailWord_2009628 prefixEnd_2009628 1031905100733768554907895 := by
  unfold tailWord_2009628
  simp only [CollatzResearch.WordTrace]
  refine ⟨36648577381734223991298769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48864769842312298655065025 36648577381734223991298769)
  ·
    refine ⟨27486433036300667993474077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36648577381734223991298769 27486433036300667993474077)
    ·
      refine ⟨10307412388612750497552779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27486433036300667993474077 10307412388612750497552779)
      ·
        refine ⟨15461118582919125746329169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10307412388612750497552779 15461118582919125746329169)
        ·
          refine ⟨11595838937189344309746877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15461118582919125746329169 11595838937189344309746877)
          ·
            refine ⟨4348439601446004116155079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11595838937189344309746877 4348439601446004116155079)
            ·
              refine ⟨6522659402169006174232619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348439601446004116155079 6522659402169006174232619)
              ·
                refine ⟨9783989103253509261348929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522659402169006174232619 9783989103253509261348929)
                ·
                  refine ⟨7337991827440131946011697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9783989103253509261348929 7337991827440131946011697)
                  ·
                    refine ⟨5503493870580098959508773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7337991827440131946011697 5503493870580098959508773)
                    ·
                      refine ⟨1031905100733768554907895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5503493870580098959508773 1031905100733768554907895)
                      ·
                        rfl

theorem cell23_2009628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2009628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009628 prefixEnd_2009628 := by exact prefixLift 2009628
  have htrace : WordTrace (prefixWord ++ tailWord_2009628) baseStart_2009628 baseEnd_2009628 := by
    simpa [prefixWord, tailWord_2009628, baseEnd_2009628] using wordTrace_append hprefix tailTrace_2009628
  have hstable : (prefixWord ++ tailWord_2009628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009628).length < 2 ^ (prefixWord ++ tailWord_2009628).sum := by decide
  have hdescent : baseEnd_2009628 < baseStart_2009628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009632 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2009632 : Nat := 118140960795 + 2009632 * 2 ^ 59
def prefixEnd_2009632 : Nat := 4983230072969 + 3 ^ 40 * 2009632 * 2
def baseEnd_2009632 : Nat := 1031907154656386539257877

theorem tailTrace_2009632 : CollatzResearch.WordTrace tailWord_2009632 prefixEnd_2009632 1031907154656386539257877 := by
  unfold tailWord_2009632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36648650327726978332871575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48864867103635971110495433 36648650327726978332871575)
  ·
    refine ⟨54972975491590467499307363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36648650327726978332871575 54972975491590467499307363)
    ·
      refine ⟨82459463237385701248961045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54972975491590467499307363 82459463237385701248961045)
      ·
        refine ⟨3865287339252454746045049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82459463237385701248961045 3865287339252454746045049)
        ·
          refine ⟨2898965504439341059533787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3865287339252454746045049 2898965504439341059533787)
          ·
            refine ⟨4348448256659011589300681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898965504439341059533787 4348448256659011589300681)
            ·
              refine ⟨3261336192494258691975511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348448256659011589300681 3261336192494258691975511)
              ·
                refine ⟨4892004288741388037963267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261336192494258691975511 4892004288741388037963267)
                ·
                  refine ⟨7338006433112082056944901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892004288741388037963267 7338006433112082056944901)
                  ·
                    refine ⟨1375876206208515385677169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7338006433112082056944901 1375876206208515385677169)
                    ·
                      refine ⟨1031907154656386539257877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1375876206208515385677169 1031907154656386539257877)
                      ·
                        rfl

theorem cell23_2009632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2009632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009632 prefixEnd_2009632 := by exact prefixLift 2009632
  have htrace : WordTrace (prefixWord ++ tailWord_2009632) baseStart_2009632 baseEnd_2009632 := by
    simpa [prefixWord, tailWord_2009632, baseEnd_2009632] using wordTrace_append hprefix tailTrace_2009632
  have hstable : (prefixWord ++ tailWord_2009632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009632).length < 2 ^ (prefixWord ++ tailWord_2009632).sum := by decide
  have hdescent : baseEnd_2009632 < baseStart_2009632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009651 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 7]
def baseStart_2009651 : Nat := 118140960795 + 2009651 * 2 ^ 59
def prefixEnd_2009651 : Nat := 4983230072969 + 3 ^ 40 * 2009651 * 2
def baseEnd_2009651 : Nat := 343972303596273988306763

theorem tailTrace_2009651 : CollatzResearch.WordTrace tailWord_2009651 prefixEnd_2009651 343972303596273988306763 := by
  unfold tailWord_2009651
  simp only [CollatzResearch.WordTrace]
  refine ⟨73297993642385122910684807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48865329094923415273789871 73297993642385122910684807)
  ·
    refine ⟨109946990463577684366027211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73297993642385122910684807 109946990463577684366027211)
    ·
      refine ⟨164920485695366526549040817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109946990463577684366027211 164920485695366526549040817)
      ·
        refine ⟨123690364271524894911780613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164920485695366526549040817 123690364271524894911780613)
        ·
          refine ⟨23191943300910917795958865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123690364271524894911780613 23191943300910917795958865)
          ·
            refine ⟨17393957475683188346969149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23191943300910917795958865 17393957475683188346969149)
            ·
              refine ⟨6522734053381195630113431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17393957475683188346969149 6522734053381195630113431)
              ·
                refine ⟨9784101080071793445170147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522734053381195630113431 9784101080071793445170147)
                ·
                  refine ⟨14676151620107690167755221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784101080071793445170147 14676151620107690167755221)
                  ·
                    refine ⟨343972303596273988306763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14676151620107690167755221 343972303596273988306763)
                    ·
                      rfl

theorem cell23_2009651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_2009651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009651 prefixEnd_2009651 := by exact prefixLift 2009651
  have htrace : WordTrace (prefixWord ++ tailWord_2009651) baseStart_2009651 baseEnd_2009651 := by
    simpa [prefixWord, tailWord_2009651, baseEnd_2009651] using wordTrace_append hprefix tailTrace_2009651
  have hstable : (prefixWord ++ tailWord_2009651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009651).length < 2 ^ (prefixWord ++ tailWord_2009651).sum := by decide
  have hdescent : baseEnd_2009651 < baseStart_2009651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009708 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_2009708 : Nat := 118140960795 + 2009708 * 2 ^ 59
def prefixEnd_2009708 : Nat := 4983230072969 + 3 ^ 40 * 2009708 * 2
def baseEnd_2009708 : Nat := 1031946179186128241907527

theorem tailTrace_2009708 : CollatzResearch.WordTrace tailWord_2009708 prefixEnd_2009708 1031946179186128241907527 := by
  unfold tailWord_2009708
  simp only [CollatzResearch.WordTrace]
  refine ⟨36650036301589310822754889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48866715068785747763673185 36650036301589310822754889)
  ·
    refine ⟨27487527226191983117066167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36650036301589310822754889 27487527226191983117066167)
    ·
      refine ⟨41231290839287974675599251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27487527226191983117066167 41231290839287974675599251)
      ·
        refine ⟨61846936258931962013398877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41231290839287974675599251 61846936258931962013398877)
        ·
          refine ⟨23192601097099485755024579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61846936258931962013398877 23192601097099485755024579)
          ·
            refine ⟨34788901645649228632536869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23192601097099485755024579 34788901645649228632536869)
            ·
              refine ⟨6522919058559230368600663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34788901645649228632536869 6522919058559230368600663)
              ·
                refine ⟨9784378587838845552900995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522919058559230368600663 9784378587838845552900995)
                ·
                  refine ⟨14676567881758268329351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784378587838845552900995 14676567881758268329351493)
                  ·
                    refine ⟨2751856477829675311753405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14676567881758268329351493 2751856477829675311753405)
                    ·
                      refine ⟨1031946179186128241907527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2751856477829675311753405 1031946179186128241907527)
                      ·
                        rfl

theorem cell23_2009708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_2009708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009708 prefixEnd_2009708 := by exact prefixLift 2009708
  have htrace : WordTrace (prefixWord ++ tailWord_2009708) baseStart_2009708 baseEnd_2009708 := by
    simpa [prefixWord, tailWord_2009708, baseEnd_2009708] using wordTrace_append hprefix tailTrace_2009708
  have hstable : (prefixWord ++ tailWord_2009708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009708).length < 2 ^ (prefixWord ++ tailWord_2009708).sum := by decide
  have hdescent : baseEnd_2009708 < baseStart_2009708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2009711 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 8]
def baseStart_2009711 : Nat := 118140960795 + 2009711 * 2 ^ 59
def prefixEnd_2009711 : Nat := 4983230072969 + 3 ^ 40 * 2009711 * 2
def baseEnd_2009711 : Nat := 114660857736454636685557

theorem tailTrace_2009711 : CollatzResearch.WordTrace tailWord_2009711 prefixEnd_2009711 114660857736454636685557 := by
  unfold tailWord_2009711
  simp only [CollatzResearch.WordTrace]
  refine ⟨73300182022167753157868987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48866788014778502105245991 73300182022167753157868987)
  ·
    refine ⟨109950273033251629736803481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73300182022167753157868987 109950273033251629736803481)
    ·
      refine ⟨82462704774938722302602611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109950273033251629736803481 82462704774938722302602611)
      ·
        refine ⟨123694057162408083453903917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82462704774938722302602611 123694057162408083453903917)
        ·
          refine ⟨46385271435903031295213969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123694057162408083453903917 46385271435903031295213969)
          ·
            refine ⟨34788953576927273471410477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46385271435903031295213969 34788953576927273471410477)
            ·
              refine ⟨13045857591347727551778929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34788953576927273471410477 13045857591347727551778929)
              ·
                refine ⟨9784393193510795663834197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045857591347727551778929 9784393193510795663834197)
                ·
                  refine ⟨114660857736454636685557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9784393193510795663834197 114660857736454636685557)
                  ·
                    rfl

theorem cell23_2009711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 8].length) (baseStart_2009711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2009711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2009711 prefixEnd_2009711 := by exact prefixLift 2009711
  have htrace : WordTrace (prefixWord ++ tailWord_2009711) baseStart_2009711 baseEnd_2009711 := by
    simpa [prefixWord, tailWord_2009711, baseEnd_2009711] using wordTrace_append hprefix tailTrace_2009711
  have hstable : (prefixWord ++ tailWord_2009711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2009711).length < 2 ^ (prefixWord ++ tailWord_2009711).sum := by decide
  have hdescent : baseEnd_2009711 < baseStart_2009711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2009711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
