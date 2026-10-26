import V185TrunkScan22Chunk204

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1827119 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 4, 3]
def baseStart_1827119 : Nat := 118140960795 + 1827119 * 2 ^ 59
def prefixEnd_1827119 : Nat := 4983230072969 + 3 ^ 40 * 1827119 * 2
def baseEnd_1827119 : Nat := 625460173308228081473159

theorem tailTrace_1827119 : CollatzResearch.WordTrace tailWord_1827119 prefixEnd_1827119 625460173308228081473159 := by
  unfold tailWord_1827119
  simp only [CollatzResearch.WordTrace]
  refine ⟨66640504667667384926972411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44427003111778256617981607 66640504667667384926972411)
  ·
    refine ⟨99960757001501077390458617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66640504667667384926972411 99960757001501077390458617)
    ·
      refine ⟨74970567751125808042843963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99960757001501077390458617 74970567751125808042843963)
      ·
        refine ⟨112455851626688712064265945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74970567751125808042843963 112455851626688712064265945)
        ·
          refine ⟨84341888720016534048199459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112455851626688712064265945 84341888720016534048199459)
          ·
            refine ⟨126512833080024801072299189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84341888720016534048199459 126512833080024801072299189)
            ·
              refine ⟨11860578101252325100528049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126512833080024801072299189 11860578101252325100528049)
              ·
                refine ⟨8895433575939243825396037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11860578101252325100528049 8895433575939243825396037)
                ·
                  refine ⟨1667893795488608217261757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8895433575939243825396037 1667893795488608217261757)
                  ·
                    refine ⟨625460173308228081473159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1667893795488608217261757 625460173308228081473159)
                    ·
                      rfl

theorem cell22_1827119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_1827119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827119 prefixEnd_1827119 := by exact prefixLift 1827119
  have htrace : WordTrace (prefixWord ++ tailWord_1827119) baseStart_1827119 baseEnd_1827119 := by
    simpa [prefixWord, tailWord_1827119, baseEnd_1827119] using wordTrace_append hprefix tailTrace_1827119
  have hstable : (prefixWord ++ tailWord_1827119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827119).length < 2 ^ (prefixWord ++ tailWord_1827119).sum := by decide
  have hdescent : baseEnd_1827119 < baseStart_1827119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827147 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_1827147 : Nat := 118140960795 + 1827147 * 2 ^ 59
def prefixEnd_1827147 : Nat := 4983230072969 + 3 ^ 40 * 1827147 * 2
def baseEnd_1827147 : Nat := 625469758280445341773073

theorem tailTrace_1827147 : CollatzResearch.WordTrace tailWord_1827147 prefixEnd_1827147 625469758280445341773073 := by
  unfold tailWord_1827147
  simp only [CollatzResearch.WordTrace]
  refine ⟨66641525911565945708991695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44427683941043963805994463 66641525911565945708991695)
  ·
    refine ⟨99962288867348918563487543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66641525911565945708991695 99962288867348918563487543)
    ·
      refine ⟨149943433301023377845231315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99962288867348918563487543 149943433301023377845231315)
      ·
        refine ⟨224915149951535066767846973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149943433301023377845231315 224915149951535066767846973)
        ·
          refine ⟨84343181231825650037942615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224915149951535066767846973 84343181231825650037942615)
          ·
            refine ⟨126514771847738475056913923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84343181231825650037942615 126514771847738475056913923)
            ·
              refine ⟨189772157771607712585370885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126514771847738475056913923 189772157771607712585370885)
              ·
                refine ⟨35582279582176446109757041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189772157771607712585370885 35582279582176446109757041)
                ·
                  refine ⟨26686709686632334582317781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35582279582176446109757041 26686709686632334582317781)
                  ·
                    refine ⟨625469758280445341773073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26686709686632334582317781 625469758280445341773073)
                    ·
                      rfl

theorem cell22_1827147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_1827147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827147 prefixEnd_1827147 := by exact prefixLift 1827147
  have htrace : WordTrace (prefixWord ++ tailWord_1827147) baseStart_1827147 baseEnd_1827147 := by
    simpa [prefixWord, tailWord_1827147, baseEnd_1827147] using wordTrace_append hprefix tailTrace_1827147
  have hstable : (prefixWord ++ tailWord_1827147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827147).length < 2 ^ (prefixWord ++ tailWord_1827147).sum := by decide
  have hdescent : baseEnd_1827147 < baseStart_1827147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827153 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_1827153 : Nat := 118140960795 + 1827153 * 2 ^ 59
def prefixEnd_1827153 : Nat := 4983230072969 + 3 ^ 40 * 1827153 * 2
def baseEnd_1827153 : Nat := 625471812203063326123055

theorem tailTrace_1827153 : CollatzResearch.WordTrace tailWord_1827153 prefixEnd_1827153 625471812203063326123055 := by
  unfold tailWord_1827153
  simp only [CollatzResearch.WordTrace]
  refine ⟨66641744749544208733710113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44427829833029472489140075 66641744749544208733710113)
  ·
    refine ⟨49981308562158156550282585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66641744749544208733710113 49981308562158156550282585)
    ·
      refine ⟨37485981421618617412711939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49981308562158156550282585 37485981421618617412711939)
      ·
        refine ⟨56228972132427926119067909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37485981421618617412711939 56228972132427926119067909)
        ·
          refine ⟨10542932274830236147325233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56228972132427926119067909 10542932274830236147325233)
          ·
            refine ⟨7907199206122677110493925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10542932274830236147325233 7907199206122677110493925)
            ·
              refine ⟨1482599851148001958217611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7907199206122677110493925 1482599851148001958217611)
              ·
                refine ⟨2223899776722002937326417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482599851148001958217611 2223899776722002937326417)
                ·
                  refine ⟨1667924832541502202994813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2223899776722002937326417 1667924832541502202994813)
                  ·
                    refine ⟨625471812203063326123055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1667924832541502202994813 625471812203063326123055)
                    ·
                      rfl

theorem cell22_1827153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_1827153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827153 prefixEnd_1827153 := by exact prefixLift 1827153
  have htrace : WordTrace (prefixWord ++ tailWord_1827153) baseStart_1827153 baseEnd_1827153 := by
    simpa [prefixWord, tailWord_1827153, baseEnd_1827153] using wordTrace_append hprefix tailTrace_1827153
  have hstable : (prefixWord ++ tailWord_1827153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827153).length < 2 ^ (prefixWord ++ tailWord_1827153).sum := by decide
  have hdescent : baseEnd_1827153 < baseStart_1827153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827209 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_1827209 : Nat := 118140960795 + 1827209 * 2 ^ 59
def prefixEnd_1827209 : Nat := 4983230072969 + 3 ^ 40 * 1827209 * 2
def baseEnd_1827209 : Nat := 625490982147497846722883

theorem tailTrace_1827209 : CollatzResearch.WordTrace tailWord_1827209 prefixEnd_1827209 625490982147497846722883 := by
  unfold tailWord_1827209
  simp only [CollatzResearch.WordTrace]
  refine ⟨66643787237341330297748681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44429191491560886865165787 66643787237341330297748681)
  ·
    refine ⟨49982840428005997723311511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66643787237341330297748681 49982840428005997723311511)
    ·
      refine ⟨74974260642008996584967267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49982840428005997723311511 74974260642008996584967267)
      ·
        refine ⟨112461390963013494877450901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74974260642008996584967267 112461390963013494877450901)
        ·
          refine ⟨5271627701391257572380511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112461390963013494877450901 5271627701391257572380511)
          ·
            refine ⟨7907441552086886358570767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271627701391257572380511 7907441552086886358570767)
            ·
              refine ⟨11861162328130329537856151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907441552086886358570767 11861162328130329537856151)
              ·
                refine ⟨17791743492195494306784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11861162328130329537856151 17791743492195494306784227)
                ·
                  refine ⟨26687615238293241460176341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17791743492195494306784227 26687615238293241460176341)
                  ·
                    refine ⟨625490982147497846722883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26687615238293241460176341 625490982147497846722883)
                    ·
                      rfl

theorem cell22_1827209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_1827209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827209 prefixEnd_1827209 := by exact prefixLift 1827209
  have htrace : WordTrace (prefixWord ++ tailWord_1827209) baseStart_1827209 baseEnd_1827209 := by
    simpa [prefixWord, tailWord_1827209, baseEnd_1827209] using wordTrace_append hprefix tailTrace_1827209
  have hstable : (prefixWord ++ tailWord_1827209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827209).length < 2 ^ (prefixWord ++ tailWord_1827209).sum := by decide
  have hdescent : baseEnd_1827209 < baseStart_1827209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827245 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 5]
def baseStart_1827245 : Nat := 118140960795 + 1827245 * 2 ^ 59
def prefixEnd_1827245 : Nat := 4983230072969 + 3 ^ 40 * 1827245 * 2
def baseEnd_1827245 : Nat := 208501101894401917607591

theorem tailTrace_1827245 : CollatzResearch.WordTrace tailWord_1827245 prefixEnd_1827245 208501101894401917607591 := by
  unfold tailWord_1827245
  simp only [CollatzResearch.WordTrace]
  refine ⟨66645100265210908446059189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44430066843473938964039459 66645100265210908446059189)
  ·
    refine ⟨6247978149863522666818049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66645100265210908446059189 6247978149863522666818049)
    ·
      refine ⟨4685983612397642000113537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6247978149863522666818049 4685983612397642000113537)
      ·
        refine ⟨3514487709298231500085153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4685983612397642000113537 3514487709298231500085153)
        ·
          refine ⟨2635865781973673625063865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514487709298231500085153 2635865781973673625063865)
          ·
            refine ⟨1976899336480255218797899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635865781973673625063865 1976899336480255218797899)
            ·
              refine ⟨2965349004720382828196849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976899336480255218797899 2965349004720382828196849)
              ·
                refine ⟨2224011753540287121147637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965349004720382828196849 2224011753540287121147637)
                ·
                  refine ⟨208501101894401917607591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2224011753540287121147637 208501101894401917607591)
                  ·
                    rfl

theorem cell22_1827245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_1827245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827245 prefixEnd_1827245 := by exact prefixLift 1827245
  have htrace : WordTrace (prefixWord ++ tailWord_1827245) baseStart_1827245 baseEnd_1827245 := by
    simpa [prefixWord, tailWord_1827245, baseEnd_1827245] using wordTrace_append hprefix tailTrace_1827245
  have hstable : (prefixWord ++ tailWord_1827245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827245).length < 2 ^ (prefixWord ++ tailWord_1827245).sum := by decide
  have hdescent : baseEnd_1827245 < baseStart_1827245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827271 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1827271 : Nat := 118140960795 + 1827271 * 2 ^ 59
def prefixEnd_1827271 : Nat := 4983230072969 + 3 ^ 40 * 1827271 * 2
def baseEnd_1827271 : Nat := 625512206014550351672693

theorem tailTrace_1827271 : CollatzResearch.WordTrace tailWord_1827271 prefixEnd_1827271 625512206014550351672693 := by
  unfold tailWord_1827271
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646048563116714886505667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44430699042077809924337111 66646048563116714886505667)
  ·
    refine ⟨99969072844675072329758501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66646048563116714886505667 99969072844675072329758501)
    ·
      refine ⟨18744201158376576061829719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99969072844675072329758501 18744201158376576061829719)
      ·
        refine ⟨28116301737564864092744579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18744201158376576061829719 28116301737564864092744579)
        ·
          refine ⟨42174452606347296139116869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28116301737564864092744579 42174452606347296139116869)
          ·
            refine ⟨7907709863690118026084413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42174452606347296139116869 7907709863690118026084413)
            ·
              refine ⟨2965391198883794259781655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7907709863690118026084413 2965391198883794259781655)
              ·
                refine ⟨4448086798325691389672483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965391198883794259781655 4448086798325691389672483)
                ·
                  refine ⟨6672130197488537084508725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448086798325691389672483 6672130197488537084508725)
                  ·
                    refine ⟨625512206014550351672693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6672130197488537084508725 625512206014550351672693)
                    ·
                      rfl

theorem cell22_1827271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1827271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827271 prefixEnd_1827271 := by exact prefixLift 1827271
  have htrace : WordTrace (prefixWord ++ tailWord_1827271) baseStart_1827271 baseEnd_1827271 := by
    simpa [prefixWord, tailWord_1827271, baseEnd_1827271] using wordTrace_append hprefix tailTrace_1827271
  have hstable : (prefixWord ++ tailWord_1827271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827271).length < 2 ^ (prefixWord ++ tailWord_1827271).sum := by decide
  have hdescent : baseEnd_1827271 < baseStart_1827271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827361 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1827361 : Nat := 118140960795 + 1827361 * 2 ^ 59
def prefixEnd_1827361 : Nat := 4983230072969 + 3 ^ 40 * 1827361 * 2
def baseEnd_1827361 : Nat := 625543014853820116922417

theorem tailTrace_1827361 : CollatzResearch.WordTrace tailWord_1827361 prefixEnd_1827361 625543014853820116922417 := by
  unfold tailWord_1827361
  simp only [CollatzResearch.WordTrace]
  refine ⟨66649331132790660257281937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44432887421860440171521291 66649331132790660257281937)
  ·
    refine ⟨49986998349592995192961453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66649331132790660257281937 49986998349592995192961453)
    ·
      refine ⟨18745124381097373197360545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49986998349592995192961453 18745124381097373197360545)
      ·
        refine ⟨14058843285823029898020409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18745124381097373197360545 14058843285823029898020409)
        ·
          refine ⟨10544132464367272423515307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14058843285823029898020409 10544132464367272423515307)
          ·
            refine ⟨15816198696550908635272961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544132464367272423515307 15816198696550908635272961)
            ·
              refine ⟨11862149022413181476454721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15816198696550908635272961 11862149022413181476454721)
              ·
                refine ⟨8896611766809886107341041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862149022413181476454721 8896611766809886107341041)
                ·
                  refine ⟨6672458825107414580505781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896611766809886107341041 6672458825107414580505781)
                  ·
                    refine ⟨625543014853820116922417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6672458825107414580505781 625543014853820116922417)
                    ·
                      rfl

theorem cell22_1827361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1827361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827361 prefixEnd_1827361 := by exact prefixLift 1827361
  have htrace : WordTrace (prefixWord ++ tailWord_1827361) baseStart_1827361 baseEnd_1827361 := by
    simpa [prefixWord, tailWord_1827361, baseEnd_1827361] using wordTrace_append hprefix tailTrace_1827361
  have hstable : (prefixWord ++ tailWord_1827361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827361).length < 2 ^ (prefixWord ++ tailWord_1827361).sum := by decide
  have hdescent : baseEnd_1827361 < baseStart_1827361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827363 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 5]
def baseStart_1827363 : Nat := 118140960795 + 1827363 * 2 ^ 59
def prefixEnd_1827363 : Nat := 4983230072969 + 3 ^ 40 * 1827363 * 2
def baseEnd_1827363 : Nat := 208514566498230926124137

theorem tailTrace_1827363 : CollatzResearch.WordTrace tailWord_1827363 prefixEnd_1827363 208514566498230926124137 := by
  unfold tailWord_1827363
  simp only [CollatzResearch.WordTrace]
  refine ⟨66649404078783414598854743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44432936052522276399236495 66649404078783414598854743)
  ·
    refine ⟨99974106118175121898282115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66649404078783414598854743 99974106118175121898282115)
    ·
      refine ⟨149961159177262682847423173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99974106118175121898282115 149961159177262682847423173)
      ·
        refine ⟨28117717345736753033891845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149961159177262682847423173 28117717345736753033891845)
        ·
          refine ⟨5272072002325641193854721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28117717345736753033891845 5272072002325641193854721)
          ·
            refine ⟨3954054001744230895391041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5272072002325641193854721 3954054001744230895391041)
            ·
              refine ⟨2965540501308173171543281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954054001744230895391041 2965540501308173171543281)
              ·
                refine ⟨2224155375981129878657461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965540501308173171543281 2224155375981129878657461)
                ·
                  refine ⟨208514566498230926124137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2224155375981129878657461 208514566498230926124137)
                  ·
                    rfl

theorem cell22_1827363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 5].length) (baseStart_1827363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827363 prefixEnd_1827363 := by exact prefixLift 1827363
  have htrace : WordTrace (prefixWord ++ tailWord_1827363) baseStart_1827363 baseEnd_1827363 := by
    simpa [prefixWord, tailWord_1827363, baseEnd_1827363] using wordTrace_append hprefix tailTrace_1827363
  have hstable : (prefixWord ++ tailWord_1827363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827363).length < 2 ^ (prefixWord ++ tailWord_1827363).sum := by decide
  have hdescent : baseEnd_1827363 < baseStart_1827363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827376 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_1827376 : Nat := 118140960795 + 1827376 * 2 ^ 59
def prefixEnd_1827376 : Nat := 4983230072969 + 3 ^ 40 * 1827376 * 2
def baseEnd_1827376 : Nat := 625548149660365077797371

theorem tailTrace_1827376 : CollatzResearch.WordTrace tailWord_1827376 prefixEnd_1827376 625548149660365077797371 := by
  unfold tailWord_1827376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33324939113868158909538991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44433252151824211879385321 33324939113868158909538991)
  ·
    refine ⟨49987408670802238364308487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33324939113868158909538991 49987408670802238364308487)
    ·
      refine ⟨74981113006203357546462731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49987408670802238364308487 74981113006203357546462731)
      ·
        refine ⟨112471669509305036319694097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74981113006203357546462731 112471669509305036319694097)
        ·
          refine ⟨84353752131978777239770573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112471669509305036319694097 84353752131978777239770573)
          ·
            refine ⟨31632657049492041464913965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84353752131978777239770573 31632657049492041464913965)
            ·
              refine ⟨11862246393559515549342737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31632657049492041464913965 11862246393559515549342737)
              ·
                refine ⟨8896684795169636662007053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862246393559515549342737 8896684795169636662007053)
                ·
                  refine ⟨3336256798188613748252645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8896684795169636662007053 3336256798188613748252645)
                  ·
                    refine ⟨625548149660365077797371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336256798188613748252645 625548149660365077797371)
                    ·
                      rfl

theorem cell22_1827376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_1827376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827376 prefixEnd_1827376 := by exact prefixLift 1827376
  have htrace : WordTrace (prefixWord ++ tailWord_1827376) baseStart_1827376 baseEnd_1827376 := by
    simpa [prefixWord, tailWord_1827376, baseEnd_1827376] using wordTrace_append hprefix tailTrace_1827376
  have hstable : (prefixWord ++ tailWord_1827376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827376).length < 2 ^ (prefixWord ++ tailWord_1827376).sum := by decide
  have hdescent : baseEnd_1827376 < baseStart_1827376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827391 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 6]
def baseStart_1827391 : Nat := 118140960795 + 1827391 * 2 ^ 59
def prefixEnd_1827391 : Nat := 4983230072969 + 3 ^ 40 * 1827391 * 2
def baseEnd_1827391 : Nat := 208517761488970012890775

theorem tailTrace_1827391 : CollatzResearch.WordTrace tailWord_1827391 prefixEnd_1827391 208517761488970012890775 := by
  unfold tailWord_1827391
  simp only [CollatzResearch.WordTrace]
  refine ⟨66650425322681975380874027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44433616881787983587249351 66650425322681975380874027)
  ·
    refine ⟨99975637984022963071311041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66650425322681975380874027 99975637984022963071311041)
    ·
      refine ⟨74981728488017222303483281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99975637984022963071311041 74981728488017222303483281)
      ·
        refine ⟨56236296366012916727612461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74981728488017222303483281 56236296366012916727612461)
        ·
          refine ⟨21088611137254843772854673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56236296366012916727612461 21088611137254843772854673)
          ·
            refine ⟨15816458352941132829641005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21088611137254843772854673 15816458352941132829641005)
            ·
              refine ⟨5931171882352924811115377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15816458352941132829641005 5931171882352924811115377)
              ·
                refine ⟨4448378911764693608336533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931171882352924811115377 4448378911764693608336533)
                ·
                  refine ⟨208517761488970012890775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4448378911764693608336533 208517761488970012890775)
                  ·
                    rfl

theorem cell22_1827391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_1827391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827391 prefixEnd_1827391 := by exact prefixLift 1827391
  have htrace : WordTrace (prefixWord ++ tailWord_1827391) baseStart_1827391 baseEnd_1827391 := by
    simpa [prefixWord, tailWord_1827391, baseEnd_1827391] using wordTrace_append hprefix tailTrace_1827391
  have hstable : (prefixWord ++ tailWord_1827391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827391).length < 2 ^ (prefixWord ++ tailWord_1827391).sum := by decide
  have hdescent : baseEnd_1827391 < baseStart_1827391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827393 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1827393 : Nat := 118140960795 + 1827393 * 2 ^ 59
def prefixEnd_1827393 : Nat := 4983230072969 + 3 ^ 40 * 1827393 * 2
def baseEnd_1827393 : Nat := 625553969107782700122319

theorem tailTrace_1827393 : CollatzResearch.WordTrace tailWord_1827393 prefixEnd_1827393 625553969107782700122319 := by
  unfold tailWord_1827393
  simp only [CollatzResearch.WordTrace]
  refine ⟨66650498268674729722446833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44433665512449819814964555 66650498268674729722446833)
  ·
    refine ⟨49987873701506047291835125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66650498268674729722446833 49987873701506047291835125)
    ·
      refine ⟨4686363159516191933609543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49987873701506047291835125 4686363159516191933609543)
      ·
        refine ⟨7029544739274287900414315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686363159516191933609543 7029544739274287900414315)
        ·
          refine ⟨10544317108911431850621473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029544739274287900414315 10544317108911431850621473)
          ·
            refine ⟨7908237831683573887966105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544317108911431850621473 7908237831683573887966105)
            ·
              refine ⟨5931178373762680415974579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7908237831683573887966105 5931178373762680415974579)
              ·
                refine ⟨8896767560644020623961869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931178373762680415974579 8896767560644020623961869)
                ·
                  refine ⟨3336287835241507733985701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8896767560644020623961869 3336287835241507733985701)
                  ·
                    refine ⟨625553969107782700122319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336287835241507733985701 625553969107782700122319)
                    ·
                      rfl

theorem cell22_1827393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1827393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827393 prefixEnd_1827393 := by exact prefixLift 1827393
  have htrace : WordTrace (prefixWord ++ tailWord_1827393) baseStart_1827393 baseEnd_1827393 := by
    simpa [prefixWord, tailWord_1827393, baseEnd_1827393] using wordTrace_append hprefix tailTrace_1827393
  have hstable : (prefixWord ++ tailWord_1827393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827393).length < 2 ^ (prefixWord ++ tailWord_1827393).sum := by decide
  have hdescent : baseEnd_1827393 < baseStart_1827393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827438 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1827438 : Nat := 118140960795 + 1827438 * 2 ^ 59
def prefixEnd_1827438 : Nat := 4983230072969 + 3 ^ 40 * 1827438 * 2
def baseEnd_1827438 : Nat := 625569373527417582747181

theorem tailTrace_1827438 : CollatzResearch.WordTrace tailWord_1827438 prefixEnd_1827438 625569373527417582747181 := by
  unfold tailWord_1827438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8331517444188962800979371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44434759702341134938556645 8331517444188962800979371)
  ·
    refine ⟨12497276166283444201469057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8331517444188962800979371 12497276166283444201469057)
    ·
      refine ⟨9372957124712583151101793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497276166283444201469057 9372957124712583151101793)
      ·
        refine ⟨7029717843534437363326345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9372957124712583151101793 7029717843534437363326345)
        ·
          refine ⟨5272288382650828022494759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7029717843534437363326345 5272288382650828022494759)
          ·
            refine ⟨7908432573976242033742139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272288382650828022494759 7908432573976242033742139)
            ·
              refine ⟨11862648860964363050613209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908432573976242033742139 11862648860964363050613209)
              ·
                refine ⟨8896986645723272287959907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862648860964363050613209 8896986645723272287959907)
                ·
                  refine ⟨13345479968584908431939861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896986645723272287959907 13345479968584908431939861)
                  ·
                    refine ⟨625569373527417582747181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13345479968584908431939861 625569373527417582747181)
                    ·
                      rfl

theorem cell22_1827438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1827438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827438 prefixEnd_1827438 := by exact prefixLift 1827438
  have htrace : WordTrace (prefixWord ++ tailWord_1827438) baseStart_1827438 baseEnd_1827438 := by
    simpa [prefixWord, tailWord_1827438, baseEnd_1827438] using wordTrace_append hprefix tailTrace_1827438
  have hstable : (prefixWord ++ tailWord_1827438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827438).length < 2 ^ (prefixWord ++ tailWord_1827438).sum := by decide
  have hdescent : baseEnd_1827438 < baseStart_1827438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827440 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_1827440 : Nat := 118140960795 + 1827440 * 2 ^ 59
def prefixEnd_1827440 : Nat := 4983230072969 + 3 ^ 40 * 1827440 * 2
def baseEnd_1827440 : Nat := 625570058168290244197175

theorem tailTrace_1827440 : CollatzResearch.WordTrace tailWord_1827440 prefixEnd_1827440 625570058168290244197175 := by
  unfold tailWord_1827440
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326106249752228374703887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44434808333002971166271849 33326106249752228374703887)
  ·
    refine ⟨49989159374628342562055831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33326106249752228374703887 49989159374628342562055831)
    ·
      refine ⟨74983739061942513843083747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49989159374628342562055831 74983739061942513843083747)
      ·
        refine ⟨112475608592913770764625621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74983739061942513843083747 112475608592913770764625621)
        ·
          refine ⟨2636147076396416502295913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 112475608592913770764625621 2636147076396416502295913)
          ·
            refine ⟨1977110307297312376721935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636147076396416502295913 1977110307297312376721935)
            ·
              refine ⟨2965665460945968565082903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977110307297312376721935 2965665460945968565082903)
              ·
                refine ⟨4448498191418952847624355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965665460945968565082903 4448498191418952847624355)
                ·
                  refine ⟨6672747287128429271436533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448498191418952847624355 6672747287128429271436533)
                  ·
                    refine ⟨625570058168290244197175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6672747287128429271436533 625570058168290244197175)
                    ·
                      rfl

theorem cell22_1827440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_1827440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827440 prefixEnd_1827440 := by exact prefixLift 1827440
  have htrace : WordTrace (prefixWord ++ tailWord_1827440) baseStart_1827440 baseEnd_1827440 := by
    simpa [prefixWord, tailWord_1827440, baseEnd_1827440] using wordTrace_append hprefix tailTrace_1827440
  have hstable : (prefixWord ++ tailWord_1827440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827440).length < 2 ^ (prefixWord ++ tailWord_1827440).sum := by decide
  have hdescent : baseEnd_1827440 < baseStart_1827440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827453 : List Nat := [1, 4, 1, 1, 5, 1, 1, 8]
def baseStart_1827453 : Nat := 118140960795 + 1827453 * 2 ^ 59
def prefixEnd_1827453 : Nat := 4983230072969 + 3 ^ 40 * 1827453 * 2
def baseEnd_1827453 : Nat := 69508278703773615958015

theorem tailTrace_1827453 : CollatzResearch.WordTrace tailWord_1827453 prefixEnd_1827453 69508278703773615958015 := by
  unfold tailWord_1827453
  simp only [CollatzResearch.WordTrace]
  refine ⟨66652686648457359969631013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44435124432304906646420675 66652686648457359969631013)
  ·
    refine ⟨12497378746585754994305815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66652686648457359969631013 12497378746585754994305815)
    ·
      refine ⟨18746068119878632491458723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497378746585754994305815 18746068119878632491458723)
      ·
        refine ⟨28119102179817948737188085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18746068119878632491458723 28119102179817948737188085)
        ·
          refine ⟨2636165829357932694111383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28119102179817948737188085 2636165829357932694111383)
          ·
            refine ⟨3954248744036899041167075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636165829357932694111383 3954248744036899041167075)
            ·
              refine ⟨5931373116055348561750613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954248744036899041167075 5931373116055348561750613)
              ·
                refine ⟨69508278703773615958015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5931373116055348561750613 69508278703773615958015)
                ·
                  rfl

theorem cell22_1827453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 8].length) (baseStart_1827453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827453 prefixEnd_1827453 := by exact prefixLift 1827453
  have htrace : WordTrace (prefixWord ++ tailWord_1827453) baseStart_1827453 baseEnd_1827453 := by
    simpa [prefixWord, tailWord_1827453, baseEnd_1827453] using wordTrace_append hprefix tailTrace_1827453
  have hstable : (prefixWord ++ tailWord_1827453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827453).length < 2 ^ (prefixWord ++ tailWord_1827453).sum := by decide
  have hdescent : baseEnd_1827453 < baseStart_1827453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827481 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 7]
def baseStart_1827481 : Nat := 118140960795 + 1827481 * 2 ^ 59
def prefixEnd_1827481 : Nat := 4983230072969 + 3 ^ 40 * 1827481 * 2
def baseEnd_1827481 : Nat := 208528031102059934640683

theorem tailTrace_1827481 : CollatzResearch.WordTrace tailWord_1827481 prefixEnd_1827481 208528031102059934640683 := by
  unfold tailWord_1827481
  simp only [CollatzResearch.WordTrace]
  refine ⟨66653707892355920751650297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44435805261570613834433531 66653707892355920751650297)
  ·
    refine ⟨49990280919266940563737723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66653707892355920751650297 49990280919266940563737723)
    ·
      refine ⟨74985421378900410845606585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49990280919266940563737723 74985421378900410845606585)
      ·
        refine ⟨56239066034175308134204939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74985421378900410845606585 56239066034175308134204939)
        ·
          refine ⟨84358599051262962201307409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56239066034175308134204939 84358599051262962201307409)
          ·
            refine ⟨63268949288447221650980557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84358599051262962201307409 63268949288447221650980557)
            ·
              refine ⟨23725855983167708119117709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63268949288447221650980557 23725855983167708119117709)
              ·
                refine ⟨8897195993687890544669141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23725855983167708119117709 8897195993687890544669141)
                ·
                  refine ⟨208528031102059934640683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8897195993687890544669141 208528031102059934640683)
                  ·
                    rfl

theorem cell22_1827481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_1827481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827481 prefixEnd_1827481 := by exact prefixLift 1827481
  have htrace : WordTrace (prefixWord ++ tailWord_1827481) baseStart_1827481 baseEnd_1827481 := by
    simpa [prefixWord, tailWord_1827481, baseEnd_1827481] using wordTrace_append hprefix tailTrace_1827481
  have hstable : (prefixWord ++ tailWord_1827481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827481).length < 2 ^ (prefixWord ++ tailWord_1827481).sum := by decide
  have hdescent : baseEnd_1827481 < baseStart_1827481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827485 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1827485 : Nat := 118140960795 + 1827485 * 2 ^ 59
def prefixEnd_1827485 : Nat := 4983230072969 + 3 ^ 40 * 1827485 * 2
def baseEnd_1827485 : Nat := 625585462587925126822037

theorem tailTrace_1827485 : CollatzResearch.WordTrace tailWord_1827485 prefixEnd_1827485 625585462587925126822037 := by
  unfold tailWord_1827485
  simp only [CollatzResearch.WordTrace]
  refine ⟨66653853784341429434795909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44435902522894286289863939 66653853784341429434795909)
  ·
    refine ⟨12497597584564018019024233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66653853784341429434795909 12497597584564018019024233)
    ·
      refine ⟨9373198188423013514268175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497597584564018019024233 9373198188423013514268175)
      ·
        refine ⟨14059797282634520271402263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373198188423013514268175 14059797282634520271402263)
        ·
          refine ⟨21089695923951780407103395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059797282634520271402263 21089695923951780407103395)
          ·
            refine ⟨31634543885927670610655093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21089695923951780407103395 31634543885927670610655093)
            ·
              refine ⟨2965738489305719119748915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31634543885927670610655093 2965738489305719119748915)
              ·
                refine ⟨4448607733958578679623373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965738489305719119748915 4448607733958578679623373)
                ·
                  refine ⟨1668227900234467004858765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4448607733958578679623373 1668227900234467004858765)
                  ·
                    refine ⟨625585462587925126822037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1668227900234467004858765 625585462587925126822037)
                    ·
                      rfl

theorem cell22_1827485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1827485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827485 prefixEnd_1827485 := by exact prefixLift 1827485
  have htrace : WordTrace (prefixWord ++ tailWord_1827485) baseStart_1827485 baseEnd_1827485 := by
    simpa [prefixWord, tailWord_1827485, baseEnd_1827485] using wordTrace_append hprefix tailTrace_1827485
  have hstable : (prefixWord ++ tailWord_1827485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827485).length < 2 ^ (prefixWord ++ tailWord_1827485).sum := by decide
  have hdescent : baseEnd_1827485 < baseStart_1827485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827560 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_1827560 : Nat := 118140960795 + 1827560 * 2 ^ 59
def prefixEnd_1827560 : Nat := 4983230072969 + 3 ^ 40 * 1827560 * 2
def baseEnd_1827560 : Nat := 208537045540216643732269

theorem tailTrace_1827560 : CollatzResearch.WordTrace tailWord_1827560 prefixEnd_1827560 208537045540216643732269 := by
  unfold tailWord_1827560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33328294629534858621888067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44437726172713144829184089 33328294629534858621888067)
  ·
    refine ⟨49992441944302287932832101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33328294629534858621888067 49992441944302287932832101)
    ·
      refine ⟨9373582864556678987406019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49992441944302287932832101 9373582864556678987406019)
      ·
        refine ⟨14060374296835018481109029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373582864556678987406019 14060374296835018481109029)
        ·
          refine ⟨2636320180656565965207943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14060374296835018481109029 2636320180656565965207943)
          ·
            refine ⟨3954480270984848947811915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636320180656565965207943 3954480270984848947811915)
            ·
              refine ⟨5931720406477273421717873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954480270984848947811915 5931720406477273421717873)
              ·
                refine ⟨4448790304857955066288405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931720406477273421717873 4448790304857955066288405)
                ·
                  refine ⟨208537045540216643732269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4448790304857955066288405 208537045540216643732269)
                  ·
                    rfl

theorem cell22_1827560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_1827560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827560 prefixEnd_1827560 := by exact prefixLift 1827560
  have htrace : WordTrace (prefixWord ++ tailWord_1827560) baseStart_1827560 baseEnd_1827560 := by
    simpa [prefixWord, tailWord_1827560, baseEnd_1827560] using wordTrace_append hprefix tailTrace_1827560
  have hstable : (prefixWord ++ tailWord_1827560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827560).length < 2 ^ (prefixWord ++ tailWord_1827560).sum := by decide
  have hdescent : baseEnd_1827560 < baseStart_1827560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827588 : List Nat := [2, 3, 2, 2, 1, 1, 11]
def baseStart_1827588 : Nat := 118140960795 + 1827588 * 2 ^ 59
def prefixEnd_1827588 : Nat := 4983230072969 + 3 ^ 40 * 1827588 * 2
def baseEnd_1827588 : Nat := 23171137836772858944323

theorem tailTrace_1827588 : CollatzResearch.WordTrace tailWord_1827588 prefixEnd_1827588 23171137836772858944323 := by
  unfold tailWord_1827588
  simp only [CollatzResearch.WordTrace]
  refine ⟨33328805251484139012897709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44438407001978852017196945 33328805251484139012897709)
  ·
    refine ⟨12498301969306552129836641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33328805251484139012897709 12498301969306552129836641)
    ·
      refine ⟨9373726476979914097377481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12498301969306552129836641 9373726476979914097377481)
      ·
        refine ⟨7030294857734935573033111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9373726476979914097377481 7030294857734935573033111)
        ·
          refine ⟨10545442286602403359549667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030294857734935573033111 10545442286602403359549667)
          ·
            refine ⟨15818163429903605039324501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545442286602403359549667 15818163429903605039324501)
            ·
              refine ⟨23171137836772858944323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15818163429903605039324501 23171137836772858944323)
              ·
                rfl

theorem cell22_1827588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 11].length) (baseStart_1827588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827588 prefixEnd_1827588 := by exact prefixLift 1827588
  have htrace : WordTrace (prefixWord ++ tailWord_1827588) baseStart_1827588 baseEnd_1827588 := by
    simpa [prefixWord, tailWord_1827588, baseEnd_1827588] using wordTrace_append hprefix tailTrace_1827588
  have hstable : (prefixWord ++ tailWord_1827588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827588).length < 2 ^ (prefixWord ++ tailWord_1827588).sum := by decide
  have hdescent : baseEnd_1827588 < baseStart_1827588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827592 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_1827592 : Nat := 118140960795 + 1827592 * 2 ^ 59
def prefixEnd_1827592 : Nat := 4983230072969 + 3 ^ 40 * 1827592 * 2
def baseEnd_1827592 : Nat := 625622090874612514396709

theorem tailTrace_1827592 : CollatzResearch.WordTrace tailWord_1827592 prefixEnd_1827592 625622090874612514396709 := by
  unfold tailWord_1827592
  simp only [CollatzResearch.WordTrace]
  refine ⟨33328878197476893354470515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44438504263302524472627353 33328878197476893354470515)
  ·
    refine ⟨49993317296215340031705773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33328878197476893354470515 49993317296215340031705773)
    ·
      refine ⟨18747493986080752511889665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49993317296215340031705773 18747493986080752511889665)
      ·
        refine ⟨14060620489560564383917249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18747493986080752511889665 14060620489560564383917249)
        ·
          refine ⟨10545465367170423287937937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14060620489560564383917249 10545465367170423287937937)
          ·
            refine ⟨7909099025377817465953453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10545465367170423287937937 7909099025377817465953453)
            ·
              refine ⟨2965912134516681549732545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7909099025377817465953453 2965912134516681549732545)
              ·
                refine ⟨2224434100887511162299409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965912134516681549732545 2224434100887511162299409)
                ·
                  refine ⟨1668325575665633371724557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2224434100887511162299409 1668325575665633371724557)
                  ·
                    refine ⟨625622090874612514396709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1668325575665633371724557 625622090874612514396709)
                    ·
                      rfl

theorem cell22_1827592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_1827592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827592 prefixEnd_1827592 := by exact prefixLift 1827592
  have htrace : WordTrace (prefixWord ++ tailWord_1827592) baseStart_1827592 baseEnd_1827592 := by
    simpa [prefixWord, tailWord_1827592, baseEnd_1827592] using wordTrace_append hprefix tailTrace_1827592
  have hstable : (prefixWord ++ tailWord_1827592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827592).length < 2 ^ (prefixWord ++ tailWord_1827592).sum := by decide
  have hdescent : baseEnd_1827592 < baseStart_1827592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827633 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 9]
def baseStart_1827633 : Nat := 118140960795 + 1827633 * 2 ^ 59
def prefixEnd_1827633 : Nat := 4983230072969 + 3 ^ 40 * 1827633 * 2
def baseEnd_1827633 : Nat := 208545375337500691373861

theorem tailTrace_1827633 : CollatzResearch.WordTrace tailWord_1827633 prefixEnd_1827633 208545375337500691373861 := by
  unfold tailWord_1827633
  simp only [CollatzResearch.WordTrace]
  refine ⟨66659251787805250711183553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44439501191870167140789035 66659251787805250711183553)
  ·
    refine ⟨49994438840853938033387665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66659251787805250711183553 49994438840853938033387665)
    ·
      refine ⟨37495829130640453525040749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49994438840853938033387665 37495829130640453525040749)
      ·
        refine ⟨14060935923990170071890281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37495829130640453525040749 14060935923990170071890281)
        ·
          refine ⟨10545701942992627553917711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14060935923990170071890281 10545701942992627553917711)
          ·
            refine ⟨15818552914488941330876567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545701942992627553917711 15818552914488941330876567)
            ·
              refine ⟨23727829371733411996314851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15818552914488941330876567 23727829371733411996314851)
              ·
                refine ⟨35591744057600117994472277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23727829371733411996314851 35591744057600117994472277)
                ·
                  refine ⟨208545375337500691373861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35591744057600117994472277 208545375337500691373861)
                  ·
                    rfl

theorem cell22_1827633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_1827633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827633 prefixEnd_1827633 := by exact prefixLift 1827633
  have htrace : WordTrace (prefixWord ++ tailWord_1827633) baseStart_1827633 baseEnd_1827633 := by
    simpa [prefixWord, tailWord_1827633, baseEnd_1827633] using wordTrace_append hprefix tailTrace_1827633
  have hstable : (prefixWord ++ tailWord_1827633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827633).length < 2 ^ (prefixWord ++ tailWord_1827633).sum := by decide
  have hdescent : baseEnd_1827633 < baseStart_1827633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827648 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_1827648 : Nat := 118140960795 + 1827648 * 2 ^ 59
def prefixEnd_1827648 : Nat := 4983230072969 + 3 ^ 40 * 1827648 * 2
def baseEnd_1827648 : Nat := 625641260819047034996537

theorem tailTrace_1827648 : CollatzResearch.WordTrace tailWord_1827648 prefixEnd_1827648 625641260819047034996537 := by
  unfold tailWord_1827648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33329899441375454136489799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44439865921833938848653065 33329899441375454136489799)
  ·
    refine ⟨49994849162063181204734699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33329899441375454136489799 49994849162063181204734699)
    ·
      refine ⟨74992273743094771807102049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49994849162063181204734699 74992273743094771807102049)
      ·
        refine ⟨56244205307321078855326537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74992273743094771807102049 56244205307321078855326537)
        ·
          refine ⟨42183153980490809141494903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56244205307321078855326537 42183153980490809141494903)
          ·
            refine ⟨63274730970736213712242355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42183153980490809141494903 63274730970736213712242355)
            ·
              refine ⟨94912096456104320568363533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63274730970736213712242355 94912096456104320568363533)
              ·
                refine ⟨35592036171039120213136325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94912096456104320568363533 35592036171039120213136325)
                ·
                  refine ⟨6673506782069835039963061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35592036171039120213136325 6673506782069835039963061)
                  ·
                    refine ⟨625641260819047034996537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6673506782069835039963061 625641260819047034996537)
                    ·
                      rfl

theorem cell22_1827648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_1827648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827648 prefixEnd_1827648 := by exact prefixLift 1827648
  have htrace : WordTrace (prefixWord ++ tailWord_1827648) baseStart_1827648 baseEnd_1827648 := by
    simpa [prefixWord, tailWord_1827648, baseEnd_1827648] using wordTrace_append hprefix tailTrace_1827648
  have hstable : (prefixWord ++ tailWord_1827648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827648).length < 2 ^ (prefixWord ++ tailWord_1827648).sum := by decide
  have hdescent : baseEnd_1827648 < baseStart_1827648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827680 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_1827680 : Nat := 118140960795 + 1827680 * 2 ^ 59
def prefixEnd_1827680 : Nat := 4983230072969 + 3 ^ 40 * 1827680 * 2
def baseEnd_1827680 : Nat := 625652215073009618196439

theorem tailTrace_1827680 : CollatzResearch.WordTrace tailWord_1827680 prefixEnd_1827680 625652215073009618196439 := by
  unfold tailWord_1827680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330483009317488869072247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44440644012423318492096329 33330483009317488869072247)
  ·
    refine ⟨49995724513976233303608371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33330483009317488869072247 49995724513976233303608371)
    ·
      refine ⟨74993586770964349955412557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49995724513976233303608371 74993586770964349955412557)
      ·
        refine ⟨28122595039111631233279709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74993586770964349955412557 28122595039111631233279709)
        ·
          refine ⟨10545973139666861712479891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28122595039111631233279709 10545973139666861712479891)
          ·
            refine ⟨15818959709500292568719837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10545973139666861712479891 15818959709500292568719837)
            ·
              refine ⟨5932109891062609713269939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15818959709500292568719837 5932109891062609713269939)
              ·
                refine ⟨8898164836593914569904909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932109891062609713269939 8898164836593914569904909)
                ·
                  refine ⟨3336811813722717963714341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8898164836593914569904909 3336811813722717963714341)
                  ·
                    refine ⟨625652215073009618196439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336811813722717963714341 625652215073009618196439)
                    ·
                      rfl

theorem cell22_1827680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_1827680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827680 prefixEnd_1827680 := by exact prefixLift 1827680
  have htrace : WordTrace (prefixWord ++ tailWord_1827680) baseStart_1827680 baseEnd_1827680 := by
    simpa [prefixWord, tailWord_1827680, baseEnd_1827680] using wordTrace_append hprefix tailTrace_1827680
  have hstable : (prefixWord ++ tailWord_1827680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827680).length < 2 ^ (prefixWord ++ tailWord_1827680).sum := by decide
  have hdescent : baseEnd_1827680 < baseStart_1827680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827761 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_1827761 : Nat := 118140960795 + 1827761 * 2 ^ 59
def prefixEnd_1827761 : Nat := 4983230072969 + 3 ^ 40 * 1827761 * 2
def baseEnd_1827761 : Nat := 625679943028352406921191

theorem tailTrace_1827761 : CollatzResearch.WordTrace tailWord_1827761 prefixEnd_1827761 625679943028352406921191 := by
  unfold tailWord_1827761
  simp only [CollatzResearch.WordTrace]
  refine ⟨66663920331341528571843137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44442613554227685714562091 66663920331341528571843137)
  ·
    refine ⟨49997940248506146428882353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66663920331341528571843137 49997940248506146428882353)
    ·
      refine ⟨37498455186379609821661765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49997940248506146428882353 37498455186379609821661765)
      ·
        refine ⟨7030960347446176841561581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37498455186379609821661765 7030960347446176841561581)
        ·
          refine ⟨2636610130292316315585593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030960347446176841561581 2636610130292316315585593)
          ·
            refine ⟨1977457597719237236689195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2636610130292316315585593 1977457597719237236689195)
            ·
              refine ⟨2966186396578855855033793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977457597719237236689195 2966186396578855855033793)
              ·
                refine ⟨2224639797434141891275345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966186396578855855033793 2224639797434141891275345)
                ·
                  refine ⟨1668479848075606418456509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2224639797434141891275345 1668479848075606418456509)
                  ·
                    refine ⟨625679943028352406921191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1668479848075606418456509 625679943028352406921191)
                    ·
                      rfl

theorem cell22_1827761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_1827761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827761 prefixEnd_1827761 := by exact prefixLift 1827761
  have htrace : WordTrace (prefixWord ++ tailWord_1827761) baseStart_1827761 baseEnd_1827761 := by
    simpa [prefixWord, tailWord_1827761, baseEnd_1827761] using wordTrace_append hprefix tailTrace_1827761
  have hstable : (prefixWord ++ tailWord_1827761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827761).length < 2 ^ (prefixWord ++ tailWord_1827761).sum := by decide
  have hdescent : baseEnd_1827761 < baseStart_1827761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827875 : List Nat := [1, 1, 1, 4, 3, 12]
def baseStart_1827875 : Nat := 118140960795 + 1827875 * 2 ^ 59
def prefixEnd_1827875 : Nat := 4983230072969 + 3 ^ 40 * 1827875 * 2
def baseEnd_1827875 : Nat := 7724925525408569253961

theorem tailTrace_1827875 : CollatzResearch.WordTrace tailWord_1827875 prefixEnd_1827875 7724925525408569253961 := by
  unfold tailWord_1827875
  simp only [CollatzResearch.WordTrace]
  refine ⟨66668078252928526041493079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44445385501952350694328719 66668078252928526041493079)
  ·
    refine ⟨100002117379392789062239619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66668078252928526041493079 100002117379392789062239619)
    ·
      refine ⟨150003176069089183593359429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100002117379392789062239619 150003176069089183593359429)
      ·
        refine ⟨28125595512954221923754893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150003176069089183593359429 28125595512954221923754893)
        ·
          refine ⟨10547098317357833221408085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28125595512954221923754893 10547098317357833221408085)
          ·
            refine ⟨7724925525408569253961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10547098317357833221408085 7724925525408569253961)
            ·
              rfl

theorem cell22_1827875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 12].length) (baseStart_1827875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827875 prefixEnd_1827875 := by exact prefixLift 1827875
  have htrace : WordTrace (prefixWord ++ tailWord_1827875) baseStart_1827875 baseEnd_1827875 := by
    simpa [prefixWord, tailWord_1827875, baseEnd_1827875] using wordTrace_append hprefix tailTrace_1827875
  have hstable : (prefixWord ++ tailWord_1827875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827875).length < 2 ^ (prefixWord ++ tailWord_1827875).sum := by decide
  have hdescent : baseEnd_1827875 < baseStart_1827875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827877 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1827877 : Nat := 118140960795 + 1827877 * 2 ^ 59
def prefixEnd_1827877 : Nat := 4983230072969 + 3 ^ 40 * 1827877 * 2
def baseEnd_1827877 : Nat := 625719652198966771020835

theorem tailTrace_1827877 : CollatzResearch.WordTrace tailWord_1827877 prefixEnd_1827877 625719652198966771020835 := by
  unfold tailWord_1827877
  simp only [CollatzResearch.WordTrace]
  refine ⟨66668151198921280383065885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44445434132614186922043923 66668151198921280383065885)
  ·
    refine ⟨25000556699595480143649707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66668151198921280383065885 25000556699595480143649707)
    ·
      refine ⟨37500835049393220215474561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25000556699595480143649707 37500835049393220215474561)
      ·
        refine ⟨28125626287044915161605921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37500835049393220215474561 28125626287044915161605921)
        ·
          refine ⟨21094219715283686371204441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28125626287044915161605921 21094219715283686371204441)
          ·
            refine ⟨15820664786462764778403331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21094219715283686371204441 15820664786462764778403331)
            ·
              refine ⟨23730997179694147167604997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15820664786462764778403331 23730997179694147167604997)
              ·
                refine ⟨4449561971192652593925937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23730997179694147167604997 4449561971192652593925937)
                ·
                  refine ⟨3337171478394489445444453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449561971192652593925937 3337171478394489445444453)
                  ·
                    refine ⟨625719652198966771020835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337171478394489445444453 625719652198966771020835)
                    ·
                      rfl

theorem cell22_1827877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1827877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827877 prefixEnd_1827877 := by exact prefixLift 1827877
  have htrace : WordTrace (prefixWord ++ tailWord_1827877) baseStart_1827877 baseEnd_1827877 := by
    simpa [prefixWord, tailWord_1827877, baseEnd_1827877] using wordTrace_append hprefix tailTrace_1827877
  have hstable : (prefixWord ++ tailWord_1827877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827877).length < 2 ^ (prefixWord ++ tailWord_1827877).sum := by decide
  have hdescent : baseEnd_1827877 < baseStart_1827877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827926 : List Nat := [5, 2, 2, 1, 2, 1, 9]
def baseStart_1827926 : Nat := 118140960795 + 1827926 * 2 ^ 59
def prefixEnd_1827926 : Nat := 4983230072969 + 3 ^ 40 * 1827926 * 2
def baseEnd_1827926 : Nat := 23175423181494332464655

theorem tailTrace_1827926 : CollatzResearch.WordTrace tailWord_1827926 prefixEnd_1827926 23175423181494332464655 := by
  unfold tailWord_1827926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166871148483985109474977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44446625583829174501066421 4166871148483985109474977)
  ·
    refine ⟨3125153361362988832106233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4166871148483985109474977 3125153361362988832106233)
    ·
      refine ⟨2343865021022241624079675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3125153361362988832106233 2343865021022241624079675)
      ·
        refine ⟨3515797531533362436119513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343865021022241624079675 3515797531533362436119513)
        ·
          refine ⟨2636848148650021827089635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515797531533362436119513 2636848148650021827089635)
          ·
            refine ⟨3955272222975032740634453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636848148650021827089635 3955272222975032740634453)
            ·
              refine ⟨23175423181494332464655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3955272222975032740634453 23175423181494332464655)
              ·
                rfl

theorem cell22_1827926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 9].length) (baseStart_1827926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827926 prefixEnd_1827926 := by exact prefixLift 1827926
  have htrace : WordTrace (prefixWord ++ tailWord_1827926) baseStart_1827926 baseEnd_1827926 := by
    simpa [prefixWord, tailWord_1827926, baseEnd_1827926] using wordTrace_append hprefix tailTrace_1827926
  have hstable : (prefixWord ++ tailWord_1827926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827926).length < 2 ^ (prefixWord ++ tailWord_1827926).sum := by decide
  have hdescent : baseEnd_1827926 < baseStart_1827926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827941 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_1827941 : Nat := 118140960795 + 1827941 * 2 ^ 59
def prefixEnd_1827941 : Nat := 4983230072969 + 3 ^ 40 * 1827941 * 2
def baseEnd_1827941 : Nat := 625741560706891937420639

theorem tailTrace_1827941 : CollatzResearch.WordTrace tailWord_1827941 prefixEnd_1827941 625741560706891937420639 := by
  unfold tailWord_1827941
  simp only [CollatzResearch.WordTrace]
  refine ⟨66670485470689419313395677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44446990313792946208930451 66670485470689419313395677)
  ·
    refine ⟨25001432051508532242523379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66670485470689419313395677 25001432051508532242523379)
    ·
      refine ⟨37502148077262798363785069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25001432051508532242523379 37502148077262798363785069)
      ·
        refine ⟨14063305528973549386419401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37502148077262798363785069 14063305528973549386419401)
        ·
          refine ⟨10547479146730162039814551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14063305528973549386419401 10547479146730162039814551)
          ·
            refine ⟨15821218720095243059721827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547479146730162039814551 15821218720095243059721827)
            ·
              refine ⟨23731828080142864589582741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15821218720095243059721827 23731828080142864589582741)
              ·
                refine ⟨1112429441256696777636691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23731828080142864589582741 1112429441256696777636691)
                ·
                  refine ⟨1668644161885045166455037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112429441256696777636691 1668644161885045166455037)
                  ·
                    refine ⟨625741560706891937420639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1668644161885045166455037 625741560706891937420639)
                    ·
                      rfl

theorem cell22_1827941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_1827941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827941 prefixEnd_1827941 := by exact prefixLift 1827941
  have htrace : WordTrace (prefixWord ++ tailWord_1827941) baseStart_1827941 baseEnd_1827941 := by
    simpa [prefixWord, tailWord_1827941, baseEnd_1827941] using wordTrace_append hprefix tailTrace_1827941
  have hstable : (prefixWord ++ tailWord_1827941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827941).length < 2 ^ (prefixWord ++ tailWord_1827941).sum := by decide
  have hdescent : baseEnd_1827941 < baseStart_1827941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827952 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_1827952 : Nat := 118140960795 + 1827952 * 2 ^ 59
def prefixEnd_1827952 : Nat := 4983230072969 + 3 ^ 40 * 1827952 * 2
def baseEnd_1827952 : Nat := 625745326231691575395605

theorem tailTrace_1827952 : CollatzResearch.WordTrace tailWord_1827952 prefixEnd_1827952 625745326231691575395605 := by
  unfold tailWord_1827952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33335443336824784096023055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44447257782433045461364073 33335443336824784096023055)
  ·
    refine ⟨50003165005237176144034583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33335443336824784096023055 50003165005237176144034583)
    ·
      refine ⟨75004747507855764216051875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50003165005237176144034583 75004747507855764216051875)
      ·
        refine ⟨112507121261783646324077813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75004747507855764216051875 112507121261783646324077813)
        ·
          refine ⟨10547542618292216842882295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112507121261783646324077813 10547542618292216842882295)
          ·
            refine ⟨15821313927438325264323443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547542618292216842882295 15821313927438325264323443)
            ·
              refine ⟨23731970891157487896485165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15821313927438325264323443 23731970891157487896485165)
              ·
                refine ⟨8899489084184057961181937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23731970891157487896485165 8899489084184057961181937)
                ·
                  refine ⟨6674616813138043470886453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8899489084184057961181937 6674616813138043470886453)
                  ·
                    refine ⟨625745326231691575395605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6674616813138043470886453 625745326231691575395605)
                    ·
                      rfl

theorem cell22_1827952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_1827952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827952 prefixEnd_1827952 := by exact prefixLift 1827952
  have htrace : WordTrace (prefixWord ++ tailWord_1827952) baseStart_1827952 baseEnd_1827952 := by
    simpa [prefixWord, tailWord_1827952, baseEnd_1827952] using wordTrace_append hprefix tailTrace_1827952
  have hstable : (prefixWord ++ tailWord_1827952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827952).length < 2 ^ (prefixWord ++ tailWord_1827952).sum := by decide
  have hdescent : baseEnd_1827952 < baseStart_1827952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828012 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_1828012 : Nat := 118140960795 + 1828012 * 2 ^ 59
def prefixEnd_1828012 : Nat := 4983230072969 + 3 ^ 40 * 1828012 * 2
def baseEnd_1828012 : Nat := 625765865457871418895421

theorem tailTrace_1828012 : CollatzResearch.WordTrace tailWord_1828012 prefixEnd_1828012 625765865457871418895421 := by
  unfold tailWord_1828012
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336537526716099219615145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44448716702288132292820193 33336537526716099219615145)
  ·
    refine ⟨25002403145037074414711359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33336537526716099219615145 25002403145037074414711359)
    ·
      refine ⟨37503604717555611622067039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25002403145037074414711359 37503604717555611622067039)
      ·
        refine ⟨56255407076333417433100559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37503604717555611622067039 56255407076333417433100559)
        ·
          refine ⟨84383110614500126149650839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56255407076333417433100559 84383110614500126149650839)
          ·
            refine ⟨126574665921750189224476259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84383110614500126149650839 126574665921750189224476259)
            ·
              refine ⟨189861998882625283836714389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126574665921750189224476259 189861998882625283836714389)
              ·
                refine ⟨8899781197623060179845987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189861998882625283836714389 8899781197623060179845987)
                ·
                  refine ⟨13349671796434590269768981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8899781197623060179845987 13349671796434590269768981)
                  ·
                    refine ⟨625765865457871418895421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13349671796434590269768981 625765865457871418895421)
                    ·
                      rfl

theorem cell22_1828012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_1828012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828012 prefixEnd_1828012 := by exact prefixLift 1828012
  have htrace : WordTrace (prefixWord ++ tailWord_1828012) baseStart_1828012 baseEnd_1828012 := by
    simpa [prefixWord, tailWord_1828012, baseEnd_1828012] using wordTrace_append hprefix tailTrace_1828012
  have hstable : (prefixWord ++ tailWord_1828012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828012).length < 2 ^ (prefixWord ++ tailWord_1828012).sum := by decide
  have hdescent : baseEnd_1828012 < baseStart_1828012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828029 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1828029 : Nat := 118140960795 + 1828029 * 2 ^ 59
def prefixEnd_1828029 : Nat := 4983230072969 + 3 ^ 40 * 1828029 * 2
def baseEnd_1828029 : Nat := 625771684905289041220369

theorem tailTrace_1828029 : CollatzResearch.WordTrace tailWord_1828029 prefixEnd_1828029 625771684905289041220369 := by
  unfold tailWord_1828029
  simp only [CollatzResearch.WordTrace]
  refine ⟨66673695094370610342599141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44449130062913740228399427 66673695094370610342599141)
  ·
    refine ⟨12501317830194489439237339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66673695094370610342599141 12501317830194489439237339)
    ·
      refine ⟨18751976745291734158856009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12501317830194489439237339 18751976745291734158856009)
      ·
        refine ⟨14063982558968800619142007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18751976745291734158856009 14063982558968800619142007)
        ·
          refine ⟨21095973838453200928713011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063982558968800619142007 21095973838453200928713011)
          ·
            refine ⟨31643960757679801393069517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21095973838453200928713011 31643960757679801393069517)
            ·
              refine ⟨11866485284129925522401069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31643960757679801393069517 11866485284129925522401069)
              ·
                refine ⟨4449931981548722070900401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11866485284129925522401069 4449931981548722070900401)
                ·
                  refine ⟨3337448986161541553175301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449931981548722070900401 3337448986161541553175301)
                  ·
                    refine ⟨625771684905289041220369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337448986161541553175301 625771684905289041220369)
                    ·
                      rfl

theorem cell22_1828029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1828029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828029 prefixEnd_1828029 := by exact prefixLift 1828029
  have htrace : WordTrace (prefixWord ++ tailWord_1828029) baseStart_1828029 baseEnd_1828029 := by
    simpa [prefixWord, tailWord_1828029, baseEnd_1828029] using wordTrace_append hprefix tailTrace_1828029
  have hstable : (prefixWord ++ tailWord_1828029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828029).length < 2 ^ (prefixWord ++ tailWord_1828029).sum := by decide
  have hdescent : baseEnd_1828029 < baseStart_1828029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828076 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_1828076 : Nat := 118140960795 + 1828076 * 2 ^ 59
def prefixEnd_1828076 : Nat := 4983230072969 + 3 ^ 40 * 1828076 * 2
def baseEnd_1828076 : Nat := 625787773965796585295225

theorem tailTrace_1828076 : CollatzResearch.WordTrace tailWord_1828076 prefixEnd_1828076 625787773965796585295225 := by
  unfold tailWord_1828076
  simp only [CollatzResearch.WordTrace]
  refine ⟨33337704662600168684780041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44450272883466891579706721 33337704662600168684780041)
  ·
    refine ⟨25003278496950126513585031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33337704662600168684780041 25003278496950126513585031)
    ·
      refine ⟨37504917745425189770377547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25003278496950126513585031 37504917745425189770377547)
      ·
        refine ⟨56257376618137784655566321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37504917745425189770377547 56257376618137784655566321)
        ·
          refine ⟨42193032463603338491674741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56257376618137784655566321 42193032463603338491674741)
          ·
            refine ⟨3955596793462812983594507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42193032463603338491674741 3955596793462812983594507)
            ·
              refine ⟨5933395190194219475391761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955596793462812983594507 5933395190194219475391761)
              ·
                refine ⟨4450046392645664606543821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933395190194219475391761 4450046392645664606543821)
                ·
                  refine ⟨1668767397242124227453933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4450046392645664606543821 1668767397242124227453933)
                  ·
                    refine ⟨625787773965796585295225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1668767397242124227453933 625787773965796585295225)
                    ·
                      rfl

theorem cell22_1828076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_1828076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828076 prefixEnd_1828076 := by exact prefixLift 1828076
  have htrace : WordTrace (prefixWord ++ tailWord_1828076) baseStart_1828076 baseEnd_1828076 := by
    simpa [prefixWord, tailWord_1828076, baseEnd_1828076] using wordTrace_append hprefix tailTrace_1828076
  have hstable : (prefixWord ++ tailWord_1828076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828076).length < 2 ^ (prefixWord ++ tailWord_1828076).sum := by decide
  have hdescent : baseEnd_1828076 < baseStart_1828076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828179 : List Nat := [1, 1, 1, 2, 1, 1, 8, 7]
def baseStart_1828179 : Nat := 118140960795 + 1828179 * 2 ^ 59
def prefixEnd_1828179 : Nat := 4983230072969 + 3 ^ 40 * 1828179 * 2
def baseEnd_1828179 : Nat := 69535892552304294441101

theorem tailTrace_1828179 : CollatzResearch.WordTrace tailWord_1828179 prefixEnd_1828179 69535892552304294441101 := by
  unfold tailWord_1828179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66679166043827185960559591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44452777362551457307039727 66679166043827185960559591)
  ·
    refine ⟨100018749065740778940839387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66679166043827185960559591 100018749065740778940839387)
    ·
      refine ⟨150028123598611168411259081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100018749065740778940839387 150028123598611168411259081)
      ·
        refine ⟨112521092698958376308444311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150028123598611168411259081 112521092698958376308444311)
        ·
          refine ⟨168781639048437564462666467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112521092698958376308444311 168781639048437564462666467)
          ·
            refine ⟨253172458572656346693999701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168781639048437564462666467 253172458572656346693999701)
            ·
              refine ⟨2966864748898316562820309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 253172458572656346693999701 2966864748898316562820309)
              ·
                refine ⟨69535892552304294441101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2966864748898316562820309 69535892552304294441101)
                ·
                  rfl

theorem cell22_1828179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 7].length) (baseStart_1828179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828179 prefixEnd_1828179 := by exact prefixLift 1828179
  have htrace : WordTrace (prefixWord ++ tailWord_1828179) baseStart_1828179 baseEnd_1828179 := by
    simpa [prefixWord, tailWord_1828179, baseEnd_1828179] using wordTrace_append hprefix tailTrace_1828179
  have hstable : (prefixWord ++ tailWord_1828179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828179).length < 2 ^ (prefixWord ++ tailWord_1828179).sum := by decide
  have hdescent : baseEnd_1828179 < baseStart_1828179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828183 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 2, 3]
def baseStart_1828183 : Nat := 118140960795 + 1828183 * 2 ^ 59
def prefixEnd_1828183 : Nat := 4983230072969 + 3 ^ 40 * 1828183 * 2
def baseEnd_1828183 : Nat := 625824402252483972869897

theorem tailTrace_1828183 : CollatzResearch.WordTrace tailWord_1828183 prefixEnd_1828183 625824402252483972869897 := by
  unfold tailWord_1828183
  simp only [CollatzResearch.WordTrace]
  refine ⟨66679311935812694643705203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44452874623875129762470135 66679311935812694643705203)
  ·
    refine ⟨100018967903719041965557805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66679311935812694643705203 100018967903719041965557805)
    ·
      refine ⟨37507112963894640737084177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100018967903719041965557805 37507112963894640737084177)
      ·
        refine ⟨28130334722920980552813133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37507112963894640737084177 28130334722920980552813133)
        ·
          refine ⟨10548875521095367707304925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28130334722920980552813133 10548875521095367707304925)
          ·
            refine ⟨3955828320410762890239347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10548875521095367707304925 3955828320410762890239347)
            ·
              refine ⟨5933742480616144335359021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955828320410762890239347 5933742480616144335359021)
              ·
                refine ⟨2225153430231054125759633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5933742480616144335359021 2225153430231054125759633)
                ·
                  refine ⟨1668865072673290594319725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225153430231054125759633 1668865072673290594319725)
                  ·
                    refine ⟨625824402252483972869897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1668865072673290594319725 625824402252483972869897)
                    ·
                      rfl

theorem cell22_1828183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_1828183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828183 prefixEnd_1828183 := by exact prefixLift 1828183
  have htrace : WordTrace (prefixWord ++ tailWord_1828183) baseStart_1828183 baseEnd_1828183 := by
    simpa [prefixWord, tailWord_1828183, baseEnd_1828183] using wordTrace_append hprefix tailTrace_1828183
  have hstable : (prefixWord ++ tailWord_1828183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828183).length < 2 ^ (prefixWord ++ tailWord_1828183).sum := by decide
  have hdescent : baseEnd_1828183 < baseStart_1828183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828224 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_1828224 : Nat := 118140960795 + 1828224 * 2 ^ 59
def prefixEnd_1828224 : Nat := 4983230072969 + 3 ^ 40 * 1828224 * 2
def baseEnd_1828224 : Nat := 208612812463457844198257

theorem tailTrace_1828224 : CollatzResearch.WordTrace tailWord_1828224 prefixEnd_1828224 208612812463457844198257 := by
  unfold tailWord_1828224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33340403664332079322973863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44453871552442772430631817 33340403664332079322973863)
  ·
    refine ⟨50010605496498118984460795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33340403664332079322973863 50010605496498118984460795)
    ·
      refine ⟨75015908244747178476691193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50010605496498118984460795 75015908244747178476691193)
      ·
        refine ⟨56261931183560383857518395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75015908244747178476691193 56261931183560383857518395)
        ·
          refine ⟨84392896775340575786277593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56261931183560383857518395 84392896775340575786277593)
          ·
            refine ⟨63294672581505431839708195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84392896775340575786277593 63294672581505431839708195)
            ·
              refine ⟨94942008872258147759562293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63294672581505431839708195 94942008872258147759562293)
              ·
                refine ⟨8900813331774201352458965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94942008872258147759562293 8900813331774201352458965)
                ·
                  refine ⟨208612812463457844198257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8900813331774201352458965 208612812463457844198257)
                  ·
                    rfl

theorem cell22_1828224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_1828224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828224 prefixEnd_1828224 := by exact prefixLift 1828224
  have htrace : WordTrace (prefixWord ++ tailWord_1828224) baseStart_1828224 baseEnd_1828224 := by
    simpa [prefixWord, tailWord_1828224, baseEnd_1828224] using wordTrace_append hprefix tailTrace_1828224
  have hstable : (prefixWord ++ tailWord_1828224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828224).length < 2 ^ (prefixWord ++ tailWord_1828224).sum := by decide
  have hdescent : baseEnd_1828224 < baseStart_1828224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828382 : List Nat := [4, 3, 3, 1, 1, 10]
def baseStart_1828382 : Nat := 118140960795 + 1828382 * 2 ^ 59
def prefixEnd_1828382 : Nat := 4983230072969 + 3 ^ 40 * 1828382 * 2
def baseEnd_1828382 : Nat := 7727068197769306014127

theorem tailTrace_1828382 : CollatzResearch.WordTrace tailWord_1828382 prefixEnd_1828382 7727068197769306014127 := by
  unfold tailWord_1828382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335821257761468953774925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44457713374727834420132933 8335821257761468953774925)
  ·
    refine ⟨3125932971660550857665597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8335821257761468953774925 3125932971660550857665597)
    ·
      refine ⟨1172224864372706571624599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3125932971660550857665597 1172224864372706571624599)
      ·
        refine ⟨1758337296559059857436899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172224864372706571624599 1758337296559059857436899)
        ·
          refine ⟨2637505944838589786155349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758337296559059857436899 2637505944838589786155349)
          ·
            refine ⟨7727068197769306014127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2637505944838589786155349 7727068197769306014127)
            ·
              rfl

theorem cell22_1828382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 10].length) (baseStart_1828382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828382 prefixEnd_1828382 := by exact prefixLift 1828382
  have htrace : WordTrace (prefixWord ++ tailWord_1828382) baseStart_1828382 baseEnd_1828382 := by
    simpa [prefixWord, tailWord_1828382, baseEnd_1828382] using wordTrace_append hprefix tailTrace_1828382
  have hstable : (prefixWord ++ tailWord_1828382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828382).length < 2 ^ (prefixWord ++ tailWord_1828382).sum := by decide
  have hdescent : baseEnd_1828382 < baseStart_1828382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828408 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_1828408 : Nat := 118140960795 + 1828408 * 2 ^ 59
def prefixEnd_1828408 : Nat := 4983230072969 + 3 ^ 40 * 1828408 * 2
def baseEnd_1828408 : Nat := 625901424350658385994207

theorem tailTrace_1828408 : CollatzResearch.WordTrace tailWord_1828408 prefixEnd_1828408 625901424350658385994207 := by
  unfold tailWord_1828408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343759179998779035322939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44458345573331705380430585 33343759179998779035322939)
  ·
    refine ⟨50015638769998168552984409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33343759179998779035322939 50015638769998168552984409)
    ·
      refine ⟨37511729077498626414738307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50015638769998168552984409 37511729077498626414738307)
      ·
        refine ⟨56267593616247939622107461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37511729077498626414738307 56267593616247939622107461)
        ·
          refine ⟨10550173803046488679145149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56267593616247939622107461 10550173803046488679145149)
          ·
            refine ⟨3956315176142433254679431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10550173803046488679145149 3956315176142433254679431)
            ·
              refine ⟨5934472764213649882019147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956315176142433254679431 5934472764213649882019147)
              ·
                refine ⟨8901709146320474823028721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934472764213649882019147 8901709146320474823028721)
                ·
                  refine ⟨6676281859740356117271541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8901709146320474823028721 6676281859740356117271541)
                  ·
                    refine ⟨625901424350658385994207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6676281859740356117271541 625901424350658385994207)
                    ·
                      rfl

theorem cell22_1828408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_1828408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828408 prefixEnd_1828408 := by exact prefixLift 1828408
  have htrace : WordTrace (prefixWord ++ tailWord_1828408) baseStart_1828408 baseEnd_1828408 := by
    simpa [prefixWord, tailWord_1828408, baseEnd_1828408] using wordTrace_append hprefix tailTrace_1828408
  have hstable : (prefixWord ++ tailWord_1828408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828408).length < 2 ^ (prefixWord ++ tailWord_1828408).sum := by decide
  have hdescent : baseEnd_1828408 < baseStart_1828408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828455 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 4]
def baseStart_1828455 : Nat := 118140960795 + 1828455 * 2 ^ 59
def prefixEnd_1828455 : Nat := 4983230072969 + 3 ^ 40 * 1828455 * 2
def baseEnd_1828455 : Nat := 208639171137055310023021

theorem tailTrace_1828455 : CollatzResearch.WordTrace tailWord_1828455 prefixEnd_1828455 208639171137055310023021 := by
  unfold tailWord_1828455
  simp only [CollatzResearch.WordTrace]
  refine ⟨66689232590827285097606819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44459488393884856731737879 66689232590827285097606819)
  ·
    refine ⟨100033848886240927646410229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66689232590827285097606819 100033848886240927646410229)
    ·
      refine ⟨9378173333085086966850959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100033848886240927646410229 9378173333085086966850959)
      ·
        refine ⟨14067259999627630450276439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378173333085086966850959 14067259999627630450276439)
        ·
          refine ⟨21100889999441445675414659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14067259999627630450276439 21100889999441445675414659)
          ·
            refine ⟨31651334999162168513121989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21100889999441445675414659 31651334999162168513121989)
            ·
              refine ⟨5934625312342906596210373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31651334999162168513121989 5934625312342906596210373)
              ·
                refine ⟨1112742246064294986789445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5934625312342906596210373 1112742246064294986789445)
                ·
                  refine ⟨208639171137055310023021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1112742246064294986789445 208639171137055310023021)
                  ·
                    rfl

theorem cell22_1828455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 4].length) (baseStart_1828455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828455 prefixEnd_1828455 := by exact prefixLift 1828455
  have htrace : WordTrace (prefixWord ++ tailWord_1828455) baseStart_1828455 baseEnd_1828455 := by
    simpa [prefixWord, tailWord_1828455, baseEnd_1828455] using wordTrace_append hprefix tailTrace_1828455
  have hstable : (prefixWord ++ tailWord_1828455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828455).length < 2 ^ (prefixWord ++ tailWord_1828455).sum := by decide
  have hdescent : baseEnd_1828455 < baseStart_1828455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828562 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1828562 : Nat := 118140960795 + 1828562 * 2 ^ 59
def prefixEnd_1828562 : Nat := 4983230072969 + 3 ^ 40 * 1828562 * 2
def baseEnd_1828562 : Nat := 208651380565951105881245

theorem tailTrace_1828562 : CollatzResearch.WordTrace tailWord_1828562 prefixEnd_1828562 208651380565951105881245 := by
  unfold tailWord_1828562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673283800359910592937985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44462090134293094914501293 16673283800359910592937985)
  ·
    refine ⟨12504962850269932944703489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16673283800359910592937985 12504962850269932944703489)
    ·
      refine ⟨9378722137702449708527617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12504962850269932944703489 9378722137702449708527617)
      ·
        refine ⟨7034041603276837281395713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9378722137702449708527617 7034041603276837281395713)
        ·
          refine ⟨5275531202457627961046785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7034041603276837281395713 5275531202457627961046785)
          ·
            refine ⟨3956648401843220970785089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5275531202457627961046785 3956648401843220970785089)
            ·
              refine ⟨2967486301382415728088817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956648401843220970785089 2967486301382415728088817)
              ·
                refine ⟨2225614726036811796066613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967486301382415728088817 2225614726036811796066613)
                ·
                  refine ⟨208651380565951105881245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2225614726036811796066613 208651380565951105881245)
                  ·
                    rfl

theorem cell22_1828562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1828562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828562 prefixEnd_1828562 := by exact prefixLift 1828562
  have htrace : WordTrace (prefixWord ++ tailWord_1828562) baseStart_1828562 baseEnd_1828562 := by
    simpa [prefixWord, tailWord_1828562, baseEnd_1828562] using wordTrace_append hprefix tailTrace_1828562
  have hstable : (prefixWord ++ tailWord_1828562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828562).length < 2 ^ (prefixWord ++ tailWord_1828562).sum := by decide
  have hdescent : baseEnd_1828562 < baseStart_1828562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828590 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1828590 : Nat := 118140960795 + 1828590 * 2 ^ 59
def prefixEnd_1828590 : Nat := 4983230072969 + 3 ^ 40 * 1828590 * 2
def baseEnd_1828590 : Nat := 208654575556690192647883

theorem tailTrace_1828590 : CollatzResearch.WordTrace tailWord_1828590 prefixEnd_1828590 208654575556690192647883 := by
  unfold tailWord_1828590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8336769555667275394221403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44462770963558802102514149 8336769555667275394221403)
  ·
    refine ⟨12505154333500913091332105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8336769555667275394221403 12505154333500913091332105)
    ·
      refine ⟨9378865750125684818499079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12505154333500913091332105 9378865750125684818499079)
      ·
        refine ⟨14068298625188527227748619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378865750125684818499079 14068298625188527227748619)
        ·
          refine ⟨21102447937782790841622929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14068298625188527227748619 21102447937782790841622929)
          ·
            refine ⟨15826835953337093131217197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21102447937782790841622929 15826835953337093131217197)
            ·
              refine ⟨5935063482501409924206449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15826835953337093131217197 5935063482501409924206449)
              ·
                refine ⟨4451297611876057443154837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935063482501409924206449 4451297611876057443154837)
                ·
                  refine ⟨208654575556690192647883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4451297611876057443154837 208654575556690192647883)
                  ·
                    rfl

theorem cell22_1828590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1828590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828590 prefixEnd_1828590 := by exact prefixLift 1828590
  have htrace : WordTrace (prefixWord ++ tailWord_1828590) baseStart_1828590 baseEnd_1828590 := by
    simpa [prefixWord, tailWord_1828590, baseEnd_1828590] using wordTrace_append hprefix tailTrace_1828590
  have hstable : (prefixWord ++ tailWord_1828590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828590).length < 2 ^ (prefixWord ++ tailWord_1828590).sum := by decide
  have hdescent : baseEnd_1828590 < baseStart_1828590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828620 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_1828620 : Nat := 118140960795 + 1828620 * 2 ^ 59
def prefixEnd_1828620 : Nat := 4983230072969 + 3 ^ 40 * 1828620 * 2
def baseEnd_1828620 : Nat := 625973996283160499693557

theorem tailTrace_1828620 : CollatzResearch.WordTrace tailWord_1828620 prefixEnd_1828620 625973996283160499693557 := by
  unfold tailWord_1828620
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347625317614759138681657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44463500423486345518242209 33347625317614759138681657)
  ·
    refine ⟨25010718988211069354011243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33347625317614759138681657 25010718988211069354011243)
    ·
      refine ⟨37516078482316604031016865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25010718988211069354011243 37516078482316604031016865)
      ·
        refine ⟨28137058861737453023262649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37516078482316604031016865 28137058861737453023262649)
        ·
          refine ⟨21102794146303089767446987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28137058861737453023262649 21102794146303089767446987)
          ·
            refine ⟨31654191219454634651170481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21102794146303089767446987 31654191219454634651170481)
            ·
              refine ⟨23740643414590975988377861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31654191219454634651170481 23740643414590975988377861)
              ·
                refine ⟨4451370640235807997820849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23740643414590975988377861 4451370640235807997820849)
                ·
                  refine ⟨3338527980176855998365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451370640235807997820849 3338527980176855998365637)
                  ·
                    refine ⟨625973996283160499693557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3338527980176855998365637 625973996283160499693557)
                    ·
                      rfl

theorem cell22_1828620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_1828620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828620 prefixEnd_1828620 := by exact prefixLift 1828620
  have htrace : WordTrace (prefixWord ++ tailWord_1828620) baseStart_1828620 baseEnd_1828620 := by
    simpa [prefixWord, tailWord_1828620, baseEnd_1828620] using wordTrace_append hprefix tailTrace_1828620
  have hstable : (prefixWord ++ tailWord_1828620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828620).length < 2 ^ (prefixWord ++ tailWord_1828620).sum := by decide
  have hdescent : baseEnd_1828620 < baseStart_1828620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828639 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 2, 3]
def baseStart_1828639 : Nat := 118140960795 + 1828639 * 2 ^ 59
def prefixEnd_1828639 : Nat := 4983230072969 + 3 ^ 40 * 1828639 * 2
def baseEnd_1828639 : Nat := 625980500371450783468499

theorem tailTrace_1828639 : CollatzResearch.WordTrace tailWord_1828639 prefixEnd_1828639 625980500371450783468499 := by
  unfold tailWord_1828639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66695943622160684522304971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44463962414773789681536647 66695943622160684522304971)
  ·
    refine ⟨100043915433241026783457457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66695943622160684522304971 100043915433241026783457457)
    ·
      refine ⟨75032936574930770087593093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100043915433241026783457457 75032936574930770087593093)
      ·
        refine ⟨14068675607799519391423705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75032936574930770087593093 14068675607799519391423705)
        ·
          refine ⟨10551506705849639543567779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14068675607799519391423705 10551506705849639543567779)
          ·
            refine ⟨15827260058774459315351669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551506705849639543567779 15827260058774459315351669)
            ·
              refine ⟨1483805630510105560814219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15827260058774459315351669 1483805630510105560814219)
              ·
                refine ⟨2225708445765158341221329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483805630510105560814219 2225708445765158341221329)
                ·
                  refine ⟨1669281334323868755915997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2225708445765158341221329 1669281334323868755915997)
                  ·
                    refine ⟨625980500371450783468499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1669281334323868755915997 625980500371450783468499)
                    ·
                      rfl

theorem cell22_1828639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_1828639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828639 prefixEnd_1828639 := by exact prefixLift 1828639
  have htrace : WordTrace (prefixWord ++ tailWord_1828639) baseStart_1828639 baseEnd_1828639 := by
    simpa [prefixWord, tailWord_1828639, baseEnd_1828639] using wordTrace_append hprefix tailTrace_1828639
  have hstable : (prefixWord ++ tailWord_1828639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828639).length < 2 ^ (prefixWord ++ tailWord_1828639).sum := by decide
  have hdescent : baseEnd_1828639 < baseStart_1828639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828652 : List Nat := [2, 2, 1, 1, 1, 7, 2, 6]
def baseStart_1828652 : Nat := 118140960795 + 1828652 * 2 ^ 59
def prefixEnd_1828652 : Nat := 4983230072969 + 3 ^ 40 * 1828652 * 2
def baseEnd_1828652 : Nat := 69553883393013675877051

theorem tailTrace_1828652 : CollatzResearch.WordTrace tailWord_1828652 prefixEnd_1828652 69553883393013675877051 := by
  unfold tailWord_1828652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33348208885556793871264105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44464278514075725161685473 33348208885556793871264105)
  ·
    refine ⟨25011156664167595403448079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33348208885556793871264105 25011156664167595403448079)
    ·
      refine ⟨37516734996251393105172119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25011156664167595403448079 37516734996251393105172119)
      ·
        refine ⟨56275102494377089657758179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37516734996251393105172119 56275102494377089657758179)
        ·
          refine ⟨84412653741565634486637269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56275102494377089657758179 84412653741565634486637269)
          ·
            refine ⟨1978421572067944558280561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84412653741565634486637269 1978421572067944558280561)
            ·
              refine ⟨1483816179050958418710421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978421572067944558280561 1483816179050958418710421)
              ·
                refine ⟨69553883393013675877051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1483816179050958418710421 69553883393013675877051)
                ·
                  rfl

theorem cell22_1828652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_1828652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828652 prefixEnd_1828652 := by exact prefixLift 1828652
  have htrace : WordTrace (prefixWord ++ tailWord_1828652) baseStart_1828652 baseEnd_1828652 := by
    simpa [prefixWord, tailWord_1828652, baseEnd_1828652] using wordTrace_append hprefix tailTrace_1828652
  have hstable : (prefixWord ++ tailWord_1828652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828652).length < 2 ^ (prefixWord ++ tailWord_1828652).sum := by decide
  have hdescent : baseEnd_1828652 < baseStart_1828652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828680 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_1828680 : Nat := 118140960795 + 1828680 * 2 ^ 59
def prefixEnd_1828680 : Nat := 4983230072969 + 3 ^ 40 * 1828680 * 2
def baseEnd_1828680 : Nat := 208664845169780114397791

theorem tailTrace_1828680 : CollatzResearch.WordTrace tailWord_1828680 prefixEnd_1828680 208664845169780114397791 := by
  unfold tailWord_1828680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33348719507506074262273747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44464959343341432349698329 33348719507506074262273747)
  ·
    refine ⟨50023079261259111393410621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33348719507506074262273747 50023079261259111393410621)
    ·
      refine ⟨18758654722972166772528983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50023079261259111393410621 18758654722972166772528983)
      ·
        refine ⟨28137982084458250158793475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18758654722972166772528983 28137982084458250158793475)
        ·
          refine ⟨42206973126687375238190213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28137982084458250158793475 42206973126687375238190213)
          ·
            refine ⟨7913807461253882857160665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42206973126687375238190213 7913807461253882857160665)
            ·
              refine ⟨5935355595940412142870499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913807461253882857160665 5935355595940412142870499)
              ·
                refine ⟨8903033393910618214305749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935355595940412142870499 8903033393910618214305749)
                ·
                  refine ⟨208664845169780114397791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8903033393910618214305749 208664845169780114397791)
                  ·
                    rfl

theorem cell22_1828680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_1828680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828680 prefixEnd_1828680 := by exact prefixLift 1828680
  have htrace : WordTrace (prefixWord ++ tailWord_1828680) baseStart_1828680 baseEnd_1828680 := by
    simpa [prefixWord, tailWord_1828680, baseEnd_1828680] using wordTrace_append hprefix tailTrace_1828680
  have hstable : (prefixWord ++ tailWord_1828680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828680).length < 2 ^ (prefixWord ++ tailWord_1828680).sum := by decide
  have hdescent : baseEnd_1828680 < baseStart_1828680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828757 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1828757 : Nat := 118140960795 + 1828757 * 2 ^ 59
def prefixEnd_1828757 : Nat := 4983230072969 + 3 ^ 40 * 1828757 * 2
def baseEnd_1828757 : Nat := 626020894182937809018137

theorem tailTrace_1828757 : CollatzResearch.WordTrace tailWord_1828757 prefixEnd_1828757 626020894182937809018137 := by
  unfold tailWord_1828757
  simp only [CollatzResearch.WordTrace]
  refine ⟨66700247435733190675100525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44466831623822127116733683 66700247435733190675100525)
  ·
    refine ⟨25012592788399946503162697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66700247435733190675100525 25012592788399946503162697)
    ·
      refine ⟨18759444591299959877372023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25012592788399946503162697 18759444591299959877372023)
      ·
        refine ⟨28139166886949939816058035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18759444591299959877372023 28139166886949939816058035)
        ·
          refine ⟨42208750330424909724087053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28139166886949939816058035 42208750330424909724087053)
          ·
            refine ⟨15828281373909341146532645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42208750330424909724087053 15828281373909341146532645)
            ·
              refine ⟨2967802757608001464974871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15828281373909341146532645 2967802757608001464974871)
              ·
                refine ⟨4451704136412002197462307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967802757608001464974871 4451704136412002197462307)
                ·
                  refine ⟨6677556204618003296193461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451704136412002197462307 6677556204618003296193461)
                  ·
                    refine ⟨626020894182937809018137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6677556204618003296193461 626020894182937809018137)
                    ·
                      rfl

theorem cell22_1828757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1828757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828757 prefixEnd_1828757 := by exact prefixLift 1828757
  have htrace : WordTrace (prefixWord ++ tailWord_1828757) baseStart_1828757 baseEnd_1828757 := by
    simpa [prefixWord, tailWord_1828757, baseEnd_1828757] using wordTrace_append hprefix tailTrace_1828757
  have hstable : (prefixWord ++ tailWord_1828757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828757).length < 2 ^ (prefixWord ++ tailWord_1828757).sum := by decide
  have hdescent : baseEnd_1828757 < baseStart_1828757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828772 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1828772 : Nat := 118140960795 + 1828772 * 2 ^ 59
def prefixEnd_1828772 : Nat := 4983230072969 + 3 ^ 40 * 1828772 * 2
def baseEnd_1828772 : Nat := 626026028989482769893091

theorem tailTrace_1828772 : CollatzResearch.WordTrace tailWord_1828772 prefixEnd_1828772 626026028989482769893091 := by
  unfold tailWord_1828772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33350397265339424118448285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44467196353785898824597713 33350397265339424118448285)
  ·
    refine ⟨12506398974502284044418107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33350397265339424118448285 12506398974502284044418107)
    ·
      refine ⟨18759598461753426066627161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506398974502284044418107 18759598461753426066627161)
      ·
        refine ⟨14069698846315069549970371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18759598461753426066627161 14069698846315069549970371)
        ·
          refine ⟨21104548269472604324955557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14069698846315069549970371 21104548269472604324955557)
          ·
            refine ⟨3957102800526113310929167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21104548269472604324955557 3957102800526113310929167)
            ·
              refine ⟨5935654200789169966393751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957102800526113310929167 5935654200789169966393751)
              ·
                refine ⟨8903481301183754949590627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935654200789169966393751 8903481301183754949590627)
                ·
                  refine ⟨13355221951775632424385941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8903481301183754949590627 13355221951775632424385941)
                  ·
                    refine ⟨626026028989482769893091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13355221951775632424385941 626026028989482769893091)
                    ·
                      rfl

theorem cell22_1828772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1828772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828772 prefixEnd_1828772 := by exact prefixLift 1828772
  have htrace : WordTrace (prefixWord ++ tailWord_1828772) baseStart_1828772 baseEnd_1828772 := by
    simpa [prefixWord, tailWord_1828772, baseEnd_1828772] using wordTrace_append hprefix tailTrace_1828772
  have hstable : (prefixWord ++ tailWord_1828772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828772).length < 2 ^ (prefixWord ++ tailWord_1828772).sum := by decide
  have hdescent : baseEnd_1828772 < baseStart_1828772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828904 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1828904 : Nat := 118140960795 + 1828904 * 2 ^ 59
def prefixEnd_1828904 : Nat := 4983230072969 + 3 ^ 40 * 1828904 * 2
def baseEnd_1828904 : Nat := 626071215287078425592687

theorem tailTrace_1828904 : CollatzResearch.WordTrace tailWord_1828904 prefixEnd_1828904 626071215287078425592687 := by
  unfold tailWord_1828904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33352804483100317390350883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44470405977467089853801177 33352804483100317390350883)
  ·
    refine ⟨50029206724650476085526325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33352804483100317390350883 50029206724650476085526325)
    ·
      refine ⟨4690238130435982133018093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50029206724650476085526325 4690238130435982133018093)
      ·
        refine ⟨1758839298913493299881785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4690238130435982133018093 1758839298913493299881785)
        ·
          refine ⟨1319129474185119974911339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1758839298913493299881785 1319129474185119974911339)
          ·
            refine ⟨1978694211277679962367009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319129474185119974911339 1978694211277679962367009)
            ·
              refine ⟨1484020658458259971775257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978694211277679962367009 1484020658458259971775257)
              ·
                refine ⟨1113015493843694978831443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484020658458259971775257 1113015493843694978831443)
                ·
                  refine ⟨1669523240765542468247165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113015493843694978831443 1669523240765542468247165)
                  ·
                    refine ⟨626071215287078425592687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1669523240765542468247165 626071215287078425592687)
                    ·
                      rfl

theorem cell22_1828904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1828904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828904 prefixEnd_1828904 := by exact prefixLift 1828904
  have htrace : WordTrace (prefixWord ++ tailWord_1828904) baseStart_1828904 baseEnd_1828904 := by
    simpa [prefixWord, tailWord_1828904, baseEnd_1828904] using wordTrace_append hprefix tailTrace_1828904
  have hstable : (prefixWord ++ tailWord_1828904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828904).length < 2 ^ (prefixWord ++ tailWord_1828904).sum := by decide
  have hdescent : baseEnd_1828904 < baseStart_1828904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828907 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_1828907 : Nat := 118140960795 + 1828907 * 2 ^ 59
def prefixEnd_1828907 : Nat := 4983230072969 + 3 ^ 40 * 1828907 * 2
def baseEnd_1828907 : Nat := 626072242248387417767677

theorem tailTrace_1828907 : CollatzResearch.WordTrace tailWord_1828907 prefixEnd_1828907 626072242248387417767677 := by
  unfold tailWord_1828907
  simp only [CollatzResearch.WordTrace]
  refine ⟨66705718385189766293060975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44470478923459844195373983 66705718385189766293060975)
  ·
    refine ⟨100058577577784649439591463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66705718385189766293060975 100058577577784649439591463)
    ·
      refine ⟨150087866366676974159387195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100058577577784649439591463 150087866366676974159387195)
      ·
        refine ⟨225131799550015461239080793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150087866366676974159387195 225131799550015461239080793)
        ·
          refine ⟨168848849662511595929310595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225131799550015461239080793 168848849662511595929310595)
          ·
            refine ⟨253273274493767393893965893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168848849662511595929310595 253273274493767393893965893)
            ·
              refine ⟨47488738967581386355118605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253273274493767393893965893 47488738967581386355118605)
              ·
                refine ⟨17808277112843019883169477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47488738967581386355118605 17808277112843019883169477)
                ·
                  refine ⟨3339051958658066228094277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17808277112843019883169477 3339051958658066228094277)
                  ·
                    refine ⟨626072242248387417767677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339051958658066228094277 626072242248387417767677)
                    ·
                      rfl

theorem cell22_1828907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_1828907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828907 prefixEnd_1828907 := by exact prefixLift 1828907
  have htrace : WordTrace (prefixWord ++ tailWord_1828907) baseStart_1828907 baseEnd_1828907 := by
    simpa [prefixWord, tailWord_1828907, baseEnd_1828907] using wordTrace_append hprefix tailTrace_1828907
  have hstable : (prefixWord ++ tailWord_1828907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828907).length < 2 ^ (prefixWord ++ tailWord_1828907).sum := by decide
  have hdescent : baseEnd_1828907 < baseStart_1828907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828954 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1828954 : Nat := 118140960795 + 1828954 * 2 ^ 59
def prefixEnd_1828954 : Nat := 4983230072969 + 3 ^ 40 * 1828954 * 2
def baseEnd_1828954 : Nat := 626088331308894961842533

theorem tailTrace_1828954 : CollatzResearch.WordTrace tailWord_1828954 prefixEnd_1828954 626088331308894961842533 := by
  unfold tailWord_1828954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676858154004873330005479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44471621744012995546681277 16676858154004873330005479)
  ·
    refine ⟨25015287231007309995008219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676858154004873330005479 25015287231007309995008219)
    ·
      refine ⟨37522930846510964992512329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25015287231007309995008219 37522930846510964992512329)
      ·
        refine ⟨28142198134883223744384247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37522930846510964992512329 28142198134883223744384247)
        ·
          refine ⟨42213297202324835616576371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28142198134883223744384247 42213297202324835616576371)
          ·
            refine ⟨63319945803487253424864557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42213297202324835616576371 63319945803487253424864557)
            ·
              refine ⟨23744979676307720034324209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63319945803487253424864557 23744979676307720034324209)
              ·
                refine ⟨17808734757230790025743157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23744979676307720034324209 17808734757230790025743157)
                ·
                  refine ⟨1669568883490386564913421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17808734757230790025743157 1669568883490386564913421)
                  ·
                    refine ⟨626088331308894961842533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1669568883490386564913421 626088331308894961842533)
                    ·
                      rfl

theorem cell22_1828954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1828954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1828954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1828954 prefixEnd_1828954 := by exact prefixLift 1828954
  have htrace : WordTrace (prefixWord ++ tailWord_1828954) baseStart_1828954 baseEnd_1828954 := by
    simpa [prefixWord, tailWord_1828954, baseEnd_1828954] using wordTrace_append hprefix tailTrace_1828954
  have hstable : (prefixWord ++ tailWord_1828954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828954).length < 2 ^ (prefixWord ++ tailWord_1828954).sum := by decide
  have hdescent : baseEnd_1828954 < baseStart_1828954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829022 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1829022 : Nat := 118140960795 + 1829022 * 2 ^ 59
def prefixEnd_1829022 : Nat := 4983230072969 + 3 ^ 40 * 1829022 * 2
def baseEnd_1829022 : Nat := 626111609098565451142325

theorem tailTrace_1829022 : CollatzResearch.WordTrace tailWord_1829022 prefixEnd_1829022 626111609098565451142325 := by
  unfold tailWord_1829022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338739097471642616687165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44473275186515427288998213 8338739097471642616687165)
  ·
    refine ⟨3127027161551865981257687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8338739097471642616687165 3127027161551865981257687)
    ·
      refine ⟨4690540742327798971886531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3127027161551865981257687 4690540742327798971886531)
      ·
        refine ⟨7035811113491698457829797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690540742327798971886531 7035811113491698457829797)
        ·
          refine ⟨1319214583779693460843087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7035811113491698457829797 1319214583779693460843087)
          ·
            refine ⟨1978821875669540191264631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319214583779693460843087 1978821875669540191264631)
            ·
              refine ⟨2968232813504310286896947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978821875669540191264631 2968232813504310286896947)
              ·
                refine ⟨4452349220256465430345421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968232813504310286896947 4452349220256465430345421)
                ·
                  refine ⟨1669630957596174536379533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4452349220256465430345421 1669630957596174536379533)
                  ·
                    refine ⟨626111609098565451142325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1669630957596174536379533 626111609098565451142325)
                    ·
                      rfl

theorem cell22_1829022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1829022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829022 prefixEnd_1829022 := by exact prefixLift 1829022
  have htrace : WordTrace (prefixWord ++ tailWord_1829022) baseStart_1829022 baseEnd_1829022 := by
    simpa [prefixWord, tailWord_1829022, baseEnd_1829022] using wordTrace_append hprefix tailTrace_1829022
  have hstable : (prefixWord ++ tailWord_1829022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829022).length < 2 ^ (prefixWord ++ tailWord_1829022).sum := by decide
  have hdescent : baseEnd_1829022 < baseStart_1829022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829074 : List Nat := [3, 2, 2, 2, 1, 12]
def baseStart_1829074 : Nat := 118140960795 + 1829074 * 2 ^ 59
def prefixEnd_1829074 : Nat := 4983230072969 + 3 ^ 40 * 1829074 * 2
def baseEnd_1829074 : Nat := 7729992713101909244965

theorem tailTrace_1829074 : CollatzResearch.WordTrace tailWord_1829074 prefixEnd_1829074 7729992713101909244965 := by
  unfold tailWord_1829074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677952343896188453597569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44474539583723169209593517 16677952343896188453597569)
  ·
    refine ⟨12508464257922141340198177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16677952343896188453597569 12508464257922141340198177)
    ·
      refine ⟨9381348193441606005148633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12508464257922141340198177 9381348193441606005148633)
      ·
        refine ⟨7036011145081204503861475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9381348193441606005148633 7036011145081204503861475)
        ·
          refine ⟨10554016717621806755792213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036011145081204503861475 10554016717621806755792213)
          ·
            refine ⟨7729992713101909244965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10554016717621806755792213 7729992713101909244965)
            ·
              rfl

theorem cell22_1829074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 12].length) (baseStart_1829074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829074 prefixEnd_1829074 := by exact prefixLift 1829074
  have htrace : WordTrace (prefixWord ++ tailWord_1829074) baseStart_1829074 baseEnd_1829074 := by
    simpa [prefixWord, tailWord_1829074, baseEnd_1829074] using wordTrace_append hprefix tailTrace_1829074
  have hstable : (prefixWord ++ tailWord_1829074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829074).length < 2 ^ (prefixWord ++ tailWord_1829074).sum := by decide
  have hdescent : baseEnd_1829074 < baseStart_1829074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829080 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_1829080 : Nat := 118140960795 + 1829080 * 2 ^ 59
def prefixEnd_1829080 : Nat := 4983230072969 + 3 ^ 40 * 1829080 * 2
def baseEnd_1829080 : Nat := 208710487894624211064049

theorem tailTrace_1829080 : CollatzResearch.WordTrace tailWord_1829080 prefixEnd_1829080 208710487894624211064049 := by
  unfold tailWord_1829080
  simp only [CollatzResearch.WordTrace]
  refine ⟨33356014106781508419554347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44474685475708677892739129 33356014106781508419554347)
  ·
    refine ⟨50034021160172262629331521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33356014106781508419554347 50034021160172262629331521)
    ·
      refine ⟨37525515870129196971998641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50034021160172262629331521 37525515870129196971998641)
      ·
        refine ⟨28144136902596897728998981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37525515870129196971998641 28144136902596897728998981)
        ·
          refine ⟨5277025669236918324187309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28144136902596897728998981 5277025669236918324187309)
          ·
            refine ⟨1978884625963844371570241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5277025669236918324187309 1978884625963844371570241)
            ·
              refine ⟨1484163469472883278677681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978884625963844371570241 1484163469472883278677681)
              ·
                refine ⟨1113122602104662459008261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484163469472883278677681 1113122602104662459008261)
                ·
                  refine ⟨208710487894624211064049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113122602104662459008261 208710487894624211064049)
                  ·
                    rfl

theorem cell22_1829080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_1829080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829080 prefixEnd_1829080 := by exact prefixLift 1829080
  have htrace : WordTrace (prefixWord ++ tailWord_1829080) baseStart_1829080 baseEnd_1829080 := by
    simpa [prefixWord, tailWord_1829080, baseEnd_1829080] using wordTrace_append hprefix tailTrace_1829080
  have hstable : (prefixWord ++ tailWord_1829080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829080).length < 2 ^ (prefixWord ++ tailWord_1829080).sum := by decide
  have hdescent : baseEnd_1829080 < baseStart_1829080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829119 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 7]
def baseStart_1829119 : Nat := 118140960795 + 1829119 * 2 ^ 59
def prefixEnd_1829119 : Nat := 4983230072969 + 3 ^ 40 * 1829119 * 2
def baseEnd_1829119 : Nat := 208714938060296510489009

theorem tailTrace_1829119 : CollatzResearch.WordTrace tailWord_1829119 prefixEnd_1829119 208714938060296510489009 := by
  unfold tailWord_1829119
  simp only [CollatzResearch.WordTrace]
  refine ⟨66713450660421726499778411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44475633773614484333185607 66713450660421726499778411)
  ·
    refine ⟨100070175990632589749667617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66713450660421726499778411 100070175990632589749667617)
    ·
      refine ⟨75052631992974442312250713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100070175990632589749667617 75052631992974442312250713)
      ·
        refine ⟨56289473994730831734188035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75052631992974442312250713 56289473994730831734188035)
        ·
          refine ⟨84434210992096247601282053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56289473994730831734188035 84434210992096247601282053)
          ·
            refine ⟨15831414561018046425240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84434210992096247601282053 15831414561018046425240385)
            ·
              refine ⟨11873560920763534818930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15831414561018046425240385 11873560920763534818930289)
              ·
                refine ⟨8905170690572651114197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11873560920763534818930289 8905170690572651114197717)
                ·
                  refine ⟨208714938060296510489009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8905170690572651114197717 208714938060296510489009)
                  ·
                    rfl

theorem cell22_1829119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_1829119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829119 prefixEnd_1829119 := by exact prefixLift 1829119
  have htrace : WordTrace (prefixWord ++ tailWord_1829119) baseStart_1829119 baseEnd_1829119 := by
    simpa [prefixWord, tailWord_1829119, baseEnd_1829119] using wordTrace_append hprefix tailTrace_1829119
  have hstable : (prefixWord ++ tailWord_1829119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829119).length < 2 ^ (prefixWord ++ tailWord_1829119).sum := by decide
  have hdescent : baseEnd_1829119 < baseStart_1829119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829151 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_1829151 : Nat := 118140960795 + 1829151 * 2 ^ 59
def prefixEnd_1829151 : Nat := 4983230072969 + 3 ^ 40 * 1829151 * 2
def baseEnd_1829151 : Nat := 626155768434852114666929

theorem tailTrace_1829151 : CollatzResearch.WordTrace tailWord_1829151 prefixEnd_1829151 626155768434852114666929 := by
  unfold tailWord_1829151
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714617796305795964943307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44476411864203863976628871 66714617796305795964943307)
  ·
    refine ⟨100071926694458693947414961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714617796305795964943307 100071926694458693947414961)
    ·
      refine ⟨75053945020844020460561221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100071926694458693947414961 75053945020844020460561221)
      ·
        refine ⟨14072614691408253836355229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75053945020844020460561221 14072614691408253836355229)
        ·
          refine ⟨5277230509278095188633211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14072614691408253836355229 5277230509278095188633211)
          ·
            refine ⟨7915845763917142782949817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277230509278095188633211 7915845763917142782949817)
            ·
              refine ⟨5936884322937857087212363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7915845763917142782949817 5936884322937857087212363)
              ·
                refine ⟨8905326484406785630818545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936884322937857087212363 8905326484406785630818545)
                ·
                  refine ⟨6678994863305089223113909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8905326484406785630818545 6678994863305089223113909)
                  ·
                    refine ⟨626155768434852114666929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6678994863305089223113909 626155768434852114666929)
                    ·
                      rfl

theorem cell22_1829151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_1829151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829151 prefixEnd_1829151 := by exact prefixLift 1829151
  have htrace : WordTrace (prefixWord ++ tailWord_1829151) baseStart_1829151 baseEnd_1829151 := by
    simpa [prefixWord, tailWord_1829151, baseEnd_1829151] using wordTrace_append hprefix tailTrace_1829151
  have hstable : (prefixWord ++ tailWord_1829151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829151).length < 2 ^ (prefixWord ++ tailWord_1829151).sum := by decide
  have hdescent : baseEnd_1829151 < baseStart_1829151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829159 : List Nat := [1, 1, 8, 1, 2, 1, 2, 6]
def baseStart_1829159 : Nat := 118140960795 + 1829159 * 2 ^ 59
def prefixEnd_1829159 : Nat := 4983230072969 + 3 ^ 40 * 1829159 * 2
def baseEnd_1829159 : Nat := 69573167444260306718545

theorem tailTrace_1829159 : CollatzResearch.WordTrace tailWord_1829159 prefixEnd_1829159 69573167444260306718545 := by
  unfold tailWord_1829159
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714909580276813331234531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44476606386851208887489687 66714909580276813331234531)
  ·
    refine ⟨100072364370415219996851797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714909580276813331234531 100072364370415219996851797)
    ·
      refine ⟨1172723019965803359338107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 100072364370415219996851797 1172723019965803359338107)
      ·
        refine ⟨1759084529948705039007161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172723019965803359338107 1759084529948705039007161)
        ·
          refine ⟨1319313397461528779255371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1759084529948705039007161 1319313397461528779255371)
          ·
            refine ⟨1978970096192293168883057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319313397461528779255371 1978970096192293168883057)
            ·
              refine ⟨1484227572144219876662293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978970096192293168883057 1484227572144219876662293)
              ·
                refine ⟨69573167444260306718545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1484227572144219876662293 69573167444260306718545)
                ·
                  rfl

theorem cell22_1829159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 6].length) (baseStart_1829159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829159 prefixEnd_1829159 := by exact prefixLift 1829159
  have htrace : WordTrace (prefixWord ++ tailWord_1829159) baseStart_1829159 baseEnd_1829159 := by
    simpa [prefixWord, tailWord_1829159, baseEnd_1829159] using wordTrace_append hprefix tailTrace_1829159
  have hstable : (prefixWord ++ tailWord_1829159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829159).length < 2 ^ (prefixWord ++ tailWord_1829159).sum := by decide
  have hdescent : baseEnd_1829159 < baseStart_1829159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829256 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_1829256 : Nat := 118140960795 + 1829256 * 2 ^ 59
def prefixEnd_1829256 : Nat := 4983230072969 + 3 ^ 40 * 1829256 * 2
def baseEnd_1829256 : Nat := 626191712080666840791607

theorem tailTrace_1829256 : CollatzResearch.WordTrace tailWord_1829256 prefixEnd_1829256 626191712080666840791607 := by
  unfold tailWord_1829256
  simp only [CollatzResearch.WordTrace]
  refine ⟨33359223730462699448757811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44478964973950265931677081 33359223730462699448757811)
  ·
    refine ⟨50038835595694049173136717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33359223730462699448757811 50038835595694049173136717)
    ·
      refine ⟨18764563348385268439926269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50038835595694049173136717 18764563348385268439926269)
      ·
        refine ⟨7036711255644475664972351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18764563348385268439926269 7036711255644475664972351)
        ·
          refine ⟨10555066883466713497458527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036711255644475664972351 10555066883466713497458527)
          ·
            refine ⟨15832600325200070246187791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555066883466713497458527 15832600325200070246187791)
            ·
              refine ⟨23748900487800105369281687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15832600325200070246187791 23748900487800105369281687)
              ·
                refine ⟨35623350731700158053922531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23748900487800105369281687 35623350731700158053922531)
                ·
                  refine ⟨53435026097550237080883797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35623350731700158053922531 53435026097550237080883797)
                  ·
                    refine ⟨626191712080666840791607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53435026097550237080883797 626191712080666840791607)
                    ·
                      rfl

theorem cell22_1829256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_1829256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829256 prefixEnd_1829256 := by exact prefixLift 1829256
  have htrace : WordTrace (prefixWord ++ tailWord_1829256) baseStart_1829256 baseEnd_1829256 := by
    simpa [prefixWord, tailWord_1829256, baseEnd_1829256] using wordTrace_append hprefix tailTrace_1829256
  have hstable : (prefixWord ++ tailWord_1829256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829256).length < 2 ^ (prefixWord ++ tailWord_1829256).sum := by decide
  have hdescent : baseEnd_1829256 < baseStart_1829256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829305 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 5]
def baseStart_1829305 : Nat := 118140960795 + 1829305 * 2 ^ 59
def prefixEnd_1829305 : Nat := 4983230072969 + 3 ^ 40 * 1829305 * 2
def baseEnd_1829305 : Nat := 208736161927349015438819

theorem tailTrace_1829305 : CollatzResearch.WordTrace tailWord_1829305 prefixEnd_1829305 208736161927349015438819 := by
  unfold tailWord_1829305
  simp only [CollatzResearch.WordTrace]
  refine ⟨66720234637747880266049369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44480156425165253510699579 66720234637747880266049369)
  ·
    refine ⟨50040175978310910199537027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66720234637747880266049369 50040175978310910199537027)
    ·
      refine ⟨75060263967466365299305541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50040175978310910199537027 75060263967466365299305541)
      ·
        refine ⟨14073799493899943493619789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75060263967466365299305541 14073799493899943493619789)
        ·
          refine ⟨5277674810212478810107421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14073799493899943493619789 5277674810212478810107421)
          ·
            refine ⟨1979128053829679553790283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5277674810212478810107421 1979128053829679553790283)
            ·
              refine ⟨2968692080744519330685425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979128053829679553790283 2968692080744519330685425)
              ·
                refine ⟨2226519060558389498014069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968692080744519330685425 2226519060558389498014069)
                ·
                  refine ⟨208736161927349015438819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226519060558389498014069 208736161927349015438819)
                  ·
                    rfl

theorem cell22_1829305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_1829305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829305 prefixEnd_1829305 := by exact prefixLift 1829305
  have htrace : WordTrace (prefixWord ++ tailWord_1829305) baseStart_1829305 baseEnd_1829305 := by
    simpa [prefixWord, tailWord_1829305, baseEnd_1829305] using wordTrace_append hprefix tailTrace_1829305
  have hstable : (prefixWord ++ tailWord_1829305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829305).length < 2 ^ (prefixWord ++ tailWord_1829305).sum := by decide
  have hdescent : baseEnd_1829305 < baseStart_1829305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829333 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 6]
def baseStart_1829333 : Nat := 118140960795 + 1829333 * 2 ^ 59
def prefixEnd_1829333 : Nat := 4983230072969 + 3 ^ 40 * 1829333 * 2
def baseEnd_1829333 : Nat := 208739356918088102205457

theorem tailTrace_1829333 : CollatzResearch.WordTrace tailWord_1829333 prefixEnd_1829333 208739356918088102205457 := by
  unfold tailWord_1829333
  simp only [CollatzResearch.WordTrace]
  refine ⟨66721255881646441048068653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44480837254430960698712435 66721255881646441048068653)
  ·
    refine ⟨25020470955617415393025745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66721255881646441048068653 25020470955617415393025745)
    ·
      refine ⟨18765353216713061544769309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25020470955617415393025745 18765353216713061544769309)
      ·
        refine ⟨7037007456267398079288491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18765353216713061544769309 7037007456267398079288491)
        ·
          refine ⟨10555511184401097118932737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037007456267398079288491 10555511184401097118932737)
          ·
            refine ⟨7916633388300822839199553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10555511184401097118932737 7916633388300822839199553)
            ·
              refine ⟨5937475041225617129399665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7916633388300822839199553 5937475041225617129399665)
              ·
                refine ⟨4453106280919212847049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937475041225617129399665 4453106280919212847049749)
                ·
                  refine ⟨208739356918088102205457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4453106280919212847049749 208739356918088102205457)
                  ·
                    rfl

theorem cell22_1829333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_1829333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829333 prefixEnd_1829333 := by exact prefixLift 1829333
  have htrace : WordTrace (prefixWord ++ tailWord_1829333) baseStart_1829333 baseEnd_1829333 := by
    simpa [prefixWord, tailWord_1829333, baseEnd_1829333] using wordTrace_append hprefix tailTrace_1829333
  have hstable : (prefixWord ++ tailWord_1829333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829333).length < 2 ^ (prefixWord ++ tailWord_1829333).sum := by decide
  have hdescent : baseEnd_1829333 < baseStart_1829333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829363 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_1829363 : Nat := 118140960795 + 1829363 * 2 ^ 59
def prefixEnd_1829363 : Nat := 4983230072969 + 3 ^ 40 * 1829363 * 2
def baseEnd_1829363 : Nat := 626228340367354228366279

theorem tailTrace_1829363 : CollatzResearch.WordTrace tailWord_1829363 prefixEnd_1829363 626228340367354228366279 := by
  unfold tailWord_1829363
  simp only [CollatzResearch.WordTrace]
  refine ⟨66722350071537756171660743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44481566714358504114440495 66722350071537756171660743)
  ·
    refine ⟨100083525107306634257491115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66722350071537756171660743 100083525107306634257491115)
    ·
      refine ⟨150125287660959951386236673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100083525107306634257491115 150125287660959951386236673)
      ·
        refine ⟨112593965745719963539677505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150125287660959951386236673 112593965745719963539677505)
        ·
          refine ⟨84445474309289972654758129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112593965745719963539677505 84445474309289972654758129)
          ·
            refine ⟨63334105731967479491068597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84445474309289972654758129 63334105731967479491068597)
            ·
              refine ⟨5937572412371951202287681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63334105731967479491068597 5937572412371951202287681)
              ·
                refine ⟨4453179309278963401715761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937572412371951202287681 4453179309278963401715761)
                ·
                  refine ⟨3339884481959222551286821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453179309278963401715761 3339884481959222551286821)
                  ·
                    refine ⟨626228340367354228366279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339884481959222551286821 626228340367354228366279)
                    ·
                      rfl

theorem cell22_1829363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_1829363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829363 prefixEnd_1829363 := by exact prefixLift 1829363
  have htrace : WordTrace (prefixWord ++ tailWord_1829363) baseStart_1829363 baseEnd_1829363 := by
    simpa [prefixWord, tailWord_1829363, baseEnd_1829363] using wordTrace_append hprefix tailTrace_1829363
  have hstable : (prefixWord ++ tailWord_1829363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829363).length < 2 ^ (prefixWord ++ tailWord_1829363).sum := by decide
  have hdescent : baseEnd_1829363 < baseStart_1829363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829427 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 1, 3]
def baseStart_1829427 : Nat := 118140960795 + 1829427 * 2 ^ 59
def prefixEnd_1829427 : Nat := 4983230072969 + 3 ^ 40 * 1829427 * 2
def baseEnd_1829427 : Nat := 626250248875279394766083

theorem tailTrace_1829427 : CollatzResearch.WordTrace tailWord_1829427 prefixEnd_1829427 626250248875279394766083 := by
  unfold tailWord_1829427
  simp only [CollatzResearch.WordTrace]
  refine ⟨66724684343305895101990535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44483122895537263401327023 66724684343305895101990535)
  ·
    refine ⟨100087026514958842652985803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66724684343305895101990535 100087026514958842652985803)
    ·
      refine ⟨150130539772438263979478705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100087026514958842652985803 150130539772438263979478705)
      ·
        refine ⟨112597904829328697984609029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150130539772438263979478705 112597904829328697984609029)
        ·
          refine ⟨21112107155499130872114193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112597904829328697984609029 21112107155499130872114193)
          ·
            refine ⟨15834080366624348154085645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21112107155499130872114193 15834080366624348154085645)
            ·
              refine ⟨5937780137484130557782117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15834080366624348154085645 5937780137484130557782117)
              ·
                refine ⟨1113333775778274479584147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5937780137484130557782117 1113333775778274479584147)
                ·
                  refine ⟨1670000663667411719376221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113333775778274479584147 1670000663667411719376221)
                  ·
                    refine ⟨626250248875279394766083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670000663667411719376221 626250248875279394766083)
                    ·
                      rfl

theorem cell22_1829427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 3].length) (baseStart_1829427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829427 prefixEnd_1829427 := by exact prefixLift 1829427
  have htrace : WordTrace (prefixWord ++ tailWord_1829427) baseStart_1829427 baseEnd_1829427 := by
    simpa [prefixWord, tailWord_1829427, baseEnd_1829427] using wordTrace_append hprefix tailTrace_1829427
  have hstable : (prefixWord ++ tailWord_1829427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829427).length < 2 ^ (prefixWord ++ tailWord_1829427).sum := by decide
  have hdescent : baseEnd_1829427 < baseStart_1829427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829485 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1829485 : Nat := 118140960795 + 1829485 * 2 ^ 59
def prefixEnd_1829485 : Nat := 4983230072969 + 3 ^ 40 * 1829485 * 2
def baseEnd_1829485 : Nat := 208756701153528858938635

theorem tailTrace_1829485 : CollatzResearch.WordTrace tailWord_1829485 prefixEnd_1829485 208756701153528858938635 := by
  unfold tailWord_1829485
  simp only [CollatzResearch.WordTrace]
  refine ⟨66726799777095771007601909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44484533184730514005067939 66726799777095771007601909)
  ·
    refine ⟨6255637479102728531962679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66726799777095771007601909 6255637479102728531962679)
    ·
      refine ⟨9383456218654092797944019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255637479102728531962679 9383456218654092797944019)
      ·
        refine ⟨14075184327981139196916029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383456218654092797944019 14075184327981139196916029)
        ·
          refine ⟨5278194122992927198843511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14075184327981139196916029 5278194122992927198843511)
          ·
            refine ⟨7917291184489390798265267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278194122992927198843511 7917291184489390798265267)
            ·
              refine ⟨11875936776734086197397901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917291184489390798265267 11875936776734086197397901)
              ·
                refine ⟨4453476291275282324024213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11875936776734086197397901 4453476291275282324024213)
                ·
                  refine ⟨208756701153528858938635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4453476291275282324024213 208756701153528858938635)
                  ·
                    rfl

theorem cell22_1829485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1829485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829485 prefixEnd_1829485 := by exact prefixLift 1829485
  have htrace : WordTrace (prefixWord ++ tailWord_1829485) baseStart_1829485 baseEnd_1829485 := by
    simpa [prefixWord, tailWord_1829485, baseEnd_1829485] using wordTrace_append hprefix tailTrace_1829485
  have hstable : (prefixWord ++ tailWord_1829485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829485).length < 2 ^ (prefixWord ++ tailWord_1829485).sum := by decide
  have hdescent : baseEnd_1829485 < baseStart_1829485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829500 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_1829500 : Nat := 118140960795 + 1829500 * 2 ^ 59
def prefixEnd_1829500 : Nat := 4983230072969 + 3 ^ 40 * 1829500 * 2
def baseEnd_1829500 : Nat := 626275238267131537690859

theorem tailTrace_1829500 : CollatzResearch.WordTrace tailWord_1829500 prefixEnd_1829500 626275238267131537690859 := by
  unfold tailWord_1829500
  simp only [CollatzResearch.WordTrace]
  refine ⟨33363673436020714284698977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44484897914694285712931969 33363673436020714284698977)
  ·
    refine ⟨25022755077015535713524233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33363673436020714284698977 25022755077015535713524233)
    ·
      refine ⟨18767066307761651785143175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25022755077015535713524233 18767066307761651785143175)
      ·
        refine ⟨28150599461642477677714763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18767066307761651785143175 28150599461642477677714763)
        ·
          refine ⟨42225899192463716516572145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28150599461642477677714763 42225899192463716516572145)
          ·
            refine ⟨31669424394347787387429109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42225899192463716516572145 31669424394347787387429109)
            ·
              refine ⟨2969008536970105067571479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31669424394347787387429109 2969008536970105067571479)
              ·
                refine ⟨4453512805455157601357219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969008536970105067571479 4453512805455157601357219)
                ·
                  refine ⟨6680269208182736402035829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453512805455157601357219 6680269208182736402035829)
                  ·
                    refine ⟨626275238267131537690859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6680269208182736402035829 626275238267131537690859)
                    ·
                      rfl

theorem cell22_1829500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_1829500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829500 prefixEnd_1829500 := by exact prefixLift 1829500
  have htrace : WordTrace (prefixWord ++ tailWord_1829500) baseStart_1829500 baseEnd_1829500 := by
    simpa [prefixWord, tailWord_1829500, baseEnd_1829500] using wordTrace_append hprefix tailTrace_1829500
  have hstable : (prefixWord ++ tailWord_1829500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829500).length < 2 ^ (prefixWord ++ tailWord_1829500).sum := by decide
  have hdescent : baseEnd_1829500 < baseStart_1829500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829532 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1829532 : Nat := 118140960795 + 1829532 * 2 ^ 59
def prefixEnd_1829532 : Nat := 4983230072969 + 3 ^ 40 * 1829532 * 2
def baseEnd_1829532 : Nat := 626286192521094120890761

theorem tailTrace_1829532 : CollatzResearch.WordTrace tailWord_1829532 prefixEnd_1829532 626286192521094120890761 := by
  unfold tailWord_1829532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364257003962749017281425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44485676005283665356375233 33364257003962749017281425)
  ·
    refine ⟨25023192752972061762961069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33364257003962749017281425 25023192752972061762961069)
    ·
      refine ⟨9383697282364523161110401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25023192752972061762961069 9383697282364523161110401)
      ·
        refine ⟨7037772961773392370832801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9383697282364523161110401 7037772961773392370832801)
        ·
          refine ⟨5278329721330044278124601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7037772961773392370832801 5278329721330044278124601)
          ·
            refine ⟨3958747290997533208593451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278329721330044278124601 3958747290997533208593451)
            ·
              refine ⟨5938120936496299812890177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958747290997533208593451 5938120936496299812890177)
              ·
                refine ⟨4453590702372224859667633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938120936496299812890177 4453590702372224859667633)
                ·
                  refine ⟨3340193026779168644750725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453590702372224859667633 3340193026779168644750725)
                  ·
                    refine ⟨626286192521094120890761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340193026779168644750725 626286192521094120890761)
                    ·
                      rfl

theorem cell22_1829532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1829532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829532 prefixEnd_1829532 := by exact prefixLift 1829532
  have htrace : WordTrace (prefixWord ++ tailWord_1829532) baseStart_1829532 baseEnd_1829532 := by
    simpa [prefixWord, tailWord_1829532, baseEnd_1829532] using wordTrace_append hprefix tailTrace_1829532
  have hstable : (prefixWord ++ tailWord_1829532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829532).length < 2 ^ (prefixWord ++ tailWord_1829532).sum := by decide
  have hdescent : baseEnd_1829532 < baseStart_1829532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829534 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1829534 : Nat := 118140960795 + 1829534 * 2 ^ 59
def prefixEnd_1829534 : Nat := 4983230072969 + 3 ^ 40 * 1829534 * 2
def baseEnd_1829534 : Nat := 626286877161966782340755

theorem tailTrace_1829534 : CollatzResearch.WordTrace tailWord_1829534 prefixEnd_1829534 626286877161966782340755 := by
  unfold tailWord_1829534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341073369239781547016957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44485724635945501584090437 8341073369239781547016957)
  ·
    refine ⟨3127902513464918080131359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8341073369239781547016957 3127902513464918080131359)
    ·
      refine ⟨4691853770197377120197039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3127902513464918080131359 4691853770197377120197039)
      ·
        refine ⟨7037780655296065680295559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691853770197377120197039 7037780655296065680295559)
        ·
          refine ⟨10556670982944098520443339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037780655296065680295559 10556670982944098520443339)
          ·
            refine ⟨15835006474416147780665009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556670982944098520443339 15835006474416147780665009)
            ·
              refine ⟨11876254855812110835498757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15835006474416147780665009 11876254855812110835498757)
              ·
                refine ⟨2226797785464770781656017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11876254855812110835498757 2226797785464770781656017)
                ·
                  refine ⟨1670098339098578086242013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2226797785464770781656017 1670098339098578086242013)
                  ·
                    refine ⟨626286877161966782340755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670098339098578086242013 626286877161966782340755)
                    ·
                      rfl

theorem cell22_1829534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1829534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829534 prefixEnd_1829534 := by exact prefixLift 1829534
  have htrace : WordTrace (prefixWord ++ tailWord_1829534) baseStart_1829534 baseEnd_1829534 := by
    simpa [prefixWord, tailWord_1829534, baseEnd_1829534] using wordTrace_append hprefix tailTrace_1829534
  have hstable : (prefixWord ++ tailWord_1829534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829534).length < 2 ^ (prefixWord ++ tailWord_1829534).sum := by decide
  have hdescent : baseEnd_1829534 < baseStart_1829534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829592 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_1829592 : Nat := 118140960795 + 1829592 * 2 ^ 59
def prefixEnd_1829592 : Nat := 4983230072969 + 3 ^ 40 * 1829592 * 2
def baseEnd_1829592 : Nat := 208768910582424654796859

theorem tailTrace_1829592 : CollatzResearch.WordTrace tailWord_1829592 prefixEnd_1829592 208768910582424654796859 := by
  unfold tailWord_1829592
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365351193854064140873515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44487134925138752187831353 33365351193854064140873515)
  ·
    refine ⟨50048026790781096211310273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33365351193854064140873515 50048026790781096211310273)
    ·
      refine ⟨37536020093085822158482705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50048026790781096211310273 37536020093085822158482705)
      ·
        refine ⟨28152015069814366618862029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37536020093085822158482705 28152015069814366618862029)
        ·
          refine ⟨10557005651180387482073261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28152015069814366618862029 10557005651180387482073261)
          ·
            refine ⟨3958877119192645305777473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10557005651180387482073261 3958877119192645305777473)
            ·
              refine ⟨2969157839394483979333105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958877119192645305777473 2969157839394483979333105)
              ·
                refine ⟨2226868379545862984499829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969157839394483979333105 2226868379545862984499829)
                ·
                  refine ⟨208768910582424654796859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226868379545862984499829 208768910582424654796859)
                  ·
                    rfl

theorem cell22_1829592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_1829592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829592 prefixEnd_1829592 := by exact prefixLift 1829592
  have htrace : WordTrace (prefixWord ++ tailWord_1829592) baseStart_1829592 baseEnd_1829592 := by
    simpa [prefixWord, tailWord_1829592, baseEnd_1829592] using wordTrace_append hprefix tailTrace_1829592
  have hstable : (prefixWord ++ tailWord_1829592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829592).length < 2 ^ (prefixWord ++ tailWord_1829592).sum := by decide
  have hdescent : baseEnd_1829592 < baseStart_1829592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829622 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1829622 : Nat := 118140960795 + 1829622 * 2 ^ 59
def prefixEnd_1829622 : Nat := 4983230072969 + 3 ^ 40 * 1829622 * 2
def baseEnd_1829622 : Nat := 626317001360363886140485

theorem tailTrace_1829622 : CollatzResearch.WordTrace tailWord_1829622 prefixEnd_1829622 626317001360363886140485 := by
  unfold tailWord_1829622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4170737286099965212833695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44487864385066295603559413 4170737286099965212833695)
  ·
    refine ⟨6256105929149947819250543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4170737286099965212833695 6256105929149947819250543)
    ·
      refine ⟨9384158893724921728875815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256105929149947819250543 9384158893724921728875815)
      ·
        refine ⟨14076238340587382593313723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9384158893724921728875815 14076238340587382593313723)
        ·
          refine ⟨21114357510881073889970585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076238340587382593313723 21114357510881073889970585)
          ·
            refine ⟨15835768133160805417477939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21114357510881073889970585 15835768133160805417477939)
            ·
              refine ⟨23753652199741208126216909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15835768133160805417477939 23753652199741208126216909)
              ·
                refine ⟨8907619574902953047331341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23753652199741208126216909 8907619574902953047331341)
                ·
                  refine ⟨3340357340588607392749253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8907619574902953047331341 3340357340588607392749253)
                  ·
                    refine ⟨626317001360363886140485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340357340588607392749253 626317001360363886140485)
                    ·
                      rfl

theorem cell22_1829622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1829622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829622 prefixEnd_1829622 := by exact prefixLift 1829622
  have htrace : WordTrace (prefixWord ++ tailWord_1829622) baseStart_1829622 baseEnd_1829622 := by
    simpa [prefixWord, tailWord_1829622, baseEnd_1829622] using wordTrace_append hprefix tailTrace_1829622
  have hstable : (prefixWord ++ tailWord_1829622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829622).length < 2 ^ (prefixWord ++ tailWord_1829622).sum := by decide
  have hdescent : baseEnd_1829622 < baseStart_1829622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829639 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1829639 : Nat := 118140960795 + 1829639 * 2 ^ 59
def prefixEnd_1829639 : Nat := 4983230072969 + 3 ^ 40 * 1829639 * 2
def baseEnd_1829639 : Nat := 626322820807781508465433

theorem tailTrace_1829639 : CollatzResearch.WordTrace tailWord_1829639 prefixEnd_1829639 626322820807781508465433 := by
  unfold tailWord_1829639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66732416618537855308707971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44488277745691903539138647 66732416618537855308707971)
  ·
    refine ⟨100098624927806782963061957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66732416618537855308707971 100098624927806782963061957)
    ·
      refine ⟨18768492173963771805574117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100098624927806782963061957 18768492173963771805574117)
      ·
        refine ⟨3519092282618207213545147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18768492173963771805574117 3519092282618207213545147)
        ·
          refine ⟨5278638423927310820317721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519092282618207213545147 5278638423927310820317721)
          ·
            refine ⟨3958978817945483115238291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278638423927310820317721 3958978817945483115238291)
            ·
              refine ⟨5938468226918224672857437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958978817945483115238291 5938468226918224672857437)
              ·
                refine ⟨2226925585094334252321539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938468226918224672857437 2226925585094334252321539)
                ·
                  refine ⟨3340388377641501378482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226925585094334252321539 3340388377641501378482309)
                  ·
                    refine ⟨626322820807781508465433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340388377641501378482309 626322820807781508465433)
                    ·
                      rfl

theorem cell22_1829639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1829639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829639 prefixEnd_1829639 := by exact prefixLift 1829639
  have htrace : WordTrace (prefixWord ++ tailWord_1829639) baseStart_1829639 baseEnd_1829639 := by
    simpa [prefixWord, tailWord_1829639, baseEnd_1829639] using wordTrace_append hprefix tailTrace_1829639
  have hstable : (prefixWord ++ tailWord_1829639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829639).length < 2 ^ (prefixWord ++ tailWord_1829639).sum := by decide
  have hdescent : baseEnd_1829639 < baseStart_1829639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829665 : List Nat := [1, 2, 3, 2, 1, 2, 2, 9]
def baseStart_1829665 : Nat := 118140960795 + 1829665 * 2 ^ 59
def prefixEnd_1829665 : Nat := 4983230072969 + 3 ^ 40 * 1829665 * 2
def baseEnd_1829665 : Nat := 69592413459902900812817

theorem tailTrace_1829665 : CollatzResearch.WordTrace tailWord_1829665 prefixEnd_1829665 69592413459902900812817 := by
  unfold tailWord_1829665
  simp only [CollatzResearch.WordTrace]
  refine ⟨66733364916443661749154449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44488909944295774499436299 66733364916443661749154449)
  ·
    refine ⟨50050023687332746311865837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66733364916443661749154449 50050023687332746311865837)
    ·
      refine ⟨18768758882749779866949689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50050023687332746311865837 18768758882749779866949689)
      ·
        refine ⟨14076569162062334900212267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18768758882749779866949689 14076569162062334900212267)
        ·
          refine ⟨21114853743093502350318401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076569162062334900212267 21114853743093502350318401)
          ·
            refine ⟨15836140307320126762738801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21114853743093502350318401 15836140307320126762738801)
            ·
              refine ⟨11877105230490095072054101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15836140307320126762738801 11877105230490095072054101)
              ·
                refine ⟨69592413459902900812817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11877105230490095072054101 69592413459902900812817)
                ·
                  rfl

theorem cell22_1829665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 9].length) (baseStart_1829665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829665 prefixEnd_1829665 := by exact prefixLift 1829665
  have htrace : WordTrace (prefixWord ++ tailWord_1829665) baseStart_1829665 baseEnd_1829665 := by
    simpa [prefixWord, tailWord_1829665, baseEnd_1829665] using wordTrace_append hprefix tailTrace_1829665
  have hstable : (prefixWord ++ tailWord_1829665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829665).length < 2 ^ (prefixWord ++ tailWord_1829665).sum := by decide
  have hdescent : baseEnd_1829665 < baseStart_1829665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829727 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 5]
def baseStart_1829727 : Nat := 118140960795 + 1829727 * 2 ^ 59
def prefixEnd_1829727 : Nat := 4983230072969 + 3 ^ 40 * 1829727 * 2
def baseEnd_1829727 : Nat := 208784315002059537421721

theorem tailTrace_1829727 : CollatzResearch.WordTrace tailWord_1829727 prefixEnd_1829727 208784315002059537421721 := by
  unfold tailWord_1829727
  simp only [CollatzResearch.WordTrace]
  refine ⟨66735626242219046337911435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44490417494812697558607623 66735626242219046337911435)
  ·
    refine ⟨100103439363328569506867153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66735626242219046337911435 100103439363328569506867153)
    ·
      refine ⟨75077579522496427130150365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100103439363328569506867153 75077579522496427130150365)
      ·
        refine ⟨28154092320936160173806387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75077579522496427130150365 28154092320936160173806387)
        ·
          refine ⟨42231138481404240260709581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28154092320936160173806387 42231138481404240260709581)
          ·
            refine ⟨15836676930526590097766093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42231138481404240260709581 15836676930526590097766093)
            ·
              refine ⟨5938753848947471286662285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15836676930526590097766093 5938753848947471286662285)
              ·
                refine ⟨2227032693355301732498357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938753848947471286662285 2227032693355301732498357)
                ·
                  refine ⟨208784315002059537421721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227032693355301732498357 208784315002059537421721)
                  ·
                    rfl

theorem cell22_1829727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 5].length) (baseStart_1829727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829727 prefixEnd_1829727 := by exact prefixLift 1829727
  have htrace : WordTrace (prefixWord ++ tailWord_1829727) baseStart_1829727 baseEnd_1829727 := by
    simpa [prefixWord, tailWord_1829727, baseEnd_1829727] using wordTrace_append hprefix tailTrace_1829727
  have hstable : (prefixWord ++ tailWord_1829727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829727).length < 2 ^ (prefixWord ++ tailWord_1829727).sum := by decide
  have hdescent : baseEnd_1829727 < baseStart_1829727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829817 : List Nat := [1, 2, 1, 4, 2, 3, 9]
def baseStart_1829817 : Nat := 118140960795 + 1829817 * 2 ^ 59
def prefixEnd_1829817 : Nat := 4983230072969 + 3 ^ 40 * 1829817 * 2
def baseEnd_1829817 : Nat := 23199398290572162130181

theorem tailTrace_1829817 : CollatzResearch.WordTrace tailWord_1829817 prefixEnd_1829817 23199398290572162130181 := by
  unfold tailWord_1829817
  simp only [CollatzResearch.WordTrace]
  refine ⟨66738908811892991708687705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44492605874595327805791803 66738908811892991708687705)
  ·
    refine ⟨50054181608919743781515779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66738908811892991708687705 50054181608919743781515779)
    ·
      refine ⟨75081272413379615672273669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50054181608919743781515779 75081272413379615672273669)
      ·
        refine ⟨14077738577508677938551313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75081272413379615672273669 14077738577508677938551313)
        ·
          refine ⟨10558303933131508453913485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14077738577508677938551313 10558303933131508453913485)
          ·
            refine ⟨3959363974924315670217557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10558303933131508453913485 3959363974924315670217557)
            ·
              refine ⟨23199398290572162130181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3959363974924315670217557 23199398290572162130181)
              ·
                rfl

theorem cell22_1829817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 9].length) (baseStart_1829817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829817 prefixEnd_1829817 := by exact prefixLift 1829817
  have htrace : WordTrace (prefixWord ++ tailWord_1829817) baseStart_1829817 baseEnd_1829817 := by
    simpa [prefixWord, tailWord_1829817, baseEnd_1829817] using wordTrace_append hprefix tailTrace_1829817
  have hstable : (prefixWord ++ tailWord_1829817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829817).length < 2 ^ (prefixWord ++ tailWord_1829817).sum := by decide
  have hdescent : baseEnd_1829817 < baseStart_1829817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829821 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1829821 : Nat := 118140960795 + 1829821 * 2 ^ 59
def prefixEnd_1829821 : Nat := 4983230072969 + 3 ^ 40 * 1829821 * 2
def baseEnd_1829821 : Nat := 626385123127193700414875

theorem tailTrace_1829821 : CollatzResearch.WordTrace tailWord_1829821 prefixEnd_1829821 626385123127193700414875 := by
  unfold tailWord_1829821
  simp only [CollatzResearch.WordTrace]
  refine ⟨66739054703878500391833317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44492703135919000261222211 66739054703878500391833317)
  ·
    refine ⟨12513572756977218823468747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66739054703878500391833317 12513572756977218823468747)
    ·
      refine ⟨18770359135465828235203121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12513572756977218823468747 18770359135465828235203121)
      ·
        refine ⟨14077769351599371176402341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18770359135465828235203121 14077769351599371176402341)
        ·
          refine ⟨2639581753424882095575439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14077769351599371176402341 2639581753424882095575439)
          ·
            refine ⟨3959372630137323143363159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639581753424882095575439 3959372630137323143363159)
            ·
              refine ⟨5939058945205984715044739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959372630137323143363159 5939058945205984715044739)
              ·
                refine ⟨8908588417808977072567109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939058945205984715044739 8908588417808977072567109)
                ·
                  refine ⟨1670360328339183201106333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8908588417808977072567109 1670360328339183201106333)
                  ·
                    refine ⟨626385123127193700414875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670360328339183201106333 626385123127193700414875)
                    ·
                      rfl

theorem cell22_1829821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1829821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829821 prefixEnd_1829821 := by exact prefixLift 1829821
  have htrace : WordTrace (prefixWord ++ tailWord_1829821) baseStart_1829821 baseEnd_1829821 := by
    simpa [prefixWord, tailWord_1829821, baseEnd_1829821] using wordTrace_append hprefix tailTrace_1829821
  have hstable : (prefixWord ++ tailWord_1829821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829821).length < 2 ^ (prefixWord ++ tailWord_1829821).sum := by decide
  have hdescent : baseEnd_1829821 < baseStart_1829821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829838 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_1829838 : Nat := 118140960795 + 1829838 * 2 ^ 59
def prefixEnd_1829838 : Nat := 4983230072969 + 3 ^ 40 * 1829838 * 2
def baseEnd_1829838 : Nat := 626390942574611322739823

theorem tailTrace_1829838 : CollatzResearch.WordTrace tailWord_1829838 prefixEnd_1829838 626390942574611322739823 := by
  unfold tailWord_1829838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342459343102114036900271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44493116496544608196801445 8342459343102114036900271)
  ·
    refine ⟨12513689014653171055350407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342459343102114036900271 12513689014653171055350407)
    ·
      refine ⟨18770533521979756583025611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12513689014653171055350407 18770533521979756583025611)
      ·
        refine ⟨28155800282969634874538417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18770533521979756583025611 28155800282969634874538417)
        ·
          refine ⟨21116850212227226155903813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28155800282969634874538417 21116850212227226155903813)
          ·
            refine ⟨3959409414792604904231965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21116850212227226155903813 3959409414792604904231965)
            ·
              refine ⟨1484778530547226839086987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959409414792604904231965 1484778530547226839086987)
              ·
                refine ⟨2227167795820840258630481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484778530547226839086987 2227167795820840258630481)
                ·
                  refine ⟨1670375846865630193972861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227167795820840258630481 1670375846865630193972861)
                  ·
                    refine ⟨626390942574611322739823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670375846865630193972861 626390942574611322739823)
                    ·
                      rfl

theorem cell22_1829838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_1829838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829838 prefixEnd_1829838 := by exact prefixLift 1829838
  have htrace : WordTrace (prefixWord ++ tailWord_1829838) baseStart_1829838 baseEnd_1829838 := by
    simpa [prefixWord, tailWord_1829838, baseEnd_1829838] using wordTrace_append hprefix tailTrace_1829838
  have hstable : (prefixWord ++ tailWord_1829838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829838).length < 2 ^ (prefixWord ++ tailWord_1829838).sum := by decide
  have hdescent : baseEnd_1829838 < baseStart_1829838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829896 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_1829896 : Nat := 118140960795 + 1829896 * 2 ^ 59
def prefixEnd_1829896 : Nat := 4983230072969 + 3 ^ 40 * 1829896 * 2
def baseEnd_1829896 : Nat := 208803599053306168263215

theorem tailTrace_1829896 : CollatzResearch.WordTrace tailWord_1829896 prefixEnd_1829896 208803599053306168263215 := by
  unfold tailWord_1829896
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370895089303394100406771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44494526785737858800542361 33370895089303394100406771)
  ·
    refine ⟨50056342633955091150610157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33370895089303394100406771 50056342633955091150610157)
    ·
      refine ⟨18771128487733159181478809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50056342633955091150610157 18771128487733159181478809)
      ·
        refine ⟨14078346365799869386109107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18771128487733159181478809 14078346365799869386109107)
        ·
          refine ⟨21117519548699804079163661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14078346365799869386109107 21117519548699804079163661)
          ·
            refine ⟨7919069830762426529686373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21117519548699804079163661 7919069830762426529686373)
            ·
              refine ⟨1484825593267954974316195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7919069830762426529686373 1484825593267954974316195)
              ·
                refine ⟨2227238389901932461474293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484825593267954974316195 2227238389901932461474293)
                ·
                  refine ⟨208803599053306168263215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227238389901932461474293 208803599053306168263215)
                  ·
                    rfl

theorem cell22_1829896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_1829896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829896 prefixEnd_1829896 := by exact prefixLift 1829896
  have htrace : WordTrace (prefixWord ++ tailWord_1829896) baseStart_1829896 baseEnd_1829896 := by
    simpa [prefixWord, tailWord_1829896, baseEnd_1829896] using wordTrace_append hprefix tailTrace_1829896
  have hstable : (prefixWord ++ tailWord_1829896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829896).length < 2 ^ (prefixWord ++ tailWord_1829896).sum := by decide
  have hdescent : baseEnd_1829896 < baseStart_1829896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829907 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 8]
def baseStart_1829907 : Nat := 118140960795 + 1829907 * 2 ^ 59
def prefixEnd_1829907 : Nat := 4983230072969 + 3 ^ 40 * 1829907 * 2
def baseEnd_1829907 : Nat := 208804854228239380921537

theorem tailTrace_1829907 : CollatzResearch.WordTrace tailWord_1829907 prefixEnd_1829907 208804854228239380921537 := by
  unfold tailWord_1829907
  simp only [CollatzResearch.WordTrace]
  refine ⟨66742191381566937079463975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44494794254377958052975983 66742191381566937079463975)
  ·
    refine ⟨100113287072350405619195963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66742191381566937079463975 100113287072350405619195963)
    ·
      refine ⟨150169930608525608428793945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100113287072350405619195963 150169930608525608428793945)
      ·
        refine ⟨112627447956394206321595459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150169930608525608428793945 112627447956394206321595459)
        ·
          refine ⟨168941171934591309482393189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112627447956394206321595459 168941171934591309482393189)
          ·
            refine ⟨31676469737735870527948723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168941171934591309482393189 31676469737735870527948723)
            ·
              refine ⟨47514704606603805791923085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31676469737735870527948723 47514704606603805791923085)
              ·
                refine ⟨17818014227476427171971157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47514704606603805791923085 17818014227476427171971157)
                ·
                  refine ⟨208804854228239380921537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17818014227476427171971157 208804854228239380921537)
                  ·
                    rfl

theorem cell22_1829907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_1829907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829907 prefixEnd_1829907 := by exact prefixLift 1829907
  have htrace : WordTrace (prefixWord ++ tailWord_1829907) baseStart_1829907 baseEnd_1829907 := by
    simpa [prefixWord, tailWord_1829907, baseEnd_1829907] using wordTrace_append hprefix tailTrace_1829907
  have hstable : (prefixWord ++ tailWord_1829907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829907).length < 2 ^ (prefixWord ++ tailWord_1829907).sum := by decide
  have hdescent : baseEnd_1829907 < baseStart_1829907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829958 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1829958 : Nat := 118140960795 + 1829958 * 2 ^ 59
def prefixEnd_1829958 : Nat := 4983230072969 + 3 ^ 40 * 1829958 * 2
def baseEnd_1829958 : Nat := 208810673675657003246485

theorem tailTrace_1829958 : CollatzResearch.WordTrace tailWord_1829958 prefixEnd_1829958 208810673675657003246485 := by
  unfold tailWord_1829958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085751609511942899674079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44496034336254781859713685 2085751609511942899674079)
  ·
    refine ⟨3128627414267914349511119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2085751609511942899674079 3128627414267914349511119)
    ·
      refine ⟨4692941121401871524266679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128627414267914349511119 4692941121401871524266679)
      ·
        refine ⟨7039411682102807286400019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692941121401871524266679 7039411682102807286400019)
        ·
          refine ⟨10559117523154210929600029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039411682102807286400019 10559117523154210929600029)
          ·
            refine ⟨3959669071182829098600011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10559117523154210929600029 3959669071182829098600011)
            ·
              refine ⟨5939503606774243647900017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959669071182829098600011 5939503606774243647900017)
              ·
                refine ⟨4454627705080682735925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5939503606774243647900017 4454627705080682735925013)
                ·
                  refine ⟨208810673675657003246485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4454627705080682735925013 208810673675657003246485)
                  ·
                    rfl

theorem cell22_1829958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1829958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829958 prefixEnd_1829958 := by exact prefixLift 1829958
  have htrace : WordTrace (prefixWord ++ tailWord_1829958) baseStart_1829958 baseEnd_1829958 := by
    simpa [prefixWord, tailWord_1829958, baseEnd_1829958] using wordTrace_append hprefix tailTrace_1829958
  have hstable : (prefixWord ++ tailWord_1829958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829958).length < 2 ^ (prefixWord ++ tailWord_1829958).sum := by decide
  have hdescent : baseEnd_1829958 < baseStart_1829958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829986 : List Nat := [3, 3, 2, 2, 1, 2, 9]
def baseStart_1829986 : Nat := 118140960795 + 1829986 * 2 ^ 59
def prefixEnd_1829986 : Nat := 4983230072969 + 3 ^ 40 * 1829986 * 2
def baseEnd_1829986 : Nat := 23201540962932898890347

theorem tailTrace_1829986 : CollatzResearch.WordTrace tailWord_1829986 prefixEnd_1829986 23201540962932898890347 := by
  unfold tailWord_1829986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16686268187070183392897453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44496715165520489047726541 16686268187070183392897453)
  ·
    refine ⟨6257350570151318772336545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16686268187070183392897453 6257350570151318772336545)
    ·
      refine ⟨4693012927613489079252409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6257350570151318772336545 4693012927613489079252409)
      ·
        refine ⟨3519759695710116809439307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693012927613489079252409 3519759695710116809439307)
        ·
          refine ⟨5279639543565175214158961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519759695710116809439307 5279639543565175214158961)
          ·
            refine ⟨3959729657673881410619221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279639543565175214158961 3959729657673881410619221)
            ·
              refine ⟨23201540962932898890347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3959729657673881410619221 23201540962932898890347)
              ·
                rfl

theorem cell22_1829986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 9].length) (baseStart_1829986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1829986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1829986 prefixEnd_1829986 := by exact prefixLift 1829986
  have htrace : WordTrace (prefixWord ++ tailWord_1829986) baseStart_1829986 baseEnd_1829986 := by
    simpa [prefixWord, tailWord_1829986, baseEnd_1829986] using wordTrace_append hprefix tailTrace_1829986
  have hstable : (prefixWord ++ tailWord_1829986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829986).length < 2 ^ (prefixWord ++ tailWord_1829986).sum := by decide
  have hdescent : baseEnd_1829986 < baseStart_1829986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830052 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_1830052 : Nat := 118140960795 + 1830052 * 2 ^ 59
def prefixEnd_1830052 : Nat := 4983230072969 + 3 ^ 40 * 1830052 * 2
def baseEnd_1830052 : Nat := 626464199147986097889167

theorem tailTrace_1830052 : CollatzResearch.WordTrace tailWord_1830052 prefixEnd_1830052 626464199147986097889167 := by
  unfold tailWord_1830052
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373739983020813421746205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44498319977361084562328273 33373739983020813421746205)
  ·
    refine ⟨12515152493632805033154827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33373739983020813421746205 12515152493632805033154827)
    ·
      refine ⟨18772728740449207549732241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12515152493632805033154827 18772728740449207549732241)
      ·
        refine ⟨14079546555336905662299181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18772728740449207549732241 14079546555336905662299181)
        ·
          refine ⟨5279829958251339623362193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14079546555336905662299181 5279829958251339623362193)
          ·
            refine ⟨3959872468688504717521645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279829958251339623362193 3959872468688504717521645)
            ·
              refine ⟨1484952175758189269070617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959872468688504717521645 1484952175758189269070617)
              ·
                refine ⟨1113714131818641951802963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1484952175758189269070617 1113714131818641951802963)
                ·
                  refine ⟨1670571197727962927704445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113714131818641951802963 1670571197727962927704445)
                  ·
                    refine ⟨626464199147986097889167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670571197727962927704445 626464199147986097889167)
                    ·
                      rfl

theorem cell22_1830052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_1830052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830052 prefixEnd_1830052 := by exact prefixLift 1830052
  have htrace : WordTrace (prefixWord ++ tailWord_1830052) baseStart_1830052 baseEnd_1830052 := by
    simpa [prefixWord, tailWord_1830052, baseEnd_1830052] using wordTrace_append hprefix tailTrace_1830052
  have hstable : (prefixWord ++ tailWord_1830052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830052).length < 2 ^ (prefixWord ++ tailWord_1830052).sum := by decide
  have hdescent : baseEnd_1830052 < baseStart_1830052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830065 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 5]
def baseStart_1830065 : Nat := 118140960795 + 1830065 * 2 ^ 59
def prefixEnd_1830065 : Nat := 4983230072969 + 3 ^ 40 * 1830065 * 2
def baseEnd_1830065 : Nat := 208822883104552799104709

theorem tailTrace_1830065 : CollatzResearch.WordTrace tailWord_1830065 prefixEnd_1830065 208822883104552799104709 := by
  unfold tailWord_1830065
  simp only [CollatzResearch.WordTrace]
  refine ⟨66747954114994530063715649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44498636076663020042477099 66747954114994530063715649)
  ·
    refine ⟨50060965586245897547786737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66747954114994530063715649 50060965586245897547786737)
    ·
      refine ⟨37545724189684423160840053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50060965586245897547786737 37545724189684423160840053)
      ·
        refine ⟨3519911642782914671328755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37545724189684423160840053 3519911642782914671328755)
        ·
          refine ⟨5279867464174372006993133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519911642782914671328755 5279867464174372006993133)
          ·
            refine ⟨1979950299065389502622425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5279867464174372006993133 1979950299065389502622425)
            ·
              refine ⟨1484962724299042126966819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979950299065389502622425 1484962724299042126966819)
              ·
                refine ⟨2227444086448563190450229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484962724299042126966819 2227444086448563190450229)
                ·
                  refine ⟨208822883104552799104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227444086448563190450229 208822883104552799104709)
                  ·
                    rfl

theorem cell22_1830065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_1830065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830065 prefixEnd_1830065 := by exact prefixLift 1830065
  have htrace : WordTrace (prefixWord ++ tailWord_1830065) baseStart_1830065 baseEnd_1830065 := by
    simpa [prefixWord, tailWord_1830065, baseEnd_1830065] using wordTrace_append hprefix tailTrace_1830065
  have hstable : (prefixWord ++ tailWord_1830065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830065).length < 2 ^ (prefixWord ++ tailWord_1830065).sum := by decide
  have hdescent : baseEnd_1830065 < baseStart_1830065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830078 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1830078 : Nat := 118140960795 + 1830078 * 2 ^ 59
def prefixEnd_1830078 : Nat := 4983230072969 + 3 ^ 40 * 1830078 * 2
def baseEnd_1830078 : Nat := 626473099479330696739087

theorem tailTrace_1830078 : CollatzResearch.WordTrace tailWord_1830078 prefixEnd_1830078 626473099479330696739087 := by
  unfold tailWord_1830078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343553532993429160492361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44498952175964955522625925 8343553532993429160492361)
  ·
    refine ⟨6257665149745071870369271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8343553532993429160492361 6257665149745071870369271)
    ·
      refine ⟨9386497724617607805553907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257665149745071870369271 9386497724617607805553907)
      ·
        refine ⟨14079746586926411708330861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9386497724617607805553907 14079746586926411708330861)
        ·
          refine ⟨5279904970097404390624073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14079746586926411708330861 5279904970097404390624073)
          ·
            refine ⟨3959928727573053292968055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279904970097404390624073 3959928727573053292968055)
            ·
              refine ⟨5939893091359579939452083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959928727573053292968055 5939893091359579939452083)
              ·
                refine ⟨8909839637039369909178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939893091359579939452083 8909839637039369909178125)
                ·
                  refine ⟨3341189863889763715941797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8909839637039369909178125 3341189863889763715941797)
                  ·
                    refine ⟨626473099479330696739087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341189863889763715941797 626473099479330696739087)
                    ·
                      rfl

theorem cell22_1830078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1830078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830078 prefixEnd_1830078 := by exact prefixLift 1830078
  have htrace : WordTrace (prefixWord ++ tailWord_1830078) baseStart_1830078 baseEnd_1830078 := by
    simpa [prefixWord, tailWord_1830078, baseEnd_1830078] using wordTrace_append hprefix tailTrace_1830078
  have hstable : (prefixWord ++ tailWord_1830078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830078).length < 2 ^ (prefixWord ++ tailWord_1830078).sum := by decide
  have hdescent : baseEnd_1830078 < baseStart_1830078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830089 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_1830089 : Nat := 118140960795 + 1830089 * 2 ^ 59
def prefixEnd_1830089 : Nat := 4983230072969 + 3 ^ 40 * 1830089 * 2
def baseEnd_1830089 : Nat := 626476865004130334714053

theorem tailTrace_1830089 : CollatzResearch.WordTrace tailWord_1830089 prefixEnd_1830089 626476865004130334714053 := by
  unfold tailWord_1830089
  simp only [CollatzResearch.WordTrace]
  refine ⟨66748829466907582162589321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44499219644605054775059547 66748829466907582162589321)
  ·
    refine ⟨50061622100180686621941991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66748829466907582162589321 50061622100180686621941991)
    ·
      refine ⟨75092433150271029932912987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50061622100180686621941991 75092433150271029932912987)
      ·
        refine ⟨112638649725406544899369481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75092433150271029932912987 112638649725406544899369481)
        ·
          refine ⟨84478987294054908674527111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112638649725406544899369481 84478987294054908674527111)
          ·
            refine ⟨126718480941082363011790667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84478987294054908674527111 126718480941082363011790667)
            ·
              refine ⟨190077721411623544517686001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126718480941082363011790667 190077721411623544517686001)
              ·
                refine ⟨142558291058717658388264501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190077721411623544517686001 142558291058717658388264501)
                ·
                  refine ⟨13364839786754780473899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142558291058717658388264501 13364839786754780473899797)
                  ·
                    refine ⟨626476865004130334714053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13364839786754780473899797 626476865004130334714053)
                    ·
                      rfl

theorem cell22_1830089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_1830089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830089 prefixEnd_1830089 := by exact prefixLift 1830089
  have htrace : WordTrace (prefixWord ++ tailWord_1830089) baseStart_1830089 baseEnd_1830089 := by
    simpa [prefixWord, tailWord_1830089, baseEnd_1830089] using wordTrace_append hprefix tailTrace_1830089
  have hstable : (prefixWord ++ tailWord_1830089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830089).length < 2 ^ (prefixWord ++ tailWord_1830089).sum := by decide
  have hdescent : baseEnd_1830089 < baseStart_1830089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830091 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 4, 3]
def baseStart_1830091 : Nat := 118140960795 + 1830091 * 2 ^ 59
def prefixEnd_1830091 : Nat := 4983230072969 + 3 ^ 40 * 1830091 * 2
def baseEnd_1830091 : Nat := 626477549645002996164047

theorem tailTrace_1830091 : CollatzResearch.WordTrace tailWord_1830091 prefixEnd_1830091 626477549645002996164047 := by
  unfold tailWord_1830091
  simp only [CollatzResearch.WordTrace]
  refine ⟨66748902412900336504162127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44499268275266891002774751 66748902412900336504162127)
  ·
    refine ⟨100123353619350504756243191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66748902412900336504162127 100123353619350504756243191)
    ·
      refine ⟨150185030429025757134364787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100123353619350504756243191 150185030429025757134364787)
      ·
        refine ⟨225277545643538635701547181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150185030429025757134364787 225277545643538635701547181)
        ·
          refine ⟨84479079616326988388080193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225277545643538635701547181 84479079616326988388080193)
          ·
            refine ⟨63359309712245241291060145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84479079616326988388080193 63359309712245241291060145)
            ·
              refine ⟨47519482284183930968295109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63359309712245241291060145 47519482284183930968295109)
              ·
                refine ⟨8909902928284487056555333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47519482284183930968295109 8909902928284487056555333)
                ·
                  refine ⟨1670606799053341323104125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8909902928284487056555333 1670606799053341323104125)
                  ·
                    refine ⟨626477549645002996164047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670606799053341323104125 626477549645002996164047)
                    ·
                      rfl

theorem cell22_1830091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3].length) (baseStart_1830091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830091 prefixEnd_1830091 := by exact prefixLift 1830091
  have htrace : WordTrace (prefixWord ++ tailWord_1830091) baseStart_1830091 baseEnd_1830091 := by
    simpa [prefixWord, tailWord_1830091, baseEnd_1830091] using wordTrace_append hprefix tailTrace_1830091
  have hstable : (prefixWord ++ tailWord_1830091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830091).length < 2 ^ (prefixWord ++ tailWord_1830091).sum := by decide
  have hdescent : baseEnd_1830091 < baseStart_1830091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830104 : List Nat := [2, 1, 2, 2, 15]
def baseStart_1830104 : Nat := 118140960795 + 1830104 * 2 ^ 59
def prefixEnd_1830104 : Nat := 4983230072969 + 3 ^ 40 * 1830104 * 2
def baseEnd_1830104 : Nat := 2578115225558334549749

theorem tailTrace_1830104 : CollatzResearch.WordTrace tailWord_1830104 prefixEnd_1830104 2578115225558334549749 := by
  unfold tailWord_1830104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33374688280926619862192683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44499584374568826482923577 33374688280926619862192683)
  ·
    refine ⟨50062032421389929793289025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33374688280926619862192683 50062032421389929793289025)
    ·
      refine ⟨37546524316042447344966769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50062032421389929793289025 37546524316042447344966769)
      ·
        refine ⟨28159893237031835508725077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37546524316042447344966769 28159893237031835508725077)
        ·
          refine ⟨2578115225558334549749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 28159893237031835508725077 2578115225558334549749)
          ·
            rfl

theorem cell22_1830104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 15].length) (baseStart_1830104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830104 prefixEnd_1830104 := by exact prefixLift 1830104
  have htrace : WordTrace (prefixWord ++ tailWord_1830104) baseStart_1830104 baseEnd_1830104 := by
    simpa [prefixWord, tailWord_1830104, baseEnd_1830104] using wordTrace_append hprefix tailTrace_1830104
  have hstable : (prefixWord ++ tailWord_1830104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830104).length < 2 ^ (prefixWord ++ tailWord_1830104).sum := by decide
  have hdescent : baseEnd_1830104 < baseStart_1830104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830125 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1830125 : Nat := 118140960795 + 1830125 * 2 ^ 59
def prefixEnd_1830125 : Nat := 4983230072969 + 3 ^ 40 * 1830125 * 2
def baseEnd_1830125 : Nat := 626489188539838240813943

theorem tailTrace_1830125 : CollatzResearch.WordTrace tailWord_1830125 prefixEnd_1830125 626489188539838240813943 := by
  unfold tailWord_1830125
  simp only [CollatzResearch.WordTrace]
  refine ⟨66750142494777160310899829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44500094996518106873933219 66750142494777160310899829)
  ·
    refine ⟨6257825858885358779146859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66750142494777160310899829 6257825858885358779146859)
    ·
      refine ⟨9386738788328038168720289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257825858885358779146859 9386738788328038168720289)
      ·
        refine ⟨7040054091246028626540217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9386738788328038168720289 7040054091246028626540217)
        ·
          refine ⟨5280040568434521469905163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7040054091246028626540217 5280040568434521469905163)
          ·
            refine ⟨7920060852651782204857745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280040568434521469905163 7920060852651782204857745)
            ·
              refine ⟨5940045639488836653643309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7920060852651782204857745 5940045639488836653643309)
              ·
                refine ⟨2227517114808313745116241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5940045639488836653643309 2227517114808313745116241)
                ·
                  refine ⟨1670637836106235308837181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227517114808313745116241 1670637836106235308837181)
                  ·
                    refine ⟨626489188539838240813943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670637836106235308837181 626489188539838240813943)
                    ·
                      rfl

theorem cell22_1830125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1830125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830125 prefixEnd_1830125 := by exact prefixLift 1830125
  have htrace : WordTrace (prefixWord ++ tailWord_1830125) baseStart_1830125 baseEnd_1830125 := by
    simpa [prefixWord, tailWord_1830125, baseEnd_1830125] using wordTrace_append hprefix tailTrace_1830125
  have hstable : (prefixWord ++ tailWord_1830125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830125).length < 2 ^ (prefixWord ++ tailWord_1830125).sum := by decide
  have hdescent : baseEnd_1830125 < baseStart_1830125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830140 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_1830140 : Nat := 118140960795 + 1830140 * 2 ^ 59
def prefixEnd_1830140 : Nat := 4983230072969 + 3 ^ 40 * 1830140 * 2
def baseEnd_1830140 : Nat := 626494323346383201688897

theorem tailTrace_1830140 : CollatzResearch.WordTrace tailWord_1830140 prefixEnd_1830140 626494323346383201688897 := by
  unfold tailWord_1830140
  simp only [CollatzResearch.WordTrace]
  refine ⟨33375344794861408936347937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44500459726481878581797249 33375344794861408936347937)
  ·
    refine ⟨25031508596146056702260953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33375344794861408936347937 25031508596146056702260953)
    ·
      refine ⟨18773631447109542526695715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25031508596146056702260953 18773631447109542526695715)
      ·
        refine ⟨28160447170664313790043573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18773631447109542526695715 28160447170664313790043573)
        ·
          refine ⟨2640041922249779417816585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28160447170664313790043573 2640041922249779417816585)
          ·
            refine ⟨1980031441687334563362439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640041922249779417816585 1980031441687334563362439)
            ·
              refine ⟨2970047162531001845043659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980031441687334563362439 2970047162531001845043659)
              ·
                refine ⟨4455070743796502767565489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970047162531001845043659 4455070743796502767565489)
                ·
                  refine ⟨3341303057847377075674117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455070743796502767565489 3341303057847377075674117)
                  ·
                    refine ⟨626494323346383201688897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341303057847377075674117 626494323346383201688897)
                    ·
                      rfl

theorem cell22_1830140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_1830140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830140 prefixEnd_1830140 := by exact prefixLift 1830140
  have htrace : WordTrace (prefixWord ++ tailWord_1830140) baseStart_1830140 baseEnd_1830140 := by
    simpa [prefixWord, tailWord_1830140, baseEnd_1830140] using wordTrace_append hprefix tailTrace_1830140
  have hstable : (prefixWord ++ tailWord_1830140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830140).length < 2 ^ (prefixWord ++ tailWord_1830140).sum := by decide
  have hdescent : baseEnd_1830140 < baseStart_1830140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830170 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_1830170 : Nat := 118140960795 + 1830170 * 2 ^ 59
def prefixEnd_1830170 : Nat := 4983230072969 + 3 ^ 40 * 1830170 * 2
def baseEnd_1830170 : Nat := 626504592959473123438805

theorem tailTrace_1830170 : CollatzResearch.WordTrace tailWord_1830170 prefixEnd_1830170 626504592959473123438805 := by
  unfold tailWord_1830170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687945944903533249071991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44501189186409421997525309 16687945944903533249071991)
  ·
    refine ⟨25031918917355299873607987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16687945944903533249071991 25031918917355299873607987)
    ·
      refine ⟨37547878376032949810411981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25031918917355299873607987 37547878376032949810411981)
      ·
        refine ⟨14080454391012356178904493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37547878376032949810411981 14080454391012356178904493)
        ·
          refine ⟨5280170396629633567089185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14080454391012356178904493 5280170396629633567089185)
          ·
            refine ⟨3960127797472225175316889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280170396629633567089185 3960127797472225175316889)
            ·
              refine ⟨2970095848104168881487667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960127797472225175316889 2970095848104168881487667)
              ·
                refine ⟨4455143772156253322231501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970095848104168881487667 4455143772156253322231501)
                ·
                  refine ⟨1670678914558594995836813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4455143772156253322231501 1670678914558594995836813)
                  ·
                    refine ⟨626504592959473123438805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670678914558594995836813 626504592959473123438805)
                    ·
                      rfl

theorem cell22_1830170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_1830170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830170 prefixEnd_1830170 := by exact prefixLift 1830170
  have htrace : WordTrace (prefixWord ++ tailWord_1830170) baseStart_1830170 baseEnd_1830170 := by
    simpa [prefixWord, tailWord_1830170, baseEnd_1830170] using wordTrace_append hprefix tailTrace_1830170
  have hstable : (prefixWord ++ tailWord_1830170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830170).length < 2 ^ (prefixWord ++ tailWord_1830170).sum := by decide
  have hdescent : baseEnd_1830170 < baseStart_1830170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830221 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1830221 : Nat := 118140960795 + 1830221 * 2 ^ 59
def prefixEnd_1830221 : Nat := 4983230072969 + 3 ^ 40 * 1830221 * 2
def baseEnd_1830221 : Nat := 626522051301725990413649

theorem tailTrace_1830221 : CollatzResearch.WordTrace tailWord_1830221 prefixEnd_1830221 626522051301725990413649 := by
  unfold tailWord_1830221
  simp only [CollatzResearch.WordTrace]
  refine ⟨66753643902429368706394517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44502429268286245804263011 66753643902429368706394517)
  ·
    refine ⟨3129077057926376658112243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66753643902429368706394517 3129077057926376658112243)
    ·
      refine ⟨4693615586889564987168365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129077057926376658112243 4693615586889564987168365)
      ·
        refine ⟨1760105845083586870188137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4693615586889564987168365 1760105845083586870188137)
        ·
          refine ⟨1320079383812690152641103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1760105845083586870188137 1320079383812690152641103)
          ·
            refine ⟨1980119075719035228961655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320079383812690152641103 1980119075719035228961655)
            ·
              refine ⟨2970178613578552843442483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980119075719035228961655 2970178613578552843442483)
              ·
                refine ⟨4455267920367829265163725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970178613578552843442483 4455267920367829265163725)
                ·
                  refine ⟨1670725470137935974436397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4455267920367829265163725 1670725470137935974436397)
                  ·
                    refine ⟨626522051301725990413649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1670725470137935974436397 626522051301725990413649)
                    ·
                      rfl

theorem cell22_1830221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1830221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830221 prefixEnd_1830221 := by exact prefixLift 1830221
  have htrace : WordTrace (prefixWord ++ tailWord_1830221) baseStart_1830221 baseEnd_1830221 := by
    simpa [prefixWord, tailWord_1830221, baseEnd_1830221] using wordTrace_append hprefix tailTrace_1830221
  have hstable : (prefixWord ++ tailWord_1830221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830221).length < 2 ^ (prefixWord ++ tailWord_1830221).sum := by decide
  have hdescent : baseEnd_1830221 < baseStart_1830221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830241 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1830241 : Nat := 118140960795 + 1830241 * 2 ^ 59
def prefixEnd_1830241 : Nat := 4983230072969 + 3 ^ 40 * 1830241 * 2
def baseEnd_1830241 : Nat := 626528897710452604913587

theorem tailTrace_1830241 : CollatzResearch.WordTrace tailWord_1830241 prefixEnd_1830241 626528897710452604913587 := by
  unfold tailWord_1830241
  simp only [CollatzResearch.WordTrace]
  refine ⟨66754373362356912122122577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44502915574904608081415051 66754373362356912122122577)
  ·
    refine ⟨50065780021767684091591933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66754373362356912122122577 50065780021767684091591933)
    ·
      refine ⟨18774667508162881534346975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50065780021767684091591933 18774667508162881534346975)
      ·
        refine ⟨28162001262244322301520463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18774667508162881534346975 28162001262244322301520463)
        ·
          refine ⟨42243001893366483452280695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28162001262244322301520463 42243001893366483452280695)
          ·
            refine ⟨63364502840049725178421043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42243001893366483452280695 63364502840049725178421043)
            ·
              refine ⟨95046754260074587767631565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63364502840049725178421043 95046754260074587767631565)
              ·
                refine ⟨35642532847527970412861837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95046754260074587767631565 35642532847527970412861837)
                ·
                  refine ⟨13365949817822988904823189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35642532847527970412861837 13365949817822988904823189)
                  ·
                    refine ⟨626528897710452604913587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13365949817822988904823189 626528897710452604913587)
                    ·
                      rfl

theorem cell22_1830241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1830241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830241 prefixEnd_1830241 := by exact prefixLift 1830241
  have htrace : WordTrace (prefixWord ++ tailWord_1830241) baseStart_1830241 baseEnd_1830241 := by
    simpa [prefixWord, tailWord_1830241, baseEnd_1830241] using wordTrace_append hprefix tailTrace_1830241
  have hstable : (prefixWord ++ tailWord_1830241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830241).length < 2 ^ (prefixWord ++ tailWord_1830241).sum := by decide
  have hdescent : baseEnd_1830241 < baseStart_1830241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830247 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1830247 : Nat := 118140960795 + 1830247 * 2 ^ 59
def prefixEnd_1830247 : Nat := 4983230072969 + 3 ^ 40 * 1830247 * 2
def baseEnd_1830247 : Nat := 626530951633070589263569

theorem tailTrace_1830247 : CollatzResearch.WordTrace tailWord_1830247 prefixEnd_1830247 626530951633070589263569 := by
  unfold tailWord_1830247
  simp only [CollatzResearch.WordTrace]
  refine ⟨66754592200335175146840995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44503061466890116764560663 66754592200335175146840995)
  ·
    refine ⟨100131888300502762720261493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66754592200335175146840995 100131888300502762720261493)
    ·
      refine ⟨9387364528172134005024515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100131888300502762720261493 9387364528172134005024515)
      ·
        refine ⟨14081046792258201007536773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387364528172134005024515 14081046792258201007536773)
        ·
          refine ⟨2640196273548412688913145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14081046792258201007536773 2640196273548412688913145)
          ·
            refine ⟨1980147205161309516684859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640196273548412688913145 1980147205161309516684859)
            ·
              refine ⟨2970220807741964275027289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980147205161309516684859 2970220807741964275027289)
              ·
                refine ⟨2227665605806473206270467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970220807741964275027289 2227665605806473206270467)
                ·
                  refine ⟨3341498408709709809405701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227665605806473206270467 3341498408709709809405701)
                  ·
                    refine ⟨626530951633070589263569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341498408709709809405701 626530951633070589263569)
                    ·
                      rfl

theorem cell22_1830247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1830247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830247 prefixEnd_1830247 := by exact prefixLift 1830247
  have htrace : WordTrace (prefixWord ++ tailWord_1830247) baseStart_1830247 baseEnd_1830247 := by
    simpa [prefixWord, tailWord_1830247, baseEnd_1830247] using wordTrace_append hprefix tailTrace_1830247
  have hstable : (prefixWord ++ tailWord_1830247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830247).length < 2 ^ (prefixWord ++ tailWord_1830247).sum := by decide
  have hdescent : baseEnd_1830247 < baseStart_1830247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830256 : List Nat := [2, 1, 1, 1, 4, 2, 1, 10]
def baseStart_1830256 : Nat := 118140960795 + 1830256 * 2 ^ 59
def prefixEnd_1830256 : Nat := 4983230072969 + 3 ^ 40 * 1830256 * 2
def baseEnd_1830256 : Nat := 69614892501888618420949

theorem tailTrace_1830256 : CollatzResearch.WordTrace tailWord_1830256 prefixEnd_1830256 69614892501888618420949 := by
  unfold tailWord_1830256
  simp only [CollatzResearch.WordTrace]
  refine ⟨33377460228651284841959311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44503280304868379789279081 33377460228651284841959311)
  ·
    refine ⟨50066190342976927262938967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33377460228651284841959311 50066190342976927262938967)
    ·
      refine ⟨75099285514465390894408451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50066190342976927262938967 75099285514465390894408451)
      ·
        refine ⟨112648928271698086341612677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75099285514465390894408451 112648928271698086341612677)
        ·
          refine ⟨21121674050943391189052377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112648928271698086341612677 21121674050943391189052377)
          ·
            refine ⟨15841255538207543391789283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21121674050943391189052377 15841255538207543391789283)
            ·
              refine ⟨23761883307311315087683925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841255538207543391789283 23761883307311315087683925)
              ·
                refine ⟨69614892501888618420949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23761883307311315087683925 69614892501888618420949)
                ·
                  rfl

theorem cell22_1830256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_1830256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830256 prefixEnd_1830256 := by exact prefixLift 1830256
  have htrace : WordTrace (prefixWord ++ tailWord_1830256) baseStart_1830256 baseEnd_1830256 := by
    simpa [prefixWord, tailWord_1830256, baseEnd_1830256] using wordTrace_append hprefix tailTrace_1830256
  have hstable : (prefixWord ++ tailWord_1830256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830256).length < 2 ^ (prefixWord ++ tailWord_1830256).sum := by decide
  have hdescent : baseEnd_1830256 < baseStart_1830256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830273 : List Nat := [1, 2, 4, 3, 2, 10]
def baseStart_1830273 : Nat := 118140960795 + 1830273 * 2 ^ 59
def prefixEnd_1830273 : Nat := 4983230072969 + 3 ^ 40 * 1830273 * 2
def baseEnd_1830273 : Nat := 7735059900795249235969

theorem tailTrace_1830273 : CollatzResearch.WordTrace tailWord_1830273 prefixEnd_1830273 7735059900795249235969 := by
  unfold tailWord_1830273
  simp only [CollatzResearch.WordTrace]
  refine ⟨66755540498240981587287473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44503693665493987724858315 66755540498240981587287473)
  ·
    refine ⟨50066655373680736190465605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66755540498240981587287473 50066655373680736190465605)
    ·
      refine ⟨9387497882565138035712301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50066655373680736190465605 9387497882565138035712301)
      ·
        refine ⟨3520311705961926763392113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9387497882565138035712301 3520311705961926763392113)
        ·
          refine ⟨2640233779471445072544085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520311705961926763392113 2640233779471445072544085)
          ·
            refine ⟨7735059900795249235969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2640233779471445072544085 7735059900795249235969)
            ·
              rfl

theorem cell22_1830273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 10].length) (baseStart_1830273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830273 prefixEnd_1830273 := by exact prefixLift 1830273
  have htrace : WordTrace (prefixWord ++ tailWord_1830273) baseStart_1830273 baseEnd_1830273 := by
    simpa [prefixWord, tailWord_1830273, baseEnd_1830273] using wordTrace_append hprefix tailTrace_1830273
  have hstable : (prefixWord ++ tailWord_1830273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830273).length < 2 ^ (prefixWord ++ tailWord_1830273).sum := by decide
  have hdescent : baseEnd_1830273 < baseStart_1830273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830333 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1830333 : Nat := 118140960795 + 1830333 * 2 ^ 59
def prefixEnd_1830333 : Nat := 4983230072969 + 3 ^ 40 * 1830333 * 2
def baseEnd_1830333 : Nat := 626560391190595031613305

theorem tailTrace_1830333 : CollatzResearch.WordTrace tailWord_1830333 prefixEnd_1830333 626560391190595031613305 := by
  unfold tailWord_1830333
  simp only [CollatzResearch.WordTrace]
  refine ⟨66757728878023611834471653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44505152585349074556314435 66757728878023611834471653)
  ·
    refine ⟨12517074164629427218963435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66757728878023611834471653 12517074164629427218963435)
    ·
      refine ⟨18775611246944140828445153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12517074164629427218963435 18775611246944140828445153)
      ·
        refine ⟨14081708435208105621333865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18775611246944140828445153 14081708435208105621333865)
        ·
          refine ⟨10561281326406079216000399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14081708435208105621333865 10561281326406079216000399)
          ·
            refine ⟨15841921989609118824000599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561281326406079216000399 15841921989609118824000599)
            ·
              refine ⟨23762882984413678236000899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841921989609118824000599 23762882984413678236000899)
              ·
                refine ⟨35644324476620517354001349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23762882984413678236000899 35644324476620517354001349)
                ·
                  refine ⟨6683310839366347003875253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35644324476620517354001349 6683310839366347003875253)
                  ·
                    refine ⟨626560391190595031613305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6683310839366347003875253 626560391190595031613305)
                    ·
                      rfl

theorem cell22_1830333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1830333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830333 prefixEnd_1830333 := by exact prefixLift 1830333
  have htrace : WordTrace (prefixWord ++ tailWord_1830333) baseStart_1830333 baseEnd_1830333 := by
    simpa [prefixWord, tailWord_1830333, baseEnd_1830333] using wordTrace_append hprefix tailTrace_1830333
  have hstable : (prefixWord ++ tailWord_1830333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830333).length < 2 ^ (prefixWord ++ tailWord_1830333).sum := by decide
  have hdescent : baseEnd_1830333 < baseStart_1830333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830380 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1830380 : Nat := 118140960795 + 1830380 * 2 ^ 59
def prefixEnd_1830380 : Nat := 4983230072969 + 3 ^ 40 * 1830380 * 2
def baseEnd_1830380 : Nat := 208858826750367525229387

theorem tailTrace_1830380 : CollatzResearch.WordTrace tailWord_1830380 prefixEnd_1830380 208858826750367525229387 := by
  unfold tailWord_1830380
  simp only [CollatzResearch.WordTrace]
  refine ⟨33379721554426669430716297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44506295405902225907621729 33379721554426669430716297)
  ·
    refine ⟨25034791165820002073037223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33379721554426669430716297 25034791165820002073037223)
    ·
      refine ⟨37552186748730003109555835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25034791165820002073037223 37552186748730003109555835)
      ·
        refine ⟨56328280123095004664333753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37552186748730003109555835 56328280123095004664333753)
        ·
          refine ⟨42246210092321253498250315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56328280123095004664333753 42246210092321253498250315)
          ·
            refine ⟨63369315138481880247375473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42246210092321253498250315 63369315138481880247375473)
            ·
              refine ⟨47526986353861410185531605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63369315138481880247375473 47526986353861410185531605)
              ·
                refine ⟨1113913742668626801223397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47526986353861410185531605 1113913742668626801223397)
                ·
                  refine ⟨208858826750367525229387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1113913742668626801223397 208858826750367525229387)
                  ·
                    rfl

theorem cell22_1830380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1830380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830380 prefixEnd_1830380 := by exact prefixLift 1830380
  have htrace : WordTrace (prefixWord ++ tailWord_1830380) baseStart_1830380 baseEnd_1830380 := by
    simpa [prefixWord, tailWord_1830380, baseEnd_1830380] using wordTrace_append hprefix tailTrace_1830380
  have hstable : (prefixWord ++ tailWord_1830380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830380).length < 2 ^ (prefixWord ++ tailWord_1830380).sum := by decide
  have hdescent : baseEnd_1830380 < baseStart_1830380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830408 : List Nat := [2, 1, 3, 2, 1, 1, 3, 9]
def baseStart_1830408 : Nat := 118140960795 + 1830408 * 2 ^ 59
def prefixEnd_1830408 : Nat := 4983230072969 + 3 ^ 40 * 1830408 * 2
def baseEnd_1830408 : Nat := 69620673913702203998675

theorem tailTrace_1830408 : CollatzResearch.WordTrace tailWord_1830408 prefixEnd_1830408 69620673913702203998675 := by
  unfold tailWord_1830408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380232176375949821725939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44506976235167933095634585 33380232176375949821725939)
  ·
    refine ⟨50070348264563924732588909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33380232176375949821725939 50070348264563924732588909)
    ·
      refine ⟨18776380599211471774720841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50070348264563924732588909 18776380599211471774720841)
      ·
        refine ⟨14082285449408603831040631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18776380599211471774720841 14082285449408603831040631)
        ·
          refine ⟨21123428174112905746560947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082285449408603831040631 21123428174112905746560947)
          ·
            refine ⟨31685142261169358619841421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123428174112905746560947 31685142261169358619841421)
            ·
              refine ⟨11881928347938509482440533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31685142261169358619841421 11881928347938509482440533)
              ·
                refine ⟨69620673913702203998675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11881928347938509482440533 69620673913702203998675)
                ·
                  rfl

theorem cell22_1830408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_1830408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830408 prefixEnd_1830408 := by exact prefixLift 1830408
  have htrace : WordTrace (prefixWord ++ tailWord_1830408) baseStart_1830408 baseEnd_1830408 := by
    simpa [prefixWord, tailWord_1830408, baseEnd_1830408] using wordTrace_append hprefix tailTrace_1830408
  have hstable : (prefixWord ++ tailWord_1830408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830408).length < 2 ^ (prefixWord ++ tailWord_1830408).sum := by decide
  have hdescent : baseEnd_1830408 < baseStart_1830408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830483 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_1830483 : Nat := 118140960795 + 1830483 * 2 ^ 59
def prefixEnd_1830483 : Nat := 4983230072969 + 3 ^ 40 * 1830483 * 2
def baseEnd_1830483 : Nat := 626611739256044640362845

theorem tailTrace_1830483 : CollatzResearch.WordTrace tailWord_1830483 prefixEnd_1830483 626611739256044640362845 := by
  unfold tailWord_1830483
  simp only [CollatzResearch.WordTrace]
  refine ⟨66763199827480187452432103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44508799884986791634954735 66763199827480187452432103)
  ·
    refine ⟨100144799741220281178648155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66763199827480187452432103 100144799741220281178648155)
    ·
      refine ⟨150217199611830421767972233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100144799741220281178648155 150217199611830421767972233)
      ·
        refine ⟨112662899708872816325979175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150217199611830421767972233 112662899708872816325979175)
        ·
          refine ⟨168994349563309224488968763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112662899708872816325979175 168994349563309224488968763)
          ·
            refine ⟨253491524344963836733453145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168994349563309224488968763 253491524344963836733453145)
            ·
              refine ⟨190118643258722877550089859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253491524344963836733453145 190118643258722877550089859)
              ·
                refine ⟨285177964888084316325134789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190118643258722877550089859 285177964888084316325134789)
                ·
                  refine ⟨53470868416515809310962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285177964888084316325134789 53470868416515809310962773)
                  ·
                    refine ⟨626611739256044640362845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53470868416515809310962773 626611739256044640362845)
                    ·
                      rfl

theorem cell22_1830483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_1830483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830483 prefixEnd_1830483 := by exact prefixLift 1830483
  have htrace : WordTrace (prefixWord ++ tailWord_1830483) baseStart_1830483 baseEnd_1830483 := by
    simpa [prefixWord, tailWord_1830483, baseEnd_1830483] using wordTrace_append hprefix tailTrace_1830483
  have hstable : (prefixWord ++ tailWord_1830483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830483).length < 2 ^ (prefixWord ++ tailWord_1830483).sum := by decide
  have hdescent : baseEnd_1830483 < baseStart_1830483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830504 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_1830504 : Nat := 118140960795 + 1830504 * 2 ^ 59
def prefixEnd_1830504 : Nat := 4983230072969 + 3 ^ 40 * 1830504 * 2
def baseEnd_1830504 : Nat := 208872975995069195195927

theorem tailTrace_1830504 : CollatzResearch.WordTrace tailWord_1830504 prefixEnd_1830504 208872975995069195195927 := by
  unfold tailWord_1830504
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381982880202054019473283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44509310506936072025964377 33381982880202054019473283)
  ·
    refine ⟨50072974320303081029209925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33381982880202054019473283 50072974320303081029209925)
    ·
      refine ⟨9388682685056827692976861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50072974320303081029209925 9388682685056827692976861)
      ·
        refine ⟨3520756006896310384866323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9388682685056827692976861 3520756006896310384866323)
        ·
          refine ⟨5281134010344465577299485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520756006896310384866323 5281134010344465577299485)
          ·
            refine ⟨1980425253879174591487307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5281134010344465577299485 1980425253879174591487307)
            ·
              refine ⟨2970637880818761887230961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980425253879174591487307 2970637880818761887230961)
              ·
                refine ⟨2227978410614071415423221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970637880818761887230961 2227978410614071415423221)
                ·
                  refine ⟨208872975995069195195927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227978410614071415423221 208872975995069195195927)
                  ·
                    rfl

theorem cell22_1830504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_1830504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830504 prefixEnd_1830504 := by exact prefixLift 1830504
  have htrace : WordTrace (prefixWord ++ tailWord_1830504) baseStart_1830504 baseEnd_1830504 := by
    simpa [prefixWord, tailWord_1830504, baseEnd_1830504] using wordTrace_append hprefix tailTrace_1830504
  have hstable : (prefixWord ++ tailWord_1830504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830504).length < 2 ^ (prefixWord ++ tailWord_1830504).sum := by decide
  have hdescent : baseEnd_1830504 < baseStart_1830504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830560 : List Nat := [2, 1, 1, 4, 3, 1, 10]
def baseStart_1830560 : Nat := 118140960795 + 1830560 * 2 ^ 59
def prefixEnd_1830560 : Nat := 4983230072969 + 3 ^ 40 * 1830560 * 2
def baseEnd_1830560 : Nat := 23208818441838596525467

theorem tailTrace_1830560 : CollatzResearch.WordTrace tailWord_1830560 prefixEnd_1830560 23208818441838596525467 := by
  unfold tailWord_1830560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383004124100614801492567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44510672165467486401990089 33383004124100614801492567)
  ·
    refine ⟨50074506186150922202238851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33383004124100614801492567 50074506186150922202238851)
    ·
      refine ⟨75111759279226383303358277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50074506186150922202238851 75111759279226383303358277)
      ·
        refine ⟨14083454864854946869379677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75111759279226383303358277 14083454864854946869379677)
        ·
          refine ⟨5281295574320605076017379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14083454864854946869379677 5281295574320605076017379)
          ·
            refine ⟨7921943361480907614026069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281295574320605076017379 7921943361480907614026069)
            ·
              refine ⟨23208818441838596525467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7921943361480907614026069 23208818441838596525467)
              ·
                rfl

theorem cell22_1830560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 10].length) (baseStart_1830560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830560 prefixEnd_1830560 := by exact prefixLift 1830560
  have htrace : WordTrace (prefixWord ++ tailWord_1830560) baseStart_1830560 baseEnd_1830560 := by
    simpa [prefixWord, tailWord_1830560, baseEnd_1830560] using wordTrace_append hprefix tailTrace_1830560
  have hstable : (prefixWord ++ tailWord_1830560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830560).length < 2 ^ (prefixWord ++ tailWord_1830560).sum := by decide
  have hdescent : baseEnd_1830560 < baseStart_1830560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830581 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1830581 : Nat := 118140960795 + 1830581 * 2 ^ 59
def prefixEnd_1830581 : Nat := 4983230072969 + 3 ^ 40 * 1830581 * 2
def baseEnd_1830581 : Nat := 626645286658805051412545

theorem tailTrace_1830581 : CollatzResearch.WordTrace tailWord_1830581 prefixEnd_1830581 626645286658805051412545 := by
  unfold tailWord_1830581
  simp only [CollatzResearch.WordTrace]
  refine ⟨66766774181125150189499597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44511182787416766792999731 66766774181125150189499597)
  ·
    refine ⟨25037540317921931321062349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66766774181125150189499597 25037540317921931321062349)
    ·
      refine ⟨9389077619220724245398381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25037540317921931321062349 9389077619220724245398381)
      ·
        refine ⟨3520904107207771592024393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9389077619220724245398381 3520904107207771592024393)
        ·
          refine ⟨2640678080405828694018295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520904107207771592024393 2640678080405828694018295)
          ·
            refine ⟨3961017120608743041027443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640678080405828694018295 3961017120608743041027443)
            ·
              refine ⟨5941525680913114561541165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961017120608743041027443 5941525680913114561541165)
              ·
                refine ⟨2228072130342417960577937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5941525680913114561541165 2228072130342417960577937)
                ·
                  refine ⟨1671054097756813470433453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228072130342417960577937 1671054097756813470433453)
                  ·
                    refine ⟨626645286658805051412545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671054097756813470433453 626645286658805051412545)
                    ·
                      rfl

theorem cell22_1830581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1830581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830581 prefixEnd_1830581 := by exact prefixLift 1830581
  have htrace : WordTrace (prefixWord ++ tailWord_1830581) baseStart_1830581 baseEnd_1830581 := by
    simpa [prefixWord, tailWord_1830581, baseEnd_1830581] using wordTrace_append hprefix tailTrace_1830581
  have hstable : (prefixWord ++ tailWord_1830581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830581).length < 2 ^ (prefixWord ++ tailWord_1830581).sum := by decide
  have hdescent : baseEnd_1830581 < baseStart_1830581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830592 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_1830592 : Nat := 118140960795 + 1830592 * 2 ^ 59
def prefixEnd_1830592 : Nat := 4983230072969 + 3 ^ 40 * 1830592 * 2
def baseEnd_1830592 : Nat := 626649052183604689387511

theorem tailTrace_1830592 : CollatzResearch.WordTrace tailWord_1830592 prefixEnd_1830592 626649052183604689387511 := by
  unfold tailWord_1830592
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383587692042649534075015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44511450256056866045433353 33383587692042649534075015)
  ·
    refine ⟨50075381538063974301112523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33383587692042649534075015 50075381538063974301112523)
    ·
      refine ⟨75113072307095961451668785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50075381538063974301112523 75113072307095961451668785)
      ·
        refine ⟨56334804230321971088751589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75113072307095961451668785 56334804230321971088751589)
        ·
          refine ⟨10562775793185369579140923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56334804230321971088751589 10562775793185369579140923)
          ·
            refine ⟨15844163689778054368711385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562775793185369579140923 15844163689778054368711385)
            ·
              refine ⟨11883122767333540776533539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15844163689778054368711385 11883122767333540776533539)
              ·
                refine ⟨17824684151000311164800309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883122767333540776533539 17824684151000311164800309)
                ·
                  refine ⟨1671064139156279171700029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17824684151000311164800309 1671064139156279171700029)
                  ·
                    refine ⟨626649052183604689387511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671064139156279171700029 626649052183604689387511)
                    ·
                      rfl

theorem cell22_1830592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_1830592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830592 prefixEnd_1830592 := by exact prefixLift 1830592
  have htrace : WordTrace (prefixWord ++ tailWord_1830592) baseStart_1830592 baseEnd_1830592 := by
    simpa [prefixWord, tailWord_1830592, baseEnd_1830592] using wordTrace_append hprefix tailTrace_1830592
  have hstable : (prefixWord ++ tailWord_1830592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830592).length < 2 ^ (prefixWord ++ tailWord_1830592).sum := by decide
  have hdescent : baseEnd_1830592 < baseStart_1830592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830637 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1830637 : Nat := 118140960795 + 1830637 * 2 ^ 59
def prefixEnd_1830637 : Nat := 4983230072969 + 3 ^ 40 * 1830637 * 2
def baseEnd_1830637 : Nat := 626664456603239572012373

theorem tailTrace_1830637 : CollatzResearch.WordTrace tailWord_1830637 prefixEnd_1830637 626664456603239572012373 := by
  unfold tailWord_1830637
  simp only [CollatzResearch.WordTrace]
  refine ⟨66768816668922271753538165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44512544445948181169025443 66768816668922271753538165)
  ·
    refine ⟨6259576562711462976894203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66768816668922271753538165 6259576562711462976894203)
    ·
      refine ⟨9389364844067194465341305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6259576562711462976894203 9389364844067194465341305)
      ·
        refine ⟨7042023633050395849005979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9389364844067194465341305 7042023633050395849005979)
        ·
          refine ⟨10563035449575593773508969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042023633050395849005979 10563035449575593773508969)
          ·
            refine ⟨7922276587181695330131727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563035449575593773508969 7922276587181695330131727)
            ·
              refine ⟨11883414880772542995197591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922276587181695330131727 11883414880772542995197591)
              ·
                refine ⟨17825122321158814492796387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883414880772542995197591 17825122321158814492796387)
                ·
                  refine ⟨26737683481738221739194581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17825122321158814492796387 26737683481738221739194581)
                  ·
                    refine ⟨626664456603239572012373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26737683481738221739194581 626664456603239572012373)
                    ·
                      rfl

theorem cell22_1830637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1830637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830637 prefixEnd_1830637 := by exact prefixLift 1830637
  have htrace : WordTrace (prefixWord ++ tailWord_1830637) baseStart_1830637 baseEnd_1830637 := by
    simpa [prefixWord, tailWord_1830637, baseEnd_1830637] using wordTrace_append hprefix tailTrace_1830637
  have hstable : (prefixWord ++ tailWord_1830637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830637).length < 2 ^ (prefixWord ++ tailWord_1830637).sum := by decide
  have hdescent : baseEnd_1830637 < baseStart_1830637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830652 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_1830652 : Nat := 118140960795 + 1830652 * 2 ^ 59
def prefixEnd_1830652 : Nat := 4983230072969 + 3 ^ 40 * 1830652 * 2
def baseEnd_1830652 : Nat := 626669591409784532887327

theorem tailTrace_1830652 : CollatzResearch.WordTrace tailWord_1830652 prefixEnd_1830652 626669591409784532887327 := by
  unfold tailWord_1830652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33384681881933964657667105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44512909175911952876889473 33384681881933964657667105)
  ·
    refine ⟨25038511411450473493250329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33384681881933964657667105 25038511411450473493250329)
    ·
      refine ⟨18778883558587855119937747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25038511411450473493250329 18778883558587855119937747)
      ·
        refine ⟨28168325337881782679906621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18778883558587855119937747 28168325337881782679906621)
        ·
          refine ⟨10563122001705668504964983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28168325337881782679906621 10563122001705668504964983)
          ·
            refine ⟨15844683002558502757447475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563122001705668504964983 15844683002558502757447475)
            ·
              refine ⟨23767024503837754136171213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844683002558502757447475 23767024503837754136171213)
              ·
                refine ⟨8912634188939157801064205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23767024503837754136171213 8912634188939157801064205)
                ·
                  refine ⟨3342237820852184175399077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8912634188939157801064205 3342237820852184175399077)
                  ·
                    refine ⟨626669591409784532887327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3342237820852184175399077 626669591409784532887327)
                    ·
                      rfl

theorem cell22_1830652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_1830652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830652 prefixEnd_1830652 := by exact prefixLift 1830652
  have htrace : WordTrace (prefixWord ++ tailWord_1830652) baseStart_1830652 baseEnd_1830652 := by
    simpa [prefixWord, tailWord_1830652, baseEnd_1830652] using wordTrace_append hprefix tailTrace_1830652
  have hstable : (prefixWord ++ tailWord_1830652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830652).length < 2 ^ (prefixWord ++ tailWord_1830652).sum := by decide
  have hdescent : baseEnd_1830652 < baseStart_1830652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830684 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_1830684 : Nat := 118140960795 + 1830684 * 2 ^ 59
def prefixEnd_1830684 : Nat := 4983230072969 + 3 ^ 40 * 1830684 * 2
def baseEnd_1830684 : Nat := 208893515221249038695743

theorem tailTrace_1830684 : CollatzResearch.WordTrace tailWord_1830684 prefixEnd_1830684 208893515221249038695743 := by
  unfold tailWord_1830684
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385265449875999390249553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44513687266501332520332737 33385265449875999390249553)
  ·
    refine ⟨25038949087406999542687165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33385265449875999390249553 25038949087406999542687165)
    ·
      refine ⟨9389605907777624828507687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25038949087406999542687165 9389605907777624828507687)
      ·
        refine ⟨14084408861666437242761531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9389605907777624828507687 14084408861666437242761531)
        ·
          refine ⟨21126613292499655864142297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14084408861666437242761531 21126613292499655864142297)
          ·
            refine ⟨15844959969374741898106723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21126613292499655864142297 15844959969374741898106723)
            ·
              refine ⟨23767439954062112847160085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844959969374741898106723 23767439954062112847160085)
              ·
                refine ⟨1114098747846661539710629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23767439954062112847160085 1114098747846661539710629)
                ·
                  refine ⟨208893515221249038695743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114098747846661539710629 208893515221249038695743)
                  ·
                    rfl

theorem cell22_1830684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_1830684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830684 prefixEnd_1830684 := by exact prefixLift 1830684
  have htrace : WordTrace (prefixWord ++ tailWord_1830684) baseStart_1830684 baseEnd_1830684 := by
    simpa [prefixWord, tailWord_1830684, baseEnd_1830684] using wordTrace_append hprefix tailTrace_1830684
  have hstable : (prefixWord ++ tailWord_1830684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830684).length < 2 ^ (prefixWord ++ tailWord_1830684).sum := by decide
  have hdescent : baseEnd_1830684 < baseStart_1830684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830712 : List Nat := [2, 1, 2, 1, 3, 4, 1, 8]
def baseStart_1830712 : Nat := 118140960795 + 1830712 * 2 ^ 59
def prefixEnd_1830712 : Nat := 4983230072969 + 3 ^ 40 * 1830712 * 2
def baseEnd_1830712 : Nat := 69632236737329375154127

theorem tailTrace_1830712 : CollatzResearch.WordTrace tailWord_1830712 prefixEnd_1830712 69632236737329375154127 := by
  unfold tailWord_1830712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385776071825279781259195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44514368095767039708345593 33385776071825279781259195)
  ·
    refine ⟨50078664107737919671888793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33385776071825279781259195 50078664107737919671888793)
    ·
      refine ⟨37558998080803439753916595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50078664107737919671888793 37558998080803439753916595)
      ·
        refine ⟨56338497121205159630874893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37558998080803439753916595 56338497121205159630874893)
        ·
          refine ⟨21126936420451934861578085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56338497121205159630874893 21126936420451934861578085)
          ·
            refine ⟨3961300578834737786545891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21126936420451934861578085 3961300578834737786545891)
            ·
              refine ⟨5941950868252106679818837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961300578834737786545891 5941950868252106679818837)
              ·
                refine ⟨69632236737329375154127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5941950868252106679818837 69632236737329375154127)
                ·
                  rfl

theorem cell22_1830712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_1830712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830712 prefixEnd_1830712 := by exact prefixLift 1830712
  have htrace : WordTrace (prefixWord ++ tailWord_1830712) baseStart_1830712 baseEnd_1830712 := by
    simpa [prefixWord, tailWord_1830712, baseEnd_1830712] using wordTrace_append hprefix tailTrace_1830712
  have hstable : (prefixWord ++ tailWord_1830712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830712).length < 2 ^ (prefixWord ++ tailWord_1830712).sum := by decide
  have hdescent : baseEnd_1830712 < baseStart_1830712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830718 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1830718 : Nat := 118140960795 + 1830718 * 2 ^ 59
def prefixEnd_1830718 : Nat := 4983230072969 + 3 ^ 40 * 1830718 * 2
def baseEnd_1830718 : Nat := 208897394852860786912375

theorem tailTrace_1830718 : CollatzResearch.WordTrace tailWord_1830718 prefixEnd_1830718 208897394852860786912375 := by
  unfold tailWord_1830718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346471372703602823404601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44514513987752548391491205 8346471372703602823404601)
  ·
    refine ⟨6259853529527702117553451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8346471372703602823404601 6259853529527702117553451)
    ·
      refine ⟨9389780294291553176330177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6259853529527702117553451 9389780294291553176330177)
      ·
        refine ⟨7042335220718664882247633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9389780294291553176330177 7042335220718664882247633)
        ·
          refine ⟨5281751415538998661685725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7042335220718664882247633 5281751415538998661685725)
          ·
            refine ⟨1980656780827124498132147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5281751415538998661685725 1980656780827124498132147)
            ·
              refine ⟨2970985171240686747198221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980656780827124498132147 2970985171240686747198221)
              ·
                refine ⟨1114119439215257530199333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970985171240686747198221 1114119439215257530199333)
                ·
                  refine ⟨208897394852860786912375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114119439215257530199333 208897394852860786912375)
                  ·
                    rfl

theorem cell22_1830718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1830718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830718 prefixEnd_1830718 := by exact prefixLift 1830718
  have htrace : WordTrace (prefixWord ++ tailWord_1830718) baseStart_1830718 baseEnd_1830718 := by
    simpa [prefixWord, tailWord_1830718, baseEnd_1830718] using wordTrace_append hprefix tailTrace_1830718
  have hstable : (prefixWord ++ tailWord_1830718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830718).length < 2 ^ (prefixWord ++ tailWord_1830718).sum := by decide
  have hdescent : baseEnd_1830718 < baseStart_1830718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830791 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 5]
def baseStart_1830791 : Nat := 118140960795 + 1830791 * 2 ^ 59
def prefixEnd_1830791 : Nat := 4983230072969 + 3 ^ 40 * 1830791 * 2
def baseEnd_1830791 : Nat := 208905724650144834553967

theorem tailTrace_1830791 : CollatzResearch.WordTrace tailWord_1830791 prefixEnd_1830791 208905724650144834553967 := by
  unfold tailWord_1830791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66774433510364356054644227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44516289006909570703096151 66774433510364356054644227)
  ·
    refine ⟨100161650265546534081966341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66774433510364356054644227 100161650265546534081966341)
    ·
      refine ⟨18780309424789975140368689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100161650265546534081966341 18780309424789975140368689)
      ·
        refine ⟨14085232068592481355276517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18780309424789975140368689 14085232068592481355276517)
        ·
          refine ⟨2640981012861090254114347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14085232068592481355276517 2640981012861090254114347)
          ·
            refine ⟨3961471519291635381171521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640981012861090254114347 3961471519291635381171521)
            ·
              refine ⟨2971103639468726535878641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961471519291635381171521 2971103639468726535878641)
              ·
                refine ⟨2228327729601544901908981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971103639468726535878641 2228327729601544901908981)
                ·
                  refine ⟨208905724650144834553967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228327729601544901908981 208905724650144834553967)
                  ·
                    rfl

theorem cell22_1830791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 5].length) (baseStart_1830791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830791 prefixEnd_1830791 := by exact prefixLift 1830791
  have htrace : WordTrace (prefixWord ++ tailWord_1830791) baseStart_1830791 baseEnd_1830791 := by
    simpa [prefixWord, tailWord_1830791, baseEnd_1830791] using wordTrace_append hprefix tailTrace_1830791
  have hstable : (prefixWord ++ tailWord_1830791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830791).length < 2 ^ (prefixWord ++ tailWord_1830791).sum := by decide
  have hdescent : baseEnd_1830791 < baseStart_1830791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830847 : List Nat := [1, 1, 2, 2, 2, 1, 13]
def baseStart_1830847 : Nat := 118140960795 + 1830847 * 2 ^ 59
def prefixEnd_1830847 : Nat := 4983230072969 + 3 ^ 40 * 1830847 * 2
def baseEnd_1830847 : Nat := 23212457181291445343027

theorem tailTrace_1830847 : CollatzResearch.WordTrace tailWord_1830847 prefixEnd_1830847 23212457181291445343027 := by
  unfold tailWord_1830847
  simp only [CollatzResearch.WordTrace]
  refine ⟨66776475998161477618682795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44517650665440985079121863 66776475998161477618682795)
  ·
    refine ⟨100164713997242216428024193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66776475998161477618682795 100164713997242216428024193)
    ·
      refine ⟨75123535497931662321018145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100164713997242216428024193 75123535497931662321018145)
      ·
        refine ⟨56342651623448746740763609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75123535497931662321018145 56342651623448746740763609)
        ·
          refine ⟨42256988717586560055572707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56342651623448746740763609 42256988717586560055572707)
          ·
            refine ⟨63385483076379840083359061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42256988717586560055572707 63385483076379840083359061)
            ·
              refine ⟨23212457181291445343027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 63385483076379840083359061 23212457181291445343027)
              ·
                rfl

theorem cell22_1830847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 13].length) (baseStart_1830847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830847 prefixEnd_1830847 := by exact prefixLift 1830847
  have htrace : WordTrace (prefixWord ++ tailWord_1830847) baseStart_1830847 baseEnd_1830847 := by
    simpa [prefixWord, tailWord_1830847, baseEnd_1830847] using wordTrace_append hprefix tailTrace_1830847
  have hstable : (prefixWord ++ tailWord_1830847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830847).length < 2 ^ (prefixWord ++ tailWord_1830847).sum := by decide
  have hdescent : baseEnd_1830847 < baseStart_1830847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830909 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1830909 : Nat := 118140960795 + 1830909 * 2 ^ 59
def prefixEnd_1830909 : Nat := 4983230072969 + 3 ^ 40 * 1830909 * 2
def baseEnd_1830909 : Nat := 208919189253973843070513

theorem tailTrace_1830909 : CollatzResearch.WordTrace tailWord_1830909 prefixEnd_1830909 208919189253973843070513 := by
  unfold tailWord_1830909
  simp only [CollatzResearch.WordTrace]
  refine ⟨66778737323936862207439781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44519158215957908138293187 66778737323936862207439781)
  ·
    refine ⟨12521013248238161663894959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66778737323936862207439781 12521013248238161663894959)
    ·
      refine ⟨18781519872357242495842439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521013248238161663894959 18781519872357242495842439)
      ·
        refine ⟨28172279808535863743763659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18781519872357242495842439 28172279808535863743763659)
        ·
          refine ⟨42258419712803795615645489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28172279808535863743763659 42258419712803795615645489)
          ·
            refine ⟨31693814784602846711734117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42258419712803795615645489 31693814784602846711734117)
            ·
              refine ⟨5942590272113033758450147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31693814784602846711734117 5942590272113033758450147)
              ·
                refine ⟨8913885408169550637675221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942590272113033758450147 8913885408169550637675221)
                ·
                  refine ⟨208919189253973843070513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8913885408169550637675221 208919189253973843070513)
                  ·
                    rfl

theorem cell22_1830909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1830909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830909 prefixEnd_1830909 := by exact prefixLift 1830909
  have htrace : WordTrace (prefixWord ++ tailWord_1830909) baseStart_1830909 baseEnd_1830909 := by
    simpa [prefixWord, tailWord_1830909, baseEnd_1830909] using wordTrace_append hprefix tailTrace_1830909
  have hstable : (prefixWord ++ tailWord_1830909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830909).length < 2 ^ (prefixWord ++ tailWord_1830909).sum := by decide
  have hdescent : baseEnd_1830909 < baseStart_1830909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830924 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_1830924 : Nat := 118140960795 + 1830924 * 2 ^ 59
def prefixEnd_1830924 : Nat := 4983230072969 + 3 ^ 40 * 1830924 * 2
def baseEnd_1830924 : Nat := 626762702568466490086493

theorem tailTrace_1830924 : CollatzResearch.WordTrace tailWord_1830924 prefixEnd_1830924 626762702568466490086493 := by
  unfold tailWord_1830924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33389642209441259884617913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44519522945921679846157217 33389642209441259884617913)
  ·
    refine ⟨25042231657080944913463435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33389642209441259884617913 25042231657080944913463435)
    ·
      refine ⟨37563347485621417370195153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25042231657080944913463435 37563347485621417370195153)
      ·
        refine ⟨28172510614216063027646365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37563347485621417370195153 28172510614216063027646365)
        ·
          refine ⟨10564691480331023635367387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28172510614216063027646365 10564691480331023635367387)
          ·
            refine ⟨15847037220496535453051081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10564691480331023635367387 15847037220496535453051081)
            ·
              refine ⟨11885277915372401589788311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15847037220496535453051081 11885277915372401589788311)
              ·
                refine ⟨17827916873058602384682467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11885277915372401589788311 17827916873058602384682467)
                ·
                  refine ⟨26741875309587903577023701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17827916873058602384682467 26741875309587903577023701)
                  ·
                    refine ⟨626762702568466490086493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26741875309587903577023701 626762702568466490086493)
                    ·
                      rfl

theorem cell22_1830924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_1830924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830924 prefixEnd_1830924 := by exact prefixLift 1830924
  have htrace : WordTrace (prefixWord ++ tailWord_1830924) baseStart_1830924 baseEnd_1830924 := by
    simpa [prefixWord, tailWord_1830924, baseEnd_1830924] using wordTrace_append hprefix tailTrace_1830924
  have hstable : (prefixWord ++ tailWord_1830924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830924).length < 2 ^ (prefixWord ++ tailWord_1830924).sum := by decide
  have hdescent : baseEnd_1830924 < baseStart_1830924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830926 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1830926 : Nat := 118140960795 + 1830926 * 2 ^ 59
def prefixEnd_1830926 : Nat := 4983230072969 + 3 ^ 40 * 1830926 * 2
def baseEnd_1830926 : Nat := 208921129069779717178829

theorem tailTrace_1830926 : CollatzResearch.WordTrace tailWord_1830926 prefixEnd_1830926 208921129069779717178829 := by
  unfold tailWord_1830926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8347419670609409263851079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44519571576583516073872421 8347419670609409263851079)
  ·
    refine ⟨12521129505914113895776619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8347419670609409263851079 12521129505914113895776619)
    ·
      refine ⟨18781694258871170843664929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521129505914113895776619 18781694258871170843664929)
      ·
        refine ⟨14086270694153378132748697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18781694258871170843664929 14086270694153378132748697)
        ·
          refine ⟨10564703020615033599561523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14086270694153378132748697 10564703020615033599561523)
          ·
            refine ⟨15847054530922550399342285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10564703020615033599561523 15847054530922550399342285)
            ·
              refine ⟨5942645449095956399753357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15847054530922550399342285 5942645449095956399753357)
              ·
                refine ⟨2228492043410983649907509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5942645449095956399753357 2228492043410983649907509)
                ·
                  refine ⟨208921129069779717178829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228492043410983649907509 208921129069779717178829)
                  ·
                    rfl

theorem cell22_1830926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1830926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830926 prefixEnd_1830926 := by exact prefixLift 1830926
  have htrace : WordTrace (prefixWord ++ tailWord_1830926) baseStart_1830926 baseEnd_1830926 := by
    simpa [prefixWord, tailWord_1830926, baseEnd_1830926] using wordTrace_append hprefix tailTrace_1830926
  have hstable : (prefixWord ++ tailWord_1830926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830926).length < 2 ^ (prefixWord ++ tailWord_1830926).sum := by decide
  have hdescent : baseEnd_1830926 < baseStart_1830926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 4]
def baseStart_1830971 : Nat := 118140960795 + 1830971 * 2 ^ 59
def prefixEnd_1830971 : Nat := 4983230072969 + 3 ^ 40 * 1830971 * 2
def baseEnd_1830971 : Nat := 208926263876324678053783

theorem tailTrace_1830971 : CollatzResearch.WordTrace tailWord_1830971 prefixEnd_1830971 208926263876324678053783 := by
  unfold tailWord_1830971
  simp only [CollatzResearch.WordTrace]
  refine ⟨66780998649712246796196767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44520665766474831197464511 66780998649712246796196767)
  ·
    refine ⟨100171497974568370194295151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66780998649712246796196767 100171497974568370194295151)
    ·
      refine ⟨150257246961852555291442727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100171497974568370194295151 150257246961852555291442727)
      ·
        refine ⟨225385870442778832937164091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150257246961852555291442727 225385870442778832937164091)
        ·
          refine ⟨338078805664168249405746137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225385870442778832937164091 338078805664168249405746137)
          ·
            refine ⟨253559104248126187054309603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338078805664168249405746137 253559104248126187054309603)
            ·
              refine ⟨380338656372189280581464405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253559104248126187054309603 380338656372189280581464405)
              ·
                refine ⟨1114273407340398282953509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 380338656372189280581464405 1114273407340398282953509)
                ·
                  refine ⟨208926263876324678053783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114273407340398282953509 208926263876324678053783)
                  ·
                    rfl

theorem cell22_1830971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 4].length) (baseStart_1830971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830971 prefixEnd_1830971 := by exact prefixLift 1830971
  have htrace : WordTrace (prefixWord ++ tailWord_1830971) baseStart_1830971 baseEnd_1830971 := by
    simpa [prefixWord, tailWord_1830971, baseEnd_1830971] using wordTrace_append hprefix tailTrace_1830971
  have hstable : (prefixWord ++ tailWord_1830971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830971).length < 2 ^ (prefixWord ++ tailWord_1830971).sum := by decide
  have hdescent : baseEnd_1830971 < baseStart_1830971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830986 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1830986 : Nat := 118140960795 + 1830986 * 2 ^ 59
def prefixEnd_1830986 : Nat := 4983230072969 + 3 ^ 40 * 1830986 * 2
def baseEnd_1830986 : Nat := 626783926435518995036303

theorem tailTrace_1830986 : CollatzResearch.WordTrace tailWord_1830986 prefixEnd_1830986 626783926435518995036303 := by
  unfold tailWord_1830986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695386436164476089498203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44521030496438602905328541 16695386436164476089498203)
  ·
    refine ⟨25043079654246714134247305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16695386436164476089498203 25043079654246714134247305)
    ·
      refine ⟨18782309740685035600685479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25043079654246714134247305 18782309740685035600685479)
      ·
        refine ⟨28173464611027553401028219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18782309740685035600685479 28173464611027553401028219)
        ·
          refine ⟨42260196916541330101542329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28173464611027553401028219 42260196916541330101542329)
          ·
            refine ⟨31695147687405997576156747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42260196916541330101542329 31695147687405997576156747)
            ·
              refine ⟨47542721531108996364235121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31695147687405997576156747 47542721531108996364235121)
              ·
                refine ⟨35657041148331747273176341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47542721531108996364235121 35657041148331747273176341)
                ·
                  refine ⟨1671423803828050653430141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35657041148331747273176341 1671423803828050653430141)
                  ·
                    refine ⟨626783926435518995036303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671423803828050653430141 626783926435518995036303)
                    ·
                      rfl

theorem cell22_1830986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1830986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830986 prefixEnd_1830986 := by exact prefixLift 1830986
  have htrace : WordTrace (prefixWord ++ tailWord_1830986) baseStart_1830986 baseEnd_1830986 := by
    simpa [prefixWord, tailWord_1830986, baseEnd_1830986] using wordTrace_append hprefix tailTrace_1830986
  have hstable : (prefixWord ++ tailWord_1830986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830986).length < 2 ^ (prefixWord ++ tailWord_1830986).sum := by decide
  have hdescent : baseEnd_1830986 < baseStart_1830986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830999 : List Nat := [1, 1, 3, 2, 2, 1, 2, 10]
def baseStart_1830999 : Nat := 118140960795 + 1830999 * 2 ^ 59
def prefixEnd_1830999 : Nat := 4983230072969 + 3 ^ 40 * 1830999 * 2
def baseEnd_1830999 : Nat := 69643152955687921606807

theorem tailTrace_1830999 : CollatzResearch.WordTrace tailWord_1830999 prefixEnd_1830999 69643152955687921606807 := by
  unfold tailWord_1830999
  simp only [CollatzResearch.WordTrace]
  refine ⟨66782019893610807578216051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44521346595740538385477367 66782019893610807578216051)
  ·
    refine ⟨100173029840416211367324077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66782019893610807578216051 100173029840416211367324077)
    ·
      refine ⟨37564886190156079262746529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100173029840416211367324077 37564886190156079262746529)
      ·
        refine ⟨28173664642617059447059897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37564886190156079262746529 28173664642617059447059897)
        ·
          refine ⟨21130248481962794585294923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28173664642617059447059897 21130248481962794585294923)
          ·
            refine ⟨31695372722944191877942385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21130248481962794585294923 31695372722944191877942385)
            ·
              refine ⟨23771529542208143908456789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31695372722944191877942385 23771529542208143908456789)
              ·
                refine ⟨69643152955687921606807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23771529542208143908456789 69643152955687921606807)
                ·
                  rfl

theorem cell22_1830999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 10].length) (baseStart_1830999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1830999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1830999 prefixEnd_1830999 := by exact prefixLift 1830999
  have htrace : WordTrace (prefixWord ++ tailWord_1830999) baseStart_1830999 baseEnd_1830999 := by
    simpa [prefixWord, tailWord_1830999, baseEnd_1830999] using wordTrace_append hprefix tailTrace_1830999
  have hstable : (prefixWord ++ tailWord_1830999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830999).length < 2 ^ (prefixWord ++ tailWord_1830999).sum := by decide
  have hdescent : baseEnd_1830999 < baseStart_1830999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831005 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 4]
def baseStart_1831005 : Nat := 118140960795 + 1831005 * 2 ^ 59
def prefixEnd_1831005 : Nat := 4983230072969 + 3 ^ 40 * 1831005 * 2
def baseEnd_1831005 : Nat := 208930143507936426270415

theorem tailTrace_1831005 : CollatzResearch.WordTrace tailWord_1831005 prefixEnd_1831005 208930143507936426270415 := by
  unfold tailWord_1831005
  simp only [CollatzResearch.WordTrace]
  refine ⟨66782238731589070602934469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44521492487726047068622979 66782238731589070602934469)
  ·
    refine ⟨12521669762172950738050213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66782238731589070602934469 12521669762172950738050213)
    ·
      refine ⟨2347813080407428263384415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12521669762172950738050213 2347813080407428263384415)
      ·
        refine ⟨3521719620611142395076623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347813080407428263384415 3521719620611142395076623)
        ·
          refine ⟨5282579430916713592614935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521719620611142395076623 5282579430916713592614935)
          ·
            refine ⟨7923869146375070388922403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282579430916713592614935 7923869146375070388922403)
            ·
              refine ⟨11885803719562605583383605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923869146375070388922403 11885803719562605583383605)
              ·
                refine ⟨1114294098708994273442213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11885803719562605583383605 1114294098708994273442213)
                ·
                  refine ⟨208930143507936426270415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114294098708994273442213 208930143507936426270415)
                  ·
                    rfl

theorem cell22_1831005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_1831005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831005 prefixEnd_1831005 := by exact prefixLift 1831005
  have htrace : WordTrace (prefixWord ++ tailWord_1831005) baseStart_1831005 baseEnd_1831005 := by
    simpa [prefixWord, tailWord_1831005, baseEnd_1831005] using wordTrace_append hprefix tailTrace_1831005
  have hstable : (prefixWord ++ tailWord_1831005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831005).length < 2 ^ (prefixWord ++ tailWord_1831005).sum := by decide
  have hdescent : baseEnd_1831005 < baseStart_1831005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831020 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_1831020 : Nat := 118140960795 + 1831020 * 2 ^ 59
def prefixEnd_1831020 : Nat := 4983230072969 + 3 ^ 40 * 1831020 * 2
def baseEnd_1831020 : Nat := 626795565330354239686199

theorem tailTrace_1831020 : CollatzResearch.WordTrace tailWord_1831020 prefixEnd_1831020 626795565330354239686199 := by
  unfold tailWord_1831020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33391392913267364082365257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44521857217689818776487009 33391392913267364082365257)
  ·
    refine ⟨25043544684950523061773943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33391392913267364082365257 25043544684950523061773943)
    ·
      refine ⟨37565317027425784592660915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25043544684950523061773943 37565317027425784592660915)
      ·
        refine ⟨56347975541138676888991373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37565317027425784592660915 56347975541138676888991373)
        ·
          refine ⟨21130490827927003833371765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56347975541138676888991373 21130490827927003833371765)
          ·
            refine ⟨1980983515118156609378603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21130490827927003833371765 1980983515118156609378603)
            ·
              refine ⟨2971475272677234914067905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980983515118156609378603 2971475272677234914067905)
              ·
                refine ⟨2228606454507926185550929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971475272677234914067905 2228606454507926185550929)
                ·
                  refine ⟨1671454840880944639163197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228606454507926185550929 1671454840880944639163197)
                  ·
                    refine ⟨626795565330354239686199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671454840880944639163197 626795565330354239686199)
                    ·
                      rfl

theorem cell22_1831020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_1831020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831020 prefixEnd_1831020 := by exact prefixLift 1831020
  have htrace : WordTrace (prefixWord ++ tailWord_1831020) baseStart_1831020 baseEnd_1831020 := by
    simpa [prefixWord, tailWord_1831020, baseEnd_1831020] using wordTrace_append hprefix tailTrace_1831020
  have hstable : (prefixWord ++ tailWord_1831020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831020).length < 2 ^ (prefixWord ++ tailWord_1831020).sum := by decide
  have hdescent : baseEnd_1831020 < baseStart_1831020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831091 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 3, 4]
def baseStart_1831091 : Nat := 118140960795 + 1831091 * 2 ^ 59
def prefixEnd_1831091 : Nat := 4983230072969 + 3 ^ 40 * 1831091 * 2
def baseEnd_1831091 : Nat := 626819870081333721160981

theorem tailTrace_1831091 : CollatzResearch.WordTrace tailWord_1831091 prefixEnd_1831091 626819870081333721160981 := by
  unfold tailWord_1831091
  simp only [CollatzResearch.WordTrace]
  refine ⟨66785375409277507290565127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44523583606185004860376751 66785375409277507290565127)
  ·
    refine ⟨100178063113916260935847691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66785375409277507290565127 100178063113916260935847691)
    ·
      refine ⟨150267094670874391403771537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100178063113916260935847691 150267094670874391403771537)
      ·
        refine ⟨112700321003155793552828653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150267094670874391403771537 112700321003155793552828653)
        ·
          refine ⟨42262620376183422582310745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112700321003155793552828653 42262620376183422582310745)
          ·
            refine ⟨31696965282137566936733059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42262620376183422582310745 31696965282137566936733059)
            ·
              refine ⟨47545447923206350405099589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31696965282137566936733059 47545447923206350405099589)
              ·
                refine ⟨8914771485601190700956173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47545447923206350405099589 8914771485601190700956173)
                ·
                  refine ⟨3343039307100446512858565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8914771485601190700956173 3343039307100446512858565)
                  ·
                    refine ⟨626819870081333721160981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343039307100446512858565 626819870081333721160981)
                    ·
                      rfl

theorem cell22_1831091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 4].length) (baseStart_1831091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831091 prefixEnd_1831091 := by exact prefixLift 1831091
  have htrace : WordTrace (prefixWord ++ tailWord_1831091) baseStart_1831091 baseEnd_1831091 := by
    simpa [prefixWord, tailWord_1831091, baseEnd_1831091] using wordTrace_append hprefix tailTrace_1831091
  have hstable : (prefixWord ++ tailWord_1831091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831091).length < 2 ^ (prefixWord ++ tailWord_1831091).sum := by decide
  have hdescent : baseEnd_1831091 < baseStart_1831091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831095 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 5]
def baseStart_1831095 : Nat := 118140960795 + 1831095 * 2 ^ 59
def prefixEnd_1831095 : Nat := 4983230072969 + 3 ^ 40 * 1831095 * 2
def baseEnd_1831095 : Nat := 208940413121026348020323

theorem tailTrace_1831095 : CollatzResearch.WordTrace tailWord_1831095 prefixEnd_1831095 208940413121026348020323 := by
  unfold tailWord_1831095
  simp only [CollatzResearch.WordTrace]
  refine ⟨66785521301263015973710739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44523680867508677315807159 66785521301263015973710739)
  ·
    refine ⟨100178281951894523960566109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66785521301263015973710739 100178281951894523960566109)
    ·
      refine ⟨37566855731960446485212291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100178281951894523960566109 37566855731960446485212291)
      ·
        refine ⟨56350283597940669727818437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37566855731960446485212291 56350283597940669727818437)
        ·
          refine ⟨10565678174613875573965957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56350283597940669727818437 10565678174613875573965957)
          ·
            refine ⟨1981064657740101670118617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10565678174613875573965957 1981064657740101670118617)
            ·
              refine ⟨1485798493305076252588963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981064657740101670118617 1485798493305076252588963)
              ·
                refine ⟨2228697739957614378883445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485798493305076252588963 2228697739957614378883445)
                ·
                  refine ⟨208940413121026348020323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228697739957614378883445 208940413121026348020323)
                  ·
                    rfl

theorem cell22_1831095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 5].length) (baseStart_1831095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831095 prefixEnd_1831095 := by exact prefixLift 1831095
  have htrace : WordTrace (prefixWord ++ tailWord_1831095) baseStart_1831095 baseEnd_1831095 := by
    simpa [prefixWord, tailWord_1831095, baseEnd_1831095] using wordTrace_append hprefix tailTrace_1831095
  have hstable : (prefixWord ++ tailWord_1831095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831095).length < 2 ^ (prefixWord ++ tailWord_1831095).sum := by decide
  have hdescent : baseEnd_1831095 < baseStart_1831095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831121 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1831121 : Nat := 118140960795 + 1831121 * 2 ^ 59
def prefixEnd_1831121 : Nat := 4983230072969 + 3 ^ 40 * 1831121 * 2
def baseEnd_1831121 : Nat := 626830139694423642910889

theorem tailTrace_1831121 : CollatzResearch.WordTrace tailWord_1831121 prefixEnd_1831121 626830139694423642910889 := by
  unfold tailWord_1831121
  simp only [CollatzResearch.WordTrace]
  refine ⟨66786469599168822414157217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44524313066112548276104811 66786469599168822414157217)
  ·
    refine ⟨50089852199376616810617913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66786469599168822414157217 50089852199376616810617913)
    ·
      refine ⟨37567389149532462607963435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50089852199376616810617913 37567389149532462607963435)
      ·
        refine ⟨56351083724298693911945153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37567389149532462607963435 56351083724298693911945153)
        ·
          refine ⟨42263312793224020433958865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56351083724298693911945153 42263312793224020433958865)
          ·
            refine ⟨31697484594918015325469149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42263312793224020433958865 31697484594918015325469149)
            ·
              refine ⟨11886556723094255747050931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31697484594918015325469149 11886556723094255747050931)
              ·
                refine ⟨17829835084641383620576397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886556723094255747050931 17829835084641383620576397)
                ·
                  refine ⟨6686188156740518857716149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17829835084641383620576397 6686188156740518857716149)
                  ·
                    refine ⟨626830139694423642910889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6686188156740518857716149 626830139694423642910889)
                    ·
                      rfl

theorem cell22_1831121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1831121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831121 prefixEnd_1831121 := by exact prefixLift 1831121
  have htrace : WordTrace (prefixWord ++ tailWord_1831121) baseStart_1831121 baseEnd_1831121 := by
    simpa [prefixWord, tailWord_1831121, baseEnd_1831121] using wordTrace_append hprefix tailTrace_1831121
  have hstable : (prefixWord ++ tailWord_1831121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831121).length < 2 ^ (prefixWord ++ tailWord_1831121).sum := by decide
  have hdescent : baseEnd_1831121 < baseStart_1831121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831170 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1831170 : Nat := 118140960795 + 1831170 * 2 ^ 59
def prefixEnd_1831170 : Nat := 4983230072969 + 3 ^ 40 * 1831170 * 2
def baseEnd_1831170 : Nat := 626846913395803848435739

theorem tailTrace_1831170 : CollatzResearch.WordTrace tailWord_1831170 prefixEnd_1831170 626846913395803848435739 := by
  unfold tailWord_1831170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697064193997825945672741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44525504517327535855127309 16697064193997825945672741)
  ·
    refine ⟨3130699536374592364813639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16697064193997825945672741 3130699536374592364813639)
    ·
      refine ⟨4696049304561888547220459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130699536374592364813639 4696049304561888547220459)
      ·
        refine ⟨7044073956842832820830689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696049304561888547220459 7044073956842832820830689)
        ·
          refine ⟨5283055467632124615623017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7044073956842832820830689 5283055467632124615623017)
          ·
            refine ⟨3962291600724093461717263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5283055467632124615623017 3962291600724093461717263)
            ·
              refine ⟨5943437401086140192575895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962291600724093461717263 5943437401086140192575895)
              ·
                refine ⟨8915156101629210288863843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943437401086140192575895 8915156101629210288863843)
                ·
                  refine ⟨13372734152443815433295765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915156101629210288863843 13372734152443815433295765)
                  ·
                    refine ⟨626846913395803848435739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13372734152443815433295765 626846913395803848435739)
                    ·
                      rfl

theorem cell22_1831170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1831170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831170 prefixEnd_1831170 := by exact prefixLift 1831170
  have htrace : WordTrace (prefixWord ++ tailWord_1831170) baseStart_1831170 baseEnd_1831170 := by
    simpa [prefixWord, tailWord_1831170, baseEnd_1831170] using wordTrace_append hprefix tailTrace_1831170
  have hstable : (prefixWord ++ tailWord_1831170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831170).length < 2 ^ (prefixWord ++ tailWord_1831170).sum := by decide
  have hdescent : baseEnd_1831170 < baseStart_1831170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831200 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_1831200 : Nat := 118140960795 + 1831200 * 2 ^ 59
def prefixEnd_1831200 : Nat := 4983230072969 + 3 ^ 40 * 1831200 * 2
def baseEnd_1831200 : Nat := 626857183008893770185647

theorem tailTrace_1831200 : CollatzResearch.WordTrace tailWord_1831200 prefixEnd_1831200 626857183008893770185647 := by
  unfold tailWord_1831200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33394675482941309453141527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44526233977255079270855369 33394675482941309453141527)
  ·
    refine ⟨50092013224411964179712291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33394675482941309453141527 50092013224411964179712291)
    ·
      refine ⟨75138019836617946269568437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50092013224411964179712291 75138019836617946269568437)
      ·
        refine ⟨7044189359682932462772041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75138019836617946269568437 7044189359682932462772041)
        ·
          refine ⟨5283142019762199347079031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7044189359682932462772041 5283142019762199347079031)
          ·
            refine ⟨7924713029643299020618547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283142019762199347079031 7924713029643299020618547)
            ·
              refine ⟨11887069544464948530927821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924713029643299020618547 11887069544464948530927821)
              ·
                refine ⟨4457651079174355699097933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11887069544464948530927821 4457651079174355699097933)
                ·
                  refine ⟨1671619154690383387161725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4457651079174355699097933 1671619154690383387161725)
                  ·
                    refine ⟨626857183008893770185647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671619154690383387161725 626857183008893770185647)
                    ·
                      rfl

theorem cell22_1831200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_1831200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831200 prefixEnd_1831200 := by exact prefixLift 1831200
  have htrace : WordTrace (prefixWord ++ tailWord_1831200) baseStart_1831200 baseEnd_1831200 := by
    simpa [prefixWord, tailWord_1831200, baseEnd_1831200] using wordTrace_append hprefix tailTrace_1831200
  have hstable : (prefixWord ++ tailWord_1831200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831200).length < 2 ^ (prefixWord ++ tailWord_1831200).sum := by decide
  have hdescent : baseEnd_1831200 < baseStart_1831200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831264 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_1831264 : Nat := 118140960795 + 1831264 * 2 ^ 59
def prefixEnd_1831264 : Nat := 4983230072969 + 3 ^ 40 * 1831264 * 2
def baseEnd_1831264 : Nat := 208959697172272978861817

theorem tailTrace_1831264 : CollatzResearch.WordTrace tailWord_1831264 prefixEnd_1831264 208959697172272978861817 := by
  unfold tailWord_1831264
  simp only [CollatzResearch.WordTrace]
  refine ⟨33395842618825378918306423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44527790158433838557741897 33395842618825378918306423)
  ·
    refine ⟨50093763928238068377459635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33395842618825378918306423 50093763928238068377459635)
    ·
      refine ⟨75140645892357102566189453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50093763928238068377459635 75140645892357102566189453)
      ·
        refine ⟨28177742209633913462321045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75140645892357102566189453 28177742209633913462321045)
        ·
          refine ⟨1320831666076589693546299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28177742209633913462321045 1320831666076589693546299)
          ·
            refine ⟨1981247499114884540319449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320831666076589693546299 1981247499114884540319449)
            ·
              refine ⟨1485935624336163405239587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981247499114884540319449 1485935624336163405239587)
              ·
                refine ⟨2228903436504245107859381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485935624336163405239587 2228903436504245107859381)
                ·
                  refine ⟨208959697172272978861817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228903436504245107859381 208959697172272978861817)
                  ·
                    rfl

theorem cell22_1831264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_1831264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831264 prefixEnd_1831264 := by exact prefixLift 1831264
  have htrace : WordTrace (prefixWord ++ tailWord_1831264) baseStart_1831264 baseEnd_1831264 := by
    simpa [prefixWord, tailWord_1831264, baseEnd_1831264] using wordTrace_append hprefix tailTrace_1831264
  have hstable : (prefixWord ++ tailWord_1831264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831264).length < 2 ^ (prefixWord ++ tailWord_1831264).sum := by decide
  have hdescent : baseEnd_1831264 < baseStart_1831264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831273 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1831273 : Nat := 118140960795 + 1831273 * 2 ^ 59
def prefixEnd_1831273 : Nat := 4983230072969 + 3 ^ 40 * 1831273 * 2
def baseEnd_1831273 : Nat := 626882172400745913110423

theorem tailTrace_1831273 : CollatzResearch.WordTrace tailWord_1831273 prefixEnd_1831273 626882172400745913110423 := by
  unfold tailWord_1831273
  simp only [CollatzResearch.WordTrace]
  refine ⟨66792013494618152373690473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44528008996412101582460315 66792013494618152373690473)
  ·
    refine ⟨50094010120963614280267855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66792013494618152373690473 50094010120963614280267855)
    ·
      refine ⟨75141015181445421420401783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50094010120963614280267855 75141015181445421420401783)
      ·
        refine ⟨112711522772168132130602675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75141015181445421420401783 112711522772168132130602675)
        ·
          refine ⟨169067284158252198195904013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112711522772168132130602675 169067284158252198195904013)
          ·
            refine ⟨63400231559344574323464005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169067284158252198195904013 63400231559344574323464005)
            ·
              refine ⟨11887543417377107685649501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63400231559344574323464005 11887543417377107685649501)
              ·
                refine ⟨4457828781516415382118563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11887543417377107685649501 4457828781516415382118563)
                ·
                  refine ⟨6686743172274623073177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457828781516415382118563 6686743172274623073177845)
                  ·
                    refine ⟨626882172400745913110423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6686743172274623073177845 626882172400745913110423)
                    ·
                      rfl

theorem cell22_1831273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1831273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831273 prefixEnd_1831273 := by exact prefixLift 1831273
  have htrace : WordTrace (prefixWord ++ tailWord_1831273) baseStart_1831273 baseEnd_1831273 := by
    simpa [prefixWord, tailWord_1831273, baseEnd_1831273] using wordTrace_append hprefix tailTrace_1831273
  have hstable : (prefixWord ++ tailWord_1831273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831273).length < 2 ^ (prefixWord ++ tailWord_1831273).sum := by decide
  have hdescent : baseEnd_1831273 < baseStart_1831273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831305 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_1831305 : Nat := 118140960795 + 1831305 * 2 ^ 59
def prefixEnd_1831305 : Nat := 4983230072969 + 3 ^ 40 * 1831305 * 2
def baseEnd_1831305 : Nat := 626893126654708496310325

theorem tailTrace_1831305 : CollatzResearch.WordTrace tailWord_1831305 prefixEnd_1831305 626893126654708496310325 := by
  unfold tailWord_1831305
  simp only [CollatzResearch.WordTrace]
  refine ⟨66793180630502221838855369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44528787087001481225903579 66793180630502221838855369)
  ·
    refine ⟨50094885472876666379141527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66793180630502221838855369 50094885472876666379141527)
    ·
      refine ⟨75142328209314999568712291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50094885472876666379141527 75142328209314999568712291)
      ·
        refine ⟨112713492313972499353068437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75142328209314999568712291 112713492313972499353068437)
        ·
          refine ⟨5283444952217460907175083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112713492313972499353068437 5283444952217460907175083)
          ·
            refine ⟨7925167428326191360762625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283444952217460907175083 7925167428326191360762625)
            ·
              refine ⟨5943875571244643520571969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7925167428326191360762625 5943875571244643520571969)
              ·
                refine ⟨4457906678433482640428977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943875571244643520571969 4457906678433482640428977)
                ·
                  refine ⟨3343430008825111980321733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457906678433482640428977 3343430008825111980321733)
                  ·
                    refine ⟨626893126654708496310325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343430008825111980321733 626893126654708496310325)
                    ·
                      rfl

theorem cell22_1831305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_1831305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831305 prefixEnd_1831305 := by exact prefixLift 1831305
  have htrace : WordTrace (prefixWord ++ tailWord_1831305) baseStart_1831305 baseEnd_1831305 := by
    simpa [prefixWord, tailWord_1831305, baseEnd_1831305] using wordTrace_append hprefix tailTrace_1831305
  have hstable : (prefixWord ++ tailWord_1831305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831305).length < 2 ^ (prefixWord ++ tailWord_1831305).sum := by decide
  have hdescent : baseEnd_1831305 < baseStart_1831305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831307 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 2, 3]
def baseStart_1831307 : Nat := 118140960795 + 1831307 * 2 ^ 59
def prefixEnd_1831307 : Nat := 4983230072969 + 3 ^ 40 * 1831307 * 2
def baseEnd_1831307 : Nat := 626893811295581157760319

theorem tailTrace_1831307 : CollatzResearch.WordTrace tailWord_1831307 prefixEnd_1831307 626893811295581157760319 := by
  unfold tailWord_1831307
  simp only [CollatzResearch.WordTrace]
  refine ⟨66793253576494976180428175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44528835717663317453618783 66793253576494976180428175)
  ·
    refine ⟨100189880364742464270642263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66793253576494976180428175 100189880364742464270642263)
    ·
      refine ⟨150284820547113696405963395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100189880364742464270642263 150284820547113696405963395)
      ·
        refine ⟨225427230820670544608945093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150284820547113696405963395 225427230820670544608945093)
        ·
          refine ⟨42267605778875727114177205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225427230820670544608945093 42267605778875727114177205)
          ·
            refine ⟨3962588041769599416954113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42267605778875727114177205 3962588041769599416954113)
            ·
              refine ⟨2971941031327199562715585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962588041769599416954113 2971941031327199562715585)
              ·
                refine ⟨2228955773495399672036689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971941031327199562715585 2228955773495399672036689)
                ·
                  refine ⟨1671716830121549754027517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228955773495399672036689 1671716830121549754027517)
                  ·
                    refine ⟨626893811295581157760319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671716830121549754027517 626893811295581157760319)
                    ·
                      rfl

theorem cell22_1831307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 3].length) (baseStart_1831307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831307 prefixEnd_1831307 := by exact prefixLift 1831307
  have htrace : WordTrace (prefixWord ++ tailWord_1831307) baseStart_1831307 baseEnd_1831307 := by
    simpa [prefixWord, tailWord_1831307, baseEnd_1831307] using wordTrace_append hprefix tailTrace_1831307
  have hstable : (prefixWord ++ tailWord_1831307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831307).length < 2 ^ (prefixWord ++ tailWord_1831307).sum := by decide
  have hdescent : baseEnd_1831307 < baseStart_1831307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831320 : List Nat := [2, 1, 2, 5, 1, 1, 3, 7]
def baseStart_1831320 : Nat := 118140960795 + 1831320 * 2 ^ 59
def prefixEnd_1831320 : Nat := 4983230072969 + 3 ^ 40 * 1831320 * 2
def baseEnd_1831320 : Nat := 69655362384583717465031

theorem tailTrace_1831320 : CollatzResearch.WordTrace tailWord_1831320 prefixEnd_1831320 69655362384583717465031 := by
  unfold tailWord_1831320
  simp only [CollatzResearch.WordTrace]
  refine ⟨33396863862723939700325707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44529151816965252933767609 33396863862723939700325707)
  ·
    refine ⟨50095295794085909550488561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33396863862723939700325707 50095295794085909550488561)
    ·
      refine ⟨37571471845564432162866421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50095295794085909550488561 37571471845564432162866421)
      ·
        refine ⟨3522325485521665515268727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37571471845564432162866421 3522325485521665515268727)
        ·
          refine ⟨5283488228282498272903091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522325485521665515268727 5283488228282498272903091)
          ·
            refine ⟨7925232342423747409354637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283488228282498272903091 7925232342423747409354637)
            ·
              refine ⟨2971962128408905278507989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7925232342423747409354637 2971962128408905278507989)
              ·
                refine ⟨69655362384583717465031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2971962128408905278507989 69655362384583717465031)
                ·
                  rfl

theorem cell22_1831320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_1831320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831320 prefixEnd_1831320 := by exact prefixLift 1831320
  have htrace : WordTrace (prefixWord ++ tailWord_1831320) baseStart_1831320 baseEnd_1831320 := by
    simpa [prefixWord, tailWord_1831320, baseEnd_1831320] using wordTrace_append hprefix tailTrace_1831320
  have hstable : (prefixWord ++ tailWord_1831320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831320).length < 2 ^ (prefixWord ++ tailWord_1831320).sum := by decide
  have hdescent : baseEnd_1831320 < baseStart_1831320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831333 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1831333 : Nat := 118140960795 + 1831333 * 2 ^ 59
def prefixEnd_1831333 : Nat := 4983230072969 + 3 ^ 40 * 1831333 * 2
def baseEnd_1831333 : Nat := 626902711626925756610239

theorem tailTrace_1831333 : CollatzResearch.WordTrace tailWord_1831333 prefixEnd_1831333 626902711626925756610239 := by
  unfold tailWord_1831333
  simp only [CollatzResearch.WordTrace]
  refine ⟨66794201874400782620874653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44529467916267188413916435 66794201874400782620874653)
  ·
    refine ⟨25047825702900293482827995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66794201874400782620874653 25047825702900293482827995)
    ·
      refine ⟨37571738554350440224241993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25047825702900293482827995 37571738554350440224241993)
      ·
        refine ⟨28178803915762830168181495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37571738554350440224241993 28178803915762830168181495)
        ·
          refine ⟨42268205873644245252272243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28178803915762830168181495 42268205873644245252272243)
          ·
            refine ⟨63402308810466367878408365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42268205873644245252272243 63402308810466367878408365)
            ·
              refine ⟨23775865803924887954403137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63402308810466367878408365 23775865803924887954403137)
              ·
                refine ⟨17831899352943665965802353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23775865803924887954403137 17831899352943665965802353)
                ·
                  refine ⟨13373924514707749474351765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17831899352943665965802353 13373924514707749474351765)
                  ·
                    refine ⟨626902711626925756610239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13373924514707749474351765 626902711626925756610239)
                    ·
                      rfl

theorem cell22_1831333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1831333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831333 prefixEnd_1831333 := by exact prefixLift 1831333
  have htrace : WordTrace (prefixWord ++ tailWord_1831333) baseStart_1831333 baseEnd_1831333 := by
    simpa [prefixWord, tailWord_1831333, baseEnd_1831333] using wordTrace_append hprefix tailTrace_1831333
  have hstable : (prefixWord ++ tailWord_1831333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831333).length < 2 ^ (prefixWord ++ tailWord_1831333).sum := by decide
  have hdescent : baseEnd_1831333 < baseStart_1831333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831457 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1831457 : Nat := 118140960795 + 1831457 * 2 ^ 59
def prefixEnd_1831457 : Nat := 4983230072969 + 3 ^ 40 * 1831457 * 2
def baseEnd_1831457 : Nat := 626945159361030766509859

theorem tailTrace_1831457 : CollatzResearch.WordTrace tailWord_1831457 prefixEnd_1831457 626945159361030766509859 := by
  unfold tailWord_1831457
  simp only [CollatzResearch.WordTrace]
  refine ⟨66798724525951551798388625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44532483017301034532259083 66798724525951551798388625)
  ·
    refine ⟨50099043394463663848791469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66798724525951551798388625 50099043394463663848791469)
    ·
      refine ⟨18787141272923873943296801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50099043394463663848791469 18787141272923873943296801)
      ·
        refine ⟨14090355954692905457472601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18787141272923873943296801 14090355954692905457472601)
        ·
          refine ⟨10567766966019679093104451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14090355954692905457472601 10567766966019679093104451)
          ·
            refine ⟨15851650449029518639656677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567766966019679093104451 15851650449029518639656677)
            ·
              refine ⟨2972184459193034744935627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15851650449029518639656677 2972184459193034744935627)
              ·
                refine ⟨4458276688789552117403441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972184459193034744935627 4458276688789552117403441)
                ·
                  refine ⟨3343707516592164088052581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4458276688789552117403441 3343707516592164088052581)
                  ·
                    refine ⟨626945159361030766509859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343707516592164088052581 626945159361030766509859)
                    ·
                      rfl

theorem cell22_1831457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1831457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831457 prefixEnd_1831457 := by exact prefixLift 1831457
  have htrace : WordTrace (prefixWord ++ tailWord_1831457) baseStart_1831457 baseEnd_1831457 := by
    simpa [prefixWord, tailWord_1831457, baseEnd_1831457] using wordTrace_append hprefix tailTrace_1831457
  have hstable : (prefixWord ++ tailWord_1831457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831457).length < 2 ^ (prefixWord ++ tailWord_1831457).sum := by decide
  have hdescent : baseEnd_1831457 < baseStart_1831457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831463 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1831463 : Nat := 118140960795 + 1831463 * 2 ^ 59
def prefixEnd_1831463 : Nat := 4983230072969 + 3 ^ 40 * 1831463 * 2
def baseEnd_1831463 : Nat := 626947213283648750859841

theorem tailTrace_1831463 : CollatzResearch.WordTrace tailWord_1831463 prefixEnd_1831463 626947213283648750859841 := by
  unfold tailWord_1831463
  simp only [CollatzResearch.WordTrace]
  refine ⟨66798943363929814823107043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44532628909286543215404695 66798943363929814823107043)
  ·
    refine ⟨100198415045894722234660565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66798943363929814823107043 100198415045894722234660565)
    ·
      refine ⟨2348400352638157552374857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 100198415045894722234660565 2348400352638157552374857)
      ·
        refine ⟨1761300264478618164281143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2348400352638157552374857 1761300264478618164281143)
        ·
          refine ⟨2641950396717927246421715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761300264478618164281143 2641950396717927246421715)
          ·
            refine ⟨3962925595076890869632573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641950396717927246421715 3962925595076890869632573)
            ·
              refine ⟨1486097098153834076112215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3962925595076890869632573 1486097098153834076112215)
              ·
                refine ⟨2229145647230751114168323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486097098153834076112215 2229145647230751114168323)
                ·
                  refine ⟨3343718470846126671252485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229145647230751114168323 3343718470846126671252485)
                  ·
                    refine ⟨626947213283648750859841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343718470846126671252485 626947213283648750859841)
                    ·
                      rfl

theorem cell22_1831463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1831463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831463 prefixEnd_1831463 := by exact prefixLift 1831463
  have htrace : WordTrace (prefixWord ++ tailWord_1831463) baseStart_1831463 baseEnd_1831463 := by
    simpa [prefixWord, tailWord_1831463, baseEnd_1831463] using wordTrace_append hprefix tailTrace_1831463
  have hstable : (prefixWord ++ tailWord_1831463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831463).length < 2 ^ (prefixWord ++ tailWord_1831463).sum := by decide
  have hdescent : baseEnd_1831463 < baseStart_1831463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831478 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1831478 : Nat := 118140960795 + 1831478 * 2 ^ 59
def prefixEnd_1831478 : Nat := 4983230072969 + 3 ^ 40 * 1831478 * 2
def baseEnd_1831478 : Nat := 208984116030064570578265

theorem tailTrace_1831478 : CollatzResearch.WordTrace tailWord_1831478 prefixEnd_1831478 208984116030064570578265 := by
  unfold tailWord_1831478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174968153679717024056443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44532993639250314923268725 4174968153679717024056443)
  ·
    refine ⟨6262452230519575536084665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4174968153679717024056443 6262452230519575536084665)
    ·
      refine ⟨4696839172889681652063499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6262452230519575536084665 4696839172889681652063499)
      ·
        refine ⟨7045258759334522478095249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696839172889681652063499 7045258759334522478095249)
        ·
          refine ⟨5283944069500891858571437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7045258759334522478095249 5283944069500891858571437)
          ·
            refine ⟨1981479026062834446964289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5283944069500891858571437 1981479026062834446964289)
            ·
              refine ⟨1486109269547125835223217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981479026062834446964289 1486109269547125835223217)
              ·
                refine ⟨1114581952160344376417413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486109269547125835223217 1114581952160344376417413)
                ·
                  refine ⟨208984116030064570578265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1114581952160344376417413 208984116030064570578265)
                  ·
                    rfl

theorem cell22_1831478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1831478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831478 prefixEnd_1831478 := by exact prefixLift 1831478
  have htrace : WordTrace (prefixWord ++ tailWord_1831478) baseStart_1831478 baseEnd_1831478 := by
    simpa [prefixWord, tailWord_1831478, baseEnd_1831478] using wordTrace_append hprefix tailTrace_1831478
  have hstable : (prefixWord ++ tailWord_1831478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831478).length < 2 ^ (prefixWord ++ tailWord_1831478).sum := by decide
  have hdescent : baseEnd_1831478 < baseStart_1831478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831487 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 3, 3]
def baseStart_1831487 : Nat := 118140960795 + 1831487 * 2 ^ 59
def prefixEnd_1831487 : Nat := 4983230072969 + 3 ^ 40 * 1831487 * 2
def baseEnd_1831487 : Nat := 626955428974120688259767

theorem tailTrace_1831487 : CollatzResearch.WordTrace tailWord_1831487 prefixEnd_1831487 626955428974120688259767 := by
  unfold tailWord_1831487
  simp only [CollatzResearch.WordTrace]
  refine ⟨66799818715842866921980715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44533212477228577947987143 66799818715842866921980715)
  ·
    refine ⟨100199728073764300382971073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66799818715842866921980715 100199728073764300382971073)
    ·
      refine ⟨75149796055323225287228305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100199728073764300382971073 75149796055323225287228305)
      ·
        refine ⟨56362347041492418965421229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75149796055323225287228305 56362347041492418965421229)
        ·
          refine ⟨21135880140559657112032961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56362347041492418965421229 21135880140559657112032961)
          ·
            refine ⟨15851910105419742834024721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21135880140559657112032961 15851910105419742834024721)
            ·
              refine ⟨11888932579064807125518541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15851910105419742834024721 11888932579064807125518541)
              ·
                refine ⟨4458349717149302672069453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11888932579064807125518541 4458349717149302672069453)
                ·
                  refine ⟨1671881143930988502026045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4458349717149302672069453 1671881143930988502026045)
                  ·
                    refine ⟨626955428974120688259767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671881143930988502026045 626955428974120688259767)
                    ·
                      rfl

theorem cell22_1831487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_1831487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831487 prefixEnd_1831487 := by exact prefixLift 1831487
  have htrace : WordTrace (prefixWord ++ tailWord_1831487) baseStart_1831487 baseEnd_1831487 := by
    simpa [prefixWord, tailWord_1831487, baseEnd_1831487] using wordTrace_append hprefix tailTrace_1831487
  have hstable : (prefixWord ++ tailWord_1831487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831487).length < 2 ^ (prefixWord ++ tailWord_1831487).sum := by decide
  have hdescent : baseEnd_1831487 < baseStart_1831487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831521 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 1, 3]
def baseStart_1831521 : Nat := 118140960795 + 1831521 * 2 ^ 59
def prefixEnd_1831521 : Nat := 4983230072969 + 3 ^ 40 * 1831521 * 2
def baseEnd_1831521 : Nat := 626967067868955932909663

theorem tailTrace_1831521 : CollatzResearch.WordTrace tailWord_1831521 prefixEnd_1831521 626967067868955932909663 := by
  unfold tailWord_1831521
  simp only [CollatzResearch.WordTrace]
  refine ⟨66801058797719690728718417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44534039198479793819145611 66801058797719690728718417)
  ·
    refine ⟨50100794098289768046538813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66801058797719690728718417 50100794098289768046538813)
    ·
      refine ⟨18787797786858663017452055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50100794098289768046538813 18787797786858663017452055)
      ·
        refine ⟨28181696680287994526178083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18787797786858663017452055 28181696680287994526178083)
        ·
          refine ⟨42272545020431991789267125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28181696680287994526178083 42272545020431991789267125)
          ·
            refine ⟨3963051095665499230243793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42272545020431991789267125 3963051095665499230243793)
            ·
              refine ⟨2972288321749124422682845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3963051095665499230243793 2972288321749124422682845)
              ·
                refine ⟨1114608120655921658506067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972288321749124422682845 1114608120655921658506067)
                ·
                  refine ⟨1671912180983882487759101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114608120655921658506067 1671912180983882487759101)
                  ·
                    refine ⟨626967067868955932909663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671912180983882487759101 626967067868955932909663)
                    ·
                      rfl

theorem cell22_1831521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_1831521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831521 prefixEnd_1831521 := by exact prefixLift 1831521
  have htrace : WordTrace (prefixWord ++ tailWord_1831521) baseStart_1831521 baseEnd_1831521 := by
    simpa [prefixWord, tailWord_1831521, baseEnd_1831521] using wordTrace_append hprefix tailTrace_1831521
  have hstable : (prefixWord ++ tailWord_1831521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831521).length < 2 ^ (prefixWord ++ tailWord_1831521).sum := by decide
  have hdescent : baseEnd_1831521 < baseStart_1831521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831534 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1831534 : Nat := 118140960795 + 1831534 * 2 ^ 59
def prefixEnd_1831534 : Nat := 4983230072969 + 3 ^ 40 * 1831534 * 2
def baseEnd_1831534 : Nat := 208990506011542744111541

theorem tailTrace_1831534 : CollatzResearch.WordTrace tailWord_1831534 prefixEnd_1831534 208990506011542744111541 := by
  unfold tailWord_1831534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350191618334074243617707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44534355297781729299294437 8350191618334074243617707)
  ·
    refine ⟨12525287427501111365426561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8350191618334074243617707 12525287427501111365426561)
    ·
      refine ⟨9393965570625833524069921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12525287427501111365426561 9393965570625833524069921)
      ·
        refine ⟨7045474177969375143052441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9393965570625833524069921 7045474177969375143052441)
        ·
          refine ⟨5284105633477031357289331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7045474177969375143052441 5284105633477031357289331)
          ·
            refine ⟨7926158450215547035933997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284105633477031357289331 7926158450215547035933997)
            ·
              refine ⟨2972309418830830138475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7926158450215547035933997 2972309418830830138475249)
              ·
                refine ⟨2229232064123122603856437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972309418830830138475249 2229232064123122603856437)
                ·
                  refine ⟨208990506011542744111541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229232064123122603856437 208990506011542744111541)
                  ·
                    rfl

theorem cell22_1831534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1831534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831534 prefixEnd_1831534 := by exact prefixLift 1831534
  have htrace : WordTrace (prefixWord ++ tailWord_1831534) baseStart_1831534 baseEnd_1831534 := by
    simpa [prefixWord, tailWord_1831534, baseEnd_1831534] using wordTrace_append hprefix tailTrace_1831534
  have hstable : (prefixWord ++ tailWord_1831534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831534).length < 2 ^ (prefixWord ++ tailWord_1831534).sum := by decide
  have hdescent : baseEnd_1831534 < baseStart_1831534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831577 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_1831577 : Nat := 118140960795 + 1831577 * 2 ^ 59
def prefixEnd_1831577 : Nat := 4983230072969 + 3 ^ 40 * 1831577 * 2
def baseEnd_1831577 : Nat := 626986237813390453509491

theorem tailTrace_1831577 : CollatzResearch.WordTrace tailWord_1831577 prefixEnd_1831577 626986237813390453509491 := by
  unfold tailWord_1831577
  simp only [CollatzResearch.WordTrace]
  refine ⟨66803101285516812292756985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44535400857011208195171323 66803101285516812292756985)
  ·
    refine ⟨50102325964137609219567739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66803101285516812292756985 50102325964137609219567739)
    ·
      refine ⟨75153488946206413829351609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50102325964137609219567739 75153488946206413829351609)
      ·
        refine ⟨56365116709654810372013707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75153488946206413829351609 56365116709654810372013707)
        ·
          refine ⟨84547675064482215558020561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56365116709654810372013707 84547675064482215558020561)
          ·
            refine ⟨63410756298361661668515421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84547675064482215558020561 63410756298361661668515421)
            ·
              refine ⟨23779033611885623125693283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63410756298361661668515421 23779033611885623125693283)
              ·
                refine ⟨35668550417828434688539925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23779033611885623125693283 35668550417828434688539925)
                ·
                  refine ⟨1671963300835707876025309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35668550417828434688539925 1671963300835707876025309)
                  ·
                    refine ⟨626986237813390453509491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1671963300835707876025309 626986237813390453509491)
                    ·
                      rfl

theorem cell22_1831577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_1831577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831577 prefixEnd_1831577 := by exact prefixLift 1831577
  have htrace : WordTrace (prefixWord ++ tailWord_1831577) baseStart_1831577 baseEnd_1831577 := by
    simpa [prefixWord, tailWord_1831577, baseEnd_1831577] using wordTrace_append hprefix tailTrace_1831577
  have hstable : (prefixWord ++ tailWord_1831577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831577).length < 2 ^ (prefixWord ++ tailWord_1831577).sum := by decide
  have hdescent : baseEnd_1831577 < baseStart_1831577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831699 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 1, 4]
def baseStart_1831699 : Nat := 118140960795 + 1831699 * 2 ^ 59
def prefixEnd_1831699 : Nat := 4983230072969 + 3 ^ 40 * 1831699 * 2
def baseEnd_1831699 : Nat := 627028000906622801959117

theorem tailTrace_1831699 : CollatzResearch.WordTrace tailWord_1831699 prefixEnd_1831699 627028000906622801959117 := by
  unfold tailWord_1831699
  simp only [CollatzResearch.WordTrace]
  refine ⟨66807550991074827128698151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44538367327383218085798767 66807550991074827128698151)
  ·
    refine ⟨100211326486612240693047227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66807550991074827128698151 100211326486612240693047227)
    ·
      refine ⟨150316989729918361039570841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100211326486612240693047227 150316989729918361039570841)
      ·
        refine ⟨112737742297438770779678131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150316989729918361039570841 112737742297438770779678131)
        ·
          refine ⟨169106613446158156169517197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112737742297438770779678131 169106613446158156169517197)
          ·
            refine ⟨63414980042309308563568949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169106613446158156169517197 63414980042309308563568949)
            ·
              refine ⟨5945154378966497677834589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63414980042309308563568949 5945154378966497677834589)
              ·
                refine ⟨2229432892112436629187971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5945154378966497677834589 2229432892112436629187971)
                ·
                  refine ⟨3344149338168654943781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229432892112436629187971 3344149338168654943781957)
                  ·
                    refine ⟨627028000906622801959117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3344149338168654943781957 627028000906622801959117)
                    ·
                      rfl

theorem cell22_1831699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4].length) (baseStart_1831699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831699 prefixEnd_1831699 := by exact prefixLift 1831699
  have htrace : WordTrace (prefixWord ++ tailWord_1831699) baseStart_1831699 baseEnd_1831699 := by
    simpa [prefixWord, tailWord_1831699, baseEnd_1831699] using wordTrace_append hprefix tailTrace_1831699
  have hstable : (prefixWord ++ tailWord_1831699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831699).length < 2 ^ (prefixWord ++ tailWord_1831699).sum := by decide
  have hdescent : baseEnd_1831699 < baseStart_1831699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831703 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 5]
def baseStart_1831703 : Nat := 118140960795 + 1831703 * 2 ^ 59
def prefixEnd_1831703 : Nat := 4983230072969 + 3 ^ 40 * 1831703 * 2
def baseEnd_1831703 : Nat := 209009790062789374953035

theorem tailTrace_1831703 : CollatzResearch.WordTrace tailWord_1831703 prefixEnd_1831703 209009790062789374953035 := by
  unfold tailWord_1831703
  simp only [CollatzResearch.WordTrace]
  refine ⟨66807696883060335811843763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44538464588706890541229175 66807696883060335811843763)
  ·
    refine ⟨100211545324590503717765645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66807696883060335811843763 100211545324590503717765645)
    ·
      refine ⟨37579329496721438894162117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100211545324590503717765645 37579329496721438894162117)
      ·
        refine ⟨7046124280635269792655397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37579329496721438894162117 7046124280635269792655397)
        ·
          refine ⟨1321148302619113086122887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7046124280635269792655397 1321148302619113086122887)
          ·
            refine ⟨1981722453928669629184331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321148302619113086122887 1981722453928669629184331)
            ·
              refine ⟨2972583680893004443776497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981722453928669629184331 2972583680893004443776497)
              ·
                refine ⟨2229437760669753332832373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972583680893004443776497 2229437760669753332832373)
                ·
                  refine ⟨209009790062789374953035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229437760669753332832373 209009790062789374953035)
                  ·
                    rfl

theorem cell22_1831703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 5].length) (baseStart_1831703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831703 prefixEnd_1831703 := by exact prefixLift 1831703
  have htrace : WordTrace (prefixWord ++ tailWord_1831703) baseStart_1831703 baseEnd_1831703 := by
    simpa [prefixWord, tailWord_1831703, baseEnd_1831703] using wordTrace_append hprefix tailTrace_1831703
  have hstable : (prefixWord ++ tailWord_1831703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831703).length < 2 ^ (prefixWord ++ tailWord_1831703).sum := by decide
  have hdescent : baseEnd_1831703 < baseStart_1831703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831714 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1831714 : Nat := 118140960795 + 1831714 * 2 ^ 59
def prefixEnd_1831714 : Nat := 4983230072969 + 3 ^ 40 * 1831714 * 2
def baseEnd_1831714 : Nat := 209011045237722587611357

theorem tailTrace_1831714 : CollatzResearch.WordTrace tailWord_1831714 prefixEnd_1831714 209011045237722587611357 := by
  unfold tailWord_1831714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702024521505121172623549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44538732057346989793662797 16702024521505121172623549)
  ·
    refine ⟨6263259195564420439733831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16702024521505121172623549 6263259195564420439733831)
    ·
      refine ⟨9394888793346630659600747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263259195564420439733831 9394888793346630659600747)
      ·
        refine ⟨14092333190019945989401121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394888793346630659600747 14092333190019945989401121)
        ·
          refine ⟨10569249892514959492050841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14092333190019945989401121 10569249892514959492050841)
          ·
            refine ⟨7926937419386219619038131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10569249892514959492050841 7926937419386219619038131)
            ·
              refine ⟨11890406129079329428557197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926937419386219619038131 11890406129079329428557197)
              ·
                refine ⟨4458902298404748535708949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11890406129079329428557197 4458902298404748535708949)
                ·
                  refine ⟨209011045237722587611357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4458902298404748535708949 209011045237722587611357)
                  ·
                    rfl

theorem cell22_1831714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1831714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831714 prefixEnd_1831714 := by exact prefixLift 1831714
  have htrace : WordTrace (prefixWord ++ tailWord_1831714) baseStart_1831714 baseEnd_1831714 := by
    simpa [prefixWord, tailWord_1831714, baseEnd_1831714] using wordTrace_append hprefix tailTrace_1831714
  have hstable : (prefixWord ++ tailWord_1831714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831714).length < 2 ^ (prefixWord ++ tailWord_1831714).sum := by decide
  have hdescent : baseEnd_1831714 < baseStart_1831714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831761 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1831761 : Nat := 118140960795 + 1831761 * 2 ^ 59
def prefixEnd_1831761 : Nat := 4983230072969 + 3 ^ 40 * 1831761 * 2
def baseEnd_1831761 : Nat := 627049224773675306908927

theorem tailTrace_1831761 : CollatzResearch.WordTrace tailWord_1831761 prefixEnd_1831761 627049224773675306908927 := by
  unfold tailWord_1831761
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809812316850211717455137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44539874877900141144970091 66809812316850211717455137)
  ·
    refine ⟨50107359237637658788091353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66809812316850211717455137 50107359237637658788091353)
    ·
      refine ⟨37580519428228244091068515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50107359237637658788091353 37580519428228244091068515)
      ·
        refine ⟨56370779142342366136602773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37580519428228244091068515 56370779142342366136602773)
        ·
          refine ⟨2642380272297298412653255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56370779142342366136602773 2642380272297298412653255)
          ·
            refine ⟨3963570408445947618979883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642380272297298412653255 3963570408445947618979883)
            ·
              refine ⟨5945355612668921428469825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963570408445947618979883 5945355612668921428469825)
              ·
                refine ⟨4459016709501691071352369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945355612668921428469825 4459016709501691071352369)
                ·
                  refine ⟨3344262532126268303514277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4459016709501691071352369 3344262532126268303514277)
                  ·
                    refine ⟨627049224773675306908927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3344262532126268303514277 627049224773675306908927)
                    ·
                      rfl

theorem cell22_1831761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1831761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831761 prefixEnd_1831761 := by exact prefixLift 1831761
  have htrace : WordTrace (prefixWord ++ tailWord_1831761) baseStart_1831761 baseEnd_1831761 := by
    simpa [prefixWord, tailWord_1831761, baseEnd_1831761] using wordTrace_append hprefix tailTrace_1831761
  have hstable : (prefixWord ++ tailWord_1831761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831761).length < 2 ^ (prefixWord ++ tailWord_1831761).sum := by decide
  have hdescent : baseEnd_1831761 < baseStart_1831761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831780 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_1831780 : Nat := 118140960795 + 1831780 * 2 ^ 59
def prefixEnd_1831780 : Nat := 4983230072969 + 3 ^ 40 * 1831780 * 2
def baseEnd_1831780 : Nat := 627055728861965590683869

theorem tailTrace_1831780 : CollatzResearch.WordTrace tailWord_1831780 prefixEnd_1831780 627055728861965590683869 := by
  unfold tailWord_1831780
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405252651890688981198397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44540336869187585308264529 33405252651890688981198397)
  ·
    refine ⟨12526969744459008367949399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33405252651890688981198397 12526969744459008367949399)
    ·
      refine ⟨18790454616688512551924099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12526969744459008367949399 18790454616688512551924099)
      ·
        refine ⟨28185681925032768827886149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18790454616688512551924099 28185681925032768827886149)
        ·
          refine ⟨5284815360943644155228653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28185681925032768827886149 5284815360943644155228653)
          ·
            refine ⟨1981805760353866558210745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5284815360943644155228653 1981805760353866558210745)
            ·
              refine ⟨1486354320265399918658059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981805760353866558210745 1486354320265399918658059)
              ·
                refine ⟨2229531480398099877987089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486354320265399918658059 2229531480398099877987089)
                ·
                  refine ⟨1672148610298574908490317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229531480398099877987089 1672148610298574908490317)
                  ·
                    refine ⟨627055728861965590683869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672148610298574908490317 627055728861965590683869)
                    ·
                      rfl

theorem cell22_1831780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_1831780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831780 prefixEnd_1831780 := by exact prefixLift 1831780
  have htrace : WordTrace (prefixWord ++ tailWord_1831780) baseStart_1831780 baseEnd_1831780 := by
    simpa [prefixWord, tailWord_1831780, baseEnd_1831780] using wordTrace_append hprefix tailTrace_1831780
  have hstable : (prefixWord ++ tailWord_1831780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831780).length < 2 ^ (prefixWord ++ tailWord_1831780).sum := by decide
  have hdescent : baseEnd_1831780 < baseStart_1831780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831849 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 6]
def baseStart_1831849 : Nat := 118140960795 + 1831849 * 2 ^ 59
def prefixEnd_1831849 : Nat := 4983230072969 + 3 ^ 40 * 1831849 * 2
def baseEnd_1831849 : Nat := 209026449657357470236219

theorem tailTrace_1831849 : CollatzResearch.WordTrace tailWord_1831849 prefixEnd_1831849 209026449657357470236219 := by
  unfold tailWord_1831849
  simp only [CollatzResearch.WordTrace]
  refine ⟨66813021940531402746658601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44542014627020935164439067 66813021940531402746658601)
  ·
    refine ⟨50109766455398552059993951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66813021940531402746658601 50109766455398552059993951)
    ·
      refine ⟨75164649683097828089990927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50109766455398552059993951 75164649683097828089990927)
      ·
        refine ⟨112746974524646742134986391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75164649683097828089990927 112746974524646742134986391)
        ·
          refine ⟨169120461786970113202479587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112746974524646742134986391 169120461786970113202479587)
          ·
            refine ⟨253680692680455169803719381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169120461786970113202479587 253680692680455169803719381)
            ·
              refine ⟨5945641234698168042274673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253680692680455169803719381 5945641234698168042274673)
              ·
                refine ⟨4459230926023626031706005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945641234698168042274673 4459230926023626031706005)
                ·
                  refine ⟨209026449657357470236219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4459230926023626031706005 209026449657357470236219)
                  ·
                    rfl

theorem cell22_1831849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_1831849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831849 prefixEnd_1831849 := by exact prefixLift 1831849
  have htrace : WordTrace (prefixWord ++ tailWord_1831849) baseStart_1831849 baseEnd_1831849 := by
    simpa [prefixWord, tailWord_1831849, baseEnd_1831849] using wordTrace_append hprefix tailTrace_1831849
  have hstable : (prefixWord ++ tailWord_1831849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831849).length < 2 ^ (prefixWord ++ tailWord_1831849).sum := by decide
  have hdescent : baseEnd_1831849 < baseStart_1831849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831898 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_1831898 : Nat := 118140960795 + 1831898 * 2 ^ 59
def prefixEnd_1831898 : Nat := 4983230072969 + 3 ^ 40 * 1831898 * 2
def baseEnd_1831898 : Nat := 627096122673452616233507

theorem tailTrace_1831898 : CollatzResearch.WordTrace tailWord_1831898 prefixEnd_1831898 627096122673452616233507 := by
  unfold tailWord_1831898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16703702279338471028798087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44543206078235922743461565 16703702279338471028798087)
  ·
    refine ⟨25055553419007706543197131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16703702279338471028798087 25055553419007706543197131)
    ·
      refine ⟨37583330128511559814795697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25055553419007706543197131 37583330128511559814795697)
      ·
        refine ⟨28187497596383669861096773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37583330128511559814795697 28187497596383669861096773)
        ·
          refine ⟨5285155799321938098955645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28187497596383669861096773 5285155799321938098955645)
          ·
            refine ⟨1981933424745726787108367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5285155799321938098955645 1981933424745726787108367)
            ·
              refine ⟨2972900137118590180662551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981933424745726787108367 2972900137118590180662551)
              ·
                refine ⟨4459350205677885270993827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972900137118590180662551 4459350205677885270993827)
                ·
                  refine ⟨6689025308516827906490741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459350205677885270993827 6689025308516827906490741)
                  ·
                    refine ⟨627096122673452616233507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6689025308516827906490741 627096122673452616233507)
                    ·
                      rfl

theorem cell22_1831898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_1831898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831898 prefixEnd_1831898 := by exact prefixLift 1831898
  have htrace : WordTrace (prefixWord ++ tailWord_1831898) baseStart_1831898 baseEnd_1831898 := by
    simpa [prefixWord, tailWord_1831898, baseEnd_1831898] using wordTrace_append hprefix tailTrace_1831898
  have hstable : (prefixWord ++ tailWord_1831898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831898).length < 2 ^ (prefixWord ++ tailWord_1831898).sum := by decide
  have hdescent : baseEnd_1831898 < baseStart_1831898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831911 : List Nat := [1, 1, 5, 2, 2, 2, 1, 8]
def baseStart_1831911 : Nat := 118140960795 + 1831911 * 2 ^ 59
def prefixEnd_1831911 : Nat := 4983230072969 + 3 ^ 40 * 1831911 * 2
def baseEnd_1831911 : Nat := 69677841426569435073163

theorem tailTrace_1831911 : CollatzResearch.WordTrace tailWord_1831911 prefixEnd_1831911 69677841426569435073163 := by
  unfold tailWord_1831911
  simp only [CollatzResearch.WordTrace]
  refine ⟨66815283266306787335415587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44543522177537858223610391 66815283266306787335415587)
  ·
    refine ⟨100222924899460181003123381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66815283266306787335415587 100222924899460181003123381)
    ·
      refine ⟨9395899209324391969042817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100222924899460181003123381 9395899209324391969042817)
      ·
        refine ⟨7046924406993293976782113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9395899209324391969042817 7046924406993293976782113)
        ·
          refine ⟨5285193305244970482586585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7046924406993293976782113 5285193305244970482586585)
          ·
            refine ⟨3963894978933727861939939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5285193305244970482586585 3963894978933727861939939)
            ·
              refine ⟨5945842468400591792909909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963894978933727861939939 5945842468400591792909909)
              ·
                refine ⟨69677841426569435073163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5945842468400591792909909 69677841426569435073163)
                ·
                  rfl

theorem cell22_1831911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 8].length) (baseStart_1831911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831911 prefixEnd_1831911 := by exact prefixLift 1831911
  have htrace : WordTrace (prefixWord ++ tailWord_1831911) baseStart_1831911 baseEnd_1831911 := by
    simpa [prefixWord, tailWord_1831911, baseEnd_1831911] using wordTrace_append hprefix tailTrace_1831911
  have hstable : (prefixWord ++ tailWord_1831911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831911).length < 2 ^ (prefixWord ++ tailWord_1831911).sum := by decide
  have hdescent : baseEnd_1831911 < baseStart_1831911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831990 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1831990 : Nat := 118140960795 + 1831990 * 2 ^ 59
def prefixEnd_1831990 : Nat := 4983230072969 + 3 ^ 40 * 1831990 * 2
def baseEnd_1831990 : Nat := 209042538717865014311075

theorem tailTrace_1831990 : CollatzResearch.WordTrace tailWord_1831990 prefixEnd_1831990 209042538717865014311075 := by
  unfold tailWord_1831990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176135289563786489221339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44545443088680389218360949 4176135289563786489221339)
  ·
    refine ⟨6264202934345679733832009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176135289563786489221339 6264202934345679733832009)
    ·
      refine ⟨4698152200759259800374007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6264202934345679733832009 4698152200759259800374007)
      ·
        refine ⟨7047228301138889700561011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698152200759259800374007 7047228301138889700561011)
        ·
          refine ⟨10570842451708334550841517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047228301138889700561011 10570842451708334550841517)
          ·
            refine ⟨3964065919390625456565569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10570842451708334550841517 3964065919390625456565569)
            ·
              refine ⟨2973049439542969092424177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3964065919390625456565569 2973049439542969092424177)
              ·
                refine ⟨2229787079657226819318133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973049439542969092424177 2229787079657226819318133)
                ·
                  refine ⟨209042538717865014311075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229787079657226819318133 209042538717865014311075)
                  ·
                    rfl

theorem cell22_1831990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1831990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1831990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1831990 prefixEnd_1831990 := by exact prefixLift 1831990
  have htrace : WordTrace (prefixWord ++ tailWord_1831990) baseStart_1831990 baseEnd_1831990 := by
    simpa [prefixWord, tailWord_1831990, baseEnd_1831990] using wordTrace_append hprefix tailTrace_1831990
  have hstable : (prefixWord ++ tailWord_1831990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831990).length < 2 ^ (prefixWord ++ tailWord_1831990).sum := by decide
  have hdescent : baseEnd_1831990 < baseStart_1831990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832018 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1832018 : Nat := 118140960795 + 1832018 * 2 ^ 59
def prefixEnd_1832018 : Nat := 4983230072969 + 3 ^ 40 * 1832018 * 2
def baseEnd_1832018 : Nat := 209045733708604101077713

theorem tailTrace_1832018 : CollatzResearch.WordTrace tailWord_1832018 prefixEnd_1832018 209045733708604101077713 := by
  unfold tailWord_1832018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704796469229786152390177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44546123917946096406373805 16704796469229786152390177)
  ·
    refine ⟨12528597351922339614292633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16704796469229786152390177 12528597351922339614292633)
    ·
      refine ⟨9396448013941754710719475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12528597351922339614292633 9396448013941754710719475)
      ·
        refine ⟨14094672020912632066079213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396448013941754710719475 14094672020912632066079213)
        ·
          refine ⟨5285502007842237024779705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14094672020912632066079213 5285502007842237024779705)
          ·
            refine ⟨3964126505881677768584779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5285502007842237024779705 3964126505881677768584779)
            ·
              refine ⟨5946189758822516652877169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964126505881677768584779 5946189758822516652877169)
              ·
                refine ⟨4459642319116887489657877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5946189758822516652877169 4459642319116887489657877)
                ·
                  refine ⟨209045733708604101077713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4459642319116887489657877 209045733708604101077713)
                  ·
                    rfl

theorem cell22_1832018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1832018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832018 prefixEnd_1832018 := by exact prefixLift 1832018
  have htrace : WordTrace (prefixWord ++ tailWord_1832018) baseStart_1832018 baseEnd_1832018 := by
    simpa [prefixWord, tailWord_1832018, baseEnd_1832018] using wordTrace_append hprefix tailTrace_1832018
  have hstable : (prefixWord ++ tailWord_1832018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832018).length < 2 ^ (prefixWord ++ tailWord_1832018).sum := by decide
  have hdescent : baseEnd_1832018 < baseStart_1832018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832031 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 6]
def baseStart_1832031 : Nat := 118140960795 + 1832031 * 2 ^ 59
def prefixEnd_1832031 : Nat := 4983230072969 + 3 ^ 40 * 1832031 * 2
def baseEnd_1832031 : Nat := 627141651291484602658099

theorem tailTrace_1832031 : CollatzResearch.WordTrace tailWord_1832031 prefixEnd_1832031 627141651291484602658099 := by
  unfold tailWord_1832031
  simp only [CollatzResearch.WordTrace]
  refine ⟨66819660025872047829783947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44546440017248031886522631 66819660025872047829783947)
  ·
    refine ⟨100229490038808071744675921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66819660025872047829783947 100229490038808071744675921)
    ·
      refine ⟨75172117529106053808506941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100229490038808071744675921 75172117529106053808506941)
      ·
        refine ⟨28189544073414770178190103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75172117529106053808506941 28189544073414770178190103)
        ·
          refine ⟨42284316110122155267285155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28189544073414770178190103 42284316110122155267285155)
          ·
            refine ⟨63426474165183232900927733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42284316110122155267285155 63426474165183232900927733)
            ·
              refine ⟨5946231952985928084461975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63426474165183232900927733 5946231952985928084461975)
              ·
                refine ⟨8919347929478892126692963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946231952985928084461975 8919347929478892126692963)
                ·
                  refine ⟨13379021894218338190039445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8919347929478892126692963 13379021894218338190039445)
                  ·
                    refine ⟨627141651291484602658099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13379021894218338190039445 627141651291484602658099)
                    ·
                      rfl

theorem cell22_1832031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_1832031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832031 prefixEnd_1832031 := by exact prefixLift 1832031
  have htrace : WordTrace (prefixWord ++ tailWord_1832031) baseStart_1832031 baseEnd_1832031 := by
    simpa [prefixWord, tailWord_1832031, baseEnd_1832031] using wordTrace_append hprefix tailTrace_1832031
  have hstable : (prefixWord ++ tailWord_1832031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832031).length < 2 ^ (prefixWord ++ tailWord_1832031).sum := by decide
  have hdescent : baseEnd_1832031 < baseStart_1832031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832076 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_1832076 : Nat := 118140960795 + 1832076 * 2 ^ 59
def prefixEnd_1832076 : Nat := 4983230072969 + 3 ^ 40 * 1832076 * 2
def baseEnd_1832076 : Nat := 627157055711119485282961

theorem tailTrace_1832076 : CollatzResearch.WordTrace tailWord_1832076 prefixEnd_1832076 627157055711119485282961 := by
  unfold tailWord_1832076
  simp only [CollatzResearch.WordTrace]
  refine ⟨33410650655354510257586041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44547534207139347010114721 33410650655354510257586041)
  ·
    refine ⟨25057987991515882693189531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33410650655354510257586041 25057987991515882693189531)
    ·
      refine ⟨37586981987273824039784297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25057987991515882693189531 37586981987273824039784297)
      ·
        refine ⟨28190236490455368029838223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37586981987273824039784297 28190236490455368029838223)
        ·
          refine ⟨42285354735683052044757335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190236490455368029838223 42285354735683052044757335)
          ·
            refine ⟨63428032103524578067136003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42285354735683052044757335 63428032103524578067136003)
            ·
              refine ⟨95142048155286867100704005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63428032103524578067136003 95142048155286867100704005)
              ·
                refine ⟨17839134029116287581382001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95142048155286867100704005 17839134029116287581382001)
                ·
                  refine ⟨13379350521837215686036501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17839134029116287581382001 13379350521837215686036501)
                  ·
                    refine ⟨627157055711119485282961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13379350521837215686036501 627157055711119485282961)
                    ·
                      rfl

theorem cell22_1832076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_1832076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832076 prefixEnd_1832076 := by exact prefixLift 1832076
  have htrace : WordTrace (prefixWord ++ tailWord_1832076) baseStart_1832076 baseEnd_1832076 := by
    simpa [prefixWord, tailWord_1832076, baseEnd_1832076] using wordTrace_append hprefix tailTrace_1832076
  have hstable : (prefixWord ++ tailWord_1832076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832076).length < 2 ^ (prefixWord ++ tailWord_1832076).sum := by decide
  have hdescent : baseEnd_1832076 < baseStart_1832076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832118 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1832118 : Nat := 118140960795 + 1832118 * 2 ^ 59
def prefixEnd_1832118 : Nat := 4983230072969 + 3 ^ 40 * 1832118 * 2
def baseEnd_1832118 : Nat := 627171433169445375732833

theorem tailTrace_1832118 : CollatzResearch.WordTrace tailWord_1832118 prefixEnd_1832118 627171433169445375732833 := by
  unfold tailWord_1832118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176427073534803855512563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44548555451037907792134005 4176427073534803855512563)
  ·
    refine ⟨6264640610302205783268845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4176427073534803855512563 6264640610302205783268845)
    ·
      refine ⟨2349240228863327168725817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6264640610302205783268845 2349240228863327168725817)
      ·
        refine ⟨1761930171647495376544363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2349240228863327168725817 1761930171647495376544363)
        ·
          refine ⟨2642895257471243064816545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761930171647495376544363 2642895257471243064816545)
          ·
            refine ⟨1982171443103432298612409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2642895257471243064816545 1982171443103432298612409)
            ·
              refine ⟨1486628582327574223959307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982171443103432298612409 1486628582327574223959307)
              ·
                refine ⟨2229942873491361335938961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486628582327574223959307 2229942873491361335938961)
                ·
                  refine ⟨1672457155118521001954221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229942873491361335938961 1672457155118521001954221)
                  ·
                    refine ⟨627171433169445375732833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672457155118521001954221 627171433169445375732833)
                    ·
                      rfl

theorem cell22_1832118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1832118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832118 prefixEnd_1832118 := by exact prefixLift 1832118
  have htrace : WordTrace (prefixWord ++ tailWord_1832118) baseStart_1832118 baseEnd_1832118 := by
    simpa [prefixWord, tailWord_1832118, baseEnd_1832118] using wordTrace_append hprefix tailTrace_1832118
  have hstable : (prefixWord ++ tailWord_1832118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832118).length < 2 ^ (prefixWord ++ tailWord_1832118).sum := by decide
  have hdescent : baseEnd_1832118 < baseStart_1832118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832125 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 5]
def baseStart_1832125 : Nat := 118140960795 + 1832125 * 2 ^ 59
def prefixEnd_1832125 : Nat := 4983230072969 + 3 ^ 40 * 1832125 * 2
def baseEnd_1832125 : Nat := 209057943137499896935937

theorem tailTrace_1832125 : CollatzResearch.WordTrace tailWord_1832125 prefixEnd_1832125 209057943137499896935937 := by
  unfold tailWord_1832125
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823088487531501883705829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44548725658354334589137219 66823088487531501883705829)
  ·
    refine ⟨12529329091412156603194843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66823088487531501883705829 12529329091412156603194843)
    ·
      refine ⟨18793993637118234904792265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529329091412156603194843 18793993637118234904792265)
      ·
        refine ⟨14095495227838676178594199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18793993637118234904792265 14095495227838676178594199)
        ·
          refine ⟨21143242841758014267891299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14095495227838676178594199 21143242841758014267891299)
          ·
            refine ⟨31714864262637021401836949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21143242841758014267891299 31714864262637021401836949)
            ·
              refine ⟨1486634262311110378211107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31714864262637021401836949 1486634262311110378211107)
              ·
                refine ⟨2229951393466665567316661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486634262311110378211107 2229951393466665567316661)
                ·
                  refine ⟨209057943137499896935937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229951393466665567316661 209057943137499896935937)
                  ·
                    rfl

theorem cell22_1832125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_1832125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832125 prefixEnd_1832125 := by exact prefixLift 1832125
  have htrace : WordTrace (prefixWord ++ tailWord_1832125) baseStart_1832125 baseEnd_1832125 := by
    simpa [prefixWord, tailWord_1832125, baseEnd_1832125] using wordTrace_append hprefix tailTrace_1832125
  have hstable : (prefixWord ++ tailWord_1832125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832125).length < 2 ^ (prefixWord ++ tailWord_1832125).sum := by decide
  have hdescent : baseEnd_1832125 < baseStart_1832125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832168 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1832168 : Nat := 118140960795 + 1832168 * 2 ^ 59
def prefixEnd_1832168 : Nat := 4983230072969 + 3 ^ 40 * 1832168 * 2
def baseEnd_1832168 : Nat := 627188549191261911982679

theorem tailTrace_1832168 : CollatzResearch.WordTrace tailWord_1832168 prefixEnd_1832168 627188549191261911982679 := by
  unfold tailWord_1832168
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412328413187860113760579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44549771217583813485014105 33412328413187860113760579)
  ·
    refine ⟨50118492619781790170640869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33412328413187860113760579 50118492619781790170640869)
    ·
      refine ⟨9397217366209085656995163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50118492619781790170640869 9397217366209085656995163)
      ·
        refine ⟨14095826049313628485492745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9397217366209085656995163 14095826049313628485492745)
        ·
          refine ⟨10571869536985221364119559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14095826049313628485492745 10571869536985221364119559)
          ·
            refine ⟨15857804305477832046179339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10571869536985221364119559 15857804305477832046179339)
            ·
              refine ⟨23786706458216748069269009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15857804305477832046179339 23786706458216748069269009)
              ·
                refine ⟨17840029843662561051951757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23786706458216748069269009 17840029843662561051951757)
                ·
                  refine ⟨6690011191373460394481909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17840029843662561051951757 6690011191373460394481909)
                  ·
                    refine ⟨627188549191261911982679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6690011191373460394481909 627188549191261911982679)
                    ·
                      rfl

theorem cell22_1832168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1832168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832168 prefixEnd_1832168 := by exact prefixLift 1832168
  have htrace : WordTrace (prefixWord ++ tailWord_1832168) baseStart_1832168 baseEnd_1832168 := by
    simpa [prefixWord, tailWord_1832168, baseEnd_1832168] using wordTrace_append hprefix tailTrace_1832168
  have hstable : (prefixWord ++ tailWord_1832168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832168).length < 2 ^ (prefixWord ++ tailWord_1832168).sum := by decide
  have hdescent : baseEnd_1832168 < baseStart_1832168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832185 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_1832185 : Nat := 118140960795 + 1832185 * 2 ^ 59
def prefixEnd_1832185 : Nat := 4983230072969 + 3 ^ 40 * 1832185 * 2
def baseEnd_1832185 : Nat := 627194368638679534307627

theorem tailTrace_1832185 : CollatzResearch.WordTrace tailWord_1832185 prefixEnd_1832185 627194368638679534307627 := by
  unfold tailWord_1832185
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825276867314132130890009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44550184578209421420593339 66825276867314132130890009)
  ·
    refine ⟨50118957650485599098167507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66825276867314132130890009 50118957650485599098167507)
    ·
      refine ⟨75178436475728398647251261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50118957650485599098167507 75178436475728398647251261)
      ·
        refine ⟨28191913678398149492719223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75178436475728398647251261 28191913678398149492719223)
        ·
          refine ⟨42287870517597224239078835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28191913678398149492719223 42287870517597224239078835)
          ·
            refine ⟨63431805776395836358618253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42287870517597224239078835 63431805776395836358618253)
            ·
              refine ⟨23786927166148438634481845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63431805776395836358618253 23786927166148438634481845)
              ·
                refine ⟨2230024421826416121982673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23786927166148438634481845 2230024421826416121982673)
                ·
                  refine ⟨1672518316369812091487005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2230024421826416121982673 1672518316369812091487005)
                  ·
                    refine ⟨627194368638679534307627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672518316369812091487005 627194368638679534307627)
                    ·
                      rfl

theorem cell22_1832185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_1832185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832185 prefixEnd_1832185 := by exact prefixLift 1832185
  have htrace : WordTrace (prefixWord ++ tailWord_1832185) baseStart_1832185 baseEnd_1832185 := by
    simpa [prefixWord, tailWord_1832185, baseEnd_1832185] using wordTrace_append hprefix tailTrace_1832185
  have hstable : (prefixWord ++ tailWord_1832185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832185).length < 2 ^ (prefixWord ++ tailWord_1832185).sum := by decide
  have hdescent : baseEnd_1832185 < baseStart_1832185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832200 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_1832200 : Nat := 118140960795 + 1832200 * 2 ^ 59
def prefixEnd_1832200 : Nat := 4983230072969 + 3 ^ 40 * 1832200 * 2
def baseEnd_1832200 : Nat := 627199503445224495182581

theorem tailTrace_1832200 : CollatzResearch.WordTrace tailWord_1832200 prefixEnd_1832200 627199503445224495182581 := by
  unfold tailWord_1832200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412911981129894846343027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44550549308173193128457369 33412911981129894846343027)
  ·
    refine ⟨50119367971694842269514541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33412911981129894846343027 50119367971694842269514541)
    ·
      refine ⟨18794762989385565851067953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50119367971694842269514541 18794762989385565851067953)
      ·
        refine ⟨14096072242039174388300965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18794762989385565851067953 14096072242039174388300965)
        ·
          refine ⟨2643013545382345197806431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14096072242039174388300965 2643013545382345197806431)
          ·
            refine ⟨3964520318073517796709647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643013545382345197806431 3964520318073517796709647)
            ·
              refine ⟨5946780477110276695064471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964520318073517796709647 5946780477110276695064471)
              ·
                refine ⟨8920170715665415042596707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946780477110276695064471 8920170715665415042596707)
                ·
                  refine ⟨13380256073498122563895061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8920170715665415042596707 13380256073498122563895061)
                  ·
                    refine ⟨627199503445224495182581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13380256073498122563895061 627199503445224495182581)
                    ·
                      rfl

theorem cell22_1832200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_1832200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832200 prefixEnd_1832200 := by exact prefixLift 1832200
  have htrace : WordTrace (prefixWord ++ tailWord_1832200) baseStart_1832200 baseEnd_1832200 := by
    simpa [prefixWord, tailWord_1832200, baseEnd_1832200] using wordTrace_append hprefix tailTrace_1832200
  have hstable : (prefixWord ++ tailWord_1832200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832200).length < 2 ^ (prefixWord ++ tailWord_1832200).sum := by decide
  have hdescent : baseEnd_1832200 < baseStart_1832200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832249 : List Nat := [1, 2, 1, 6, 3, 1, 2, 6]
def baseStart_1832249 : Nat := 118140960795 + 1832249 * 2 ^ 59
def prefixEnd_1832249 : Nat := 4983230072969 + 3 ^ 40 * 1832249 * 2
def baseEnd_1832249 : Nat := 69690697460733855634159

theorem tailTrace_1832249 : CollatzResearch.WordTrace tailWord_1832249 prefixEnd_1832249 69690697460733855634159 := by
  unfold tailWord_1832249
  simp only [CollatzResearch.WordTrace]
  refine ⟨66827611139082271061219801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44551740759388180707479867 66827611139082271061219801)
  ·
    refine ⟨50120708354311703295914851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66827611139082271061219801 50120708354311703295914851)
    ·
      refine ⟨75181062531467554943872277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50120708354311703295914851 75181062531467554943872277)
      ·
        refine ⟨3524112306162541637994013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75181062531467554943872277 3524112306162541637994013)
        ·
          refine ⟨1321542114810953114247755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3524112306162541637994013 1321542114810953114247755)
          ·
            refine ⟨1982313172216429671371633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321542114810953114247755 1982313172216429671371633)
            ·
              refine ⟨1486734879162322253528725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982313172216429671371633 1486734879162322253528725)
              ·
                refine ⟨69690697460733855634159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1486734879162322253528725 69690697460733855634159)
                ·
                  rfl

theorem cell22_1832249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 6].length) (baseStart_1832249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832249 prefixEnd_1832249 := by exact prefixLift 1832249
  have htrace : WordTrace (prefixWord ++ tailWord_1832249) baseStart_1832249 baseEnd_1832249 := by
    simpa [prefixWord, tailWord_1832249, baseEnd_1832249] using wordTrace_append hprefix tailTrace_1832249
  have hstable : (prefixWord ++ tailWord_1832249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832249).length < 2 ^ (prefixWord ++ tailWord_1832249).sum := by decide
  have hdescent : baseEnd_1832249 < baseStart_1832249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832320 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_1832320 : Nat := 118140960795 + 1832320 * 2 ^ 59
def prefixEnd_1832320 : Nat := 4983230072969 + 3 ^ 40 * 1832320 * 2
def baseEnd_1832320 : Nat := 627240581897584182182213

theorem tailTrace_1832320 : CollatzResearch.WordTrace tailWord_1832320 prefixEnd_1832320 627240581897584182182213 := by
  unfold tailWord_1832320
  simp only [CollatzResearch.WordTrace]
  refine ⟨33415100360912525093527207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44553467147883366791369609 33415100360912525093527207)
  ·
    refine ⟨50122650541368787640290811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33415100360912525093527207 50122650541368787640290811)
    ·
      refine ⟨75183975812053181460436217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50122650541368787640290811 75183975812053181460436217)
      ·
        refine ⟨56387981859039886095327163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75183975812053181460436217 56387981859039886095327163)
        ·
          refine ⟨84581972788559829142990745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56387981859039886095327163 84581972788559829142990745)
          ·
            refine ⟨63436479591419871857243059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84581972788559829142990745 63436479591419871857243059)
            ·
              refine ⟨95154719387129807785864589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63436479591419871857243059 95154719387129807785864589)
              ·
                refine ⟨35683019770173677919699221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95154719387129807785864589 35683019770173677919699221)
                ·
                  refine ⟨1672641551726891152485901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35683019770173677919699221 1672641551726891152485901)
                  ·
                    refine ⟨627240581897584182182213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672641551726891152485901 627240581897584182182213)
                    ·
                      rfl

theorem cell22_1832320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_1832320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832320 prefixEnd_1832320 := by exact prefixLift 1832320
  have htrace : WordTrace (prefixWord ++ tailWord_1832320) baseStart_1832320 baseEnd_1832320 := by
    simpa [prefixWord, tailWord_1832320, baseEnd_1832320] using wordTrace_append hprefix tailTrace_1832320
  have hstable : (prefixWord ++ tailWord_1832320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832320).length < 2 ^ (prefixWord ++ tailWord_1832320).sum := by decide
  have hdescent : baseEnd_1832320 < baseStart_1832320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832324 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1832324 : Nat := 118140960795 + 1832324 * 2 ^ 59
def prefixEnd_1832324 : Nat := 4983230072969 + 3 ^ 40 * 1832324 * 2
def baseEnd_1832324 : Nat := 627241951179329505082201

theorem tailTrace_1832324 : CollatzResearch.WordTrace tailWord_1832324 prefixEnd_1832324 627241951179329505082201 := by
  unfold tailWord_1832324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33415173306905279435100013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44553564409207039246800017 33415173306905279435100013)
  ·
    refine ⟨12530689990089479788162505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33415173306905279435100013 12530689990089479788162505)
    ·
      refine ⟨9398017492567109841121879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12530689990089479788162505 9398017492567109841121879)
      ·
        refine ⟨14097026238850664761682819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398017492567109841121879 14097026238850664761682819)
        ·
          refine ⟨21145539358275997142524229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14097026238850664761682819 21145539358275997142524229)
          ·
            refine ⟨3964788629676749464223293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21145539358275997142524229 3964788629676749464223293)
            ·
              refine ⟨1486795736128781049083735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3964788629676749464223293 1486795736128781049083735)
              ·
                refine ⟨2230193604193171573625603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486795736128781049083735 2230193604193171573625603)
                ·
                  refine ⟨3345290406289757360438405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230193604193171573625603 3345290406289757360438405)
                  ·
                    refine ⟨627241951179329505082201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345290406289757360438405 627241951179329505082201)
                    ·
                      rfl

theorem cell22_1832324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1832324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832324 prefixEnd_1832324 := by exact prefixLift 1832324
  have htrace : WordTrace (prefixWord ++ tailWord_1832324) baseStart_1832324 baseEnd_1832324 := by
    simpa [prefixWord, tailWord_1832324, baseEnd_1832324] using wordTrace_append hprefix tailTrace_1832324
  have hstable : (prefixWord ++ tailWord_1832324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832324).length < 2 ^ (prefixWord ++ tailWord_1832324).sum := by decide
  have hdescent : baseEnd_1832324 < baseStart_1832324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832354 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1832354 : Nat := 118140960795 + 1832354 * 2 ^ 59
def prefixEnd_1832354 : Nat := 4983230072969 + 3 ^ 40 * 1832354 * 2
def baseEnd_1832354 : Nat := 627252220792419426832109

theorem tailTrace_1832354 : CollatzResearch.WordTrace tailWord_1832354 prefixEnd_1832354 627252220792419426832109 := by
  unfold tailWord_1832354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16707860200925468498448029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44554293869134582662528077 16707860200925468498448029)
  ·
    refine ⟨6265447575347050686918011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16707860200925468498448029 6265447575347050686918011)
    ·
      refine ⟨9398171363020576030377017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265447575347050686918011 9398171363020576030377017)
      ·
        refine ⟨7048628522265432022782763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9398171363020576030377017 7048628522265432022782763)
        ·
          refine ⟨10572942783398148034174145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048628522265432022782763 10572942783398148034174145)
          ·
            refine ⟨7929707087548611025630609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10572942783398148034174145 7929707087548611025630609)
            ·
              refine ⟨5947280315661458269222957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929707087548611025630609 5947280315661458269222957)
              ·
                refine ⟨2230230118373046850958609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5947280315661458269222957 2230230118373046850958609)
                ·
                  refine ⟨1672672588779785138218957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2230230118373046850958609 1672672588779785138218957)
                  ·
                    refine ⟨627252220792419426832109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672672588779785138218957 627252220792419426832109)
                    ·
                      rfl

theorem cell22_1832354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1832354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832354 prefixEnd_1832354 := by exact prefixLift 1832354
  have htrace : WordTrace (prefixWord ++ tailWord_1832354) baseStart_1832354 baseEnd_1832354 := by
    simpa [prefixWord, tailWord_1832354, baseEnd_1832354] using wordTrace_append hprefix tailTrace_1832354
  have hstable : (prefixWord ++ tailWord_1832354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832354).length < 2 ^ (prefixWord ++ tailWord_1832354).sum := by decide
  have hdescent : baseEnd_1832354 < baseStart_1832354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832382 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1832382 : Nat := 118140960795 + 1832382 * 2 ^ 59
def prefixEnd_1832382 : Nat := 4983230072969 + 3 ^ 40 * 1832382 * 2
def baseEnd_1832382 : Nat := 627261805764636687132023

theorem tailTrace_1832382 : CollatzResearch.WordTrace tailWord_1832382 prefixEnd_1832382 627261805764636687132023 := by
  unfold tailWord_1832382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8354057755950054346976425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44554974698400289850540933 8354057755950054346976425)
  ·
    refine ⟨6265543316962540760232319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8354057755950054346976425 6265543316962540760232319)
    ·
      refine ⟨9398314975443811140348479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265543316962540760232319 9398314975443811140348479)
      ·
        refine ⟨14097472463165716710522719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398314975443811140348479 14097472463165716710522719)
        ·
          refine ⟨21146208694748575065784079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14097472463165716710522719 21146208694748575065784079)
          ·
            refine ⟨31719313042122862598676119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21146208694748575065784079 31719313042122862598676119)
            ·
              refine ⟨47578969563184293898014179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31719313042122862598676119 47578969563184293898014179)
              ·
                refine ⟨71368454344776440847021269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47578969563184293898014179 71368454344776440847021269)
                ·
                  refine ⟨1672698148705697832352061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 71368454344776440847021269 1672698148705697832352061)
                  ·
                    refine ⟨627261805764636687132023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672698148705697832352061 627261805764636687132023)
                    ·
                      rfl

theorem cell22_1832382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1832382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832382 prefixEnd_1832382 := by exact prefixLift 1832382
  have htrace : WordTrace (prefixWord ++ tailWord_1832382) baseStart_1832382 baseEnd_1832382 := by
    simpa [prefixWord, tailWord_1832382, baseEnd_1832382] using wordTrace_append hprefix tailTrace_1832382
  have hstable : (prefixWord ++ tailWord_1832382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832382).length < 2 ^ (prefixWord ++ tailWord_1832382).sum := by decide
  have hdescent : baseEnd_1832382 < baseStart_1832382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832399 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 1, 3]
def baseStart_1832399 : Nat := 118140960795 + 1832399 * 2 ^ 59
def prefixEnd_1832399 : Nat := 4983230072969 + 3 ^ 40 * 1832399 * 2
def baseEnd_1832399 : Nat := 627267625212054309456971

theorem tailTrace_1832399 : CollatzResearch.WordTrace tailWord_1832399 prefixEnd_1832399 627267625212054309456971 := by
  unfold tailWord_1832399
  simp only [CollatzResearch.WordTrace]
  refine ⟨66833082088538846679180251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44555388059025897786120167 66833082088538846679180251)
  ·
    refine ⟨100249623132808270018770377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66833082088538846679180251 100249623132808270018770377)
    ·
      refine ⟨75187217349606202514077783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100249623132808270018770377 75187217349606202514077783)
      ·
        refine ⟨112780826024409303771116675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75187217349606202514077783 112780826024409303771116675)
        ·
          refine ⟨169171239036613955656675013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112780826024409303771116675 169171239036613955656675013)
          ·
            refine ⟨31719607319365116685626565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169171239036613955656675013 31719607319365116685626565)
            ·
              refine ⟨5947426372380959378554981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31719607319365116685626565 5947426372380959378554981)
              ·
                refine ⟨1115142444821429883479059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5947426372380959378554981 1115142444821429883479059)
                ·
                  refine ⟨1672713667232144825218589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115142444821429883479059 1672713667232144825218589)
                  ·
                    refine ⟨627267625212054309456971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672713667232144825218589 627267625212054309456971)
                    ·
                      rfl

theorem cell22_1832399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_1832399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832399 prefixEnd_1832399 := by exact prefixLift 1832399
  have htrace : WordTrace (prefixWord ++ tailWord_1832399) baseStart_1832399 baseEnd_1832399 := by
    simpa [prefixWord, tailWord_1832399, baseEnd_1832399] using wordTrace_append hprefix tailTrace_1832399
  have hstable : (prefixWord ++ tailWord_1832399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832399).length < 2 ^ (prefixWord ++ tailWord_1832399).sum := by decide
  have hdescent : baseEnd_1832399 < baseStart_1832399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832425 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1832425 : Nat := 118140960795 + 1832425 * 2 ^ 59
def prefixEnd_1832425 : Nat := 4983230072969 + 3 ^ 40 * 1832425 * 2
def baseEnd_1832425 : Nat := 627276525543398908306891

theorem tailTrace_1832425 : CollatzResearch.WordTrace tailWord_1832425 prefixEnd_1832425 627276525543398908306891 := by
  unfold tailWord_1832425
  simp only [CollatzResearch.WordTrace]
  refine ⟨66834030386444653119626729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44556020257629768746417819 66834030386444653119626729)
  ·
    refine ⟨50125522789833489839720047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66834030386444653119626729 50125522789833489839720047)
    ·
      refine ⟨75188284184750234759580071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50125522789833489839720047 75188284184750234759580071)
      ·
        refine ⟨112782426277125352139370107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75188284184750234759580071 112782426277125352139370107)
        ·
          refine ⟨169173639415688028209055161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112782426277125352139370107 169173639415688028209055161)
          ·
            refine ⟨126880229561766021156791371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169173639415688028209055161 126880229561766021156791371)
            ·
              refine ⟨190320344342649031735187057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126880229561766021156791371 190320344342649031735187057)
              ·
                refine ⟨142740258256986773801390293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190320344342649031735187057 142740258256986773801390293)
                ·
                  refine ⟨3345474802898127510970085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142740258256986773801390293 3345474802898127510970085)
                  ·
                    refine ⟨627276525543398908306891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345474802898127510970085 627276525543398908306891)
                    ·
                      rfl

theorem cell22_1832425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1832425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832425 prefixEnd_1832425 := by exact prefixLift 1832425
  have htrace : WordTrace (prefixWord ++ tailWord_1832425) baseStart_1832425 baseEnd_1832425 := by
    simpa [prefixWord, tailWord_1832425, baseEnd_1832425] using wordTrace_append hprefix tailTrace_1832425
  have hstable : (prefixWord ++ tailWord_1832425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832425).length < 2 ^ (prefixWord ++ tailWord_1832425).sum := by decide
  have hdescent : baseEnd_1832425 < baseStart_1832425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832442 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1832442 : Nat := 118140960795 + 1832442 * 2 ^ 59
def prefixEnd_1832442 : Nat := 4983230072969 + 3 ^ 40 * 1832442 * 2
def baseEnd_1832442 : Nat := 627282344990816530631839

theorem tailTrace_1832442 : CollatzResearch.WordTrace tailWord_1832442 prefixEnd_1832442 627282344990816530631839 := by
  unfold tailWord_1832442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708662606845766255748895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44556433618255376681997053 16708662606845766255748895)
  ·
    refine ⟨25062993910268649383623343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16708662606845766255748895 25062993910268649383623343)
    ·
      refine ⟨37594490865402974075435015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25062993910268649383623343 37594490865402974075435015)
      ·
        refine ⟨56391736298104461113152523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37594490865402974075435015 56391736298104461113152523)
        ·
          refine ⟨84587604447156691669728785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56391736298104461113152523 84587604447156691669728785)
          ·
            refine ⟨63440703335367518752296589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84587604447156691669728785 63440703335367518752296589)
            ·
              refine ⟨23790263750762819532111221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63440703335367518752296589 23790263750762819532111221)
              ·
                refine ⟨2230337226634014331135427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23790263750762819532111221 2230337226634014331135427)
                ·
                  refine ⟨3345505839951021496703141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230337226634014331135427 3345505839951021496703141)
                  ·
                    refine ⟨627282344990816530631839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345505839951021496703141 627282344990816530631839)
                    ·
                      rfl

theorem cell22_1832442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1832442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832442 prefixEnd_1832442 := by exact prefixLift 1832442
  have htrace : WordTrace (prefixWord ++ tailWord_1832442) baseStart_1832442 baseEnd_1832442 := by
    simpa [prefixWord, tailWord_1832442, baseEnd_1832442] using wordTrace_append hprefix tailTrace_1832442
  have hstable : (prefixWord ++ tailWord_1832442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832442).length < 2 ^ (prefixWord ++ tailWord_1832442).sum := by decide
  have hdescent : baseEnd_1832442 < baseStart_1832442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832450 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1832450 : Nat := 118140960795 + 1832450 * 2 ^ 59
def prefixEnd_1832450 : Nat := 4983230072969 + 3 ^ 40 * 1832450 * 2
def baseEnd_1832450 : Nat := 627285083554307176431815

theorem tailTrace_1832450 : CollatzResearch.WordTrace tailWord_1832450 prefixEnd_1832450 627285083554307176431815 := by
  unfold tailWord_1832450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708735552838520597321701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44556628140902721592857869 16708735552838520597321701)
  ·
    refine ⟨3132887916157222611997819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16708735552838520597321701 3132887916157222611997819)
    ·
      refine ⟨4699331874235833917996729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3132887916157222611997819 4699331874235833917996729)
      ·
        refine ⟨3524498905676875438497547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4699331874235833917996729 3524498905676875438497547)
        ·
          refine ⟨5286748358515313157746321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524498905676875438497547 5286748358515313157746321)
          ·
            refine ⟨3965061268886484868309741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5286748358515313157746321 3965061268886484868309741)
            ·
              refine ⟨1486897975832431825616153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3965061268886484868309741 1486897975832431825616153)
              ·
                refine ⟨1115173481874323869212115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486897975832431825616153 1115173481874323869212115)
                ·
                  refine ⟨1672760222811485803818173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115173481874323869212115 1672760222811485803818173)
                  ·
                    refine ⟨627285083554307176431815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672760222811485803818173 627285083554307176431815)
                    ·
                      rfl

theorem cell22_1832450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1832450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832450 prefixEnd_1832450 := by exact prefixLift 1832450
  have htrace : WordTrace (prefixWord ++ tailWord_1832450) baseStart_1832450 baseEnd_1832450 := by
    simpa [prefixWord, tailWord_1832450, baseEnd_1832450] using wordTrace_append hprefix tailTrace_1832450
  have hstable : (prefixWord ++ tailWord_1832450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832450).length < 2 ^ (prefixWord ++ tailWord_1832450).sum := by decide
  have hdescent : baseEnd_1832450 < baseStart_1832450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832502 : List Nat := [5, 1, 2, 1, 13]
def baseStart_1832502 : Nat := 118140960795 + 1832502 * 2 ^ 59
def prefixEnd_1832502 : Nat := 4983230072969 + 3 ^ 40 * 1832502 * 2
def baseEnd_1832502 : Nat := 2581493350687227877085

theorem tailTrace_1832502 : CollatzResearch.WordTrace tailWord_1832502 prefixEnd_1832502 2581493350687227877085 := by
  unfold tailWord_1832502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177302425447855954386235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44557892538110463513453173 4177302425447855954386235)
  ·
    refine ⟨6265953638171783931579353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4177302425447855954386235 6265953638171783931579353)
    ·
      refine ⟨4699465228628837948684515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6265953638171783931579353 4699465228628837948684515)
      ·
        refine ⟨7049197842943256923026773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699465228628837948684515 7049197842943256923026773)
        ·
          refine ⟨2581493350687227877085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7049197842943256923026773 2581493350687227877085)
          ·
            rfl

theorem cell22_1832502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 13].length) (baseStart_1832502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832502 prefixEnd_1832502 := by exact prefixLift 1832502
  have htrace : WordTrace (prefixWord ++ tailWord_1832502) baseStart_1832502 baseEnd_1832502 := by
    simpa [prefixWord, tailWord_1832502, baseEnd_1832502] using wordTrace_append hprefix tailTrace_1832502
  have hstable : (prefixWord ++ tailWord_1832502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832502).length < 2 ^ (prefixWord ++ tailWord_1832502).sum := by decide
  have hdescent : baseEnd_1832502 < baseStart_1832502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832508 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_1832508 : Nat := 118140960795 + 1832508 * 2 ^ 59
def prefixEnd_1832508 : Nat := 4983230072969 + 3 ^ 40 * 1832508 * 2
def baseEnd_1832508 : Nat := 209101646046538119493879

theorem tailTrace_1832508 : CollatzResearch.WordTrace tailWord_1832508 prefixEnd_1832508 209101646046538119493879 := by
  unfold tailWord_1832508
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418528822571979147449089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44558038430095972196598785 33418528822571979147449089)
  ·
    refine ⟨25063896616928984360586817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33418528822571979147449089 25063896616928984360586817)
    ·
      refine ⟨18797922462696738270440113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25063896616928984360586817 18797922462696738270440113)
      ·
        refine ⟨14098441847022553702830085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18797922462696738270440113 14098441847022553702830085)
        ·
          refine ⟨2643457846316728819280641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14098441847022553702830085 2643457846316728819280641)
          ·
            refine ⟨1982593384737546614460481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643457846316728819280641 1982593384737546614460481)
            ·
              refine ⟨1486945038553159960845361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982593384737546614460481 1486945038553159960845361)
              ·
                refine ⟨1115208778914869970634021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486945038553159960845361 1115208778914869970634021)
                ·
                  refine ⟨209101646046538119493879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115208778914869970634021 209101646046538119493879)
                  ·
                    rfl

theorem cell22_1832508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_1832508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832508 prefixEnd_1832508 := by exact prefixLift 1832508
  have htrace : WordTrace (prefixWord ++ tailWord_1832508) baseStart_1832508 baseEnd_1832508 := by
    simpa [prefixWord, tailWord_1832508, baseEnd_1832508] using wordTrace_append hprefix tailTrace_1832508
  have hstable : (prefixWord ++ tailWord_1832508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832508).length < 2 ^ (prefixWord ++ tailWord_1832508).sum := by decide
  have hdescent : baseEnd_1832508 < baseStart_1832508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832519 : List Nat := [1, 1, 4, 1, 5, 2, 1, 7]
def baseStart_1832519 : Nat := 118140960795 + 1832519 * 2 ^ 59
def prefixEnd_1832519 : Nat := 4983230072969 + 3 ^ 40 * 1832519 * 2
def baseEnd_1832519 : Nat := 69700967073823777384067

theorem tailTrace_1832519 : CollatzResearch.WordTrace tailWord_1832519 prefixEnd_1832519 69700967073823777384067 := by
  unfold tailWord_1832519
  simp only [CollatzResearch.WordTrace]
  refine ⟨66837458848104107173548611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44558305898736071449032407 66837458848104107173548611)
  ·
    refine ⟨100256188272156160760322917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66837458848104107173548611 100256188272156160760322917)
    ·
      refine ⟨18798035301029280142560547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100256188272156160760322917 18798035301029280142560547)
      ·
        refine ⟨28197052951543920213840821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18798035301029280142560547 28197052951543920213840821)
        ·
          refine ⟨2643473714207242520047577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28197052951543920213840821 2643473714207242520047577)
          ·
            refine ⟨1982605285655431890035683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643473714207242520047577 1982605285655431890035683)
            ·
              refine ⟨2973907928483147835053525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982605285655431890035683 2973907928483147835053525)
              ·
                refine ⟨69700967073823777384067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2973907928483147835053525 69700967073823777384067)
                ·
                  rfl

theorem cell22_1832519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 7].length) (baseStart_1832519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832519 prefixEnd_1832519 := by exact prefixLift 1832519
  have htrace : WordTrace (prefixWord ++ tailWord_1832519) baseStart_1832519 baseEnd_1832519 := by
    simpa [prefixWord, tailWord_1832519, baseEnd_1832519] using wordTrace_append hprefix tailTrace_1832519
  have hstable : (prefixWord ++ tailWord_1832519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832519).length < 2 ^ (prefixWord ++ tailWord_1832519).sum := by decide
  have hdescent : baseEnd_1832519 < baseStart_1832519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832532 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1832532 : Nat := 118140960795 + 1832532 * 2 ^ 59
def prefixEnd_1832532 : Nat := 4983230072969 + 3 ^ 40 * 1832532 * 2
def baseEnd_1832532 : Nat := 627313153830086295881563

theorem tailTrace_1832532 : CollatzResearch.WordTrace tailWord_1832532 prefixEnd_1832532 627313153830086295881563 := by
  unfold tailWord_1832532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418966498528505196885925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44558621998038006929181233 33418966498528505196885925)
  ·
    refine ⟨6266056218474094724416111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33418966498528505196885925 6266056218474094724416111)
    ·
      refine ⟨9399084327711142086624167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6266056218474094724416111 9399084327711142086624167)
      ·
        refine ⟨14098626491566713129936251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399084327711142086624167 14098626491566713129936251)
        ·
          refine ⟨21147939737350069694904377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098626491566713129936251 21147939737350069694904377)
          ·
            refine ⟨15860954803012552271178283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21147939737350069694904377 15860954803012552271178283)
            ·
              refine ⟨23791432204518828406767425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15860954803012552271178283 23791432204518828406767425)
              ·
                refine ⟨17843574153389121305075569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23791432204518828406767425 17843574153389121305075569)
                ·
                  refine ⟨13382680615041840978806677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17843574153389121305075569 13382680615041840978806677)
                  ·
                    refine ⟨627313153830086295881563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13382680615041840978806677 627313153830086295881563)
                    ·
                      rfl

theorem cell22_1832532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1832532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832532 prefixEnd_1832532 := by exact prefixLift 1832532
  have htrace : WordTrace (prefixWord ++ tailWord_1832532) baseStart_1832532 baseEnd_1832532 := by
    simpa [prefixWord, tailWord_1832532, baseEnd_1832532] using wordTrace_append hprefix tailTrace_1832532
  have hstable : (prefixWord ++ tailWord_1832532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832532).length < 2 ^ (prefixWord ++ tailWord_1832532).sum := by decide
  have hdescent : baseEnd_1832532 < baseStart_1832532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832551 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1832551 : Nat := 118140960795 + 1832551 * 2 ^ 59
def prefixEnd_1832551 : Nat := 4983230072969 + 3 ^ 40 * 1832551 * 2
def baseEnd_1832551 : Nat := 627319657918376579656505

theorem tailTrace_1832551 : CollatzResearch.WordTrace tailWord_1832551 prefixEnd_1832551 627319657918376579656505 := by
  unfold tailWord_1832551
  simp only [CollatzResearch.WordTrace]
  refine ⟨66838625983988176638713507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44559083989325451092475671 66838625983988176638713507)
  ·
    refine ⟨100257938975982264958070261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66838625983988176638713507 100257938975982264958070261)
    ·
      refine ⟨9399181778998337339819087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100257938975982264958070261 9399181778998337339819087)
      ·
        refine ⟨14098772668497506009728631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399181778998337339819087 14098772668497506009728631)
        ·
          refine ⟨21148159002746259014592947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098772668497506009728631 21148159002746259014592947)
          ·
            refine ⟨31722238504119388521889421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21148159002746259014592947 31722238504119388521889421)
            ·
              refine ⟨11895839439044770695708533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31722238504119388521889421 11895839439044770695708533)
              ·
                refine ⟨1115234947410447252722675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11895839439044770695708533 1115234947410447252722675)
                ·
                  refine ⟨1672852421115670879084013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115234947410447252722675 1672852421115670879084013)
                  ·
                    refine ⟨627319657918376579656505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672852421115670879084013 627319657918376579656505)
                    ·
                      rfl

theorem cell22_1832551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1832551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832551 prefixEnd_1832551 := by exact prefixLift 1832551
  have htrace : WordTrace (prefixWord ++ tailWord_1832551) baseStart_1832551 baseEnd_1832551 := by
    simpa [prefixWord, tailWord_1832551, baseEnd_1832551] using wordTrace_append hprefix tailTrace_1832551
  have hstable : (prefixWord ++ tailWord_1832551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832551).length < 2 ^ (prefixWord ++ tailWord_1832551).sum := by decide
  have hdescent : baseEnd_1832551 < baseStart_1832551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832624 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_1832624 : Nat := 118140960795 + 1832624 * 2 ^ 59
def prefixEnd_1832624 : Nat := 4983230072969 + 3 ^ 40 * 1832624 * 2
def baseEnd_1832624 : Nat := 627344647310228722581281

theorem tailTrace_1832624 : CollatzResearch.WordTrace tailWord_1832624 prefixEnd_1832624 627344647310228722581281 := by
  unfold tailWord_1832624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33420644256361855053060463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44560859008482473404080617 33420644256361855053060463)
  ·
    refine ⟨50130966384542782579590695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33420644256361855053060463 50130966384542782579590695)
    ·
      refine ⟨75196449576814173869386043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50130966384542782579590695 75196449576814173869386043)
      ·
        refine ⟨112794674365221260804079065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75196449576814173869386043 112794674365221260804079065)
        ·
          refine ⟨84596005773915945603059299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112794674365221260804079065 84596005773915945603059299)
          ·
            refine ⟨126894008660873918404588949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84596005773915945603059299 126894008660873918404588949)
            ·
              refine ⟨5948156655978464925215107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126894008660873918404588949 5948156655978464925215107)
              ·
                refine ⟨8922234983967697387822661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948156655978464925215107 8922234983967697387822661)
                ·
                  refine ⟨1672919059493943260216749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8922234983967697387822661 1672919059493943260216749)
                  ·
                    refine ⟨627344647310228722581281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672919059493943260216749 627344647310228722581281)
                    ·
                      rfl

theorem cell22_1832624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_1832624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832624 prefixEnd_1832624 := by exact prefixLift 1832624
  have htrace : WordTrace (prefixWord ++ tailWord_1832624) baseStart_1832624 baseEnd_1832624 := by
    simpa [prefixWord, tailWord_1832624, baseEnd_1832624] using wordTrace_append hprefix tailTrace_1832624
  have hstable : (prefixWord ++ tailWord_1832624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832624).length < 2 ^ (prefixWord ++ tailWord_1832624).sum := by decide
  have hdescent : baseEnd_1832624 < baseStart_1832624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832662 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1832662 : Nat := 118140960795 + 1832662 * 2 ^ 59
def prefixEnd_1832662 : Nat := 4983230072969 + 3 ^ 40 * 1832662 * 2
def baseEnd_1832662 : Nat := 627357655486809290131165

theorem tailTrace_1832662 : CollatzResearch.WordTrace tailWord_1832662 prefixEnd_1832662 627357655486809290131165 := by
  unfold tailWord_1832662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177667155411627662250265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44561782991057361730669493 4177667155411627662250265)
  ·
    refine ⟨3133250366558720746687699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4177667155411627662250265 3133250366558720746687699)
    ·
      refine ⟨4699875549838081120031549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133250366558720746687699 4699875549838081120031549)
      ·
        refine ⟨1762453331189280420011831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4699875549838081120031549 1762453331189280420011831)
        ·
          refine ⟨2643679996783920630017747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762453331189280420011831 2643679996783920630017747)
          ·
            refine ⟨3965519995175880945026621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643679996783920630017747 3965519995175880945026621)
            ·
              refine ⟨1487069998190955354384983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3965519995175880945026621 1487069998190955354384983)
              ·
                refine ⟨2230604997286433031577475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487069998190955354384983 2230604997286433031577475)
                ·
                  refine ⟨3345907495929649547366213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230604997286433031577475 3345907495929649547366213)
                  ·
                    refine ⟨627357655486809290131165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345907495929649547366213 627357655486809290131165)
                    ·
                      rfl

theorem cell22_1832662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1832662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832662 prefixEnd_1832662 := by exact prefixLift 1832662
  have htrace : WordTrace (prefixWord ++ tailWord_1832662) baseStart_1832662 baseEnd_1832662 := by
    simpa [prefixWord, tailWord_1832662, baseEnd_1832662] using wordTrace_append hprefix tailTrace_1832662
  have hstable : (prefixWord ++ tailWord_1832662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832662).length < 2 ^ (prefixWord ++ tailWord_1832662).sum := by decide
  have hdescent : baseEnd_1832662 < baseStart_1832662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832686 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1832686 : Nat := 118140960795 + 1832686 * 2 ^ 59
def prefixEnd_1832686 : Nat := 4983230072969 + 3 ^ 40 * 1832686 * 2
def baseEnd_1832686 : Nat := 627365871177281227531091

theorem tailTrace_1832686 : CollatzResearch.WordTrace tailWord_1832686 prefixEnd_1832686 627365871177281227531091 := by
  unfold tailWord_1832686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355443729812386836859739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44562366558999396463251941 8355443729812386836859739)
  ·
    refine ⟨12533165594718580255289609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8355443729812386836859739 12533165594718580255289609)
    ·
      refine ⟨9399874196038935191467207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12533165594718580255289609 9399874196038935191467207)
      ·
        refine ⟨14099811294058402787200811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399874196038935191467207 14099811294058402787200811)
        ·
          refine ⟨21149716941087604180801217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099811294058402787200811 21149716941087604180801217)
          ·
            refine ⟨15862287705815703135600913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21149716941087604180801217 15862287705815703135600913)
            ·
              refine ⟨11896715779361777351700685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15862287705815703135600913 11896715779361777351700685)
              ·
                refine ⟨4461268417260666506887757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11896715779361777351700685 4461268417260666506887757)
                ·
                  refine ⟨1672975656472749940082909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4461268417260666506887757 1672975656472749940082909)
                  ·
                    refine ⟨627365871177281227531091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1672975656472749940082909 627365871177281227531091)
                    ·
                      rfl

theorem cell22_1832686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1832686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832686 prefixEnd_1832686 := by exact prefixLift 1832686
  have htrace : WordTrace (prefixWord ++ tailWord_1832686) baseStart_1832686 baseEnd_1832686 := by
    simpa [prefixWord, tailWord_1832686, baseEnd_1832686] using wordTrace_append hprefix tailTrace_1832686
  have hstable : (prefixWord ++ tailWord_1832686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832686).length < 2 ^ (prefixWord ++ tailWord_1832686).sum := by decide
  have hdescent : baseEnd_1832686 < baseStart_1832686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832750 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_1832750 : Nat := 118140960795 + 1832750 * 2 ^ 59
def prefixEnd_1832750 : Nat := 4983230072969 + 3 ^ 40 * 1832750 * 2
def baseEnd_1832750 : Nat := 209129259895068797976965

theorem tailTrace_1832750 : CollatzResearch.WordTrace tailWord_1832750 prefixEnd_1832750 209129259895068797976965 := by
  unfold tailWord_1832750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355735513783404203150963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44563922740178155750138469 8355735513783404203150963)
  ·
    refine ⟨12533603270675106304726445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8355735513783404203150963 12533603270675106304726445)
    ·
      refine ⟨4700101226503164864272417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12533603270675106304726445 4700101226503164864272417)
      ·
        refine ⟨3525075919877373648204313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700101226503164864272417 3525075919877373648204313)
        ·
          refine ⟨2643806939908030236153235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3525075919877373648204313 2643806939908030236153235)
          ·
            refine ⟨3965710409862045354229853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643806939908030236153235 3965710409862045354229853)
            ·
              refine ⟨1487141403698267007836195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3965710409862045354229853 1487141403698267007836195)
              ·
                refine ⟨2230712105547400511754293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487141403698267007836195 2230712105547400511754293)
                ·
                  refine ⟨209129259895068797976965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2230712105547400511754293 209129259895068797976965)
                  ·
                    rfl

theorem cell22_1832750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_1832750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832750 prefixEnd_1832750 := by exact prefixLift 1832750
  have htrace : WordTrace (prefixWord ++ tailWord_1832750) baseStart_1832750 baseEnd_1832750 := by
    simpa [prefixWord, tailWord_1832750, baseEnd_1832750] using wordTrace_append hprefix tailTrace_1832750
  have hstable : (prefixWord ++ tailWord_1832750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832750).length < 2 ^ (prefixWord ++ tailWord_1832750).sum := by decide
  have hdescent : baseEnd_1832750 < baseStart_1832750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832759 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1832759 : Nat := 118140960795 + 1832759 * 2 ^ 59
def prefixEnd_1832759 : Nat := 4983230072969 + 3 ^ 40 * 1832759 * 2
def baseEnd_1832759 : Nat := 627390860569133370455867

theorem tailTrace_1832759 : CollatzResearch.WordTrace tailWord_1832759 prefixEnd_1832759 627390860569133370455867 := by
  unfold tailWord_1832759
  simp only [CollatzResearch.WordTrace]
  refine ⟨66846212367234628162285331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44564141578156418774856887 66846212367234628162285331)
  ·
    refine ⟨100269318550851942243427997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66846212367234628162285331 100269318550851942243427997)
    ·
      refine ⟨37600994456569478341285499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100269318550851942243427997 37600994456569478341285499)
      ·
        refine ⟨56401491684854217511928249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37600994456569478341285499 56401491684854217511928249)
        ·
          refine ⟨42301118763640663133946187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56401491684854217511928249 42301118763640663133946187)
          ·
            refine ⟨63451678145460994700919281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42301118763640663133946187 63451678145460994700919281)
            ·
              refine ⟨47588758609095746025689461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63451678145460994700919281 47588758609095746025689461)
              ·
                refine ⟨4461446119602726189908387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47588758609095746025689461 4461446119602726189908387)
                ·
                  refine ⟨6692169179404089284862581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461446119602726189908387 6692169179404089284862581)
                  ·
                    refine ⟨627390860569133370455867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6692169179404089284862581 627390860569133370455867)
                    ·
                      rfl

theorem cell22_1832759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1832759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832759 prefixEnd_1832759 := by exact prefixLift 1832759
  have htrace : WordTrace (prefixWord ++ tailWord_1832759) baseStart_1832759 baseEnd_1832759 := by
    simpa [prefixWord, tailWord_1832759, baseEnd_1832759] using wordTrace_append hprefix tailTrace_1832759
  have hstable : (prefixWord ++ tailWord_1832759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832759).length < 2 ^ (prefixWord ++ tailWord_1832759).sum := by decide
  have hdescent : baseEnd_1832759 < baseStart_1832759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832776 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_1832776 : Nat := 118140960795 + 1832776 * 2 ^ 59
def prefixEnd_1832776 : Nat := 4983230072969 + 3 ^ 40 * 1832776 * 2
def baseEnd_1832776 : Nat := 627396680016550992780815

theorem tailTrace_1832776 : CollatzResearch.WordTrace tailWord_1832776 prefixEnd_1832776 627396680016550992780815 := by
  unfold tailWord_1832776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423416204086520032827091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44564554938782026710436121 33423416204086520032827091)
  ·
    refine ⟨50135124306129780049240637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33423416204086520032827091 50135124306129780049240637)
    ·
      refine ⟨18800671614798667518465239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50135124306129780049240637 18800671614798667518465239)
      ·
        refine ⟨28201007422198001277697859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18800671614798667518465239 28201007422198001277697859)
        ·
          refine ⟨42301511133297001916546789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28201007422198001277697859 42301511133297001916546789)
          ·
            refine ⟨7931533337493187859352523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42301511133297001916546789 7931533337493187859352523)
            ·
              refine ⟨11897300006239781789028785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931533337493187859352523 11897300006239781789028785)
              ·
                refine ⟨8922975004679836341771589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11897300006239781789028785 8922975004679836341771589)
                ·
                  refine ⟨1673057813377469314082173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8922975004679836341771589 1673057813377469314082173)
                  ·
                    refine ⟨627396680016550992780815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673057813377469314082173 627396680016550992780815)
                    ·
                      rfl

theorem cell22_1832776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_1832776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832776 prefixEnd_1832776 := by exact prefixLift 1832776
  have htrace : WordTrace (prefixWord ++ tailWord_1832776) baseStart_1832776 baseEnd_1832776 := by
    simpa [prefixWord, tailWord_1832776, baseEnd_1832776] using wordTrace_append hprefix tailTrace_1832776
  have hstable : (prefixWord ++ tailWord_1832776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832776).length < 2 ^ (prefixWord ++ tailWord_1832776).sum := by decide
  have hdescent : baseEnd_1832776 < baseStart_1832776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832789 : List Nat := [1, 3, 2, 2, 2, 2, 10]
def baseStart_1832789 : Nat := 118140960795 + 1832789 * 2 ^ 59
def prefixEnd_1832789 : Nat := 4983230072969 + 3 ^ 40 * 1832789 * 2
def baseEnd_1832789 : Nat := 23237078895637899711325

theorem tailTrace_1832789 : CollatzResearch.WordTrace tailWord_1832789 prefixEnd_1832789 23237078895637899711325 := by
  unfold tailWord_1832789
  simp only [CollatzResearch.WordTrace]
  refine ⟨66847306557125943285877421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44564871038083962190584947 66847306557125943285877421)
  ·
    refine ⟨25067739958922228732204033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66847306557125943285877421 25067739958922228732204033)
    ·
      refine ⟨18800804969191671549153025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25067739958922228732204033 18800804969191671549153025)
      ·
        refine ⟨14100603726893753661864769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18800804969191671549153025 14100603726893753661864769)
        ·
          refine ⟨10575452795170315246398577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14100603726893753661864769 10575452795170315246398577)
          ·
            refine ⟨7931589596377736434798933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10575452795170315246398577 7931589596377736434798933)
            ·
              refine ⟨23237078895637899711325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7931589596377736434798933 23237078895637899711325)
              ·
                rfl

theorem cell22_1832789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 10].length) (baseStart_1832789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832789 prefixEnd_1832789 := by exact prefixLift 1832789
  have htrace : WordTrace (prefixWord ++ tailWord_1832789) baseStart_1832789 baseEnd_1832789 := by
    simpa [prefixWord, tailWord_1832789, baseEnd_1832789] using wordTrace_append hprefix tailTrace_1832789
  have hstable : (prefixWord ++ tailWord_1832789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832789).length < 2 ^ (prefixWord ++ tailWord_1832789).sum := by decide
  have hdescent : baseEnd_1832789 < baseStart_1832789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832855 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 1, 3]
def baseStart_1832855 : Nat := 118140960795 + 1832855 * 2 ^ 59
def prefixEnd_1832855 : Nat := 4983230072969 + 3 ^ 40 * 1832855 * 2
def baseEnd_1832855 : Nat := 627423723331021120055573

theorem tailTrace_1832855 : CollatzResearch.WordTrace tailWord_1832855 prefixEnd_1832855 627423723331021120055573 := by
  unfold tailWord_1832855
  simp only [CollatzResearch.WordTrace]
  refine ⟨66849713774886836557780019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44566475849924557705186679 66849713774886836557780019)
  ·
    refine ⟨100274570662330254836670029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66849713774886836557780019 100274570662330254836670029)
    ·
      refine ⟨37602963998373845563751261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100274570662330254836670029 37602963998373845563751261)
      ·
        refine ⟨14101111499390192086406723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37602963998373845563751261 14101111499390192086406723)
        ·
          refine ⟨21151667249085288129610085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101111499390192086406723 21151667249085288129610085)
          ·
            refine ⟨3965937609203491524301891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21151667249085288129610085 3965937609203491524301891)
            ·
              refine ⟨5948906413805237286452837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965937609203491524301891 5948906413805237286452837)
              ·
                refine ⟨1115419952588481991209907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5948906413805237286452837 1115419952588481991209907)
                ·
                  refine ⟨1673129928882722986814861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115419952588481991209907 1673129928882722986814861)
                  ·
                    refine ⟨627423723331021120055573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673129928882722986814861 627423723331021120055573)
                    ·
                      rfl

theorem cell22_1832855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_1832855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832855 prefixEnd_1832855 := by exact prefixLift 1832855
  have htrace : WordTrace (prefixWord ++ tailWord_1832855) baseStart_1832855 baseEnd_1832855 := by
    simpa [prefixWord, tailWord_1832855, baseEnd_1832855] using wordTrace_append hprefix tailTrace_1832855
  have hstable : (prefixWord ++ tailWord_1832855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832855).length < 2 ^ (prefixWord ++ tailWord_1832855).sum := by decide
  have hdescent : baseEnd_1832855 < baseStart_1832855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832872 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1832872 : Nat := 118140960795 + 1832872 * 2 ^ 59
def prefixEnd_1832872 : Nat := 4983230072969 + 3 ^ 40 * 1832872 * 2
def baseEnd_1832872 : Nat := 627429542778438742380521

theorem tailTrace_1832872 : CollatzResearch.WordTrace tailWord_1832872 prefixEnd_1832872 627429542778438742380521 := by
  unfold tailWord_1832872
  simp only [CollatzResearch.WordTrace]
  refine ⟨33425166907912624230574435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44566889210550165640765913 33425166907912624230574435)
  ·
    refine ⟨50137750361868936345861653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33425166907912624230574435 50137750361868936345861653)
    ·
      refine ⟨2350207048212606391212265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50137750361868936345861653 2350207048212606391212265)
      ·
        refine ⟨1762655286159454793409199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350207048212606391212265 1762655286159454793409199)
        ·
          refine ⟨2643982929239182190113799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762655286159454793409199 2643982929239182190113799)
          ·
            refine ⟨3965974393858773285170699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643982929239182190113799 3965974393858773285170699)
            ·
              refine ⟨5948961590788159927756049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965974393858773285170699 5948961590788159927756049)
              ·
                refine ⟨4461721193091119945817037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948961590788159927756049 4461721193091119945817037)
                ·
                  refine ⟨1673145447409169979681389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4461721193091119945817037 1673145447409169979681389)
                  ·
                    refine ⟨627429542778438742380521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673145447409169979681389 627429542778438742380521)
                    ·
                      rfl

theorem cell22_1832872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1832872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832872 prefixEnd_1832872 := by exact prefixLift 1832872
  have htrace : WordTrace (prefixWord ++ tailWord_1832872) baseStart_1832872 baseEnd_1832872 := by
    simpa [prefixWord, tailWord_1832872, baseEnd_1832872] using wordTrace_append hprefix tailTrace_1832872
  have hstable : (prefixWord ++ tailWord_1832872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832872).length < 2 ^ (prefixWord ++ tailWord_1832872).sum := by decide
  have hdescent : baseEnd_1832872 < baseStart_1832872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832928 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_1832928 : Nat := 118140960795 + 1832928 * 2 ^ 59
def prefixEnd_1832928 : Nat := 4983230072969 + 3 ^ 40 * 1832928 * 2
def baseEnd_1832928 : Nat := 627448712722873262980349

theorem tailTrace_1832928 : CollatzResearch.WordTrace tailWord_1832928 prefixEnd_1832928 627448712722873262980349 := by
  unfold tailWord_1832928
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426188151811185012593719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44568250869081580016791625 33426188151811185012593719)
  ·
    refine ⟨50139282227716777518890579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33426188151811185012593719 50139282227716777518890579)
    ·
      refine ⟨75208923341575166278335869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50139282227716777518890579 75208923341575166278335869)
      ·
        refine ⟨28203346253090687354375951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75208923341575166278335869 28203346253090687354375951)
        ·
          refine ⟨42305019379636031031563927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28203346253090687354375951 42305019379636031031563927)
          ·
            refine ⟨63457529069454046547345891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42305019379636031031563927 63457529069454046547345891)
            ·
              refine ⟨95186293604181069821018837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63457529069454046547345891 95186293604181069821018837)
              ·
                refine ⟨2230928756347993823930129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95186293604181069821018837 2230928756347993823930129)
                ·
                  refine ⟨1673196567260995367947597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2230928756347993823930129 1673196567260995367947597)
                  ·
                    refine ⟨627448712722873262980349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673196567260995367947597 627448712722873262980349)
                    ·
                      rfl

theorem cell22_1832928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_1832928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832928 prefixEnd_1832928 := by exact prefixLift 1832928
  have htrace : WordTrace (prefixWord ++ tailWord_1832928) baseStart_1832928 baseEnd_1832928 := by
    simpa [prefixWord, tailWord_1832928, baseEnd_1832928] using wordTrace_append hprefix tailTrace_1832928
  have hstable : (prefixWord ++ tailWord_1832928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832928).length < 2 ^ (prefixWord ++ tailWord_1832928).sum := by decide
  have hdescent : baseEnd_1832928 < baseStart_1832928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832958 : List Nat := [4, 2, 2, 2, 1, 1, 10]
def baseStart_1832958 : Nat := 118140960795 + 1832958 * 2 ^ 59
def prefixEnd_1832958 : Nat := 4983230072969 + 3 ^ 40 * 1832958 * 2
def baseEnd_1832958 : Nat := 23239221567998636471491

theorem tailTrace_1832958 : CollatzResearch.WordTrace tailWord_1832958 prefixEnd_1832958 23239221567998636471491 := by
  unfold tailWord_1832958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8356683811689210643597441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44568980329009123432519685 8356683811689210643597441)
  ·
    refine ⟨6267512858766907982698081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8356683811689210643597441 6267512858766907982698081)
    ·
      refine ⟨4700634644075180987023561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6267512858766907982698081 4700634644075180987023561)
      ·
        refine ⟨3525475983056385740267671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700634644075180987023561 3525475983056385740267671)
        ·
          refine ⟨5288213974584578610401507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525475983056385740267671 5288213974584578610401507)
          ·
            refine ⟨7932320961876867915602261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288213974584578610401507 7932320961876867915602261)
            ·
              refine ⟨23239221567998636471491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7932320961876867915602261 23239221567998636471491)
              ·
                rfl

theorem cell22_1832958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 10].length) (baseStart_1832958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832958 prefixEnd_1832958 := by exact prefixLift 1832958
  have htrace : WordTrace (prefixWord ++ tailWord_1832958) baseStart_1832958 baseEnd_1832958 := by
    simpa [prefixWord, tailWord_1832958, baseEnd_1832958] using wordTrace_append hprefix tailTrace_1832958
  have hstable : (prefixWord ++ tailWord_1832958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832958).length < 2 ^ (prefixWord ++ tailWord_1832958).sum := by decide
  have hdescent : baseEnd_1832958 < baseStart_1832958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832964 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_1832964 : Nat := 118140960795 + 1832964 * 2 ^ 59
def prefixEnd_1832964 : Nat := 4983230072969 + 3 ^ 40 * 1832964 * 2
def baseEnd_1832964 : Nat := 209153678752860389693413

theorem tailTrace_1832964 : CollatzResearch.WordTrace tailWord_1832964 prefixEnd_1832964 209153678752860389693413 := by
  unfold tailWord_1832964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426844665745974086748973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44569126220994632115665297 33426844665745974086748973)
  ·
    refine ⟨12535066749654740282530865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33426844665745974086748973 12535066749654740282530865)
    ·
      refine ⟨9401300062241055211898149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12535066749654740282530865 9401300062241055211898149)
      ·
        refine ⟨1762743761670197852230903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9401300062241055211898149 1762743761670197852230903)
        ·
          refine ⟨2644115642505296778346355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762743761670197852230903 2644115642505296778346355)
          ·
            refine ⟨3966173463757945167519533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644115642505296778346355 3966173463757945167519533)
            ·
              refine ⟨1487315048909229437819825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3966173463757945167519533 1487315048909229437819825)
              ·
                refine ⟨1115486286681922078364869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487315048909229437819825 1115486286681922078364869)
                ·
                  refine ⟨209153678752860389693413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115486286681922078364869 209153678752860389693413)
                  ·
                    rfl

theorem cell22_1832964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_1832964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832964 prefixEnd_1832964 := by exact prefixLift 1832964
  have htrace : WordTrace (prefixWord ++ tailWord_1832964) baseStart_1832964 baseEnd_1832964 := by
    simpa [prefixWord, tailWord_1832964, baseEnd_1832964] using wordTrace_append hprefix tailTrace_1832964
  have hstable : (prefixWord ++ tailWord_1832964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832964).length < 2 ^ (prefixWord ++ tailWord_1832964).sum := by decide
  have hdescent : baseEnd_1832964 < baseStart_1832964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832971 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_1832971 : Nat := 118140960795 + 1832971 * 2 ^ 59
def prefixEnd_1832971 : Nat := 4983230072969 + 3 ^ 40 * 1832971 * 2
def baseEnd_1832971 : Nat := 627463432501635484155217

theorem tailTrace_1832971 : CollatzResearch.WordTrace tailWord_1832971 prefixEnd_1832971 627463432501635484155217 := by
  unfold tailWord_1832971
  simp only [CollatzResearch.WordTrace]
  refine ⟨66853944642466588369002767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44569296428311058912668511 66853944642466588369002767)
  ·
    refine ⟨100280916963699882553504151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66853944642466588369002767 100280916963699882553504151)
    ·
      refine ⟨150421375445549823830256227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100280916963699882553504151 150421375445549823830256227)
      ·
        refine ⟨225632063168324735745384341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150421375445549823830256227 225632063168324735745384341)
        ·
          refine ⟨10576502961015221988064891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225632063168324735745384341 10576502961015221988064891)
          ·
            refine ⟨15864754441522832982097337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10576502961015221988064891 15864754441522832982097337)
            ·
              refine ⟨11898565831142124736573003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15864754441522832982097337 11898565831142124736573003)
              ·
                refine ⟨17847848746713187104859505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11898565831142124736573003 17847848746713187104859505)
                ·
                  refine ⟨13385886560034890328644629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17847848746713187104859505 13385886560034890328644629)
                  ·
                    refine ⟨627463432501635484155217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13385886560034890328644629 627463432501635484155217)
                    ·
                      rfl

theorem cell22_1832971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_1832971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1832971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1832971 prefixEnd_1832971 := by exact prefixLift 1832971
  have htrace : WordTrace (prefixWord ++ tailWord_1832971) baseStart_1832971 baseEnd_1832971 := by
    simpa [prefixWord, tailWord_1832971, baseEnd_1832971] using wordTrace_append hprefix tailTrace_1832971
  have hstable : (prefixWord ++ tailWord_1832971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832971).length < 2 ^ (prefixWord ++ tailWord_1832971).sum := by decide
  have hdescent : baseEnd_1832971 < baseStart_1832971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833024 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 1, 3]
def baseStart_1833024 : Nat := 118140960795 + 1833024 * 2 ^ 59
def prefixEnd_1833024 : Nat := 4983230072969 + 3 ^ 40 * 1833024 * 2
def baseEnd_1833024 : Nat := 627481575484761012580055

theorem tailTrace_1833024 : CollatzResearch.WordTrace tailWord_1833024 prefixEnd_1833024 627481575484761012580055 := by
  unfold tailWord_1833024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427938855637289210341063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44570585140849718947121417 33427938855637289210341063)
  ·
    refine ⟨50141908283455933815511595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33427938855637289210341063 50141908283455933815511595)
    ·
      refine ⟨75212862425183900723267393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50141908283455933815511595 75212862425183900723267393)
      ·
        refine ⟨56409646818887925542450545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75212862425183900723267393 56409646818887925542450545)
        ·
          refine ⟨42307235114165944156837909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56409646818887925542450545 42307235114165944156837909)
          ·
            refine ⟨1983151645976528632351777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42307235114165944156837909 1983151645976528632351777)
            ·
              refine ⟨1487363734482396474263833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983151645976528632351777 1487363734482396474263833)
              ·
                refine ⟨1115522800861797355697875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487363734482396474263833 1115522800861797355697875)
                ·
                  refine ⟨1673284201292696033546813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115522800861797355697875 1673284201292696033546813)
                  ·
                    refine ⟨627481575484761012580055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673284201292696033546813 627481575484761012580055)
                    ·
                      rfl

theorem cell22_1833024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_1833024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833024 prefixEnd_1833024 := by exact prefixLift 1833024
  have htrace : WordTrace (prefixWord ++ tailWord_1833024) baseStart_1833024 baseEnd_1833024 := by
    simpa [prefixWord, tailWord_1833024, baseEnd_1833024] using wordTrace_append hprefix tailTrace_1833024
  have hstable : (prefixWord ++ tailWord_1833024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833024).length < 2 ^ (prefixWord ++ tailWord_1833024).sum := by decide
  have hdescent : baseEnd_1833024 < baseStart_1833024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833048 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_1833048 : Nat := 118140960795 + 1833048 * 2 ^ 59
def prefixEnd_1833048 : Nat := 4983230072969 + 3 ^ 40 * 1833048 * 2
def baseEnd_1833048 : Nat := 209163263725077649993327

theorem tailTrace_1833048 : CollatzResearch.WordTrace tailWord_1833048 prefixEnd_1833048 209163263725077649993327 := by
  unfold tailWord_1833048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33428376531593815259777899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44571168708791753679703865 33428376531593815259777899)
  ·
    refine ⟨50142564797390722889666849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33428376531593815259777899 50142564797390722889666849)
    ·
      refine ⟨37606923598043042167250137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50142564797390722889666849 37606923598043042167250137)
      ·
        refine ⟨28205192698532281625437603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37606923598043042167250137 28205192698532281625437603)
        ·
          refine ⟨42307789047798422438156405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28205192698532281625437603 42307789047798422438156405)
          ·
            refine ⟨3966355223231102103577163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42307789047798422438156405 3966355223231102103577163)
            ·
              refine ⟨5949532834846653155365745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966355223231102103577163 5949532834846653155365745)
              ·
                refine ⟨4462149626134989866524309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949532834846653155365745 4462149626134989866524309)
                ·
                  refine ⟨209163263725077649993327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4462149626134989866524309 209163263725077649993327)
                  ·
                    rfl

theorem cell22_1833048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_1833048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833048 prefixEnd_1833048 := by exact prefixLift 1833048
  have htrace : WordTrace (prefixWord ++ tailWord_1833048) baseStart_1833048 baseEnd_1833048 := by
    simpa [prefixWord, tailWord_1833048, baseEnd_1833048] using wordTrace_append hprefix tailTrace_1833048
  have hstable : (prefixWord ++ tailWord_1833048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833048).length < 2 ^ (prefixWord ++ tailWord_1833048).sum := by decide
  have hdescent : baseEnd_1833048 < baseStart_1833048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833063 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1833063 : Nat := 118140960795 + 1833063 * 2 ^ 59
def prefixEnd_1833063 : Nat := 4983230072969 + 3 ^ 40 * 1833063 * 2
def baseEnd_1833063 : Nat := 627494925981777910854935

theorem tailTrace_1833063 : CollatzResearch.WordTrace tailWord_1833063 prefixEnd_1833063 627494925981777910854935 := by
  unfold tailWord_1833063
  simp only [CollatzResearch.WordTrace]
  refine ⟨66857300158133288081351843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44571533438755525387567895 66857300158133288081351843)
  ·
    refine ⟨100285950237199932122027765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66857300158133288081351843 100285950237199932122027765)
    ·
      refine ⟨9401807834737493636440103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100285950237199932122027765 9401807834737493636440103)
      ·
        refine ⟨14102711752106240454660155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9401807834737493636440103 14102711752106240454660155)
        ·
          refine ⟨21154067628159360681990233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14102711752106240454660155 21154067628159360681990233)
          ·
            refine ⟨15865550721119520511492675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21154067628159360681990233 15865550721119520511492675)
            ·
              refine ⟨23798326081679280767239013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865550721119520511492675 23798326081679280767239013)
              ·
                refine ⟨4462186140314865143857315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23798326081679280767239013 4462186140314865143857315)
                ·
                  refine ⟨6693279210472297715785973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462186140314865143857315 6693279210472297715785973)
                  ·
                    refine ⟨627494925981777910854935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6693279210472297715785973 627494925981777910854935)
                    ·
                      rfl

theorem cell22_1833063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1833063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833063 prefixEnd_1833063 := by exact prefixLift 1833063
  have htrace : WordTrace (prefixWord ++ tailWord_1833063) baseStart_1833063 baseEnd_1833063 := by
    simpa [prefixWord, tailWord_1833063, baseEnd_1833063] using wordTrace_append hprefix tailTrace_1833063
  have hstable : (prefixWord ++ tailWord_1833063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833063).length < 2 ^ (prefixWord ++ tailWord_1833063).sum := by decide
  have hdescent : baseEnd_1833063 < baseStart_1833063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833065 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 4]
def baseStart_1833065 : Nat := 118140960795 + 1833065 * 2 ^ 59
def prefixEnd_1833065 : Nat := 4983230072969 + 3 ^ 40 * 1833065 * 2
def baseEnd_1833065 : Nat := 209165203540883524101643

theorem tailTrace_1833065 : CollatzResearch.WordTrace tailWord_1833065 prefixEnd_1833065 209165203540883524101643 := by
  unfold tailWord_1833065
  simp only [CollatzResearch.WordTrace]
  refine ⟨66857373104126042422924649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44571582069417361615283099 66857373104126042422924649)
  ·
    refine ⟨50143029828094531817193487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66857373104126042422924649 50143029828094531817193487)
    ·
      refine ⟨75214544742141797725790231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50143029828094531817193487 75214544742141797725790231)
      ·
        refine ⟨112821817113212696588685347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75214544742141797725790231 112821817113212696588685347)
        ·
          refine ⟨169232725669819044883028021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112821817113212696588685347 169232725669819044883028021)
          ·
            refine ⟨15865568031545535457783877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169232725669819044883028021 15865568031545535457783877)
            ·
              refine ⟨2974794005914787898334477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15865568031545535457783877 2974794005914787898334477)
              ·
                refine ⟨1115547752218045461875429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2974794005914787898334477 1115547752218045461875429)
                ·
                  refine ⟨209165203540883524101643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115547752218045461875429 209165203540883524101643)
                  ·
                    rfl

theorem cell22_1833065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_1833065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833065 prefixEnd_1833065 := by exact prefixLift 1833065
  have htrace : WordTrace (prefixWord ++ tailWord_1833065) baseStart_1833065 baseEnd_1833065 := by
    simpa [prefixWord, tailWord_1833065, baseEnd_1833065] using wordTrace_append hprefix tailTrace_1833065
  have hstable : (prefixWord ++ tailWord_1833065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833065).length < 2 ^ (prefixWord ++ tailWord_1833065).sum := by decide
  have hdescent : baseEnd_1833065 < baseStart_1833065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833097 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_1833097 : Nat := 118140960795 + 1833097 * 2 ^ 59
def prefixEnd_1833097 : Nat := 4983230072969 + 3 ^ 40 * 1833097 * 2
def baseEnd_1833097 : Nat := 627506564876613155504831

theorem tailTrace_1833097 : CollatzResearch.WordTrace tailWord_1833097 prefixEnd_1833097 627506564876613155504831 := by
  unfold tailWord_1833097
  simp only [CollatzResearch.WordTrace]
  refine ⟨66858540240010111888089545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44572360160006741258726363 66858540240010111888089545)
  ·
    refine ⟨50143905180007583916067159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66858540240010111888089545 50143905180007583916067159)
    ·
      refine ⟨75215857770011375874100739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50143905180007583916067159 75215857770011375874100739)
      ·
        refine ⟨112823786655017063811151109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75215857770011375874100739 112823786655017063811151109)
        ·
          refine ⟨21154459997815699464590833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112823786655017063811151109 21154459997815699464590833)
          ·
            refine ⟨15865844998361774598443125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21154459997815699464590833 15865844998361774598443125)
            ·
              refine ⟨1487422968596416368604043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15865844998361774598443125 1487422968596416368604043)
              ·
                refine ⟨2231134452894624552906065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487422968596416368604043 2231134452894624552906065)
                ·
                  refine ⟨1673350839670968414679549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2231134452894624552906065 1673350839670968414679549)
                  ·
                    refine ⟨627506564876613155504831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673350839670968414679549 627506564876613155504831)
                    ·
                      rfl

theorem cell22_1833097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_1833097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833097 prefixEnd_1833097 := by exact prefixLift 1833097
  have htrace : WordTrace (prefixWord ++ tailWord_1833097) baseStart_1833097 baseEnd_1833097 := by
    simpa [prefixWord, tailWord_1833097, baseEnd_1833097] using wordTrace_append hprefix tailTrace_1833097
  have hstable : (prefixWord ++ tailWord_1833097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833097).length < 2 ^ (prefixWord ++ tailWord_1833097).sum := by decide
  have hdescent : baseEnd_1833097 < baseStart_1833097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833127 : List Nat := [1, 1, 6, 2, 3, 1, 8]
def baseStart_1833127 : Nat := 118140960795 + 1833127 * 2 ^ 59
def prefixEnd_1833127 : Nat := 4983230072969 + 3 ^ 40 * 1833127 * 2
def baseEnd_1833127 : Nat := 23241364240359373231657

theorem tailTrace_1833127 : CollatzResearch.WordTrace tailWord_1833127 prefixEnd_1833127 23241364240359373231657 := by
  unfold tailWord_1833127
  simp only [CollatzResearch.WordTrace]
  refine ⟨66859634429901427011681635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44573089619934284674454423 66859634429901427011681635)
  ·
    refine ⟨100289451644852140517522453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66859634429901427011681635 100289451644852140517522453)
    ·
      refine ⟨4701068045852444086758865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100289451644852140517522453 4701068045852444086758865)
      ·
        refine ⟨3525801034389333065069149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4701068045852444086758865 3525801034389333065069149)
        ·
          refine ⟨1322175387895999899400931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3525801034389333065069149 1322175387895999899400931)
          ·
            refine ⟨1983263081843999849101397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322175387895999899400931 1983263081843999849101397)
            ·
              refine ⟨23241364240359373231657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1983263081843999849101397 23241364240359373231657)
              ·
                rfl

theorem cell22_1833127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 8].length) (baseStart_1833127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833127 prefixEnd_1833127 := by exact prefixLift 1833127
  have htrace : WordTrace (prefixWord ++ tailWord_1833127) baseStart_1833127 baseEnd_1833127 := by
    simpa [prefixWord, tailWord_1833127, baseEnd_1833127] using wordTrace_append hprefix tailTrace_1833127
  have hstable : (prefixWord ++ tailWord_1833127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833127).length < 2 ^ (prefixWord ++ tailWord_1833127).sum := by decide
  have hdescent : baseEnd_1833127 < baseStart_1833127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833138 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_1833138 : Nat := 118140960795 + 1833138 * 2 ^ 59
def prefixEnd_1833138 : Nat := 4983230072969 + 3 ^ 40 * 1833138 * 2
def baseEnd_1833138 : Nat := 209173533338167571743235

theorem tailTrace_1833138 : CollatzResearch.WordTrace tailWord_1833138 prefixEnd_1833138 209173533338167571743235 := by
  unfold tailWord_1833138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715008908215393972583017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44573357088574383926888045 16715008908215393972583017)
  ·
    refine ⟨12536256681161545479437263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16715008908215393972583017 12536256681161545479437263)
    ·
      refine ⟨18804385021742318219155895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536256681161545479437263 18804385021742318219155895)
      ·
        refine ⟨28206577532613477328733843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18804385021742318219155895 28206577532613477328733843)
        ·
          refine ⟨42309866298920215993100765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28206577532613477328733843 42309866298920215993100765)
          ·
            refine ⟨15866199862095080997412787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42309866298920215993100765 15866199862095080997412787)
            ·
              refine ⟨23799299793142621496119181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15866199862095080997412787 23799299793142621496119181)
              ·
                refine ⟨8924737422428483061044693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23799299793142621496119181 8924737422428483061044693)
                ·
                  refine ⟨209173533338167571743235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8924737422428483061044693 209173533338167571743235)
                  ·
                    rfl

theorem cell22_1833138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_1833138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833138 prefixEnd_1833138 := by exact prefixLift 1833138
  have htrace : WordTrace (prefixWord ++ tailWord_1833138) baseStart_1833138 baseEnd_1833138 := by
    simpa [prefixWord, tailWord_1833138, baseEnd_1833138] using wordTrace_append hprefix tailTrace_1833138
  have hstable : (prefixWord ++ tailWord_1833138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833138).length < 2 ^ (prefixWord ++ tailWord_1833138).sum := by decide
  have hdescent : baseEnd_1833138 < baseStart_1833138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833215 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1833215 : Nat := 118140960795 + 1833215 * 2 ^ 59
def prefixEnd_1833215 : Nat := 4983230072969 + 3 ^ 40 * 1833215 * 2
def baseEnd_1833215 : Nat := 627546958688100181054469

theorem tailTrace_1833215 : CollatzResearch.WordTrace tailWord_1833215 prefixEnd_1833215 627546958688100181054469 := by
  unfold tailWord_1833215
  simp only [CollatzResearch.WordTrace]
  refine ⟨66862844053582618040885099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44575229369055078693923399 66862844053582618040885099)
  ·
    refine ⟨100294266080373927061327649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66862844053582618040885099 100294266080373927061327649)
    ·
      refine ⟨75220699560280445295995737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100294266080373927061327649 75220699560280445295995737)
      ·
        refine ⟨56415524670210333971996803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75220699560280445295995737 56415524670210333971996803)
        ·
          refine ⟨84623287005315500957995205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56415524670210333971996803 84623287005315500957995205)
          ·
            refine ⟨15866866313496656429624101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84623287005315500957995205 15866866313496656429624101)
            ·
              refine ⟨2975037433780623080554519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15866866313496656429624101 2975037433780623080554519)
              ·
                refine ⟨4462556150670934620831779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975037433780623080554519 4462556150670934620831779)
                ·
                  refine ⟨6693834226006401931247669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462556150670934620831779 6693834226006401931247669)
                  ·
                    refine ⟨627546958688100181054469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6693834226006401931247669 627546958688100181054469)
                    ·
                      rfl

theorem cell22_1833215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1833215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833215 prefixEnd_1833215 := by exact prefixLift 1833215
  have htrace : WordTrace (prefixWord ++ tailWord_1833215) baseStart_1833215 baseEnd_1833215 := by
    simpa [prefixWord, tailWord_1833215, baseEnd_1833215] using wordTrace_append hprefix tailTrace_1833215
  have hstable : (prefixWord ++ tailWord_1833215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833215).length < 2 ^ (prefixWord ++ tailWord_1833215).sum := by decide
  have hdescent : baseEnd_1833215 < baseStart_1833215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833230 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1833230 : Nat := 118140960795 + 1833230 * 2 ^ 59
def prefixEnd_1833230 : Nat := 4983230072969 + 3 ^ 40 * 1833230 * 2
def baseEnd_1833230 : Nat := 627552093494645141929423

theorem tailTrace_1833230 : CollatzResearch.WordTrace tailWord_1833230 prefixEnd_1833230 627552093494645141929423 := by
  unfold tailWord_1833230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357923893566034450335143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44575594099018850401787429 8357923893566034450335143)
  ·
    refine ⟨12536885840349051675502715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357923893566034450335143 12536885840349051675502715)
    ·
      refine ⟨18805328760523577513254073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536885840349051675502715 18805328760523577513254073)
      ·
        refine ⟨14103996570392683134940555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18805328760523577513254073 14103996570392683134940555)
        ·
          refine ⟨21155994855589024702410833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103996570392683134940555 21155994855589024702410833)
          ·
            refine ⟨15866996141691768526808125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21155994855589024702410833 15866996141691768526808125)
            ·
              refine ⟨5950123553134413197553047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15866996141691768526808125 5950123553134413197553047)
              ·
                refine ⟨8925185329701619796329571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950123553134413197553047 8925185329701619796329571)
                ·
                  refine ⟨13387777994552429694494357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8925185329701619796329571 13387777994552429694494357)
                  ·
                    refine ⟨627552093494645141929423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13387777994552429694494357 627552093494645141929423)
                    ·
                      rfl

theorem cell22_1833230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1833230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833230 prefixEnd_1833230 := by exact prefixLift 1833230
  have htrace : WordTrace (prefixWord ++ tailWord_1833230) baseStart_1833230 baseEnd_1833230 := by
    simpa [prefixWord, tailWord_1833230, baseEnd_1833230] using wordTrace_append hprefix tailTrace_1833230
  have hstable : (prefixWord ++ tailWord_1833230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833230).length < 2 ^ (prefixWord ++ tailWord_1833230).sum := by decide
  have hdescent : baseEnd_1833230 < baseStart_1833230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833266 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1833266 : Nat := 118140960795 + 1833266 * 2 ^ 59
def prefixEnd_1833266 : Nat := 4983230072969 + 3 ^ 40 * 1833266 * 2
def baseEnd_1833266 : Nat := 627564417030353048029313

theorem tailTrace_1833266 : CollatzResearch.WordTrace tailWord_1833266 prefixEnd_1833266 627564417030353048029313 := by
  unfold tailWord_1833266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716176044099463437747913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44576469450931902500661101 16716176044099463437747913)
  ·
    refine ⟨12537132033074597578310935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16716176044099463437747913 12537132033074597578310935)
    ·
      refine ⟨18805698049611896367466403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537132033074597578310935 18805698049611896367466403)
      ·
        refine ⟨28208547074417844551199605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18805698049611896367466403 28208547074417844551199605)
        ·
          refine ⟨2644551288226672926674963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28208547074417844551199605 2644551288226672926674963)
          ·
            refine ⟨3966826932340009390012445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644551288226672926674963 3966826932340009390012445)
            ·
              refine ⟨1487560099627503521254667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3966826932340009390012445 1487560099627503521254667)
              ·
                refine ⟨2231340149441255281882001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487560099627503521254667 2231340149441255281882001)
                ·
                  refine ⟨1673505112080941461411501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2231340149441255281882001 1673505112080941461411501)
                  ·
                    refine ⟨627564417030353048029313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673505112080941461411501 627564417030353048029313)
                    ·
                      rfl

theorem cell22_1833266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1833266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833266 prefixEnd_1833266 := by exact prefixLift 1833266
  have htrace : WordTrace (prefixWord ++ tailWord_1833266) baseStart_1833266 baseEnd_1833266 := by
    simpa [prefixWord, tailWord_1833266, baseEnd_1833266] using wordTrace_append hprefix tailTrace_1833266
  have hstable : (prefixWord ++ tailWord_1833266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833266).length < 2 ^ (prefixWord ++ tailWord_1833266).sum := by decide
  have hdescent : baseEnd_1833266 < baseStart_1833266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833294 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_1833294 : Nat := 118140960795 + 1833294 * 2 ^ 59
def prefixEnd_1833294 : Nat := 4983230072969 + 3 ^ 40 * 1833294 * 2
def baseEnd_1833294 : Nat := 627574002002570308329227

theorem tailTrace_1833294 : CollatzResearch.WordTrace tailWord_1833294 prefixEnd_1833294 627574002002570308329227 := by
  unfold tailWord_1833294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358215677537051816626367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44577150280197609688673957 8358215677537051816626367)
  ·
    refine ⟨12537323516305577724939551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8358215677537051816626367 12537323516305577724939551)
    ·
      refine ⟨18805985274458366587409327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537323516305577724939551 18805985274458366587409327)
      ·
        refine ⟨28208977911687549881113991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18805985274458366587409327 28208977911687549881113991)
        ·
          refine ⟨42313466867531324821670987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28208977911687549881113991 42313466867531324821670987)
          ·
            refine ⟨63470200301296987232506481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42313466867531324821670987 63470200301296987232506481)
            ·
              refine ⟨47602650225972740424379861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63470200301296987232506481 47602650225972740424379861)
              ·
                refine ⟨1115687114671236103696403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47602650225972740424379861 1115687114671236103696403)
                ·
                  refine ⟨1673530672006854155544605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115687114671236103696403 1673530672006854155544605)
                  ·
                    refine ⟨627574002002570308329227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673530672006854155544605 627574002002570308329227)
                    ·
                      rfl

theorem cell22_1833294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_1833294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833294 prefixEnd_1833294 := by exact prefixLift 1833294
  have htrace : WordTrace (prefixWord ++ tailWord_1833294) baseStart_1833294 baseEnd_1833294 := by
    simpa [prefixWord, tailWord_1833294, baseEnd_1833294] using wordTrace_append hprefix tailTrace_1833294
  have hstable : (prefixWord ++ tailWord_1833294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833294).length < 2 ^ (prefixWord ++ tailWord_1833294).sum := by decide
  have hdescent : baseEnd_1833294 < baseStart_1833294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833365 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1833365 : Nat := 118140960795 + 1833365 * 2 ^ 59
def prefixEnd_1833365 : Nat := 4983230072969 + 3 ^ 40 * 1833365 * 2
def baseEnd_1833365 : Nat := 627598306753549789804009

theorem tailTrace_1833365 : CollatzResearch.WordTrace tailWord_1833365 prefixEnd_1833365 627598306753549789804009 := by
  unfold tailWord_1833365
  simp only [CollatzResearch.WordTrace]
  refine ⟨66868315003039193658845549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44578876668692795772563699 66868315003039193658845549)
  ·
    refine ⟨25075618126139697622067081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66868315003039193658845549 25075618126139697622067081)
    ·
      refine ⟨18806713594604773216550311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25075618126139697622067081 18806713594604773216550311)
      ·
        refine ⟨28210070391907159824825467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18806713594604773216550311 28210070391907159824825467)
        ·
          refine ⟨42315105587860739737238201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28210070391907159824825467 42315105587860739737238201)
          ·
            refine ⟨31736329190895554802928651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42315105587860739737238201 31736329190895554802928651)
            ·
              refine ⟨47604493786343332204392977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31736329190895554802928651 47604493786343332204392977)
              ·
                refine ⟨35703370339757499153294733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47604493786343332204392977 35703370339757499153294733)
                ·
                  refine ⟨13388763877409062182485525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35703370339757499153294733 13388763877409062182485525)
                  ·
                    refine ⟨627598306753549789804009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13388763877409062182485525 627598306753549789804009)
                    ·
                      rfl

theorem cell22_1833365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1833365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833365 prefixEnd_1833365 := by exact prefixLift 1833365
  have htrace : WordTrace (prefixWord ++ tailWord_1833365) baseStart_1833365 baseEnd_1833365 := by
    simpa [prefixWord, tailWord_1833365, baseEnd_1833365] using wordTrace_append hprefix tailTrace_1833365
  have hstable : (prefixWord ++ tailWord_1833365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833365).length < 2 ^ (prefixWord ++ tailWord_1833365).sum := by decide
  have hdescent : baseEnd_1833365 < baseStart_1833365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833367 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 4, 3]
def baseStart_1833367 : Nat := 118140960795 + 1833367 * 2 ^ 59
def prefixEnd_1833367 : Nat := 4983230072969 + 3 ^ 40 * 1833367 * 2
def baseEnd_1833367 : Nat := 627598991394422451254003

theorem tailTrace_1833367 : CollatzResearch.WordTrace tailWord_1833367 prefixEnd_1833367 627598991394422451254003 := by
  unfold tailWord_1833367
  simp only [CollatzResearch.WordTrace]
  refine ⟨66868387949031948000418355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44578925299354632000278903 66868387949031948000418355)
  ·
    refine ⟨100302581923547922000627533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66868387949031948000418355 100302581923547922000627533)
    ·
      refine ⟨37613468221330470750235325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100302581923547922000627533 37613468221330470750235325)
      ·
        refine ⟨14105050582998926531338247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37613468221330470750235325 14105050582998926531338247)
        ·
          refine ⟨21157575874498389797007371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14105050582998926531338247 21157575874498389797007371)
          ·
            refine ⟨31736363811747584695511057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21157575874498389797007371 31736363811747584695511057)
            ·
              refine ⟨23802272858810688521633293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31736363811747584695511057 23802272858810688521633293)
              ·
                refine ⟨8925852322054008195612485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23802272858810688521633293 8925852322054008195612485)
                ·
                  refine ⟨1673597310385126536677341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8925852322054008195612485 1673597310385126536677341)
                  ·
                    refine ⟨627598991394422451254003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673597310385126536677341 627598991394422451254003)
                    ·
                      rfl

theorem cell22_1833367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_1833367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833367 prefixEnd_1833367 := by exact prefixLift 1833367
  have htrace : WordTrace (prefixWord ++ tailWord_1833367) baseStart_1833367 baseEnd_1833367 := by
    simpa [prefixWord, tailWord_1833367, baseEnd_1833367] using wordTrace_append hprefix tailTrace_1833367
  have hstable : (prefixWord ++ tailWord_1833367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833367).length < 2 ^ (prefixWord ++ tailWord_1833367).sum := by decide
  have hdescent : baseEnd_1833367 < baseStart_1833367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833384 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1833384 : Nat := 118140960795 + 1833384 * 2 ^ 59
def prefixEnd_1833384 : Nat := 4983230072969 + 3 ^ 40 * 1833384 * 2
def baseEnd_1833384 : Nat := 627604810841840073578951

theorem tailTrace_1833384 : CollatzResearch.WordTrace tailWord_1833384 prefixEnd_1833384 627604810841840073578951 := by
  unfold tailWord_1833384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33434503994985179951893603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44579338659980239935858137 33434503994985179951893603)
  ·
    refine ⟨50151755992477769927840405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33434503994985179951893603 50151755992477769927840405)
    ·
      refine ⟨2350863562147395465367519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50151755992477769927840405 2350863562147395465367519)
      ·
        refine ⟨3526295343221093198051279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2350863562147395465367519 3526295343221093198051279)
        ·
          refine ⟨5289443014831639797076919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526295343221093198051279 5289443014831639797076919)
          ·
            refine ⟨7934164522247459695615379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289443014831639797076919 7934164522247459695615379)
            ·
              refine ⟨11901246783371189543423069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934164522247459695615379 11901246783371189543423069)
              ·
                refine ⟨4462967543764196078783651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11901246783371189543423069 4462967543764196078783651)
                ·
                  refine ⟨6694451315646294118175477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462967543764196078783651 6694451315646294118175477)
                  ·
                    refine ⟨627604810841840073578951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6694451315646294118175477 627604810841840073578951)
                    ·
                      rfl

theorem cell22_1833384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1833384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833384 prefixEnd_1833384 := by exact prefixLift 1833384
  have htrace : WordTrace (prefixWord ++ tailWord_1833384) baseStart_1833384 baseEnd_1833384 := by
    simpa [prefixWord, tailWord_1833384, baseEnd_1833384] using wordTrace_append hprefix tailTrace_1833384
  have hstable : (prefixWord ++ tailWord_1833384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833384).length < 2 ^ (prefixWord ++ tailWord_1833384).sum := by decide
  have hdescent : baseEnd_1833384 < baseStart_1833384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833399 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 2, 4]
def baseStart_1833399 : Nat := 118140960795 + 1833399 * 2 ^ 59
def prefixEnd_1833399 : Nat := 4983230072969 + 3 ^ 40 * 1833399 * 2
def baseEnd_1833399 : Nat := 627609945648385034453905

theorem tailTrace_1833399 : CollatzResearch.WordTrace tailWord_1833399 prefixEnd_1833399 627609945648385034453905 := by
  unfold tailWord_1833399
  simp only [CollatzResearch.WordTrace]
  refine ⟨66869555084916017465583251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44579703389944011643722167 66869555084916017465583251)
  ·
    refine ⟨100304332627374026198374877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66869555084916017465583251 100304332627374026198374877)
    ·
      refine ⟨37614124735265259824390579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100304332627374026198374877 37614124735265259824390579)
      ·
        refine ⟨56421187102897889736585869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37614124735265259824390579 56421187102897889736585869)
        ·
          refine ⟨21157945163586708651219701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56421187102897889736585869 21157945163586708651219701)
          ·
            refine ⟨1983557359086253936051847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21157945163586708651219701 1983557359086253936051847)
            ·
              refine ⟨2975336038629380904077771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983557359086253936051847 2975336038629380904077771)
              ·
                refine ⟨4463004057944071356116657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975336038629380904077771 4463004057944071356116657)
                ·
                  refine ⟨3347253043458053517087493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463004057944071356116657 3347253043458053517087493)
                  ·
                    refine ⟨627609945648385034453905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3347253043458053517087493 627609945648385034453905)
                    ·
                      rfl

theorem cell22_1833399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_1833399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833399 prefixEnd_1833399 := by exact prefixLift 1833399
  have htrace : WordTrace (prefixWord ++ tailWord_1833399) baseStart_1833399 baseEnd_1833399 := by
    simpa [prefixWord, tailWord_1833399, baseEnd_1833399] using wordTrace_append hprefix tailTrace_1833399
  have hstable : (prefixWord ++ tailWord_1833399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833399).length < 2 ^ (prefixWord ++ tailWord_1833399).sum := by decide
  have hdescent : baseEnd_1833399 < baseStart_1833399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833429 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1833429 : Nat := 118140960795 + 1833429 * 2 ^ 59
def prefixEnd_1833429 : Nat := 4983230072969 + 3 ^ 40 * 1833429 * 2
def baseEnd_1833429 : Nat := 627620215261474956203813

theorem tailTrace_1833429 : CollatzResearch.WordTrace tailWord_1833429 prefixEnd_1833429 627620215261474956203813 := by
  unfold tailWord_1833429
  simp only [CollatzResearch.WordTrace]
  refine ⟨66870649274807332589175341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44580432849871555059450227 66870649274807332589175341)
  ·
    refine ⟨25076493478052749720940753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66870649274807332589175341 25076493478052749720940753)
    ·
      refine ⟨18807370108539562290705565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25076493478052749720940753 18807370108539562290705565)
      ·
        refine ⟨7052763790702335859014587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18807370108539562290705565 7052763790702335859014587)
        ·
          refine ⟨10579145686053503788521881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7052763790702335859014587 10579145686053503788521881)
          ·
            refine ⟨7934359264540127841391411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10579145686053503788521881 7934359264540127841391411)
            ·
              refine ⟨11901538896810191762087117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934359264540127841391411 11901538896810191762087117)
              ·
                refine ⟨4463077086303821910782669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11901538896810191762087117 4463077086303821910782669)
                ·
                  refine ⟨1673653907363933216543501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4463077086303821910782669 1673653907363933216543501)
                  ·
                    refine ⟨627620215261474956203813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673653907363933216543501 627620215261474956203813)
                    ·
                      rfl

theorem cell22_1833429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1833429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833429 prefixEnd_1833429 := by exact prefixLift 1833429
  have htrace : WordTrace (prefixWord ++ tailWord_1833429) baseStart_1833429 baseEnd_1833429 := by
    simpa [prefixWord, tailWord_1833429, baseEnd_1833429] using wordTrace_append hprefix tailTrace_1833429
  have hstable : (prefixWord ++ tailWord_1833429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833429).length < 2 ^ (prefixWord ++ tailWord_1833429).sum := by decide
  have hdescent : baseEnd_1833429 < baseStart_1833429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833532 : List Nat := [2, 2, 2, 2, 3, 11]
def baseStart_1833532 : Nat := 118140960795 + 1833532 * 2 ^ 59
def prefixEnd_1833532 : Nat := 4983230072969 + 3 ^ 40 * 1833532 * 2
def baseEnd_1833532 : Nat := 7748833015634778035537

theorem tailTrace_1833532 : CollatzResearch.WordTrace tailWord_1833532 prefixEnd_1833532 7748833015634778035537 := by
  unfold tailWord_1833532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33437202996717090590087425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44582937328956120786783233 33437202996717090590087425)
  ·
    refine ⟨25077902247537817942565569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33437202996717090590087425 25077902247537817942565569)
    ·
      refine ⟨18808426685653363456924177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25077902247537817942565569 18808426685653363456924177)
      ·
        refine ⟨14106320014240022592693133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18808426685653363456924177 14106320014240022592693133)
        ·
          refine ⟨5289870005340008472259925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14106320014240022592693133 5289870005340008472259925)
          ·
            refine ⟨7748833015634778035537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5289870005340008472259925 7748833015634778035537)
            ·
              rfl

theorem cell22_1833532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 11].length) (baseStart_1833532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833532 prefixEnd_1833532 := by exact prefixLift 1833532
  have htrace : WordTrace (prefixWord ++ tailWord_1833532) baseStart_1833532 baseEnd_1833532 := by
    simpa [prefixWord, tailWord_1833532, baseEnd_1833532] using wordTrace_append hprefix tailTrace_1833532
  have hstable : (prefixWord ++ tailWord_1833532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833532).length < 2 ^ (prefixWord ++ tailWord_1833532).sum := by decide
  have hdescent : baseEnd_1833532 < baseStart_1833532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833577 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 7]
def baseStart_1833577 : Nat := 118140960795 + 1833577 * 2 ^ 59
def prefixEnd_1833577 : Nat := 4983230072969 + 3 ^ 40 * 1833577 * 2
def baseEnd_1833577 : Nat := 209223626228683967834453

theorem tailTrace_1833577 : CollatzResearch.WordTrace tailWord_1833577 prefixEnd_1833577 209223626228683967834453 := by
  unfold tailWord_1833577
  simp only [CollatzResearch.WordTrace]
  refine ⟨66876047278271153865562985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44584031518847435910375323 66876047278271153865562985)
  ·
    refine ⟨50157035458703365399172239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66876047278271153865562985 50157035458703365399172239)
    ·
      refine ⟨75235553188055048098758359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50157035458703365399172239 75235553188055048098758359)
      ·
        refine ⟨112853329782082572148137539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75235553188055048098758359 112853329782082572148137539)
        ·
          refine ⟨169279994673123858222206309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112853329782082572148137539 169279994673123858222206309)
          ·
            refine ⟨31739999001210723416663683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169279994673123858222206309 31739999001210723416663683)
            ·
              refine ⟨47609998501816085124995525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31739999001210723416663683 47609998501816085124995525)
              ·
                refine ⟨8926874719090515960936661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47609998501816085124995525 8926874719090515960936661)
                ·
                  refine ⟨209223626228683967834453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8926874719090515960936661 209223626228683967834453)
                  ·
                    rfl

theorem cell22_1833577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_1833577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833577 prefixEnd_1833577 := by exact prefixLift 1833577
  have htrace : WordTrace (prefixWord ++ tailWord_1833577) baseStart_1833577 baseEnd_1833577 := by
    simpa [prefixWord, tailWord_1833577, baseEnd_1833577] using wordTrace_append hprefix tailTrace_1833577
  have hstable : (prefixWord ++ tailWord_1833577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833577).length < 2 ^ (prefixWord ++ tailWord_1833577).sum := by decide
  have hdescent : baseEnd_1833577 < baseStart_1833577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833592 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_1833592 : Nat := 118140960795 + 1833592 * 2 ^ 59
def prefixEnd_1833592 : Nat := 4983230072969 + 3 ^ 40 * 1833592 * 2
def baseEnd_1833592 : Nat := 627676013492596864378313

theorem tailTrace_1833592 : CollatzResearch.WordTrace tailWord_1833592 prefixEnd_1833592 627676013492596864378313 := by
  unfold tailWord_1833592
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438297186608405713679515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44584396248811207618239353 33438297186608405713679515)
  ·
    refine ⟨50157445779912608570519273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33438297186608405713679515 50157445779912608570519273)
    ·
      refine ⟨37618084334934456427889455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50157445779912608570519273 37618084334934456427889455)
      ·
        refine ⟨56427126502401684641834183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37618084334934456427889455 56427126502401684641834183)
        ·
          refine ⟨84640689753602526962751275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56427126502401684641834183 84640689753602526962751275)
          ·
            refine ⟨126961034630403790444126913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84640689753602526962751275 126961034630403790444126913)
            ·
              refine ⟨95220775972802842833095185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126961034630403790444126913 95220775972802842833095185)
              ·
                refine ⟨71415581979602132124821389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95220775972802842833095185 71415581979602132124821389)
                ·
                  refine ⟨26780843242350799546808021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71415581979602132124821389 26780843242350799546808021)
                  ·
                    refine ⟨627676013492596864378313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26780843242350799546808021 627676013492596864378313)
                    ·
                      rfl

theorem cell22_1833592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_1833592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833592 prefixEnd_1833592 := by exact prefixLift 1833592
  have htrace : WordTrace (prefixWord ++ tailWord_1833592) baseStart_1833592 baseEnd_1833592 := by
    simpa [prefixWord, tailWord_1833592, baseEnd_1833592] using wordTrace_append hprefix tailTrace_1833592
  have hstable : (prefixWord ++ tailWord_1833592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833592).length < 2 ^ (prefixWord ++ tailWord_1833592).sum := by decide
  have hdescent : baseEnd_1833592 < baseStart_1833592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833632 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 1, 3]
def baseStart_1833632 : Nat := 118140960795 + 1833632 * 2 ^ 59
def prefixEnd_1833632 : Nat := 4983230072969 + 3 ^ 40 * 1833632 * 2
def baseEnd_1833632 : Nat := 627689706310050093378191

theorem tailTrace_1833632 : CollatzResearch.WordTrace tailWord_1833632 prefixEnd_1833632 627689706310050093378191 := by
  unfold tailWord_1833632
  simp only [CollatzResearch.WordTrace]
  refine ⟨33439026646535949129407575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44585368862047932172543433 33439026646535949129407575)
  ·
    refine ⟨50158539969803923694111363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33439026646535949129407575 50158539969803923694111363)
    ·
      refine ⟨75237809954705885541167045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50158539969803923694111363 75237809954705885541167045)
      ·
        refine ⟨14107089366507353538968821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75237809954705885541167045 14107089366507353538968821)
        ·
          refine ⟨1322539628110064394278327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14107089366507353538968821 1322539628110064394278327)
          ·
            refine ⟨1983809442165096591417491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322539628110064394278327 1983809442165096591417491)
            ·
              refine ⟨2975714163247644887126237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983809442165096591417491 2975714163247644887126237)
              ·
                refine ⟨1115892811217866832672339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2975714163247644887126237 1115892811217866832672339)
                ·
                  refine ⟨1673839216826800249008509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115892811217866832672339 1673839216826800249008509)
                  ·
                    refine ⟨627689706310050093378191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673839216826800249008509 627689706310050093378191)
                    ·
                      rfl

theorem cell22_1833632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_1833632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833632 prefixEnd_1833632 := by exact prefixLift 1833632
  have htrace : WordTrace (prefixWord ++ tailWord_1833632) baseStart_1833632 baseEnd_1833632 := by
    simpa [prefixWord, tailWord_1833632, baseEnd_1833632] using wordTrace_append hprefix tailTrace_1833632
  have hstable : (prefixWord ++ tailWord_1833632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833632).length < 2 ^ (prefixWord ++ tailWord_1833632).sum := by decide
  have hdescent : baseEnd_1833632 < baseStart_1833632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833729 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 9]
def baseStart_1833729 : Nat := 118140960795 + 1833729 * 2 ^ 59
def prefixEnd_1833729 : Nat := 4983230072969 + 3 ^ 40 * 1833729 * 2
def baseEnd_1833729 : Nat := 209240970464124724567631

theorem tailTrace_1833729 : CollatzResearch.WordTrace tailWord_1833729 prefixEnd_1833729 209240970464124724567631 := by
  unfold tailWord_1833729
  simp only [CollatzResearch.WordTrace]
  refine ⟨66881591173720483825096241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44587727449146989216730827 66881591173720483825096241)
  ·
    refine ⟨50161193380290362868822181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66881591173720483825096241 50161193380290362868822181)
    ·
      refine ⟨9405223758804443037904159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50161193380290362868822181 9405223758804443037904159)
      ·
        refine ⟨14107835638206664556856239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405223758804443037904159 14107835638206664556856239)
        ·
          refine ⟨21161753457309996835284359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14107835638206664556856239 21161753457309996835284359)
          ·
            refine ⟨31742630185964995252926539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21161753457309996835284359 31742630185964995252926539)
            ·
              refine ⟨47613945278947492879389809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31742630185964995252926539 47613945278947492879389809)
              ·
                refine ⟨35710458959210619659542357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47613945278947492879389809 35710458959210619659542357)
                ·
                  refine ⟨209240970464124724567631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35710458959210619659542357 209240970464124724567631)
                  ·
                    rfl

theorem cell22_1833729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_1833729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833729 prefixEnd_1833729 := by exact prefixLift 1833729
  have htrace : WordTrace (prefixWord ++ tailWord_1833729) baseStart_1833729 baseEnd_1833729 := by
    simpa [prefixWord, tailWord_1833729, baseEnd_1833729] using wordTrace_append hprefix tailTrace_1833729
  have hstable : (prefixWord ++ tailWord_1833729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833729).length < 2 ^ (prefixWord ++ tailWord_1833729).sum := by decide
  have hdescent : baseEnd_1833729 < baseStart_1833729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833791 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 6]
def baseStart_1833791 : Nat := 118140960795 + 1833791 * 2 ^ 59
def prefixEnd_1833791 : Nat := 4983230072969 + 3 ^ 40 * 1833791 * 2
def baseEnd_1833791 : Nat := 209248045086475559550901

theorem tailTrace_1833791 : CollatzResearch.WordTrace tailWord_1833791 prefixEnd_1833791 209248045086475559550901 := by
  unfold tailWord_1833791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66883852499495868413853227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44589234999663912275902151 66883852499495868413853227)
  ·
    refine ⟨100325778749243802620779841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66883852499495868413853227 100325778749243802620779841)
    ·
      refine ⟨75244334061932851965584881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100325778749243802620779841 75244334061932851965584881)
      ·
        refine ⟨56433250546449638974188661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75244334061932851965584881 56433250546449638974188661)
        ·
          refine ⟨5290617238729653653830187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56433250546449638974188661 5290617238729653653830187)
          ·
            refine ⟨7935925858094480480745281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290617238729653653830187 7935925858094480480745281)
            ·
              refine ⟨5951944393570860360558961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7935925858094480480745281 5951944393570860360558961)
              ·
                refine ⟨4463958295178145270419221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5951944393570860360558961 4463958295178145270419221)
                ·
                  refine ⟨209248045086475559550901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4463958295178145270419221 209248045086475559550901)
                  ·
                    rfl

theorem cell22_1833791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_1833791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833791 prefixEnd_1833791 := by exact prefixLift 1833791
  have htrace : WordTrace (prefixWord ++ tailWord_1833791) baseStart_1833791 baseEnd_1833791 := by
    simpa [prefixWord, tailWord_1833791, baseEnd_1833791] using wordTrace_append hprefix tailTrace_1833791
  have hstable : (prefixWord ++ tailWord_1833791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833791).length < 2 ^ (prefixWord ++ tailWord_1833791).sum := by decide
  have hdescent : baseEnd_1833791 < baseStart_1833791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833806 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1833806 : Nat := 118140960795 + 1833806 * 2 ^ 59
def prefixEnd_1833806 : Nat := 4983230072969 + 3 ^ 40 * 1833806 * 2
def baseEnd_1833806 : Nat := 627749270065971639527657

theorem tailTrace_1833806 : CollatzResearch.WordTrace tailWord_1833806 prefixEnd_1833806 627749270065971639527657 := by
  unfold tailWord_1833806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360549949305190746956159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44589599729627683983766181 8360549949305190746956159)
  ·
    refine ⟨12540824923957786120434239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8360549949305190746956159 12540824923957786120434239)
    ·
      refine ⟨18811237385936679180651359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12540824923957786120434239 18811237385936679180651359)
      ·
        refine ⟨28216856078905018770977039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18811237385936679180651359 28216856078905018770977039)
        ·
          refine ⟨42325284118357528156465559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28216856078905018770977039 42325284118357528156465559)
          ·
            refine ⟨63487926177536292234698339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42325284118357528156465559 63487926177536292234698339)
            ·
              refine ⟨95231889266304438352047509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63487926177536292234698339 95231889266304438352047509)
              ·
                refine ⟨4463994809358020547752227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95231889266304438352047509 4463994809358020547752227)
                ·
                  refine ⟨6695992214037030821628341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463994809358020547752227 6695992214037030821628341)
                  ·
                    refine ⟨627749270065971639527657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6695992214037030821628341 627749270065971639527657)
                    ·
                      rfl

theorem cell22_1833806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1833806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833806 prefixEnd_1833806 := by exact prefixLift 1833806
  have htrace : WordTrace (prefixWord ++ tailWord_1833806) baseStart_1833806 baseEnd_1833806 := by
    simpa [prefixWord, tailWord_1833806, baseEnd_1833806] using wordTrace_append hprefix tailTrace_1833806
  have hstable : (prefixWord ++ tailWord_1833806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833806).length < 2 ^ (prefixWord ++ tailWord_1833806).sum := by decide
  have hdescent : baseEnd_1833806 < baseStart_1833806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833808 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_1833808 : Nat := 118140960795 + 1833808 * 2 ^ 59
def prefixEnd_1833808 : Nat := 4983230072969 + 3 ^ 40 * 1833808 * 2
def baseEnd_1833808 : Nat := 209249984902281433659217

theorem tailTrace_1833808 : CollatzResearch.WordTrace tailWord_1833808 prefixEnd_1833808 209249984902281433659217 := by
  unfold tailWord_1833808
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442236270217140158611039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44589648360289520211481385 33442236270217140158611039)
  ·
    refine ⟨50163354405325710237916559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33442236270217140158611039 50163354405325710237916559)
    ·
      refine ⟨75245031607988565356874839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50163354405325710237916559 75245031607988565356874839)
      ·
        refine ⟨112867547411982848035312259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75245031607988565356874839 112867547411982848035312259)
        ·
          refine ⟨169301321117974272052968389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112867547411982848035312259 169301321117974272052968389)
          ·
            refine ⟨31743997709620176009931573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169301321117974272052968389 31743997709620176009931573)
            ·
              refine ⟨2975999785276891500931085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31743997709620176009931573 2975999785276891500931085)
              ·
                refine ⟨1115999919478834312849157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2975999785276891500931085 1115999919478834312849157)
                ·
                  refine ⟨209249984902281433659217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115999919478834312849157 209249984902281433659217)
                  ·
                    rfl

theorem cell22_1833808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_1833808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833808 prefixEnd_1833808 := by exact prefixLift 1833808
  have htrace : WordTrace (prefixWord ++ tailWord_1833808) baseStart_1833808 baseEnd_1833808 := by
    simpa [prefixWord, tailWord_1833808, baseEnd_1833808] using wordTrace_append hprefix tailTrace_1833808
  have hstable : (prefixWord ++ tailWord_1833808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833808).length < 2 ^ (prefixWord ++ tailWord_1833808).sum := by decide
  have hdescent : baseEnd_1833808 < baseStart_1833808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833823 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 2, 3]
def baseStart_1833823 : Nat := 118140960795 + 1833823 * 2 ^ 59
def prefixEnd_1833823 : Nat := 4983230072969 + 3 ^ 40 * 1833823 * 2
def baseEnd_1833823 : Nat := 627755089513389261852605

theorem tailTrace_1833823 : CollatzResearch.WordTrace tailWord_1833823 prefixEnd_1833823 627755089513389261852605 := by
  unfold tailWord_1833823
  simp only [CollatzResearch.WordTrace]
  refine ⟨66885019635379937879018123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44590013090253291919345415 66885019635379937879018123)
  ·
    refine ⟨100327529453069906818527185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66885019635379937879018123 100327529453069906818527185)
    ·
      refine ⟨75245647089802430113895389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100327529453069906818527185 75245647089802430113895389)
      ·
        refine ⟨28217117658675911292710771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75245647089802430113895389 28217117658675911292710771)
        ·
          refine ⟨42325676488013866939066157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28217117658675911292710771 42325676488013866939066157)
          ·
            refine ⟨15872128683005200102149809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42325676488013866939066157 15872128683005200102149809)
            ·
              refine ⟨11904096512253900076612357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15872128683005200102149809 11904096512253900076612357)
              ·
                refine ⟨2232018096047606264364817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11904096512253900076612357 2232018096047606264364817)
                ·
                  refine ⟨1674013572035704698273613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232018096047606264364817 1674013572035704698273613)
                  ·
                    refine ⟨627755089513389261852605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674013572035704698273613 627755089513389261852605)
                    ·
                      rfl

theorem cell22_1833823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_1833823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833823 prefixEnd_1833823 := by exact prefixLift 1833823
  have htrace : WordTrace (prefixWord ++ tailWord_1833823) baseStart_1833823 baseEnd_1833823 := by
    simpa [prefixWord, tailWord_1833823, baseEnd_1833823] using wordTrace_append hprefix tailTrace_1833823
  have hstable : (prefixWord ++ tailWord_1833823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833823).length < 2 ^ (prefixWord ++ tailWord_1833823).sum := by decide
  have hdescent : baseEnd_1833823 < baseStart_1833823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833836 : List Nat := [2, 2, 1, 1, 4, 1, 4, 7]
def baseStart_1833836 : Nat := 118140960795 + 1833836 * 2 ^ 59
def prefixEnd_1833836 : Nat := 4983230072969 + 3 ^ 40 * 1833836 * 2
def baseEnd_1833836 : Nat := 69751059964340173475285

theorem tailTrace_1833836 : CollatzResearch.WordTrace tailWord_1833836 prefixEnd_1833836 69751059964340173475285 := by
  unfold tailWord_1833836
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442746892166420549620681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44590329189555227399494241 33442746892166420549620681)
  ·
    refine ⟨25082060169124815412215511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33442746892166420549620681 25082060169124815412215511)
    ·
      refine ⟨37623090253687223118323267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082060169124815412215511 37623090253687223118323267)
      ·
        refine ⟨56434635380530834677484901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37623090253687223118323267 56434635380530834677484901)
        ·
          refine ⟨10581494133849531502028419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56434635380530834677484901 10581494133849531502028419)
          ·
            refine ⟨15872241200774297253042629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10581494133849531502028419 15872241200774297253042629)
            ·
              refine ⟨2976045225145180734945493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15872241200774297253042629 2976045225145180734945493)
              ·
                refine ⟨69751059964340173475285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2976045225145180734945493 69751059964340173475285)
                ·
                  rfl

theorem cell22_1833836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_1833836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833836 prefixEnd_1833836 := by exact prefixLift 1833836
  have htrace : WordTrace (prefixWord ++ tailWord_1833836) baseStart_1833836 baseEnd_1833836 := by
    simpa [prefixWord, tailWord_1833836, baseEnd_1833836] using wordTrace_append hprefix tailTrace_1833836
  have hstable : (prefixWord ++ tailWord_1833836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833836).length < 2 ^ (prefixWord ++ tailWord_1833836).sum := by decide
  have hdescent : baseEnd_1833836 < baseStart_1833836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833840 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_1833840 : Nat := 118140960795 + 1833840 * 2 ^ 59
def prefixEnd_1833840 : Nat := 4983230072969 + 3 ^ 40 * 1833840 * 2
def baseEnd_1833840 : Nat := 627760908960806884177553

theorem tailTrace_1833840 : CollatzResearch.WordTrace tailWord_1833840 prefixEnd_1833840 627760908960806884177553 := by
  unfold tailWord_1833840
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442819838159174891193487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44590426450878899854924649 33442819838159174891193487)
  ·
    refine ⟨50164229757238762336790231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33442819838159174891193487 50164229757238762336790231)
    ·
      refine ⟨75246344635858143505185347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50164229757238762336790231 75246344635858143505185347)
      ·
        refine ⟨112869516953787215257778021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75246344635858143505185347 112869516953787215257778021)
        ·
          refine ⟨21163034428835102860833379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112869516953787215257778021 21163034428835102860833379)
          ·
            refine ⟨31744551643252654291250069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21163034428835102860833379 31744551643252654291250069)
            ·
              refine ⟨1488025858277468169902347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31744551643252654291250069 1488025858277468169902347)
              ·
                refine ⟨2232038787416202254853521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488025858277468169902347 2232038787416202254853521)
                ·
                  refine ⟨1674029090562151691140141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232038787416202254853521 1674029090562151691140141)
                  ·
                    refine ⟨627760908960806884177553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674029090562151691140141 627760908960806884177553)
                    ·
                      rfl

theorem cell22_1833840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_1833840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1833840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1833840 prefixEnd_1833840 := by exact prefixLift 1833840
  have htrace : WordTrace (prefixWord ++ tailWord_1833840) baseStart_1833840 baseEnd_1833840 := by
    simpa [prefixWord, tailWord_1833840, baseEnd_1833840] using wordTrace_append hprefix tailTrace_1833840
  have hstable : (prefixWord ++ tailWord_1833840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833840).length < 2 ^ (prefixWord ++ tailWord_1833840).sum := by decide
  have hdescent : baseEnd_1833840 < baseStart_1833840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834037 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1834037 : Nat := 118140960795 + 1834037 * 2 ^ 59
def prefixEnd_1834037 : Nat := 4983230072969 + 3 ^ 40 * 1834037 * 2
def baseEnd_1834037 : Nat := 627828346086764037001949

theorem tailTrace_1834037 : CollatzResearch.WordTrace tailWord_1834037 prefixEnd_1834037 627828346086764037001949 := by
  unfold tailWord_1834037
  simp only [CollatzResearch.WordTrace]
  refine ⟨66892824856604652427308365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44595216571069768284872243 66892824856604652427308365)
  ·
    refine ⟨25084809321226744660240637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66892824856604652427308365 25084809321226744660240637)
    ·
      refine ⟨9406803495460029247590239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25084809321226744660240637 9406803495460029247590239)
      ·
        refine ⟨14110205243190043871385359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406803495460029247590239 14110205243190043871385359)
        ·
          refine ⟨21165307864785065807078039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14110205243190043871385359 21165307864785065807078039)
          ·
            refine ⟨31747961797177598710617059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165307864785065807078039 31747961797177598710617059)
            ·
              refine ⟨47621942695766398065925589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31747961797177598710617059 47621942695766398065925589)
              ·
                refine ⟨1116139281932024954670131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47621942695766398065925589 1116139281932024954670131)
                ·
                  refine ⟨1674208922898037432005197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116139281932024954670131 1674208922898037432005197)
                  ·
                    refine ⟨627828346086764037001949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674208922898037432005197 627828346086764037001949)
                    ·
                      rfl

theorem cell22_1834037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1834037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834037 prefixEnd_1834037 := by exact prefixLift 1834037
  have htrace : WordTrace (prefixWord ++ tailWord_1834037) baseStart_1834037 baseEnd_1834037 := by
    simpa [prefixWord, tailWord_1834037, baseEnd_1834037] using wordTrace_append hprefix tailTrace_1834037
  have hstable : (prefixWord ++ tailWord_1834037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834037).length < 2 ^ (prefixWord ++ tailWord_1834037).sum := by decide
  have hdescent : baseEnd_1834037 < baseStart_1834037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834048 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_1834048 : Nat := 118140960795 + 1834048 * 2 ^ 59
def prefixEnd_1834048 : Nat := 4983230072969 + 3 ^ 40 * 1834048 * 2
def baseEnd_1834048 : Nat := 627832111611563674976915

theorem tailTrace_1834048 : CollatzResearch.WordTrace tailWord_1834048 prefixEnd_1834048 627832111611563674976915 := by
  unfold tailWord_1834048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33446613029782400652979399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44595484039709867537305865 33446613029782400652979399)
  ·
    refine ⟨50169919544673600979469099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33446613029782400652979399 50169919544673600979469099)
    ·
      refine ⟨75254879317010401469203649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50169919544673600979469099 75254879317010401469203649)
      ·
        refine ⟨56441159487757801101902737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75254879317010401469203649 56441159487757801101902737)
        ·
          refine ⟨42330869615818350826427053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56441159487757801101902737 42330869615818350826427053)
          ·
            refine ⟨15874076105931881559910145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42330869615818350826427053 15874076105931881559910145)
            ·
              refine ⟨11905557079448911169932609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15874076105931881559910145 11905557079448911169932609)
              ·
                refine ⟨8929167809586683377449457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11905557079448911169932609 8929167809586683377449457)
                ·
                  refine ⟨6696875857190012533087093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929167809586683377449457 6696875857190012533087093)
                  ·
                    refine ⟨627832111611563674976915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6696875857190012533087093 627832111611563674976915)
                    ·
                      rfl

theorem cell22_1834048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_1834048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834048 prefixEnd_1834048 := by exact prefixLift 1834048
  have htrace : WordTrace (prefixWord ++ tailWord_1834048) baseStart_1834048 baseEnd_1834048 := by
    simpa [prefixWord, tailWord_1834048, baseEnd_1834048] using wordTrace_append hprefix tailTrace_1834048
  have hstable : (prefixWord ++ tailWord_1834048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834048).length < 2 ^ (prefixWord ++ tailWord_1834048).sum := by decide
  have hdescent : baseEnd_1834048 < baseStart_1834048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834080 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_1834080 : Nat := 118140960795 + 1834080 * 2 ^ 59
def prefixEnd_1834080 : Nat := 4983230072969 + 3 ^ 40 * 1834080 * 2
def baseEnd_1834080 : Nat := 627843065865526258176817

theorem tailTrace_1834080 : CollatzResearch.WordTrace tailWord_1834080 prefixEnd_1834080 627843065865526258176817 := by
  unfold tailWord_1834080
  simp only [CollatzResearch.WordTrace]
  refine ⟨33447196597724435385561847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44596262130299247180749129 33447196597724435385561847)
  ·
    refine ⟨50170794896586653078342771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33447196597724435385561847 50170794896586653078342771)
    ·
      refine ⟨75256192344879979617514157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50170794896586653078342771 75256192344879979617514157)
      ·
        refine ⟨28221072129329992356567809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75256192344879979617514157 28221072129329992356567809)
        ·
          refine ⟨21165804096997494267425857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28221072129329992356567809 21165804096997494267425857)
          ·
            refine ⟨15874353072748120700569393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21165804096997494267425857 15874353072748120700569393)
            ·
              refine ⟨11905764804561090525427045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15874353072748120700569393 11905764804561090525427045)
              ·
                refine ⟨2232330900855204473517571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11905764804561090525427045 2232330900855204473517571)
                ·
                  refine ⟨3348496351282806710276357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232330900855204473517571 3348496351282806710276357)
                  ·
                    refine ⟨627843065865526258176817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348496351282806710276357 627843065865526258176817)
                    ·
                      rfl

theorem cell22_1834080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_1834080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834080 prefixEnd_1834080 := by exact prefixLift 1834080
  have htrace : WordTrace (prefixWord ++ tailWord_1834080) baseStart_1834080 baseEnd_1834080 := by
    simpa [prefixWord, tailWord_1834080, baseEnd_1834080] using wordTrace_append hprefix tailTrace_1834080
  have hstable : (prefixWord ++ tailWord_1834080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834080).length < 2 ^ (prefixWord ++ tailWord_1834080).sum := by decide
  have hdescent : baseEnd_1834080 < baseStart_1834080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834101 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 5]
def baseStart_1834101 : Nat := 118140960795 + 1834101 * 2 ^ 59
def prefixEnd_1834101 : Nat := 4983230072969 + 3 ^ 40 * 1834101 * 2
def baseEnd_1834101 : Nat := 209283418198229734467251

theorem tailTrace_1834101 : CollatzResearch.WordTrace tailWord_1834101 prefixEnd_1834101 209283418198229734467251 := by
  unfold tailWord_1834101
  simp only [CollatzResearch.WordTrace]
  refine ⟨66895159128372791357638157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44596772752248527571758771 66895159128372791357638157)
  ·
    refine ⟨25085684673139796759114309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66895159128372791357638157 25085684673139796759114309)
    ·
      refine ⟨4703565876213711892333933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25085684673139796759114309 4703565876213711892333933)
      ·
        refine ⟨1763837203580141959625225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4703565876213711892333933 1763837203580141959625225)
        ·
          refine ⟨1322877902685106469718919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763837203580141959625225 1322877902685106469718919)
          ·
            refine ⟨1984316854027659704578379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322877902685106469718919 1984316854027659704578379)
            ·
              refine ⟨2976475281041489556867569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984316854027659704578379 2976475281041489556867569)
              ·
                refine ⟨2232356460781117167650677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976475281041489556867569 2232356460781117167650677)
                ·
                  refine ⟨209283418198229734467251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2232356460781117167650677 209283418198229734467251)
                  ·
                    rfl

theorem cell22_1834101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_1834101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834101 prefixEnd_1834101 := by exact prefixLift 1834101
  have htrace : WordTrace (prefixWord ++ tailWord_1834101) baseStart_1834101 baseEnd_1834101 := by
    simpa [prefixWord, tailWord_1834101, baseEnd_1834101] using wordTrace_append hprefix tailTrace_1834101
  have hstable : (prefixWord ++ tailWord_1834101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834101).length < 2 ^ (prefixWord ++ tailWord_1834101).sum := by decide
  have hdescent : baseEnd_1834101 < baseStart_1834101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834140 : List Nat := [2, 2, 3, 2, 1, 3, 1, 8]
def baseStart_1834140 : Nat := 118140960795 + 1834140 * 2 ^ 59
def prefixEnd_1834140 : Nat := 4983230072969 + 3 ^ 40 * 1834140 * 2
def baseEnd_1834140 : Nat := 69762622787967344630737

theorem tailTrace_1834140 : CollatzResearch.WordTrace tailWord_1834140 prefixEnd_1834140 69762622787967344630737 := by
  unfold tailWord_1834140
  simp only [CollatzResearch.WordTrace]
  refine ⟨33448290787615750509153937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44597721050154334012205249 33448290787615750509153937)
  ·
    refine ⟨25086218090711812881865453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33448290787615750509153937 25086218090711812881865453)
    ·
      refine ⟨9407331784016929830699545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25086218090711812881865453 9407331784016929830699545)
      ·
        refine ⟨7055498838012697373024659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9407331784016929830699545 7055498838012697373024659)
        ·
          refine ⟨10583248257019046059536989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055498838012697373024659 10583248257019046059536989)
          ·
            refine ⟨3968718096382142272326371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10583248257019046059536989 3968718096382142272326371)
            ·
              refine ⟨5953077144573213408489557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968718096382142272326371 5953077144573213408489557)
              ·
                refine ⟨69762622787967344630737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5953077144573213408489557 69762622787967344630737)
                ·
                  rfl

theorem cell22_1834140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_1834140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834140 prefixEnd_1834140 := by exact prefixLift 1834140
  have htrace : WordTrace (prefixWord ++ tailWord_1834140) baseStart_1834140 baseEnd_1834140 := by
    simpa [prefixWord, tailWord_1834140, baseEnd_1834140] using wordTrace_append hprefix tailTrace_1834140
  have hstable : (prefixWord ++ tailWord_1834140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834140).length < 2 ^ (prefixWord ++ tailWord_1834140).sum := by decide
  have hdescent : baseEnd_1834140 < baseStart_1834140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834142 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1834142 : Nat := 118140960795 + 1834142 * 2 ^ 59
def prefixEnd_1834142 : Nat := 4983230072969 + 3 ^ 40 * 1834142 * 2
def baseEnd_1834142 : Nat := 627864289732578763126627

theorem tailTrace_1834142 : CollatzResearch.WordTrace tailWord_1834142 prefixEnd_1834142 627864289732578763126627 := by
  unfold tailWord_1834142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8362081815153031919985085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44597769680816170239920453 8362081815153031919985085)
  ·
    refine ⟨3135780680682386969994407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8362081815153031919985085 3135780680682386969994407)
    ·
      refine ⟨4703671021023580454991611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135780680682386969994407 4703671021023580454991611)
      ·
        refine ⟨7055506531535370682487417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703671021023580454991611 7055506531535370682487417)
        ·
          refine ⟨5291629898651528011865563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7055506531535370682487417 5291629898651528011865563)
          ·
            refine ⟨7937444847977292017798345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291629898651528011865563 7937444847977292017798345)
            ·
              refine ⟨5953083635982969013348759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7937444847977292017798345 5953083635982969013348759)
              ·
                refine ⟨8929625453974453520023139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953083635982969013348759 8929625453974453520023139)
                ·
                  refine ⟨13394438180961680280034709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929625453974453520023139 13394438180961680280034709)
                  ·
                    refine ⟨627864289732578763126627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13394438180961680280034709 627864289732578763126627)
                    ·
                      rfl

theorem cell22_1834142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1834142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834142 prefixEnd_1834142 := by exact prefixLift 1834142
  have htrace : WordTrace (prefixWord ++ tailWord_1834142) baseStart_1834142 baseEnd_1834142 := by
    simpa [prefixWord, tailWord_1834142, baseEnd_1834142] using wordTrace_append hprefix tailTrace_1834142
  have hstable : (prefixWord ++ tailWord_1834142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834142).length < 2 ^ (prefixWord ++ tailWord_1834142).sum := by decide
  have hdescent : baseEnd_1834142 < baseStart_1834142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834146 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1834146 : Nat := 118140960795 + 1834146 * 2 ^ 59
def prefixEnd_1834146 : Nat := 4983230072969 + 3 ^ 40 * 1834146 * 2
def baseEnd_1834146 : Nat := 209288553004774695342205

theorem tailTrace_1834146 : CollatzResearch.WordTrace tailWord_1834146 prefixEnd_1834146 209288553004774695342205 := by
  unfold tailWord_1834146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16724200103302441010756573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44597866942139842695350861 16724200103302441010756573)
  ·
    refine ⟨6271575038738415379033715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16724200103302441010756573 6271575038738415379033715)
    ·
      refine ⟨9407362558107623068550573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271575038738415379033715 9407362558107623068550573)
      ·
        refine ⟨3527760959290358650706465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9407362558107623068550573 3527760959290358650706465)
        ·
          refine ⟨2645820719467768988029849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3527760959290358650706465 2645820719467768988029849)
          ·
            refine ⟨1984365539600826741022387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645820719467768988029849 1984365539600826741022387)
            ·
              refine ⟨2976548309401240111533581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984365539600826741022387 2976548309401240111533581)
              ·
                refine ⟨1116205616025465041825093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2976548309401240111533581 1116205616025465041825093)
                ·
                  refine ⟨209288553004774695342205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116205616025465041825093 209288553004774695342205)
                  ·
                    rfl

theorem cell22_1834146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1834146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834146 prefixEnd_1834146 := by exact prefixLift 1834146
  have htrace : WordTrace (prefixWord ++ tailWord_1834146) baseStart_1834146 baseEnd_1834146 := by
    simpa [prefixWord, tailWord_1834146, baseEnd_1834146] using wordTrace_append hprefix tailTrace_1834146
  have hstable : (prefixWord ++ tailWord_1834146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834146).length < 2 ^ (prefixWord ++ tailWord_1834146).sum := by decide
  have hdescent : baseEnd_1834146 < baseStart_1834146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834153 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1834153 : Nat := 118140960795 + 1834153 * 2 ^ 59
def prefixEnd_1834153 : Nat := 4983230072969 + 3 ^ 40 * 1834153 * 2
def baseEnd_1834153 : Nat := 627868055257378401101593

theorem tailTrace_1834153 : CollatzResearch.WordTrace tailWord_1834153 prefixEnd_1834153 627868055257378401101593 := by
  unfold tailWord_1834153
  simp only [CollatzResearch.WordTrace]
  refine ⟨66897055724184404238531113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44598037149456269492354075 66897055724184404238531113)
  ·
    refine ⟨50172791793138303178898335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66897055724184404238531113 50172791793138303178898335)
    ·
      refine ⟨75259187689707454768347503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50172791793138303178898335 75259187689707454768347503)
      ·
        refine ⟨112888781534561182152521255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75259187689707454768347503 112888781534561182152521255)
        ·
          refine ⟨169333172301841773228781883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112888781534561182152521255 169333172301841773228781883)
          ·
            refine ⟨253999758452762659843172825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169333172301841773228781883 253999758452762659843172825)
            ·
              refine ⟨190499818839571994882379619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253999758452762659843172825 190499818839571994882379619)
              ·
                refine ⟨285749728259357992323569429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190499818839571994882379619 285749728259357992323569429)
                ·
                  refine ⟨13394518512157405890167317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285749728259357992323569429 13394518512157405890167317)
                  ·
                    refine ⟨627868055257378401101593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13394518512157405890167317 627868055257378401101593)
                    ·
                      rfl

theorem cell22_1834153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1834153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834153 prefixEnd_1834153 := by exact prefixLift 1834153
  have htrace : WordTrace (prefixWord ++ tailWord_1834153) baseStart_1834153 baseEnd_1834153 := by
    simpa [prefixWord, tailWord_1834153, baseEnd_1834153] using wordTrace_append hprefix tailTrace_1834153
  have hstable : (prefixWord ++ tailWord_1834153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834153).length < 2 ^ (prefixWord ++ tailWord_1834153).sum := by decide
  have hdescent : baseEnd_1834153 < baseStart_1834153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834157 : List Nat := [1, 5, 2, 1, 3, 2, 8]
def baseStart_1834157 : Nat := 118140960795 + 1834157 * 2 ^ 59
def prefixEnd_1834157 : Nat := 4983230072969 + 3 ^ 40 * 1834157 * 2
def baseEnd_1834157 : Nat := 23254423131078656444503

theorem tailTrace_1834157 : CollatzResearch.WordTrace tailWord_1834157 prefixEnd_1834157 23254423131078656444503 := by
  unfold tailWord_1834157
  simp only [CollatzResearch.WordTrace]
  refine ⟨66897201616169912921676725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44598134410779941947784483 66897201616169912921676725)
  ·
    refine ⟨6271612651515929336407193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66897201616169912921676725 6271612651515929336407193)
    ·
      refine ⟨4703709488636947002305395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6271612651515929336407193 4703709488636947002305395)
      ·
        refine ⟨7055564232955420503458093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703709488636947002305395 7055564232955420503458093)
        ·
          refine ⟨2645836587358282688796785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7055564232955420503458093 2645836587358282688796785)
          ·
            refine ⟨1984377440518712016597589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645836587358282688796785 1984377440518712016597589)
            ·
              refine ⟨23254423131078656444503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1984377440518712016597589 23254423131078656444503)
              ·
                rfl

theorem cell22_1834157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 8].length) (baseStart_1834157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834157 prefixEnd_1834157 := by exact prefixLift 1834157
  have htrace : WordTrace (prefixWord ++ tailWord_1834157) baseStart_1834157 baseEnd_1834157 := by
    simpa [prefixWord, tailWord_1834157, baseEnd_1834157] using wordTrace_append hprefix tailTrace_1834157
  have hstable : (prefixWord ++ tailWord_1834157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834157).length < 2 ^ (prefixWord ++ tailWord_1834157).sum := by decide
  have hdescent : baseEnd_1834157 < baseStart_1834157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834178 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1834178 : Nat := 118140960795 + 1834178 * 2 ^ 59
def prefixEnd_1834178 : Nat := 4983230072969 + 3 ^ 40 * 1834178 * 2
def baseEnd_1834178 : Nat := 627876613268286669226517

theorem tailTrace_1834178 : CollatzResearch.WordTrace tailWord_1834178 prefixEnd_1834178 627876613268286669226517 := by
  unfold tailWord_1834178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16724491887273458377047797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44598645032729222338794125 16724491887273458377047797)
  ·
    refine ⟨1567921114431886722848231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16724491887273458377047797 1567921114431886722848231)
    ·
      refine ⟨2351881671647830084272347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567921114431886722848231 2351881671647830084272347)
      ·
        refine ⟨3527822507471745126408521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351881671647830084272347 3527822507471745126408521)
        ·
          refine ⟨2645866880603808844806391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3527822507471745126408521 2645866880603808844806391)
          ·
            refine ⟨3968800320905713267209587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645866880603808844806391 3968800320905713267209587)
            ·
              refine ⟨5953200481358569900814381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968800320905713267209587 5953200481358569900814381)
              ·
                refine ⟨2232450180509463712805393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5953200481358569900814381 2232450180509463712805393)
                ·
                  refine ⟨1674337635382097784604045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232450180509463712805393 1674337635382097784604045)
                  ·
                    refine ⟨627876613268286669226517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674337635382097784604045 627876613268286669226517)
                    ·
                      rfl

theorem cell22_1834178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1834178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834178 prefixEnd_1834178 := by exact prefixLift 1834178
  have htrace : WordTrace (prefixWord ++ tailWord_1834178) baseStart_1834178 baseEnd_1834178 := by
    simpa [prefixWord, tailWord_1834178, baseEnd_1834178] using wordTrace_append hprefix tailTrace_1834178
  have hstable : (prefixWord ++ tailWord_1834178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834178).length < 2 ^ (prefixWord ++ tailWord_1834178).sum := by decide
  have hdescent : baseEnd_1834178 < baseStart_1834178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834223 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 1, 3]
def baseStart_1834223 : Nat := 118140960795 + 1834223 * 2 ^ 59
def prefixEnd_1834223 : Nat := 4983230072969 + 3 ^ 40 * 1834223 * 2
def baseEnd_1834223 : Nat := 627892017687921551851379

theorem tailTrace_1834223 : CollatzResearch.WordTrace tailWord_1834223 prefixEnd_1834223 627892017687921551851379 := by
  unfold tailWord_1834223
  simp only [CollatzResearch.WordTrace]
  refine ⟨66899608833930806193579323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44599739222620537462386215 66899608833930806193579323)
  ·
    refine ⟨100349413250896209290368985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66899608833930806193579323 100349413250896209290368985)
    ·
      refine ⟨75262059938172156967776739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100349413250896209290368985 75262059938172156967776739)
      ·
        refine ⟨112893089907258235451665109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75262059938172156967776739 112893089907258235451665109)
        ·
          refine ⟨2645931794701364893398401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 112893089907258235451665109 2645931794701364893398401)
          ·
            refine ⟨1984448846026023670048801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645931794701364893398401 1984448846026023670048801)
            ·
              refine ⟨1488336634519517752536601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984448846026023670048801 1488336634519517752536601)
              ·
                refine ⟨1116252475889638314402451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488336634519517752536601 1116252475889638314402451)
                ·
                  refine ⟨1674378713834457471603677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116252475889638314402451 1674378713834457471603677)
                  ·
                    refine ⟨627892017687921551851379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674378713834457471603677 627892017687921551851379)
                    ·
                      rfl

theorem cell22_1834223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_1834223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834223 prefixEnd_1834223 := by exact prefixLift 1834223
  have htrace : WordTrace (prefixWord ++ tailWord_1834223) baseStart_1834223 baseEnd_1834223 := by
    simpa [prefixWord, tailWord_1834223, baseEnd_1834223] using wordTrace_append hprefix tailTrace_1834223
  have hstable : (prefixWord ++ tailWord_1834223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834223).length < 2 ^ (prefixWord ++ tailWord_1834223).sum := by decide
  have hdescent : baseEnd_1834223 < baseStart_1834223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834264 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_1834264 : Nat := 118140960795 + 1834264 * 2 ^ 59
def prefixEnd_1834264 : Nat := 4983230072969 + 3 ^ 40 * 1834264 * 2
def baseEnd_1834264 : Nat := 209302017608603703858751

theorem tailTrace_1834264 : CollatzResearch.WordTrace tailWord_1834264 prefixEnd_1834264 209302017608603703858751 := by
  unfold tailWord_1834264
  simp only [CollatzResearch.WordTrace]
  refine ⟨33450552113391135097910923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44600736151188180130547897 33450552113391135097910923)
  ·
    refine ⟨50175828170086702646866385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33450552113391135097910923 50175828170086702646866385)
    ·
      refine ⟨37631871127565026985149789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50175828170086702646866385 37631871127565026985149789)
      ·
        refine ⟨14111951672836885119431171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37631871127565026985149789 14111951672836885119431171)
        ·
          refine ⟨21167927509255327679146757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14111951672836885119431171 21167927509255327679146757)
          ·
            refine ⟨3968986407985373939840017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21167927509255327679146757 3968986407985373939840017)
            ·
              refine ⟨2976739805989030454880013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968986407985373939840017 2976739805989030454880013)
              ·
                refine ⟨1116277427245886420580005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2976739805989030454880013 1116277427245886420580005)
                ·
                  refine ⟨209302017608603703858751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1116277427245886420580005 209302017608603703858751)
                  ·
                    rfl

theorem cell22_1834264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_1834264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834264 prefixEnd_1834264 := by exact prefixLift 1834264
  have htrace : WordTrace (prefixWord ++ tailWord_1834264) baseStart_1834264 baseEnd_1834264 := by
    simpa [prefixWord, tailWord_1834264, baseEnd_1834264] using wordTrace_append hprefix tailTrace_1834264
  have hstable : (prefixWord ++ tailWord_1834264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834264).length < 2 ^ (prefixWord ++ tailWord_1834264).sum := by decide
  have hdescent : baseEnd_1834264 < baseStart_1834264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834266 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_1834266 : Nat := 118140960795 + 1834266 * 2 ^ 59
def prefixEnd_1834266 : Nat := 4983230072969 + 3 ^ 40 * 1834266 * 2
def baseEnd_1834266 : Nat := 627906737466683773026247

theorem tailTrace_1834266 : CollatzResearch.WordTrace tailWord_1834266 prefixEnd_1834266 627906737466683773026247 := by
  unfold tailWord_1834266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725294293193756134348663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44600784781850016358263101 16725294293193756134348663)
  ·
    refine ⟨25087941439790634201522995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16725294293193756134348663 25087941439790634201522995)
    ·
      refine ⟨37631912159685951302284493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25087941439790634201522995 37631912159685951302284493)
      ·
        refine ⟨14111967059882231738356685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37631912159685951302284493 14111967059882231738356685)
        ·
          refine ⟨5291987647455836901883757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14111967059882231738356685 5291987647455836901883757)
          ·
            refine ⟨1984495367795938838206409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5291987647455836901883757 1984495367795938838206409)
            ·
              refine ⟨1488371525846954128654807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984495367795938838206409 1488371525846954128654807)
              ·
                refine ⟨2232557288770431192982211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488371525846954128654807 2232557288770431192982211)
                ·
                  refine ⟨3348835933155646789473317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232557288770431192982211 3348835933155646789473317)
                  ·
                    refine ⟨627906737466683773026247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3348835933155646789473317 627906737466683773026247)
                    ·
                      rfl

theorem cell22_1834266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_1834266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834266 prefixEnd_1834266 := by exact prefixLift 1834266
  have htrace : WordTrace (prefixWord ++ tailWord_1834266) baseStart_1834266 baseEnd_1834266 := by
    simpa [prefixWord, tailWord_1834266, baseEnd_1834266] using wordTrace_append hprefix tailTrace_1834266
  have hstable : (prefixWord ++ tailWord_1834266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834266).length < 2 ^ (prefixWord ++ tailWord_1834266).sum := by decide
  have hdescent : baseEnd_1834266 < baseStart_1834266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834275 : List Nat := [1, 1, 1, 4, 2, 4, 9]
def baseStart_1834275 : Nat := 118140960795 + 1834275 * 2 ^ 59
def prefixEnd_1834275 : Nat := 4983230072969 + 3 ^ 40 * 1834275 * 2
def baseEnd_1834275 : Nat := 23255919198170768501897

theorem tailTrace_1834275 : CollatzResearch.WordTrace tailWord_1834275 prefixEnd_1834275 23255919198170768501897 := by
  unfold tailWord_1834275
  simp only [CollatzResearch.WordTrace]
  refine ⟨66901505429742419074472279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44601003619828279382981519 66901505429742419074472279)
  ·
    refine ⟨100352258144613628611708419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66901505429742419074472279 100352258144613628611708419)
    ·
      refine ⟨150528387216920442917562629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100352258144613628611708419 150528387216920442917562629)
      ·
        refine ⟨28224072603172583047042993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150528387216920442917562629 28224072603172583047042993)
        ·
          refine ⟨21168054452379437285282245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28224072603172583047042993 21168054452379437285282245)
          ·
            refine ⟨3969010209821144490990421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21168054452379437285282245 3969010209821144490990421)
            ·
              refine ⟨23255919198170768501897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3969010209821144490990421 23255919198170768501897)
              ·
                rfl

theorem cell22_1834275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 9].length) (baseStart_1834275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834275 prefixEnd_1834275 := by exact prefixLift 1834275
  have htrace : WordTrace (prefixWord ++ tailWord_1834275) baseStart_1834275 baseEnd_1834275 := by
    simpa [prefixWord, tailWord_1834275, baseEnd_1834275] using wordTrace_append hprefix tailTrace_1834275
  have hstable : (prefixWord ++ tailWord_1834275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834275).length < 2 ^ (prefixWord ++ tailWord_1834275).sum := by decide
  have hdescent : baseEnd_1834275 < baseStart_1834275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834292 : List Nat := [2, 5, 1, 1, 1, 1, 2, 9]
def baseStart_1834292 : Nat := 118140960795 + 1834292 * 2 ^ 59
def prefixEnd_1834292 : Nat := 4983230072969 + 3 ^ 40 * 1834292 * 2
def baseEnd_1834292 : Nat := 69768404199780930208463

theorem tailTrace_1834292 : CollatzResearch.WordTrace tailWord_1834292 prefixEnd_1834292 69768404199780930208463 := by
  unfold tailWord_1834292
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451062735340415488920565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44601416980453887318560753 33451062735340415488920565)
  ·
    refine ⟨3136037131438163952086303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33451062735340415488920565 3136037131438163952086303)
    ·
      refine ⟨4704055697157245928129455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136037131438163952086303 4704055697157245928129455)
      ·
        refine ⟨7056083545735868892194183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704055697157245928129455 7056083545735868892194183)
        ·
          refine ⟨10584125318603803338291275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056083545735868892194183 10584125318603803338291275)
          ·
            refine ⟨15876187977905705007436913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584125318603803338291275 15876187977905705007436913)
            ·
              refine ⟨11907140983429278755577685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15876187977905705007436913 11907140983429278755577685)
              ·
                refine ⟨69768404199780930208463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11907140983429278755577685 69768404199780930208463)
                ·
                  rfl

theorem cell22_1834292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_1834292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834292 prefixEnd_1834292 := by exact prefixLift 1834292
  have htrace : WordTrace (prefixWord ++ tailWord_1834292) baseStart_1834292 baseEnd_1834292 := by
    simpa [prefixWord, tailWord_1834292, baseEnd_1834292] using wordTrace_append hprefix tailTrace_1834292
  have hstable : (prefixWord ++ tailWord_1834292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834292).length < 2 ^ (prefixWord ++ tailWord_1834292).sum := by decide
  have hdescent : baseEnd_1834292 < baseStart_1834292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834320 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_1834320 : Nat := 118140960795 + 1834320 * 2 ^ 59
def prefixEnd_1834320 : Nat := 4983230072969 + 3 ^ 40 * 1834320 * 2
def baseEnd_1834320 : Nat := 209308407590081877392027

theorem tailTrace_1834320 : CollatzResearch.WordTrace tailWord_1834320 prefixEnd_1834320 209308407590081877392027 := by
  unfold tailWord_1834320
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451573357289695879930207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44602097809719594506573609 33451573357289695879930207)
  ·
    refine ⟨50177360035934543819895311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33451573357289695879930207 50177360035934543819895311)
    ·
      refine ⟨75266040053901815729842967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50177360035934543819895311 75266040053901815729842967)
      ·
        refine ⟨112899060080852723594764451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75266040053901815729842967 112899060080852723594764451)
        ·
          refine ⟨169348590121279085392146677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112899060080852723594764451 169348590121279085392146677)
          ·
            refine ⟨15876430323869914255513751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169348590121279085392146677 15876430323869914255513751)
            ·
              refine ⟨23814645485804871383270627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876430323869914255513751 23814645485804871383270627)
              ·
                refine ⟨35721968228707307074905941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23814645485804871383270627 35721968228707307074905941)
                ·
                  refine ⟨209308407590081877392027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35721968228707307074905941 209308407590081877392027)
                  ·
                    rfl

theorem cell22_1834320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_1834320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834320 prefixEnd_1834320 := by exact prefixLift 1834320
  have htrace : WordTrace (prefixWord ++ tailWord_1834320) baseStart_1834320 baseEnd_1834320 := by
    simpa [prefixWord, tailWord_1834320, baseEnd_1834320] using wordTrace_append hprefix tailTrace_1834320
  have hstable : (prefixWord ++ tailWord_1834320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834320).length < 2 ^ (prefixWord ++ tailWord_1834320).sum := by decide
  have hdescent : baseEnd_1834320 < baseStart_1834320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834392 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 1, 3]
def baseStart_1834392 : Nat := 118140960795 + 1834392 * 2 ^ 59
def prefixEnd_1834392 : Nat := 4983230072969 + 3 ^ 40 * 1834392 * 2
def baseEnd_1834392 : Nat := 627949869841661444375861

theorem tailTrace_1834392 : CollatzResearch.WordTrace tailWord_1834392 prefixEnd_1834392 627949869841661444375861 := by
  unfold tailWord_1834392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33452886385159274028240715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44603848513545698704320953 33452886385159274028240715)
  ·
    refine ⟨50179329577738911042361073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33452886385159274028240715 50179329577738911042361073)
    ·
      refine ⟨37634497183304183281770805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50179329577738911042361073 37634497183304183281770805)
      ·
        refine ⟨3528234110934767182666013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37634497183304183281770805 3528234110934767182666013)
        ·
          refine ⟨1323087791600537693499755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3528234110934767182666013 1323087791600537693499755)
          ·
            refine ⟨1984631687400806540249633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323087791600537693499755 1984631687400806540249633)
            ·
              refine ⟨1488473765550604905187225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984631687400806540249633 1488473765550604905187225)
              ·
                refine ⟨1116355324162953678890419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488473765550604905187225 1116355324162953678890419)
                ·
                  refine ⟨1674532986244430518335629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116355324162953678890419 1674532986244430518335629)
                  ·
                    refine ⟨627949869841661444375861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674532986244430518335629 627949869841661444375861)
                    ·
                      rfl

theorem cell22_1834392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_1834392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834392 prefixEnd_1834392 := by exact prefixLift 1834392
  have htrace : WordTrace (prefixWord ++ tailWord_1834392) baseStart_1834392 baseEnd_1834392 := by
    simpa [prefixWord, tailWord_1834392, baseEnd_1834392] using wordTrace_append hprefix tailTrace_1834392
  have hstable : (prefixWord ++ tailWord_1834392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834392).length < 2 ^ (prefixWord ++ tailWord_1834392).sum := by decide
  have hdescent : baseEnd_1834392 < baseStart_1834392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834412 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_1834412 : Nat := 118140960795 + 1834412 * 2 ^ 59
def prefixEnd_1834412 : Nat := 4983230072969 + 3 ^ 40 * 1834412 * 2
def baseEnd_1834412 : Nat := 627956716250388058875799

theorem tailTrace_1834412 : CollatzResearch.WordTrace tailWord_1834412 prefixEnd_1834412 627956716250388058875799 := by
  unfold tailWord_1834412
  simp only [CollatzResearch.WordTrace]
  refine ⟨33453251115123045736104745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44604334820164060981472993 33453251115123045736104745)
  ·
    refine ⟨25089938336342284302078559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33453251115123045736104745 25089938336342284302078559)
    ·
      refine ⟨37634907504513426453117839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25089938336342284302078559 37634907504513426453117839)
      ·
        refine ⟨56452361256770139679676759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37634907504513426453117839 56452361256770139679676759)
        ·
          refine ⟨84678541885155209519515139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56452361256770139679676759 84678541885155209519515139)
          ·
            refine ⟨127017812827732814279272709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84678541885155209519515139 127017812827732814279272709)
            ·
              refine ⟨23815839905199902677363633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127017812827732814279272709 23815839905199902677363633)
              ·
                refine ⟨17861879928899927008022725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23815839905199902677363633 17861879928899927008022725)
                ·
                  refine ⟨3349102486668736314004261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17861879928899927008022725 3349102486668736314004261)
                  ·
                    refine ⟨627956716250388058875799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349102486668736314004261 627956716250388058875799)
                    ·
                      rfl

theorem cell22_1834412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_1834412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834412 prefixEnd_1834412 := by exact prefixLift 1834412
  have htrace : WordTrace (prefixWord ++ tailWord_1834412) baseStart_1834412 baseEnd_1834412 := by
    simpa [prefixWord, tailWord_1834412, baseEnd_1834412] using wordTrace_append hprefix tailTrace_1834412
  have hstable : (prefixWord ++ tailWord_1834412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834412).length < 2 ^ (prefixWord ++ tailWord_1834412).sum := by decide
  have hdescent : baseEnd_1834412 < baseStart_1834412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834487 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1834487 : Nat := 118140960795 + 1834487 * 2 ^ 59
def prefixEnd_1834487 : Nat := 4983230072969 + 3 ^ 40 * 1834487 * 2
def baseEnd_1834487 : Nat := 627982390283112863250569

theorem tailTrace_1834487 : CollatzResearch.WordTrace tailWord_1834487 prefixEnd_1834487 627982390283112863250569 := by
  unfold tailWord_1834487
  simp only [CollatzResearch.WordTrace]
  refine ⟨66909237704974379281189715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44606158469982919520793143 66909237704974379281189715)
  ·
    refine ⟨100363856557461568921784573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66909237704974379281189715 100363856557461568921784573)
    ·
      refine ⟨37636446209048088345669215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100363856557461568921784573 37636446209048088345669215)
      ·
        refine ⟨56454669313572132518503823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37636446209048088345669215 56454669313572132518503823)
        ·
          refine ⟨84682003970358198777755735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56454669313572132518503823 84682003970358198777755735)
          ·
            refine ⟨127023005955537298166633603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84682003970358198777755735 127023005955537298166633603)
            ·
              refine ⟨190534508933305947249950405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127023005955537298166633603 190534508933305947249950405)
              ·
                refine ⟨35725220424994865109365701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190534508933305947249950405 35725220424994865109365701)
                ·
                  refine ⟨6698478829686537208006069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35725220424994865109365701 6698478829686537208006069)
                  ·
                    refine ⟨627982390283112863250569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6698478829686537208006069 627982390283112863250569)
                    ·
                      rfl

theorem cell22_1834487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1834487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834487 prefixEnd_1834487 := by exact prefixLift 1834487
  have htrace : WordTrace (prefixWord ++ tailWord_1834487) baseStart_1834487 baseEnd_1834487 := by
    simpa [prefixWord, tailWord_1834487, baseEnd_1834487] using wordTrace_append hprefix tailTrace_1834487
  have hstable : (prefixWord ++ tailWord_1834487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834487).length < 2 ^ (prefixWord ++ tailWord_1834487).sum := by decide
  have hdescent : baseEnd_1834487 < baseStart_1834487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834493 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_1834493 : Nat := 118140960795 + 1834493 * 2 ^ 59
def prefixEnd_1834493 : Nat := 4983230072969 + 3 ^ 40 * 1834493 * 2
def baseEnd_1834493 : Nat := 627984444205730847600551

theorem tailTrace_1834493 : CollatzResearch.WordTrace tailWord_1834493 prefixEnd_1834493 627984444205730847600551 := by
  unfold tailWord_1834493
  simp only [CollatzResearch.WordTrace]
  refine ⟨66909456542952642305908133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44606304361968428203938755 66909456542952642305908133)
  ·
    refine ⟨12545523101803620432357775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66909456542952642305908133 12545523101803620432357775)
    ·
      refine ⟨18818284652705430648536663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545523101803620432357775 18818284652705430648536663)
      ·
        refine ⟨28227426979058145972804995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18818284652705430648536663 28227426979058145972804995)
        ·
          refine ⟨42341140468587218959207493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28227426979058145972804995 42341140468587218959207493)
          ·
            refine ⟨7938963837860103554851405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42341140468587218959207493 7938963837860103554851405)
            ·
              refine ⟨2977111439197538833069277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7938963837860103554851405 2977111439197538833069277)
              ·
                refine ⟨1116416789699077062400979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2977111439197538833069277 1116416789699077062400979)
                ·
                  refine ⟨1674625184548615593601469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116416789699077062400979 1674625184548615593601469)
                  ·
                    refine ⟨627984444205730847600551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674625184548615593601469 627984444205730847600551)
                    ·
                      rfl

theorem cell22_1834493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_1834493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834493 prefixEnd_1834493 := by exact prefixLift 1834493
  have htrace : WordTrace (prefixWord ++ tailWord_1834493) baseStart_1834493 baseEnd_1834493 := by
    simpa [prefixWord, tailWord_1834493, baseEnd_1834493] using wordTrace_append hprefix tailTrace_1834493
  have hstable : (prefixWord ++ tailWord_1834493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834493).length < 2 ^ (prefixWord ++ tailWord_1834493).sum := by decide
  have hdescent : baseEnd_1834493 < baseStart_1834493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834510 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_1834510 : Nat := 118140960795 + 1834510 * 2 ^ 59
def prefixEnd_1834510 : Nat := 4983230072969 + 3 ^ 40 * 1834510 * 2
def baseEnd_1834510 : Nat := 627990263653148469925499

theorem tailTrace_1834510 : CollatzResearch.WordTrace tailWord_1834510 prefixEnd_1834510 627990263653148469925499 := by
  unfold tailWord_1834510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363759572986381776159623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44606717722594036139517989 8363759572986381776159623)
  ·
    refine ⟨12545639359479572664239435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363759572986381776159623 12545639359479572664239435)
    ·
      refine ⟨18818459039219358996359153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545639359479572664239435 18818459039219358996359153)
      ·
        refine ⟨14113844279414519247269365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18818459039219358996359153 14113844279414519247269365)
        ·
          refine ⟨1323172901195111179431503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14113844279414519247269365 1323172901195111179431503)
          ·
            refine ⟨1984759351792666769147255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323172901195111179431503 1984759351792666769147255)
            ·
              refine ⟨2977139027689000153720883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984759351792666769147255 2977139027689000153720883)
              ·
                refine ⟨4465708541533500230581325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977139027689000153720883 4465708541533500230581325)
                ·
                  refine ⟨1674640703075062586467997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4465708541533500230581325 1674640703075062586467997)
                  ·
                    refine ⟨627990263653148469925499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674640703075062586467997 627990263653148469925499)
                    ·
                      rfl

theorem cell22_1834510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_1834510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834510 prefixEnd_1834510 := by exact prefixLift 1834510
  have htrace : WordTrace (prefixWord ++ tailWord_1834510) baseStart_1834510 baseEnd_1834510 := by
    simpa [prefixWord, tailWord_1834510, baseEnd_1834510] using wordTrace_append hprefix tailTrace_1834510
  have hstable : (prefixWord ++ tailWord_1834510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834510).length < 2 ^ (prefixWord ++ tailWord_1834510).sum := by decide
  have hdescent : baseEnd_1834510 < baseStart_1834510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834549 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1834549 : Nat := 118140960795 + 1834549 * 2 ^ 59
def prefixEnd_1834549 : Nat := 4983230072969 + 3 ^ 40 * 1834549 * 2
def baseEnd_1834549 : Nat := 628003614150165368200379

theorem tailTrace_1834549 : CollatzResearch.WordTrace tailWord_1834549 prefixEnd_1834549 628003614150165368200379 := by
  unfold tailWord_1834549
  simp only [CollatzResearch.WordTrace]
  refine ⟨66911499030749763869946701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44607666020499842579964467 66911499030749763869946701)
  ·
    refine ⟨25091812136531161451230013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66911499030749763869946701 25091812136531161451230013)
    ·
      refine ⟨9409429551199185544211255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25091812136531161451230013 9409429551199185544211255)
      ·
        refine ⟨14114144326798778316316883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409429551199185544211255 14114144326798778316316883)
        ·
          refine ⟨21171216490198167474475325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14114144326798778316316883 21171216490198167474475325)
          ·
            refine ⟨7939206183824312802928247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21171216490198167474475325 7939206183824312802928247)
            ·
              refine ⟨11908809275736469204392371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939206183824312802928247 11908809275736469204392371)
              ·
                refine ⟨17863213913604703806588557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11908809275736469204392371 17863213913604703806588557)
                ·
                  refine ⟨6698705217601763927470709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17863213913604703806588557 6698705217601763927470709)
                  ·
                    refine ⟨628003614150165368200379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6698705217601763927470709 628003614150165368200379)
                    ·
                      rfl

theorem cell22_1834549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1834549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834549 prefixEnd_1834549 := by exact prefixLift 1834549
  have htrace : WordTrace (prefixWord ++ tailWord_1834549) baseStart_1834549 baseEnd_1834549 := by
    simpa [prefixWord, tailWord_1834549, baseEnd_1834549] using wordTrace_append hprefix tailTrace_1834549
  have hstable : (prefixWord ++ tailWord_1834549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834549).length < 2 ^ (prefixWord ++ tailWord_1834549).sum := by decide
  have hdescent : baseEnd_1834549 < baseStart_1834549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834553 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_1834553 : Nat := 118140960795 + 1834553 * 2 ^ 59
def prefixEnd_1834553 : Nat := 4983230072969 + 3 ^ 40 * 1834553 * 2
def baseEnd_1834553 : Nat := 628004983431910691100367

theorem tailTrace_1834553 : CollatzResearch.WordTrace tailWord_1834553 prefixEnd_1834553 628004983431910691100367 := by
  unfold tailWord_1834553
  simp only [CollatzResearch.WordTrace]
  refine ⟨66911644922735272553092313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44607763281823515035394875 66911644922735272553092313)
  ·
    refine ⟨50183733692051454414819235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66911644922735272553092313 50183733692051454414819235)
    ·
      refine ⟨75275600538077181622228853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50183733692051454414819235 75275600538077181622228853)
      ·
        refine ⟨7057087550444735777083955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75275600538077181622228853 7057087550444735777083955)
        ·
          refine ⟨10585631325667103665625933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057087550444735777083955 10585631325667103665625933)
          ·
            refine ⟨3969611747125163874609725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10585631325667103665625933 3969611747125163874609725)
            ·
              refine ⟨1488604405171936452978647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969611747125163874609725 1488604405171936452978647)
              ·
                refine ⟨2232906607757904679467971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488604405171936452978647 2232906607757904679467971)
                ·
                  refine ⟨3349359911636857019201957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232906607757904679467971 3349359911636857019201957)
                  ·
                    refine ⟨628004983431910691100367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349359911636857019201957 628004983431910691100367)
                    ·
                      rfl

theorem cell22_1834553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_1834553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834553 prefixEnd_1834553 := by exact prefixLift 1834553
  have htrace : WordTrace (prefixWord ++ tailWord_1834553) baseStart_1834553 baseEnd_1834553 := by
    simpa [prefixWord, tailWord_1834553, baseEnd_1834553] using wordTrace_append hprefix tailTrace_1834553
  have hstable : (prefixWord ++ tailWord_1834553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834553).length < 2 ^ (prefixWord ++ tailWord_1834553).sum := by decide
  have hdescent : baseEnd_1834553 < baseStart_1834553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834596 : List Nat := [2, 3, 1, 1, 2, 4, 3, 6]
def baseStart_1834596 : Nat := 118140960795 + 1834596 * 2 ^ 59
def prefixEnd_1834596 : Nat := 4983230072969 + 3 ^ 40 * 1834596 * 2
def baseEnd_1834596 : Nat := 69779967023408101363915

theorem tailTrace_1834596 : CollatzResearch.WordTrace tailWord_1834596 prefixEnd_1834596 69779967023408101363915 := by
  unfold tailWord_1834596
  simp only [CollatzResearch.WordTrace]
  refine ⟨33456606630789745448453821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44608808841052993931271761 33456606630789745448453821)
  ·
    refine ⟨12546227486546154543170183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33456606630789745448453821 12546227486546154543170183)
    ·
      refine ⟨18819341229819231814755275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12546227486546154543170183 18819341229819231814755275)
      ·
        refine ⟨28229011844728847722132913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18819341229819231814755275 28229011844728847722132913)
        ·
          refine ⟨21171758883546635791599685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28229011844728847722132913 21171758883546635791599685)
          ·
            refine ⟨3969704790664994210924941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21171758883546635791599685 3969704790664994210924941)
            ·
              refine ⟨1488639296499372829096853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969704790664994210924941 1488639296499372829096853)
              ·
                refine ⟨69779967023408101363915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1488639296499372829096853 69779967023408101363915)
                ·
                  rfl

theorem cell22_1834596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_1834596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834596 prefixEnd_1834596 := by exact prefixLift 1834596
  have htrace : WordTrace (prefixWord ++ tailWord_1834596) baseStart_1834596 baseEnd_1834596 := by
    simpa [prefixWord, tailWord_1834596, baseEnd_1834596] using wordTrace_append hprefix tailTrace_1834596
  have hstable : (prefixWord ++ tailWord_1834596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834596).length < 2 ^ (prefixWord ++ tailWord_1834596).sum := by decide
  have hdescent : baseEnd_1834596 < baseStart_1834596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834624 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_1834624 : Nat := 118140960795 + 1834624 * 2 ^ 59
def prefixEnd_1834624 : Nat := 4983230072969 + 3 ^ 40 * 1834624 * 2
def baseEnd_1834624 : Nat := 209343096060963390858383

theorem tailTrace_1834624 : CollatzResearch.WordTrace tailWord_1834624 prefixEnd_1834624 209343096060963390858383 := by
  unfold tailWord_1834624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33457117252739025839463463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44609489670318701119284617 33457117252739025839463463)
  ·
    refine ⟨50185675879108538759195195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33457117252739025839463463 50185675879108538759195195)
    ·
      refine ⟨75278513818662808138792793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50185675879108538759195195 75278513818662808138792793)
      ·
        refine ⟨56458885363997106104094595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75278513818662808138792793 56458885363997106104094595)
        ·
          refine ⟨84688328045995659156141893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56458885363997106104094595 84688328045995659156141893)
          ·
            refine ⟨15879061508624186091776605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84688328045995659156141893 15879061508624186091776605)
            ·
              refine ⟨5954648065734069784416227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15879061508624186091776605 5954648065734069784416227)
              ·
                refine ⟨8931972098601104676624341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954648065734069784416227 8931972098601104676624341)
                ·
                  refine ⟨209343096060963390858383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8931972098601104676624341 209343096060963390858383)
                  ·
                    rfl

theorem cell22_1834624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_1834624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834624 prefixEnd_1834624 := by exact prefixLift 1834624
  have htrace : WordTrace (prefixWord ++ tailWord_1834624) baseStart_1834624 baseEnd_1834624 := by
    simpa [prefixWord, tailWord_1834624, baseEnd_1834624] using wordTrace_append hprefix tailTrace_1834624
  have hstable : (prefixWord ++ tailWord_1834624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834624).length < 2 ^ (prefixWord ++ tailWord_1834624).sum := by decide
  have hdescent : baseEnd_1834624 < baseStart_1834624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834671 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 1, 4]
def baseStart_1834671 : Nat := 118140960795 + 1834671 * 2 ^ 59
def prefixEnd_1834671 : Nat := 4983230072969 + 3 ^ 40 * 1834671 * 2
def baseEnd_1834671 : Nat := 628045377243397716650005

theorem tailTrace_1834671 : CollatzResearch.WordTrace tailWord_1834671 prefixEnd_1834671 628045377243397716650005 := by
  unfold tailWord_1834671
  simp only [CollatzResearch.WordTrace]
  refine ⟨66915948736307778705887867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44610632490871852470591911 66915948736307778705887867)
  ·
    refine ⟨100373923104461668058831801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66915948736307778705887867 100373923104461668058831801)
    ·
      refine ⟨75280442328346251044123851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100373923104461668058831801 75280442328346251044123851)
      ·
        refine ⟨112920663492519376566185777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75280442328346251044123851 112920663492519376566185777)
        ·
          refine ⟨84690497619389532424639333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112920663492519376566185777 84690497619389532424639333)
          ·
            refine ⟨15879468303635537329619875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84690497619389532424639333 15879468303635537329619875)
            ·
              refine ⟨23819202455453305994429813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15879468303635537329619875 23819202455453305994429813)
              ·
                refine ⟨2233050230198747436977795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23819202455453305994429813 2233050230198747436977795)
                ·
                  refine ⟨3349575345298121155466693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233050230198747436977795 3349575345298121155466693)
                  ·
                    refine ⟨628045377243397716650005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349575345298121155466693 628045377243397716650005)
                    ·
                      rfl

theorem cell22_1834671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_1834671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834671 prefixEnd_1834671 := by exact prefixLift 1834671
  have htrace : WordTrace (prefixWord ++ tailWord_1834671) baseStart_1834671 baseEnd_1834671 := by
    simpa [prefixWord, tailWord_1834671, baseEnd_1834671] using wordTrace_append hprefix tailTrace_1834671
  have hstable : (prefixWord ++ tailWord_1834671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834671).length < 2 ^ (prefixWord ++ tailWord_1834671).sum := by decide
  have hdescent : baseEnd_1834671 < baseStart_1834671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834699 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_1834699 : Nat := 118140960795 + 1834699 * 2 ^ 59
def prefixEnd_1834699 : Nat := 4983230072969 + 3 ^ 40 * 1834699 * 2
def baseEnd_1834699 : Nat := 628054962215614976949919

theorem tailTrace_1834699 : CollatzResearch.WordTrace tailWord_1834699 prefixEnd_1834699 628054962215614976949919 := by
  unfold tailWord_1834699
  simp only [CollatzResearch.WordTrace]
  refine ⟨66916969980206339487907151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44611313320137559658604767 66916969980206339487907151)
  ·
    refine ⟨100375454970309509231860727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66916969980206339487907151 100375454970309509231860727)
    ·
      refine ⟨150563182455464263847791091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100375454970309509231860727 150563182455464263847791091)
      ·
        refine ⟨225844773683196395771686637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150563182455464263847791091 225844773683196395771686637)
        ·
          refine ⟨84691790131198648414382489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225844773683196395771686637 84691790131198648414382489)
          ·
            refine ⟨63518842598398986310786867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84691790131198648414382489 63518842598398986310786867)
            ·
              refine ⟨95278263897598479466180301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63518842598398986310786867 95278263897598479466180301)
              ·
                refine ⟨35729348961599429799817613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95278263897598479466180301 35729348961599429799817613)
                ·
                  refine ⟨13398505860599786174931605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35729348961599429799817613 13398505860599786174931605)
                  ·
                    refine ⟨628054962215614976949919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13398505860599786174931605 628054962215614976949919)
                    ·
                      rfl

theorem cell22_1834699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_1834699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834699 prefixEnd_1834699 := by exact prefixLift 1834699
  have htrace : WordTrace (prefixWord ++ tailWord_1834699) baseStart_1834699 baseEnd_1834699 := by
    simpa [prefixWord, tailWord_1834699, baseEnd_1834699] using wordTrace_append hprefix tailTrace_1834699
  have hstable : (prefixWord ++ tailWord_1834699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834699).length < 2 ^ (prefixWord ++ tailWord_1834699).sum := by decide
  have hdescent : baseEnd_1834699 < baseStart_1834699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834733 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1834733 : Nat := 118140960795 + 1834733 * 2 ^ 59
def prefixEnd_1834733 : Nat := 4983230072969 + 3 ^ 40 * 1834733 * 2
def baseEnd_1834733 : Nat := 628066601110450221599815

theorem tailTrace_1834733 : CollatzResearch.WordTrace tailWord_1834733 prefixEnd_1834733 628066601110450221599815 := by
  unfold tailWord_1834733
  simp only [CollatzResearch.WordTrace]
  refine ⟨66918210062083163294644853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44612140041388775529763235 66918210062083163294644853)
  ·
    refine ⟨6273582193320296558872955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66918210062083163294644853 6273582193320296558872955)
    ·
      refine ⟨9410373289980444838309433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6273582193320296558872955 9410373289980444838309433)
      ·
        refine ⟨7057779967485333628732075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9410373289980444838309433 7057779967485333628732075)
        ·
          refine ⟨10586669951228000443098113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057779967485333628732075 10586669951228000443098113)
          ·
            refine ⟨7940002463421000332323585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10586669951228000443098113 7940002463421000332323585)
            ·
              refine ⟨5955001847565750249242689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940002463421000332323585 5955001847565750249242689)
              ·
                refine ⟨4466251385674312686932017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955001847565750249242689 4466251385674312686932017)
                ·
                  refine ⟨3349688539255734515199013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466251385674312686932017 3349688539255734515199013)
                  ·
                    refine ⟨628066601110450221599815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349688539255734515199013 628066601110450221599815)
                    ·
                      rfl

theorem cell22_1834733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1834733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834733 prefixEnd_1834733 := by exact prefixLift 1834733
  have htrace : WordTrace (prefixWord ++ tailWord_1834733) baseStart_1834733 baseEnd_1834733 := by
    simpa [prefixWord, tailWord_1834733, baseEnd_1834733] using wordTrace_append hprefix tailTrace_1834733
  have hstable : (prefixWord ++ tailWord_1834733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834733).length < 2 ^ (prefixWord ++ tailWord_1834733).sum := by decide
  have hdescent : baseEnd_1834733 < baseStart_1834733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834810 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_1834810 : Nat := 118140960795 + 1834810 * 2 ^ 59
def prefixEnd_1834810 : Nat := 4983230072969 + 3 ^ 40 * 1834810 * 2
def baseEnd_1834810 : Nat := 209364319928015895808193

theorem tailTrace_1834810 : CollatzResearch.WordTrace tailWord_1834810 prefixEnd_1834810 209364319928015895808193 := by
  unfold tailWord_1834810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16730254620701051361299471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44614012321869470296798589 16730254620701051361299471)
  ·
    refine ⟨25095381931051577041949207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16730254620701051361299471 25095381931051577041949207)
    ·
      refine ⟨37643072896577365562923811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25095381931051577041949207 37643072896577365562923811)
      ·
        refine ⟨56464609344866048344385717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37643072896577365562923811 56464609344866048344385717)
        ·
          refine ⟨5293557126081192032286161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56464609344866048344385717 5293557126081192032286161)
          ·
            refine ⟨3970167844560894024214621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5293557126081192032286161 3970167844560894024214621)
            ·
              refine ⟨1488812941710335259080483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3970167844560894024214621 1488812941710335259080483)
              ·
                refine ⟨2233219412565502888620725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488812941710335259080483 2233219412565502888620725)
                ·
                  refine ⟨209364319928015895808193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2233219412565502888620725 209364319928015895808193)
                  ·
                    rfl

theorem cell22_1834810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_1834810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834810 prefixEnd_1834810 := by exact prefixLift 1834810
  have htrace : WordTrace (prefixWord ++ tailWord_1834810) baseStart_1834810 baseEnd_1834810 := by
    simpa [prefixWord, tailWord_1834810, baseEnd_1834810] using wordTrace_append hprefix tailTrace_1834810
  have hstable : (prefixWord ++ tailWord_1834810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834810).length < 2 ^ (prefixWord ++ tailWord_1834810).sum := by decide
  have hdescent : baseEnd_1834810 < baseStart_1834810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834821 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 6]
def baseStart_1834821 : Nat := 118140960795 + 1834821 * 2 ^ 59
def prefixEnd_1834821 : Nat := 4983230072969 + 3 ^ 40 * 1834821 * 2
def baseEnd_1834821 : Nat := 209365575102949108466515

theorem tailTrace_1834821 : CollatzResearch.WordTrace tailWord_1834821 prefixEnd_1834821 209365575102949108466515 := by
  unfold tailWord_1834821
  simp only [CollatzResearch.WordTrace]
  refine ⟨66921419685764354323848317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44614279790509569549232211 66921419685764354323848317)
  ·
    refine ⟨25095532382161632871443119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66921419685764354323848317 25095532382161632871443119)
    ·
      refine ⟨37643298573242449307164679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25095532382161632871443119 37643298573242449307164679)
      ·
        refine ⟨56464947859863673960747019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37643298573242449307164679 56464947859863673960747019)
        ·
          refine ⟨84697421789795510941120529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56464947859863673960747019 84697421789795510941120529)
          ·
            refine ⟨63523066342346633205840397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84697421789795510941120529 63523066342346633205840397)
            ·
              refine ⟨23821149878379987452190149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63523066342346633205840397 23821149878379987452190149)
              ·
                refine ⟨4466465602196247647285653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23821149878379987452190149 4466465602196247647285653)
                ·
                  refine ⟨209365575102949108466515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4466465602196247647285653 209365575102949108466515)
                  ·
                    rfl

theorem cell22_1834821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_1834821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834821 prefixEnd_1834821 := by exact prefixLift 1834821
  have htrace : WordTrace (prefixWord ++ tailWord_1834821) baseStart_1834821 baseEnd_1834821 := by
    simpa [prefixWord, tailWord_1834821, baseEnd_1834821] using wordTrace_append hprefix tailTrace_1834821
  have hstable : (prefixWord ++ tailWord_1834821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834821).length < 2 ^ (prefixWord ++ tailWord_1834821).sum := by decide
  have hdescent : baseEnd_1834821 < baseStart_1834821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834823 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1834823 : Nat := 118140960795 + 1834823 * 2 ^ 59
def prefixEnd_1834823 : Nat := 4983230072969 + 3 ^ 40 * 1834823 * 2
def baseEnd_1834823 : Nat := 628097409949719986849539

theorem tailTrace_1834823 : CollatzResearch.WordTrace tailWord_1834823 prefixEnd_1834823 628097409949719986849539 := by
  unfold tailWord_1834823
  simp only [CollatzResearch.WordTrace]
  refine ⟨66921492631757108665421123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44614328421171405776947415 66921492631757108665421123)
  ·
    refine ⟨100382238947635662998131685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66921492631757108665421123 100382238947635662998131685)
    ·
      refine ⟨18821669802681686812149691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100382238947635662998131685 18821669802681686812149691)
      ·
        refine ⟨28232504704022530218224537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18821669802681686812149691 28232504704022530218224537)
        ·
          refine ⟨21174378528016897663668403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28232504704022530218224537 21174378528016897663668403)
          ·
            refine ⟨31761567792025346495502605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21174378528016897663668403 31761567792025346495502605)
            ·
              refine ⟨11910587922009504935813477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31761567792025346495502605 11910587922009504935813477)
              ·
                refine ⟨2233235235376782175465027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11910587922009504935813477 2233235235376782175465027)
                ·
                  refine ⟨3349852853065173263197541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233235235376782175465027 3349852853065173263197541)
                  ·
                    refine ⟨628097409949719986849539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349852853065173263197541 628097409949719986849539)
                    ·
                      rfl

theorem cell22_1834823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1834823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834823 prefixEnd_1834823 := by exact prefixLift 1834823
  have htrace : WordTrace (prefixWord ++ tailWord_1834823) baseStart_1834823 baseEnd_1834823 := by
    simpa [prefixWord, tailWord_1834823, baseEnd_1834823] using wordTrace_append hprefix tailTrace_1834823
  have hstable : (prefixWord ++ tailWord_1834823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834823).length < 2 ^ (prefixWord ++ tailWord_1834823).sum := by decide
  have hdescent : baseEnd_1834823 < baseStart_1834823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834896 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_1834896 : Nat := 118140960795 + 1834896 * 2 ^ 59
def prefixEnd_1834896 : Nat := 4983230072969 + 3 ^ 40 * 1834896 * 2
def baseEnd_1834896 : Nat := 628122399341572129774315

theorem tailTrace_1834896 : CollatzResearch.WordTrace tailWord_1834896 prefixEnd_1834896 628122399341572129774315 := by
  unfold tailWord_1834896
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462077580246321066414271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44616103440328428088552361 33462077580246321066414271)
  ·
    refine ⟨50193116370369481599621407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462077580246321066414271 50193116370369481599621407)
    ·
      refine ⟨75289674555554222399432111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193116370369481599621407 75289674555554222399432111)
      ·
        refine ⟨112934511833331333599148167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75289674555554222399432111 112934511833331333599148167)
        ·
          refine ⟨169401767749997000398722251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112934511833331333599148167 169401767749997000398722251)
          ·
            refine ⟨254102651624995500598083377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169401767749997000398722251 254102651624995500598083377)
            ·
              refine ⟨190576988718746625448562533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254102651624995500598083377 190576988718746625448562533)
              ·
                refine ⟨35733185384764992271605475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190576988718746625448562533 35733185384764992271605475)
                ·
                  refine ⟨53599778077147488407408213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35733185384764992271605475 53599778077147488407408213)
                  ·
                    refine ⟨628122399341572129774315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53599778077147488407408213 628122399341572129774315)
                    ·
                      rfl

theorem cell22_1834896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_1834896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834896 prefixEnd_1834896 := by exact prefixLift 1834896
  have htrace : WordTrace (prefixWord ++ tailWord_1834896) baseStart_1834896 baseEnd_1834896 := by
    simpa [prefixWord, tailWord_1834896, baseEnd_1834896] using wordTrace_append hprefix tailTrace_1834896
  have hstable : (prefixWord ++ tailWord_1834896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834896).length < 2 ^ (prefixWord ++ tailWord_1834896).sum := by decide
  have hdescent : baseEnd_1834896 < baseStart_1834896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834904 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_1834904 : Nat := 118140960795 + 1834904 * 2 ^ 59
def prefixEnd_1834904 : Nat := 4983230072969 + 3 ^ 40 * 1834904 * 2
def baseEnd_1834904 : Nat := 628125137905062775574291

theorem tailTrace_1834904 : CollatzResearch.WordTrace tailWord_1834904 prefixEnd_1834904 628125137905062775574291 := by
  unfold tailWord_1834904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462223472231829749559883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44616297962975772999413177 33462223472231829749559883)
  ·
    refine ⟨50193335208347744624339825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462223472231829749559883 50193335208347744624339825)
    ·
      refine ⟨37645001406260808468254869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50193335208347744624339825 37645001406260808468254869)
      ·
        refine ⟨1764609440918475396949447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37645001406260808468254869 1764609440918475396949447)
        ·
          refine ⟨2646914161377713095424171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764609440918475396949447 2646914161377713095424171)
          ·
            refine ⟨3970371242066569643136257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646914161377713095424171 3970371242066569643136257)
            ·
              refine ⟨2977778431549927232352193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970371242066569643136257 2977778431549927232352193)
              ·
                refine ⟨2233333823662445424264145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977778431549927232352193 2233333823662445424264145)
                ·
                  refine ⟨1675000367746834068198109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233333823662445424264145 1675000367746834068198109)
                  ·
                    refine ⟨628125137905062775574291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675000367746834068198109 628125137905062775574291)
                    ·
                      rfl

theorem cell22_1834904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_1834904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834904 prefixEnd_1834904 := by exact prefixLift 1834904
  have htrace : WordTrace (prefixWord ++ tailWord_1834904) baseStart_1834904 baseEnd_1834904 := by
    simpa [prefixWord, tailWord_1834904, baseEnd_1834904] using wordTrace_append hprefix tailTrace_1834904
  have hstable : (prefixWord ++ tailWord_1834904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834904).length < 2 ^ (prefixWord ++ tailWord_1834904).sum := by decide
  have hdescent : baseEnd_1834904 < baseStart_1834904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834990 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1834990 : Nat := 118140960795 + 1834990 * 2 ^ 59
def prefixEnd_1834990 : Nat := 4983230072969 + 3 ^ 40 * 1834990 * 2
def baseEnd_1834990 : Nat := 209384859154195739308009

theorem tailTrace_1834990 : CollatzResearch.WordTrace tailWord_1834990 prefixEnd_1834990 209384859154195739308009 := by
  unfold tailWord_1834990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365947952769012023343803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44618389081434730791166949 8365947952769012023343803)
  ·
    refine ⟨12548921929153518035015705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8365947952769012023343803 12548921929153518035015705)
    ·
      refine ⟨9411691446865138526261779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12548921929153518035015705 9411691446865138526261779)
      ·
        refine ⟨14117537170297707789392669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411691446865138526261779 14117537170297707789392669)
        ·
          refine ⟨5294076438861640421022251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14117537170297707789392669 5294076438861640421022251)
          ·
            refine ⟨7941114658292460631533377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294076438861640421022251 7941114658292460631533377)
            ·
              refine ⟨5955835993719345473650033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941114658292460631533377 5955835993719345473650033)
              ·
                refine ⟨4466876995289509105237525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955835993719345473650033 4466876995289509105237525)
                ·
                  refine ⟨209384859154195739308009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4466876995289509105237525 209384859154195739308009)
                  ·
                    rfl

theorem cell22_1834990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1834990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1834990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1834990 prefixEnd_1834990 := by exact prefixLift 1834990
  have htrace : WordTrace (prefixWord ++ tailWord_1834990) baseStart_1834990 baseEnd_1834990 := by
    simpa [prefixWord, tailWord_1834990, baseEnd_1834990] using wordTrace_append hprefix tailTrace_1834990
  have hstable : (prefixWord ++ tailWord_1834990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834990).length < 2 ^ (prefixWord ++ tailWord_1834990).sum := by decide
  have hdescent : baseEnd_1834990 < baseStart_1834990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835003 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_1835003 : Nat := 118140960795 + 1835003 * 2 ^ 59
def prefixEnd_1835003 : Nat := 4983230072969 + 3 ^ 40 * 1835003 * 2
def baseEnd_1835003 : Nat := 628159027628259517348987

theorem tailTrace_1835003 : CollatzResearch.WordTrace tailWord_1835003 prefixEnd_1835003 628159027628259517348987 := by
  unfold tailWord_1835003
  simp only [CollatzResearch.WordTrace]
  refine ⟨66928057771104999406973663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44618705180736666271315775 66928057771104999406973663)
  ·
    refine ⟨100392086656657499110460495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66928057771104999406973663 100392086656657499110460495)
    ·
      refine ⟨150588129984986248665690743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100392086656657499110460495 150588129984986248665690743)
      ·
        refine ⟨225882194977479372998536115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150588129984986248665690743 225882194977479372998536115)
        ·
          refine ⟨338823292466219059497804173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225882194977479372998536115 338823292466219059497804173)
          ·
            refine ⟨127058734674832147311676565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338823292466219059497804173 127058734674832147311676565)
            ·
              refine ⟨5955878187882756905234839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127058734674832147311676565 5955878187882756905234839)
              ·
                refine ⟨8933817281824135357852259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955878187882756905234839 8933817281824135357852259)
                ·
                  refine ⟨13400725922736203036778389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933817281824135357852259 13400725922736203036778389)
                  ·
                    refine ⟨628159027628259517348987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13400725922736203036778389 628159027628259517348987)
                    ·
                      rfl

theorem cell22_1835003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_1835003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835003 prefixEnd_1835003 := by exact prefixLift 1835003
  have htrace : WordTrace (prefixWord ++ tailWord_1835003) baseStart_1835003 baseEnd_1835003 := by
    simpa [prefixWord, tailWord_1835003, baseEnd_1835003] using wordTrace_append hprefix tailTrace_1835003
  have hstable : (prefixWord ++ tailWord_1835003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835003).length < 2 ^ (prefixWord ++ tailWord_1835003).sum := by decide
  have hdescent : baseEnd_1835003 < baseStart_1835003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835005 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1835005 : Nat := 118140960795 + 1835005 * 2 ^ 59
def prefixEnd_1835005 : Nat := 4983230072969 + 3 ^ 40 * 1835005 * 2
def baseEnd_1835005 : Nat := 628159712269132178798981

theorem tailTrace_1835005 : CollatzResearch.WordTrace tailWord_1835005 prefixEnd_1835005 628159712269132178798981 := by
  unfold tailWord_1835005
  simp only [CollatzResearch.WordTrace]
  refine ⟨66928130717097753748546469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44618753811398502499030979 66928130717097753748546469)
  ·
    refine ⟨12549024509455828827852463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66928130717097753748546469 12549024509455828827852463)
    ·
      refine ⟨18823536764183743241778695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549024509455828827852463 18823536764183743241778695)
      ·
        refine ⟨28235305146275614862668043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18823536764183743241778695 28235305146275614862668043)
        ·
          refine ⟨42352957719413422294002065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28235305146275614862668043 42352957719413422294002065)
          ·
            refine ⟨31764718289560066720501549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42352957719413422294002065 31764718289560066720501549)
            ·
              refine ⟨11911769358585025020188081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31764718289560066720501549 11911769358585025020188081)
              ·
                refine ⟨8933827018938768765141061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11911769358585025020188081 8933827018938768765141061)
                ·
                  refine ⟨1675092566051019143463949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8933827018938768765141061 1675092566051019143463949)
                  ·
                    refine ⟨628159712269132178798981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675092566051019143463949 628159712269132178798981)
                    ·
                      rfl

theorem cell22_1835005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1835005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835005 prefixEnd_1835005 := by exact prefixLift 1835005
  have htrace : WordTrace (prefixWord ++ tailWord_1835005) baseStart_1835005 baseEnd_1835005 := by
    simpa [prefixWord, tailWord_1835005, baseEnd_1835005] using wordTrace_append hprefix tailTrace_1835005
  have hstable : (prefixWord ++ tailWord_1835005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835005).length < 2 ^ (prefixWord ++ tailWord_1835005).sum := by decide
  have hdescent : baseEnd_1835005 < baseStart_1835005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835020 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_1835020 : Nat := 118140960795 + 1835020 * 2 ^ 59
def prefixEnd_1835020 : Nat := 4983230072969 + 3 ^ 40 * 1835020 * 2
def baseEnd_1835020 : Nat := 628164847075677139673935

theorem tailTrace_1835020 : CollatzResearch.WordTrace tailWord_1835020 prefixEnd_1835020 628164847075677139673935 := by
  unfold tailWord_1835020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464338906021705655171257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44619118541362274206895009 33464338906021705655171257)
  ·
    refine ⟨25098254179516279241378443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33464338906021705655171257 25098254179516279241378443)
    ·
      refine ⟨37647381269274418862067665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25098254179516279241378443 37647381269274418862067665)
      ·
        refine ⟨28235535951955814146550749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37647381269274418862067665 28235535951955814146550749)
        ·
          refine ⟨10588325981983430304956531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28235535951955814146550749 10588325981983430304956531)
          ·
            refine ⟨15882488972975145457434797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588325981983430304956531 15882488972975145457434797)
            ·
              refine ⟨5955933364865679546538049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15882488972975145457434797 5955933364865679546538049)
              ·
                refine ⟨4466950023649259659903537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955933364865679546538049 4466950023649259659903537)
                ·
                  refine ⟨3350212517736944744927653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466950023649259659903537 3350212517736944744927653)
                  ·
                    refine ⟨628164847075677139673935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350212517736944744927653 628164847075677139673935)
                    ·
                      rfl

theorem cell22_1835020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_1835020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835020 prefixEnd_1835020 := by exact prefixLift 1835020
  have htrace : WordTrace (prefixWord ++ tailWord_1835020) baseStart_1835020 baseEnd_1835020 := by
    simpa [prefixWord, tailWord_1835020, baseEnd_1835020] using wordTrace_append hprefix tailTrace_1835020
  have hstable : (prefixWord ++ tailWord_1835020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835020).length < 2 ^ (prefixWord ++ tailWord_1835020).sum := by decide
  have hdescent : baseEnd_1835020 < baseStart_1835020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835022 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1835022 : Nat := 118140960795 + 1835022 * 2 ^ 59
def prefixEnd_1835022 : Nat := 4983230072969 + 3 ^ 40 * 1835022 * 2
def baseEnd_1835022 : Nat := 628165531716549801123929

theorem tailTrace_1835022 : CollatzResearch.WordTrace tailWord_1835022 prefixEnd_1835022 628165531716549801123929 := by
  unfold tailWord_1835022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366093844754520706489415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44619167172024110434610213 8366093844754520706489415)
  ·
    refine ⟨12549140767131781059734123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366093844754520706489415 12549140767131781059734123)
    ·
      refine ⟨18823711150697671589601185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549140767131781059734123 18823711150697671589601185)
      ·
        refine ⟨14117783363023253692200889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18823711150697671589601185 14117783363023253692200889)
        ·
          refine ⟨10588337522267440269150667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14117783363023253692200889 10588337522267440269150667)
          ·
            refine ⟨15882506283401160403726001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588337522267440269150667 15882506283401160403726001)
            ·
              refine ⟨11911879712550870302794501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15882506283401160403726001 11911879712550870302794501)
              ·
                refine ⟨2233477446103288181773969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11911879712550870302794501 2233477446103288181773969)
                ·
                  refine ⟨1675108084577466136330477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233477446103288181773969 1675108084577466136330477)
                  ·
                    refine ⟨628165531716549801123929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675108084577466136330477 628165531716549801123929)
                    ·
                      rfl

theorem cell22_1835022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1835022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835022 prefixEnd_1835022 := by exact prefixLift 1835022
  have htrace : WordTrace (prefixWord ++ tailWord_1835022) baseStart_1835022 baseEnd_1835022 := by
    simpa [prefixWord, tailWord_1835022, baseEnd_1835022] using wordTrace_append hprefix tailTrace_1835022
  have hstable : (prefixWord ++ tailWord_1835022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835022).length < 2 ^ (prefixWord ++ tailWord_1835022).sum := by decide
  have hdescent : baseEnd_1835022 < baseStart_1835022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835063 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 9]
def baseStart_1835063 : Nat := 118140960795 + 1835063 * 2 ^ 59
def prefixEnd_1835063 : Nat := 4983230072969 + 3 ^ 40 * 1835063 * 2
def baseEnd_1835063 : Nat := 209393188951479786949601

theorem tailTrace_1835063 : CollatzResearch.WordTrace tailWord_1835063 prefixEnd_1835063 209393188951479786949601 := by
  unfold tailWord_1835063
  simp only [CollatzResearch.WordTrace]
  refine ⟨66930246150887629654157843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44620164100591753102771895 66930246150887629654157843)
  ·
    refine ⟨100395369226331444481236765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66930246150887629654157843 100395369226331444481236765)
    ·
      refine ⟨37648263459874291680463787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100395369226331444481236765 37648263459874291680463787)
      ·
        refine ⟨56472395189811437520695681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37648263459874291680463787 56472395189811437520695681)
        ·
          refine ⟨42354296392358578140521761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56472395189811437520695681 42354296392358578140521761)
          ·
            refine ⟨31765722294268933605391321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42354296392358578140521761 31765722294268933605391321)
            ·
              refine ⟨23824291720701700204043491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31765722294268933605391321 23824291720701700204043491)
              ·
                refine ⟨35736437581052550306065237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23824291720701700204043491 35736437581052550306065237)
                ·
                  refine ⟨209393188951479786949601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35736437581052550306065237 209393188951479786949601)
                  ·
                    rfl

theorem cell22_1835063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_1835063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835063 prefixEnd_1835063 := by exact prefixLift 1835063
  have htrace : WordTrace (prefixWord ++ tailWord_1835063) baseStart_1835063 baseEnd_1835063 := by
    simpa [prefixWord, tailWord_1835063, baseEnd_1835063] using wordTrace_append hprefix tailTrace_1835063
  have hstable : (prefixWord ++ tailWord_1835063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835063).length < 2 ^ (prefixWord ++ tailWord_1835063).sum := by decide
  have hdescent : baseEnd_1835063 < baseStart_1835063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835127 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1835127 : Nat := 118140960795 + 1835127 * 2 ^ 59
def prefixEnd_1835127 : Nat := 4983230072969 + 3 ^ 40 * 1835127 * 2
def baseEnd_1835127 : Nat := 628201475362364527248607

theorem tailTrace_1835127 : CollatzResearch.WordTrace tailWord_1835127 prefixEnd_1835127 628201475362364527248607 := by
  unfold tailWord_1835127
  simp only [CollatzResearch.WordTrace]
  refine ⟨66932580422655768584487635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44621720281770512389658423 66932580422655768584487635)
  ·
    refine ⟨100398870633983652876731453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66932580422655768584487635 100398870633983652876731453)
    ·
      refine ⟨37649576487743869828774295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100398870633983652876731453 37649576487743869828774295)
      ·
        refine ⟨56474364731615804743161443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37649576487743869828774295 56474364731615804743161443)
        ·
          refine ⟨84711547097423707114742165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56474364731615804743161443 84711547097423707114742165)
          ·
            refine ⟨3970853770191736271003539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84711547097423707114742165 3970853770191736271003539)
            ·
              refine ⟨5956280655287604406505309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970853770191736271003539 5956280655287604406505309)
              ·
                refine ⟨2233605245732851652439491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5956280655287604406505309 2233605245732851652439491)
                ·
                  refine ⟨3350407868599277478659237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233605245732851652439491 3350407868599277478659237)
                  ·
                    refine ⟨628201475362364527248607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350407868599277478659237 628201475362364527248607)
                    ·
                      rfl

theorem cell22_1835127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1835127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835127 prefixEnd_1835127 := by exact prefixLift 1835127
  have htrace : WordTrace (prefixWord ++ tailWord_1835127) baseStart_1835127 baseEnd_1835127 := by
    simpa [prefixWord, tailWord_1835127, baseEnd_1835127] using wordTrace_append hprefix tailTrace_1835127
  have hstable : (prefixWord ++ tailWord_1835127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835127).length < 2 ^ (prefixWord ++ tailWord_1835127).sum := by decide
  have hdescent : baseEnd_1835127 < baseStart_1835127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835296 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_1835296 : Nat := 118140960795 + 1835296 * 2 ^ 59
def prefixEnd_1835296 : Nat := 4983230072969 + 3 ^ 40 * 1835296 * 2
def baseEnd_1835296 : Nat := 628259327516104419773089

theorem tailTrace_1835296 : CollatzResearch.WordTrace tailWord_1835296 prefixEnd_1835296 628259327516104419773089 := by
  unfold tailWord_1835296
  simp only [CollatzResearch.WordTrace]
  refine ⟨33469372179521755223694871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44625829572695673631593161 33469372179521755223694871)
  ·
    refine ⟨50204058269282632835542307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33469372179521755223694871 50204058269282632835542307)
    ·
      refine ⟨75306087403923949253313461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50204058269282632835542307 75306087403923949253313461)
      ·
        refine ⟨7059945694117870242498137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75306087403923949253313461 7059945694117870242498137)
        ·
          refine ⟨5294959270588402681873603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7059945694117870242498137 5294959270588402681873603)
          ·
            refine ⟨7942438905882604022810405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294959270588402681873603 7942438905882604022810405)
            ·
              refine ⟨1489207294852988254276951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7942438905882604022810405 1489207294852988254276951)
              ·
                refine ⟨2233810942279482381415427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489207294852988254276951 2233810942279482381415427)
                ·
                  refine ⟨3350716413419223572123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233810942279482381415427 3350716413419223572123141)
                  ·
                    refine ⟨628259327516104419773089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3350716413419223572123141 628259327516104419773089)
                    ·
                      rfl

theorem cell22_1835296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_1835296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835296 prefixEnd_1835296 := by exact prefixLift 1835296
  have htrace : WordTrace (prefixWord ++ tailWord_1835296) baseStart_1835296 baseEnd_1835296 := by
    simpa [prefixWord, tailWord_1835296, baseEnd_1835296] using wordTrace_append hprefix tailTrace_1835296
  have hstable : (prefixWord ++ tailWord_1835296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835296).length < 2 ^ (prefixWord ++ tailWord_1835296).sum := by decide
  have hdescent : baseEnd_1835296 < baseStart_1835296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835326 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1835326 : Nat := 118140960795 + 1835326 * 2 ^ 59
def prefixEnd_1835326 : Nat := 4983230072969 + 3 ^ 40 * 1835326 * 2
def baseEnd_1835326 : Nat := 628269597129194341522997

theorem tailTrace_1835326 : CollatzResearch.WordTrace tailWord_1835326 prefixEnd_1835326 628269597129194341522997 := by
  unfold tailWord_1835326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367479818616853196372729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44626559032623217047321221 8367479818616853196372729)
  ·
    refine ⟨6275609863962639897279547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8367479818616853196372729 6275609863962639897279547)
    ·
      refine ⟨9413414795943959845919321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6275609863962639897279547 9413414795943959845919321)
      ·
        refine ⟨7060061096957969884439491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9413414795943959845919321 7060061096957969884439491)
        ·
          refine ⟨10590091645436954826659237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060061096957969884439491 10590091645436954826659237)
          ·
            refine ⟨1985642183519429029998607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10590091645436954826659237 1985642183519429029998607)
            ·
              refine ⟨2978463275279143544997911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985642183519429029998607 2978463275279143544997911)
              ·
                refine ⟨4467694912918715317496867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978463275279143544997911 4467694912918715317496867)
                ·
                  refine ⟨6701542369378072976245301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467694912918715317496867 6701542369378072976245301)
                  ·
                    refine ⟨628269597129194341522997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6701542369378072976245301 628269597129194341522997)
                    ·
                      rfl

theorem cell22_1835326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1835326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835326 prefixEnd_1835326 := by exact prefixLift 1835326
  have htrace : WordTrace (prefixWord ++ tailWord_1835326) baseStart_1835326 baseEnd_1835326 := by
    simpa [prefixWord, tailWord_1835326, baseEnd_1835326] using wordTrace_append hprefix tailTrace_1835326
  have hstable : (prefixWord ++ tailWord_1835326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835326).length < 2 ^ (prefixWord ++ tailWord_1835326).sum := by decide
  have hdescent : baseEnd_1835326 < baseStart_1835326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835356 : List Nat := [2, 2, 4, 3, 1, 2, 8]
def baseStart_1835356 : Nat := 118140960795 + 1835356 * 2 ^ 59
def prefixEnd_1835356 : Nat := 4983230072969 + 3 ^ 40 * 1835356 * 2
def baseEnd_1835356 : Nat := 23269624694158676417515

theorem tailTrace_1835356 : CollatzResearch.WordTrace tailWord_1835356 prefixEnd_1835356 23269624694158676417515 := by
  unfold tailWord_1835356
  simp only [CollatzResearch.WordTrace]
  refine ⟨33470466369413070347286961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44627288492550760463049281 33470466369413070347286961)
  ·
    refine ⟨25102849777059802760465221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33470466369413070347286961 25102849777059802760465221)
    ·
      refine ⟨4706784333198713017587229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25102849777059802760465221 4706784333198713017587229)
      ·
        refine ⟨1765044124949517381595211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4706784333198713017587229 1765044124949517381595211)
        ·
          refine ⟨2647566187424276072392817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765044124949517381595211 2647566187424276072392817)
          ·
            refine ⟨1985674640568207054294613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647566187424276072392817 1985674640568207054294613)
            ·
              refine ⟨23269624694158676417515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1985674640568207054294613 23269624694158676417515)
              ·
                rfl

theorem cell22_1835356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 8].length) (baseStart_1835356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835356 prefixEnd_1835356 := by exact prefixLift 1835356
  have htrace : WordTrace (prefixWord ++ tailWord_1835356) baseStart_1835356 baseEnd_1835356 := by
    simpa [prefixWord, tailWord_1835356, baseEnd_1835356] using wordTrace_append hprefix tailTrace_1835356
  have hstable : (prefixWord ++ tailWord_1835356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835356).length < 2 ^ (prefixWord ++ tailWord_1835356).sum := by decide
  have hdescent : baseEnd_1835356 < baseStart_1835356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835422 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1835422 : Nat := 118140960795 + 1835422 * 2 ^ 59
def prefixEnd_1835422 : Nat := 4983230072969 + 3 ^ 40 * 1835422 * 2
def baseEnd_1835422 : Nat := 628302459891082091122703

theorem tailTrace_1835422 : CollatzResearch.WordTrace tailWord_1835422 prefixEnd_1835422 628302459891082091122703 := by
  unfold tailWord_1835422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367917494573379245809565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44628893304391355977651013 8367917494573379245809565)
  ·
    refine ⟨3137969060465017217178587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8367917494573379245809565 3137969060465017217178587)
    ·
      refine ⟨4706953590697525825767881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137969060465017217178587 4706953590697525825767881)
      ·
        refine ⟨3530215193023144369325911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4706953590697525825767881 3530215193023144369325911)
        ·
          refine ⟨5295322789534716553988867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530215193023144369325911 5295322789534716553988867)
          ·
            refine ⟨7942984184302074830983301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295322789534716553988867 7942984184302074830983301)
            ·
              refine ⟨1489309534556639030809369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7942984184302074830983301 1489309534556639030809369)
              ·
                refine ⟨1116982150917479273107027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489309534556639030809369 1116982150917479273107027)
                ·
                  refine ⟨1675473226376218909660541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116982150917479273107027 1675473226376218909660541)
                  ·
                    refine ⟨628302459891082091122703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675473226376218909660541 628302459891082091122703)
                    ·
                      rfl

theorem cell22_1835422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1835422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835422 prefixEnd_1835422 := by exact prefixLift 1835422
  have htrace : WordTrace (prefixWord ++ tailWord_1835422) baseStart_1835422 baseEnd_1835422 := by
    simpa [prefixWord, tailWord_1835422, baseEnd_1835422] using wordTrace_append hprefix tailTrace_1835422
  have hstable : (prefixWord ++ tailWord_1835422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835422).length < 2 ^ (prefixWord ++ tailWord_1835422).sum := by decide
  have hdescent : baseEnd_1835422 < baseStart_1835422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835478 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1835478 : Nat := 118140960795 + 1835478 * 2 ^ 59
def prefixEnd_1835478 : Nat := 4983230072969 + 3 ^ 40 * 1835478 * 2
def baseEnd_1835478 : Nat := 628321629835516611722531

theorem tailTrace_1835478 : CollatzResearch.WordTrace tailWord_1835478 prefixEnd_1835478 628321629835516611722531 := by
  unfold tailWord_1835478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184086402774009720657193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44630254962922770353676725 4184086402774009720657193)
  ·
    refine ⟨3138064802080507290492895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4184086402774009720657193 3138064802080507290492895)
    ·
      refine ⟨4707097203120760935739343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138064802080507290492895 4707097203120760935739343)
      ·
        refine ⟨7060645804681141403609015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707097203120760935739343 7060645804681141403609015)
        ·
          refine ⟨10590968707021712105413523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060645804681141403609015 10590968707021712105413523)
          ·
            refine ⟨15886453060532568158120285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590968707021712105413523 15886453060532568158120285)
            ·
              refine ⟨5957419897699713059295107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15886453060532568158120285 5957419897699713059295107)
              ·
                refine ⟨8936129846549569588942661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957419897699713059295107 8936129846549569588942661)
                ·
                  refine ⟨1675524346228044297926749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8936129846549569588942661 1675524346228044297926749)
                  ·
                    refine ⟨628321629835516611722531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675524346228044297926749 628321629835516611722531)
                    ·
                      rfl

theorem cell22_1835478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1835478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835478 prefixEnd_1835478 := by exact prefixLift 1835478
  have htrace : WordTrace (prefixWord ++ tailWord_1835478) baseStart_1835478 baseEnd_1835478 := by
    simpa [prefixWord, tailWord_1835478, baseEnd_1835478] using wordTrace_append hprefix tailTrace_1835478
  have hstable : (prefixWord ++ tailWord_1835478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835478).length < 2 ^ (prefixWord ++ tailWord_1835478).sum := by decide
  have hdescent : baseEnd_1835478 < baseStart_1835478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835540 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1835540 : Nat := 118140960795 + 1835540 * 2 ^ 59
def prefixEnd_1835540 : Nat := 4983230072969 + 3 ^ 40 * 1835540 * 2
def baseEnd_1835540 : Nat := 628342853702569116672341

theorem tailTrace_1835540 : CollatzResearch.WordTrace tailWord_1835540 prefixEnd_1835540 628342853702569116672341 := by
  unfold tailWord_1835540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33473821885079770059636037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44631762513439693412848049 33473821885079770059636037)
  ·
    refine ⟨6276341603452456886181757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33473821885079770059636037 6276341603452456886181757)
    ·
      refine ⟨2353628101294671332318159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6276341603452456886181757 2353628101294671332318159)
      ·
        refine ⟨3530442151942006998477239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353628101294671332318159 3530442151942006998477239)
        ·
          refine ⟨5295663227913010497715859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530442151942006998477239 5295663227913010497715859)
          ·
            refine ⟨7943494841869515746573789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295663227913010497715859 7943494841869515746573789)
            ·
              refine ⟨2978810565701068404965171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7943494841869515746573789 2978810565701068404965171)
              ·
                refine ⟨4468215848551602607447757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978810565701068404965171 4468215848551602607447757)
                ·
                  refine ⟨1675580943206850977792909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4468215848551602607447757 1675580943206850977792909)
                  ·
                    refine ⟨628342853702569116672341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675580943206850977792909 628342853702569116672341)
                    ·
                      rfl

theorem cell22_1835540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1835540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835540 prefixEnd_1835540 := by exact prefixLift 1835540
  have htrace : WordTrace (prefixWord ++ tailWord_1835540) baseStart_1835540 baseEnd_1835540 := by
    simpa [prefixWord, tailWord_1835540, baseEnd_1835540] using wordTrace_append hprefix tailTrace_1835540
  have hstable : (prefixWord ++ tailWord_1835540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835540).length < 2 ^ (prefixWord ++ tailWord_1835540).sum := by decide
  have hdescent : baseEnd_1835540 < baseStart_1835540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835564 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1835564 : Nat := 118140960795 + 1835564 * 2 ^ 59
def prefixEnd_1835564 : Nat := 4983230072969 + 3 ^ 40 * 1835564 * 2
def baseEnd_1835564 : Nat := 209450356464347018024089

theorem tailTrace_1835564 : CollatzResearch.WordTrace tailWord_1835564 prefixEnd_1835564 209450356464347018024089 := by
  unfold tailWord_1835564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33474259561036296109072873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44632346081381728145430497 33474259561036296109072873)
  ·
    refine ⟨25105694670777222081804655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33474259561036296109072873 25105694670777222081804655)
    ·
      refine ⟨37658542006165833122706983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25105694670777222081804655 37658542006165833122706983)
      ·
        refine ⟨56487813009248749684060475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37658542006165833122706983 56487813009248749684060475)
        ·
          refine ⟨84731719513873124526090713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56487813009248749684060475 84731719513873124526090713)
          ·
            refine ⟨63548789635404843394568035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84731719513873124526090713 63548789635404843394568035)
            ·
              refine ⟨95323184453107265091852053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63548789635404843394568035 95323184453107265091852053)
              ·
                refine ⟨4468274271239403051180565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95323184453107265091852053 4468274271239403051180565)
                ·
                  refine ⟨209450356464347018024089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4468274271239403051180565 209450356464347018024089)
                  ·
                    rfl

theorem cell22_1835564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1835564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835564 prefixEnd_1835564 := by exact prefixLift 1835564
  have htrace : WordTrace (prefixWord ++ tailWord_1835564) baseStart_1835564 baseEnd_1835564 := by
    simpa [prefixWord, tailWord_1835564, baseEnd_1835564] using wordTrace_append hprefix tailTrace_1835564
  have hstable : (prefixWord ++ tailWord_1835564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835564).length < 2 ^ (prefixWord ++ tailWord_1835564).sum := by decide
  have hdescent : baseEnd_1835564 < baseStart_1835564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835583 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 1, 4]
def baseStart_1835583 : Nat := 118140960795 + 1835583 * 2 ^ 59
def prefixEnd_1835583 : Nat := 4983230072969 + 3 ^ 40 * 1835583 * 2
def baseEnd_1835583 : Nat := 628357573481331337847209

theorem tailTrace_1835583 : CollatzResearch.WordTrace tailWord_1835583 prefixEnd_1835583 628357573481331337847209 := by
  unfold tailWord_1835583
  simp only [CollatzResearch.WordTrace]
  refine ⟨66949212109003758463087403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44632808072669172308724935 66949212109003758463087403)
  ·
    refine ⟨100423818163505637694631105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66949212109003758463087403 100423818163505637694631105)
    ·
      refine ⟨75317863622629228270973329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100423818163505637694631105 75317863622629228270973329)
      ·
        refine ⟨56488397716971921203229997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75317863622629228270973329 56488397716971921203229997)
        ·
          refine ⟨21183149143864470451211249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56488397716971921203229997 21183149143864470451211249)
          ·
            refine ⟨15887361857898352838408437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21183149143864470451211249 15887361857898352838408437)
            ·
              refine ⟨1489440174177970578600791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15887361857898352838408437 1489440174177970578600791)
              ·
                refine ⟨2234160261266955867901187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489440174177970578600791 2234160261266955867901187)
                ·
                  refine ⟨3351240391900433801851781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234160261266955867901187 3351240391900433801851781)
                  ·
                    refine ⟨628357573481331337847209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351240391900433801851781 628357573481331337847209)
                    ·
                      rfl

theorem cell22_1835583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_1835583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835583 prefixEnd_1835583 := by exact prefixLift 1835583
  have htrace : WordTrace (prefixWord ++ tailWord_1835583) baseStart_1835583 baseEnd_1835583 := by
    simpa [prefixWord, tailWord_1835583, baseEnd_1835583] using wordTrace_append hprefix tailTrace_1835583
  have hstable : (prefixWord ++ tailWord_1835583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835583).length < 2 ^ (prefixWord ++ tailWord_1835583).sum := by decide
  have hdescent : baseEnd_1835583 < baseStart_1835583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835735 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1835735 : Nat := 118140960795 + 1835735 * 2 ^ 59
def prefixEnd_1835735 : Nat := 4983230072969 + 3 ^ 40 * 1835735 * 2
def baseEnd_1835735 : Nat := 628409606187653608046743

theorem tailTrace_1835735 : CollatzResearch.WordTrace tailWord_1835735 prefixEnd_1835735 628409606187653608046743 := by
  unfold tailWord_1835735
  simp only [CollatzResearch.WordTrace]
  refine ⟨66954756004453088422620659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44636504002968725615080439 66954756004453088422620659)
  ·
    refine ⟨100432134006679632633930989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66954756004453088422620659 100432134006679632633930989)
    ·
      refine ⟨37662050252504862237724121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100432134006679632633930989 37662050252504862237724121)
      ·
        refine ⟨28246537689378646678293091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37662050252504862237724121 28246537689378646678293091)
        ·
          refine ⟨42369806534067970017439637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28246537689378646678293091 42369806534067970017439637)
          ·
            refine ⟨1986084681284436094567483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42369806534067970017439637 1986084681284436094567483)
            ·
              refine ⟨2979127021926654141851225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986084681284436094567483 2979127021926654141851225)
              ·
                refine ⟨2234345266444990606388419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979127021926654141851225 2234345266444990606388419)
                ·
                  refine ⟨3351517899667485909582629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234345266444990606388419 3351517899667485909582629)
                  ·
                    refine ⟨628409606187653608046743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351517899667485909582629 628409606187653608046743)
                    ·
                      rfl

theorem cell22_1835735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1835735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835735 prefixEnd_1835735 := by exact prefixLift 1835735
  have htrace : WordTrace (prefixWord ++ tailWord_1835735) baseStart_1835735 baseEnd_1835735 := by
    simpa [prefixWord, tailWord_1835735, baseEnd_1835735] using wordTrace_append hprefix tailTrace_1835735
  have hstable : (prefixWord ++ tailWord_1835735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835735).length < 2 ^ (prefixWord ++ tailWord_1835735).sum := by decide
  have hdescent : baseEnd_1835735 < baseStart_1835735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835748 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1835748 : Nat := 118140960795 + 1835748 * 2 ^ 59
def prefixEnd_1835748 : Nat := 4983230072969 + 3 ^ 40 * 1835748 * 2
def baseEnd_1835748 : Nat := 628414056353325907471703

theorem tailTrace_1835748 : CollatzResearch.WordTrace tailWord_1835748 prefixEnd_1835748 628414056353325907471703 := by
  unfold tailWord_1835748
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477615076702995821421949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44636820102270661095229265 33477615076702995821421949)
  ·
    refine ⟨12554105653763623433033231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33477615076702995821421949 12554105653763623433033231)
    ·
      refine ⟨18831158480645435149549847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12554105653763623433033231 18831158480645435149549847)
      ·
        refine ⟨28246737720968152724324771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18831158480645435149549847 28246737720968152724324771)
        ·
          refine ⟨42370106581452229086487157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28246737720968152724324771 42370106581452229086487157)
          ·
            refine ⟨3972197492011146476858171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42370106581452229086487157 3972197492011146476858171)
            ·
              refine ⟨5958296238016719715287257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972197492011146476858171 5958296238016719715287257)
              ·
                refine ⟨4468722178512539786465443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958296238016719715287257 4468722178512539786465443)
                ·
                  refine ⟨6703083267768809679698165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468722178512539786465443 6703083267768809679698165)
                  ·
                    refine ⟨628414056353325907471703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6703083267768809679698165 628414056353325907471703)
                    ·
                      rfl

theorem cell22_1835748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1835748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835748 prefixEnd_1835748 := by exact prefixLift 1835748
  have htrace : WordTrace (prefixWord ++ tailWord_1835748) baseStart_1835748 baseEnd_1835748 := by
    simpa [prefixWord, tailWord_1835748, baseEnd_1835748] using wordTrace_append hprefix tailTrace_1835748
  have hstable : (prefixWord ++ tailWord_1835748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835748).length < 2 ^ (prefixWord ++ tailWord_1835748).sum := by decide
  have hdescent : baseEnd_1835748 < baseStart_1835748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835752 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1835752 : Nat := 118140960795 + 1835752 * 2 ^ 59
def prefixEnd_1835752 : Nat := 4983230072969 + 3 ^ 40 * 1835752 * 2
def baseEnd_1835752 : Nat := 628415425635071230371691

theorem tailTrace_1835752 : CollatzResearch.WordTrace tailWord_1835752 prefixEnd_1835752 628415425635071230371691 := by
  unfold tailWord_1835752
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477688022695750162994755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44636917363594333550659673 33477688022695750162994755)
  ·
    refine ⟨50216532034043625244492133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33477688022695750162994755 50216532034043625244492133)
    ·
      refine ⟨9415599756383179733342275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50216532034043625244492133 9415599756383179733342275)
      ·
        refine ⟨14123399634574769600013413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9415599756383179733342275 14123399634574769600013413)
        ·
          refine ⟨2648137431482769300002515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14123399634574769600013413 2648137431482769300002515)
          ·
            refine ⟨3972206147224153950003773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648137431482769300002515 3972206147224153950003773)
            ·
              refine ⟨1489577305209057731251415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3972206147224153950003773 1489577305209057731251415)
              ·
                refine ⟨2234365957813586596877123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489577305209057731251415 2234365957813586596877123)
                ·
                  refine ⟨3351548936720379895315685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234365957813586596877123 3351548936720379895315685)
                  ·
                    refine ⟨628415425635071230371691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351548936720379895315685 628415425635071230371691)
                    ·
                      rfl

theorem cell22_1835752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1835752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835752 prefixEnd_1835752 := by exact prefixLift 1835752
  have htrace : WordTrace (prefixWord ++ tailWord_1835752) baseStart_1835752 baseEnd_1835752 := by
    simpa [prefixWord, tailWord_1835752, baseEnd_1835752] using wordTrace_append hprefix tailTrace_1835752
  have hstable : (prefixWord ++ tailWord_1835752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835752).length < 2 ^ (prefixWord ++ tailWord_1835752).sum := by decide
  have hdescent : baseEnd_1835752 < baseStart_1835752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835791 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_1835791 : Nat := 118140960795 + 1835791 * 2 ^ 59
def prefixEnd_1835791 : Nat := 4983230072969 + 3 ^ 40 * 1835791 * 2
def baseEnd_1835791 : Nat := 628428776132088128646571

theorem tailTrace_1835791 : CollatzResearch.WordTrace tailWord_1835791 prefixEnd_1835791 628428776132088128646571 := by
  unfold tailWord_1835791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66956798492250209986659227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44637865661500139991106151 66956798492250209986659227)
  ·
    refine ⟨100435197738375314979988841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66956798492250209986659227 100435197738375314979988841)
    ·
      refine ⟨75326398303781486234991631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100435197738375314979988841 75326398303781486234991631)
      ·
        refine ⟨112989597455672229352487447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75326398303781486234991631 112989597455672229352487447)
        ·
          refine ⟨169484396183508344028731171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112989597455672229352487447 169484396183508344028731171)
          ·
            refine ⟨254226594275262516043096757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169484396183508344028731171 254226594275262516043096757)
            ·
              refine ⟨23833743213305860879040321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254226594275262516043096757 23833743213305860879040321)
              ·
                refine ⟨17875307409979395659280241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23833743213305860879040321 17875307409979395659280241)
                ·
                  refine ⟨13406480557484546744460181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17875307409979395659280241 13406480557484546744460181)
                  ·
                    refine ⟨628428776132088128646571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13406480557484546744460181 628428776132088128646571)
                    ·
                      rfl

theorem cell22_1835791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_1835791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835791 prefixEnd_1835791 := by exact prefixLift 1835791
  have htrace : WordTrace (prefixWord ++ tailWord_1835791) baseStart_1835791 baseEnd_1835791 := by
    simpa [prefixWord, tailWord_1835791, baseEnd_1835791] using wordTrace_append hprefix tailTrace_1835791
  have hstable : (prefixWord ++ tailWord_1835791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835791).length < 2 ^ (prefixWord ++ tailWord_1835791).sum := by decide
  have hdescent : baseEnd_1835791 < baseStart_1835791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835793 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_1835793 : Nat := 118140960795 + 1835793 * 2 ^ 59
def prefixEnd_1835793 : Nat := 4983230072969 + 3 ^ 40 * 1835793 * 2
def baseEnd_1835793 : Nat := 628429460772960790096565

theorem tailTrace_1835793 : CollatzResearch.WordTrace tailWord_1835793 prefixEnd_1835793 628429460772960790096565 := by
  unfold tailWord_1835793
  simp only [CollatzResearch.WordTrace]
  refine ⟨66956871438242964328232033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44637914292161976218821355 66956871438242964328232033)
  ·
    refine ⟨50217653578682223246174025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66956871438242964328232033 50217653578682223246174025)
    ·
      refine ⟨37663240184011667434630519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50217653578682223246174025 37663240184011667434630519)
      ·
        refine ⟨56494860276017501151945779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37663240184011667434630519 56494860276017501151945779)
        ·
          refine ⟨84742290414026251727918669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56494860276017501151945779 84742290414026251727918669)
          ·
            refine ⟨31778358905259844397969501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84742290414026251727918669 31778358905259844397969501)
            ·
              refine ⟨11916884589472441649238563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31778358905259844397969501 11916884589472441649238563)
              ·
                refine ⟨17875326884208662473857845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916884589472441649238563 17875326884208662473857845)
                ·
                  refine ⟨1675811895394562106924173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17875326884208662473857845 1675811895394562106924173)
                  ·
                    refine ⟨628429460772960790096565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675811895394562106924173 628429460772960790096565)
                    ·
                      rfl

theorem cell22_1835793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_1835793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835793 prefixEnd_1835793 := by exact prefixLift 1835793
  have htrace : WordTrace (prefixWord ++ tailWord_1835793) baseStart_1835793 baseEnd_1835793 := by
    simpa [prefixWord, tailWord_1835793, baseEnd_1835793] using wordTrace_append hprefix tailTrace_1835793
  have hstable : (prefixWord ++ tailWord_1835793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835793).length < 2 ^ (prefixWord ++ tailWord_1835793).sum := by decide
  have hdescent : baseEnd_1835793 < baseStart_1835793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835827 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 1, 3]
def baseStart_1835827 : Nat := 118140960795 + 1835827 * 2 ^ 59
def prefixEnd_1835827 : Nat := 4983230072969 + 3 ^ 40 * 1835827 * 2
def baseEnd_1835827 : Nat := 628441099667796034746461

theorem tailTrace_1835827 : CollatzResearch.WordTrace tailWord_1835827 prefixEnd_1835827 628441099667796034746461 := by
  unfold tailWord_1835827
  simp only [CollatzResearch.WordTrace]
  refine ⟨66958111520119788134969735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44638741013413192089979823 66958111520119788134969735)
  ·
    refine ⟨100437167280179682202454603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66958111520119788134969735 100437167280179682202454603)
    ·
      refine ⟨150655750920269523303681905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100437167280179682202454603 150655750920269523303681905)
      ·
        refine ⟨112991813190202142477761429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150655750920269523303681905 112991813190202142477761429)
        ·
          refine ⟨5296491243290725428645067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112991813190202142477761429 5296491243290725428645067)
          ·
            refine ⟨7944736864936088142967601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296491243290725428645067 7944736864936088142967601)
            ·
              refine ⟨5958552648702066107225701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944736864936088142967601 5958552648702066107225701)
              ·
                refine ⟨1117228621631637395104819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5958552648702066107225701 1117228621631637395104819)
                ·
                  refine ⟨1675842932447456092657229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117228621631637395104819 1675842932447456092657229)
                  ·
                    refine ⟨628441099667796034746461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675842932447456092657229 628441099667796034746461)
                    ·
                      rfl

theorem cell22_1835827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 3].length) (baseStart_1835827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835827 prefixEnd_1835827 := by exact prefixLift 1835827
  have htrace : WordTrace (prefixWord ++ tailWord_1835827) baseStart_1835827 baseEnd_1835827 := by
    simpa [prefixWord, tailWord_1835827, baseEnd_1835827] using wordTrace_append hprefix tailTrace_1835827
  have hstable : (prefixWord ++ tailWord_1835827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835827).length < 2 ^ (prefixWord ++ tailWord_1835827).sum := by decide
  have hdescent : baseEnd_1835827 < baseStart_1835827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835846 : List Nat := [6, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1835846 : Nat := 118140960795 + 1835846 * 2 ^ 59
def prefixEnd_1835846 : Nat := 4983230072969 + 3 ^ 40 * 1835846 * 2
def baseEnd_1835846 : Nat := 69827511528454035391267

theorem tailTrace_1835846 : CollatzResearch.WordTrace tailWord_1835846 prefixEnd_1835846 69827511528454035391267 := by
  unfold tailWord_1835846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092462640845342324372231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44639203004700636253274261 2092462640845342324372231)
  ·
    refine ⟨3138693961268013486558347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092462640845342324372231 3138693961268013486558347)
    ·
      refine ⟨4708040941902020229837521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138693961268013486558347 4708040941902020229837521)
      ·
        refine ⟨3531030706426515172378141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708040941902020229837521 3531030706426515172378141)
        ·
          refine ⟨1324136514909943189641803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3531030706426515172378141 1324136514909943189641803)
          ·
            refine ⟨1986204772364914784462705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324136514909943189641803 1986204772364914784462705)
            ·
              refine ⟨1489653579273686088347029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986204772364914784462705 1489653579273686088347029)
              ·
                refine ⟨69827511528454035391267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1489653579273686088347029 69827511528454035391267)
                ·
                  rfl

theorem cell22_1835846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1835846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835846 prefixEnd_1835846 := by exact prefixLift 1835846
  have htrace : WordTrace (prefixWord ++ tailWord_1835846) baseStart_1835846 baseEnd_1835846 := by
    simpa [prefixWord, tailWord_1835846, baseEnd_1835846] using wordTrace_append hprefix tailTrace_1835846
  have hstable : (prefixWord ++ tailWord_1835846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835846).length < 2 ^ (prefixWord ++ tailWord_1835846).sum := by decide
  have hdescent : baseEnd_1835846 < baseStart_1835846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
